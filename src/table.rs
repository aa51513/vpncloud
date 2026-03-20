// VpnCloud - Peer-to-Peer VPN
// Copyright (C) 2015-2021  Dennis Schwerdel
// This software is licensed under GPL-3 or newer (see LICENSE.md)

use fnv::FnvHasher;
use std::{
    cmp::min, collections::HashMap, hash::BuildHasherDefault, io, io::Write, marker::PhantomData, net::SocketAddr,
};

use crate::{
    types::{Address, Range, RangeList},
    util::{addr_nice, Duration, Time, TimeSource},
};

type Hash = BuildHasherDefault<FnvHasher>;

struct CacheValue {
    peer: SocketAddr,
    timeout: Time,
}

struct ClaimEntry {
    peer: SocketAddr,
    claim: Range,
    timeout: Time,
}

/// A node in the binary trie for CIDR-based claim lookup
struct TrieNode {
    /// Claim entry at this node (if this node represents a complete prefix)
    claim: Option<usize>, // Index into claims vector
    /// Child nodes: [0] for bit 0, [1] for bit 1
    children: [Option<Box<TrieNode>>; 2],
}

impl TrieNode {
    fn new() -> Self {
        Self { claim: None, children: [None, None] }
    }
}

/// A binary trie for O(prefix_len) CIDR-based claim lookups
struct ClaimTrie {
    root: TrieNode,
}

impl ClaimTrie {
    fn new() -> Self {
        Self { root: TrieNode::new() }
    }

    /// Insert a claim with its index in the claims vector
    fn insert(&mut self, range: &Range, claim_idx: usize) {
        let addr = &range.base;
        let prefix_len = range.prefix_len as usize;
        let max_bits = (addr.len as usize) * 8;
        let bits_to_check = std::cmp::min(prefix_len, max_bits);

        let mut node = &mut self.root;
        for bit_idx in 0..bits_to_check {
            let byte_idx = bit_idx / 8;
            let bit_pos = 7 - (bit_idx % 8); // MSB first
            let bit = ((addr.data[byte_idx] >> bit_pos) & 1) as usize;

            if node.children[bit].is_none() {
                node.children[bit] = Some(Box::new(TrieNode::new()));
            }
            node = node.children[bit].as_mut().unwrap();
        }
        node.claim = Some(claim_idx);
    }

    /// Find the longest prefix match for the given address
    /// Returns the index into the claims vector
    fn longest_match(&self, addr: &Address) -> Option<usize> {
        let mut node = &self.root;
        let mut best_match = None;
        let max_bits = (addr.len as usize) * 8;

        if node.claim.is_some() {
            best_match = node.claim;
        }

        for bit_idx in 0..max_bits {
            let byte_idx = bit_idx / 8;
            let bit_pos = 7 - (bit_idx % 8); // MSB first
            let bit = ((addr.data[byte_idx] >> bit_pos) & 1) as usize;

            match &node.children[bit] {
                Some(child) => {
                    node = child;
                    if node.claim.is_some() {
                        best_match = node.claim;
                    }
                }
                None => break,
            }
        }
        best_match
    }

    fn clear(&mut self) {
        self.root = TrieNode::new();
    }
}

pub struct ClaimTable<TS: TimeSource> {
    cache: HashMap<Address, CacheValue, Hash>,
    cache_timeout: Duration,
    claims: Vec<ClaimEntry>,
    claim_timeout: Duration,
    trie: ClaimTrie,
    _dummy: PhantomData<TS>,
}

impl<TS: TimeSource> ClaimTable<TS> {
    pub fn new(cache_timeout: Duration, claim_timeout: Duration) -> Self {
        Self {
            cache: HashMap::default(),
            cache_timeout,
            claims: vec![],
            claim_timeout,
            trie: ClaimTrie::new(),
            _dummy: PhantomData,
        }
    }

    pub fn cache(&mut self, addr: Address, peer: SocketAddr) {
        // HOT PATH
        self.cache.insert(addr, CacheValue { peer, timeout: TS::now() + self.cache_timeout as Time });
    }

    pub fn clear_cache(&mut self) {
        self.cache.clear()
    }

    pub fn set_claims(&mut self, peer: SocketAddr, mut claims: RangeList) {
        let mut removed_claim = false;
        for entry in &mut self.claims {
            if entry.peer == peer {
                let pos = claims.iter().position(|r| r == &entry.claim);
                if let Some(pos) = pos {
                    entry.timeout = TS::now() + self.claim_timeout as Time;
                    claims.swap_remove(pos);
                    if claims.is_empty() {
                        break;
                    }
                } else {
                    entry.timeout = 0;
                    removed_claim = true;
                }
            }
        }
        for claim in claims {
            self.claims.push(ClaimEntry { peer, claim, timeout: TS::now() + self.claim_timeout as Time })
        }
        if removed_claim {
            for entry in self.cache.values_mut() {
                if entry.peer == peer {
                    entry.timeout = 0
                }
            }
        }
        self.housekeep()
    }

    pub fn remove_claims(&mut self, peer: SocketAddr) {
        for entry in &mut self.claims {
            if entry.peer == peer {
                entry.timeout = 0
            }
        }
        for entry in self.cache.values_mut() {
            if entry.peer == peer {
                entry.timeout = 0
            }
        }
        self.housekeep()
    }

    pub fn lookup(&mut self, addr: Address) -> Option<SocketAddr> {
        // HOT PATH
        if let Some(entry) = self.cache.get(&addr) {
            return Some(entry.peer);
        }
        // COLD PATH - Use trie for O(prefix_len) lookup instead of O(n) linear scan
        if let Some(claim_idx) = self.trie.longest_match(&addr) {
            let entry = &self.claims[claim_idx];
            self.cache.insert(
                addr,
                CacheValue { peer: entry.peer, timeout: min(TS::now() + self.cache_timeout as Time, entry.timeout) },
            );
            return Some(entry.peer);
        }
        None
    }

    pub fn housekeep(&mut self) {
        let now = TS::now();
        self.cache.retain(|_, v| v.timeout >= now);
        self.claims.retain(|e| e.timeout >= now);
        // Rebuild trie after claims cleanup
        self.rebuild_trie();
    }

    /// Rebuild the trie from the current claims vector
    fn rebuild_trie(&mut self) {
        self.trie.clear();
        for (idx, entry) in self.claims.iter().enumerate() {
            self.trie.insert(&entry.claim, idx);
        }
    }

    pub fn cache_len(&self) -> usize {
        self.cache.len()
    }

    pub fn claim_len(&self) -> usize {
        self.claims.len()
    }

    /// Write out the table
    pub fn write_out<W: Write>(&self, out: &mut W) -> Result<(), io::Error> {
        let now = TS::now();
        writeln!(out, "forwarding_table:")?;
        writeln!(out, "  claims:")?;
        for entry in &self.claims {
            writeln!(
                out,
                "    - \"{}\": {{ peer: \"{}\", timeout: {} }}",
                entry.claim,
                addr_nice(entry.peer),
                entry.timeout - now
            )?;
        }
        writeln!(out, "  cache:")?;
        for (addr, entry) in &self.cache {
            writeln!(
                out,
                "    - \"{}\": {{ peer: \"{}\", timeout: {} }}",
                addr,
                addr_nice(entry.peer),
                entry.timeout - now
            )?;
        }
        Ok(())
    }
}

// TODO: test
