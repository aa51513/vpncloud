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

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;
    use std::net::SocketAddr;
    use std::str::FromStr;

    // Helper to create an IPv4 address
    fn ipv4_addr(s: &str) -> Address {
        Address::from_str(s).unwrap()
    }

    // Helper to create an IPv4 range (CIDR)
    fn ipv4_range(s: &str) -> Range {
        Range::from_str(s).unwrap()
    }

    // Helper to create a socket address
    fn sock_addr(s: &str) -> SocketAddr {
        SocketAddr::from_str(s).unwrap()
    }

    // --- ClaimTrie tests ---

    #[test]
    fn trie_insert_and_longest_match_basic() {
        let mut trie = ClaimTrie::new();
        trie.insert(&ipv4_range("10.0.0.0/8"), 0);
        trie.insert(&ipv4_range("192.168.0.0/16"), 1);

        // Match 10.x.x.x -> claim 0
        assert_eq!(trie.longest_match(&ipv4_addr("10.1.2.3")), Some(0));
        // Match 192.168.x.x -> claim 1
        assert_eq!(trie.longest_match(&ipv4_addr("192.168.1.1")), Some(1));
        // No match for 172.16.x.x
        assert_eq!(trie.longest_match(&ipv4_addr("172.16.0.1")), None);
    }

    #[test]
    fn trie_longest_prefix_wins() {
        let mut trie = ClaimTrie::new();
        trie.insert(&ipv4_range("10.0.0.0/8"), 0);   // /8
        trie.insert(&ipv4_range("10.1.0.0/16"), 1);   // /16
        trie.insert(&ipv4_range("10.1.2.0/24"), 2);   // /24

        // All three match, but /24 is longest
        assert_eq!(trie.longest_match(&ipv4_addr("10.1.2.5")), Some(2));
        // /16 is longest for 10.1.3.x
        assert_eq!(trie.longest_match(&ipv4_addr("10.1.3.5")), Some(1));
        // Only /8 matches for 10.2.x.x
        assert_eq!(trie.longest_match(&ipv4_addr("10.2.3.4")), Some(0));
    }

    #[test]
    fn trie_exact_match() {
        let mut trie = ClaimTrie::new();
        trie.insert(&ipv4_range("10.0.0.0/32"), 0);

        assert_eq!(trie.longest_match(&ipv4_addr("10.0.0.0")), Some(0));
        assert_eq!(trie.longest_match(&ipv4_addr("10.0.0.1")), None);
    }

    #[test]
    fn trie_default_route() {
        let mut trie = ClaimTrie::new();
        trie.insert(&ipv4_range("0.0.0.0/0"), 0);   // default route
        trie.insert(&ipv4_range("10.0.0.0/8"), 1);

        // Default route matches everything
        assert_eq!(trie.longest_match(&ipv4_addr("192.168.1.1")), Some(0));
        // But 10.x.x.x has longer prefix
        assert_eq!(trie.longest_match(&ipv4_addr("10.1.2.3")), Some(1));
    }

    #[test]
    fn trie_clear() {
        let mut trie = ClaimTrie::new();
        trie.insert(&ipv4_range("10.0.0.0/8"), 0);
        trie.insert(&ipv4_range("192.168.0.0/16"), 1);

        assert_eq!(trie.longest_match(&ipv4_addr("10.1.2.3")), Some(0));

        trie.clear();

        assert_eq!(trie.longest_match(&ipv4_addr("10.1.2.3")), None);
        assert_eq!(trie.longest_match(&ipv4_addr("192.168.1.1")), None);
    }

    #[test]
    fn trie_insert_overwrite() {
        let mut trie = ClaimTrie::new();
        trie.insert(&ipv4_range("10.0.0.0/8"), 0);
        trie.insert(&ipv4_range("10.0.0.0/8"), 1); // same prefix, different index

        // Last insert wins
        assert_eq!(trie.longest_match(&ipv4_addr("10.1.2.3")), Some(1));
    }

    #[test]
    fn trie_empty_has_no_match() {
        let trie = ClaimTrie::new();
        assert_eq!(trie.longest_match(&ipv4_addr("10.0.0.0")), None);
    }

    #[test]
    fn trie_many_prefixes() {
        let mut trie = ClaimTrie::new();
        // Insert all /24s in 10.0.0.0/16
        for i in 0..256 {
            let range = Range::from_str(&format!("10.0.{}.0/24", i)).unwrap();
            trie.insert(&range, i);
        }

        assert_eq!(trie.longest_match(&ipv4_addr("10.0.0.5")), Some(0));
        assert_eq!(trie.longest_match(&ipv4_addr("10.0.127.1")), Some(127));
        assert_eq!(trie.longest_match(&ipv4_addr("10.0.255.255")), Some(255));
        // Outside the /16 range
        assert_eq!(trie.longest_match(&ipv4_addr("10.1.0.0")), None);
    }

    // --- ClaimTable tests using a mock TimeSource ---

    use crate::util::{MockTimeSource, TimeSource};

    type TestClaimTable = ClaimTable<MockTimeSource>;

    fn new_table(cache_timeout: Duration, claim_timeout: Duration) -> TestClaimTable {
        MockTimeSource::set_time(1000);
        TestClaimTable::new(cache_timeout, claim_timeout)
    }

    #[test]
    fn table_set_claims_and_lookup() {
        let mut table = new_table(60, 300);
        let peer = sock_addr("192.168.1.1:3210");

        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // Should find the claim
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
        assert_eq!(table.claim_len(), 1);
    }

    #[test]
    fn table_lookup_caches_result() {
        let mut table = new_table(60, 300);
        let peer = sock_addr("192.168.1.1:3210");

        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // First lookup populates cache
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
        assert_eq!(table.cache_len(), 1);

        // Second lookup hits cache
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
        assert_eq!(table.cache_len(), 1);
    }

    #[test]
    fn table_remove_claims() {
        let mut table = new_table(60, 300);
        let peer1 = sock_addr("192.168.1.1:3210");
        let peer2 = sock_addr("192.168.1.2:3210");

        table.set_claims(peer1, smallvec![ipv4_range("10.0.0.0/8")]);
        table.set_claims(peer2, smallvec![ipv4_range("192.168.0.0/16")]);

        assert_eq!(table.claim_len(), 2);

        table.remove_claims(peer1);

        assert_eq!(table.claim_len(), 1);
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), None);
        assert_eq!(table.lookup(ipv4_addr("192.168.1.1")), Some(peer2));
    }

    #[test]
    fn table_claim_timeout() {
        let mut table = new_table(60, 100); // claim timeout = 100s
        let peer = sock_addr("192.168.1.1:3210");

        MockTimeSource::set_time(1000);
        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // Claim exists
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));

        // Advance time past claim timeout
        MockTimeSource::set_time(1101);
        table.housekeep();

        // Claim expired
        assert_eq!(table.claim_len(), 0);
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), None);
    }

    #[test]
    fn table_cache_timeout() {
        let mut table = new_table(50, 300); // cache timeout = 50s
        let peer = sock_addr("192.168.1.1:3210");

        MockTimeSource::set_time(1000);
        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // Lookup creates cache entry
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
        assert_eq!(table.cache_len(), 1);

        // Advance time past cache timeout but not claim timeout
        MockTimeSource::set_time(1051);
        table.housekeep();

        // Cache expired but claim still exists
        assert_eq!(table.cache_len(), 0);
        assert_eq!(table.claim_len(), 1);
        // Lookup should still work via trie
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
    }

    #[test]
    fn table_clear_cache() {
        let mut table = new_table(60, 300);
        let peer = sock_addr("192.168.1.1:3210");

        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);
        table.lookup(ipv4_addr("10.1.2.3"));
        assert_eq!(table.cache_len(), 1);

        table.clear_cache();
        assert_eq!(table.cache_len(), 0);

        // Lookup still works via trie
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
    }

    #[test]
    fn table_update_claims_refreshes_timeout() {
        let mut table = new_table(60, 100);
        let peer = sock_addr("192.168.1.1:3210");

        MockTimeSource::set_time(1000);
        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // Advance time, then update with same claim
        MockTimeSource::set_time(1050);
        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // Advance past original timeout
        MockTimeSource::set_time(1101);
        table.housekeep();

        // Claim should still exist because timeout was refreshed
        assert_eq!(table.claim_len(), 1);
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
    }

    #[test]
    fn table_longest_prefix_match() {
        let mut table = new_table(60, 300);
        let peer1 = sock_addr("192.168.1.1:3210");
        let peer2 = sock_addr("192.168.1.2:3210");

        table.set_claims(peer1, smallvec![ipv4_range("10.0.0.0/8")]);
        table.set_claims(peer2, smallvec![ipv4_range("10.1.0.0/16")]);

        // /16 should win over /8
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer2));
        // /8 matches when no longer prefix
        assert_eq!(table.lookup(ipv4_addr("10.2.3.4")), Some(peer1));
    }

    #[test]
    fn table_no_match() {
        let mut table = new_table(60, 300);
        let peer = sock_addr("192.168.1.1:3210");

        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        assert_eq!(table.lookup(ipv4_addr("192.168.1.1")), None);
    }

    #[test]
    fn table_multiple_peers() {
        let mut table = new_table(60, 300);
        let peer1 = sock_addr("192.168.1.1:3210");
        let peer2 = sock_addr("192.168.1.2:3210");
        let peer3 = sock_addr("192.168.1.3:3210");

        table.set_claims(peer1, smallvec![ipv4_range("10.0.0.0/8")]);
        table.set_claims(peer2, smallvec![ipv4_range("172.16.0.0/12")]);
        table.set_claims(peer3, smallvec![ipv4_range("192.168.0.0/16")]);

        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer1));
        assert_eq!(table.lookup(ipv4_addr("172.16.1.1")), Some(peer2));
        assert_eq!(table.lookup(ipv4_addr("192.168.1.1")), Some(peer3));
    }

    #[test]
    fn table_remove_one_peer_claims() {
        let mut table = new_table(60, 300);
        let peer1 = sock_addr("192.168.1.1:3210");
        let peer2 = sock_addr("192.168.1.2:3210");

        table.set_claims(peer1, smallvec![ipv4_range("10.0.0.0/8")]);
        table.set_claims(peer2, smallvec![ipv4_range("10.0.0.0/8")]); // same range

        assert_eq!(table.claim_len(), 2);

        table.remove_claims(peer1);

        assert_eq!(table.claim_len(), 1);
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer2));
    }

    #[test]
    fn table_cache_expires_but_claim_persists() {
        let mut table = new_table(30, 300);
        let peer = sock_addr("192.168.1.1:3210");

        MockTimeSource::set_time(1000);
        table.set_claims(peer, smallvec![ipv4_range("10.0.0.0/8")]);

        // Create cache entry
        table.lookup(ipv4_addr("10.1.2.3"));
        assert_eq!(table.cache_len(), 1);

        // Advance past cache timeout
        MockTimeSource::set_time(1031);
        table.housekeep();
        assert_eq!(table.cache_len(), 0);

        // But claim and trie still work
        assert_eq!(table.claim_len(), 1);
        assert_eq!(table.lookup(ipv4_addr("10.1.2.3")), Some(peer));
    }

    #[test]
    fn table_empty_lookup_returns_none() {
        let mut table = new_table(60, 300);
        assert_eq!(table.lookup(ipv4_addr("10.0.0.0")), None);
    }
}
