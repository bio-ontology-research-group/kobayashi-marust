//! Process-seeded FxHash-style hasher for symbol-keyed tables outside the
//! saturation engines.
//!
//! The frontend's IRI registry, axiom de-duplication set, clausifier
//! reification cache, and declaration seeding set, and the orchestrator's
//! public-output id tables, are probed once per source symbol occurrence. A
//! fast multiply-rotate mixer avoids SipHash's per-byte rounds. Unlike the
//! engine-internal tables, frontend keys can come from an untrusted ontology,
//! so each table receives a process-random seed to prevent precomputed
//! collision sets.
//!
//! Within one table the hash is deterministic for a key and its private seed.
//! Every table keyed through it is consulted only for membership or lookup:
//! no consumer reads the resulting iteration order into clause or meta output
//! (the registry's entries are sorted before they are emitted).

use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hasher};

#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        // Fold eight bytes per step, then four, then the tail, as rustc-hash
        // does: a 60-100 byte IRI costs about a dozen steps instead of one
        // multiply-rotate per byte.
        let mut words = bytes.chunks_exact(8);
        for word in &mut words {
            self.add(u64::from_le_bytes(word.try_into().expect("8-byte chunk")));
        }
        let mut rest = words.remainder();
        if rest.len() >= 4 {
            let (head, tail) = rest.split_at(4);
            self.add(u64::from(u32::from_le_bytes(
                head.try_into().expect("4-byte chunk"),
            )));
            rest = tail;
        }
        for &byte in rest {
            self.add(u64::from(byte));
        }
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        // Multiply-rotate leaves the low bits of the state a function of the
        // last few input bytes only, while `hashbrown` indexes buckets by the
        // low bits. Fold the well-mixed high half down before handing the
        // value out, so IRIs that differ in one trailing character (the
        // numeric suffixes of generated ontologies) spread over the table.
        let x = self.hash;
        let x = (x ^ (x >> 32)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        x ^ (x >> 29)
    }
}

#[derive(Clone)]
pub struct FxBuild {
    seed: u64,
}

impl Default for FxBuild {
    fn default() -> Self {
        // RandomState obtains per-instance secret keys from the standard
        // library. Hashing one fixed word once transfers that entropy into the
        // cheaper per-key mixer used by this table.
        let mut random = RandomState::new().build_hasher();
        random.write_u64(SEED);
        Self {
            seed: random.finish(),
        }
    }
}

impl BuildHasher for FxBuild {
    type Hasher = FxHasher;

    #[inline]
    fn build_hasher(&self) -> Self::Hasher {
        FxHasher { hash: self.seed }
    }
}

pub type FxHashMap<K, V> = std::collections::HashMap<K, V, FxBuild>;
pub type FxHashSet<T> = std::collections::HashSet<T, FxBuild>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::Hash;

    fn hash_of<T: Hash + ?Sized>(value: &T) -> u64 {
        let mut hasher = FxHasher::default();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn hash_is_a_function_of_the_bytes_only() {
        let owned = String::from("http://purl.obolibrary.org/obo/NCBIGene_10000");
        assert_eq!(hash_of(owned.as_str()), hash_of(&owned));
        assert_ne!(hash_of("NCBIGene_10000"), hash_of("NCBIGene_10001"));
        assert_ne!(hash_of("abcdefgh"), hash_of("abcdefg"));
    }

    #[test]
    fn trailing_character_differences_reach_the_low_bits() {
        // Bucket indexes are the low bits of the hash. Keys that differ only
        // in their last character must not share them.
        let keys: Vec<String> = (0..64)
            .map(|i| format!("http://purl.obolibrary.org/obo/NCBIGene_1000{}", i % 10))
            .collect();
        let low_bits: std::collections::HashSet<u64> =
            keys.iter().map(|k| hash_of(k.as_str()) & 0xffff).collect();
        assert!(
            low_bits.len() >= 10,
            "{} distinct low-bit patterns",
            low_bits.len()
        );
    }

    #[test]
    fn membership_matches_the_standard_table() {
        let keys: Vec<String> = (0..5_000)
            .map(|i| format!("http://e/x{i}#c{}", i % 97))
            .collect();
        let fx: FxHashSet<&str> = keys.iter().map(String::as_str).collect();
        let std: std::collections::HashSet<&str> = keys.iter().map(String::as_str).collect();
        assert_eq!(fx.len(), std.len());
        for key in &keys {
            assert!(fx.contains(key.as_str()));
        }
        assert!(!fx.contains("http://e/x0#c1"));
    }

    #[test]
    fn one_builder_reproduces_hashes_for_table_lookup() {
        let build = FxBuild::default();
        let mut left = build.build_hasher();
        let mut right = build.build_hasher();
        "http://purl.obolibrary.org/obo/UBERON_0001062".hash(&mut left);
        "http://purl.obolibrary.org/obo/UBERON_0001062".hash(&mut right);
        assert_eq!(left.finish(), right.finish());
    }
}
