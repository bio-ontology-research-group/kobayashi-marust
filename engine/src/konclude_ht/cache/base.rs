//! `cache::base` — F0 generic cache base classes + the per-cache Reader/Writer
//! abstract bases (Konclude `Reasoner/Kernel/Cache/`).
//!
//! These are the empty marker / abstract bases every cache family derives from.
//! In Konclude they are pure-virtual or near-empty classes used only as a type
//! hierarchy anchor; none carries data.
//!
//! KONCLUDE-PORT-NOTE[api]: C++ uses inheritance (`CSatisfiableCache : CCache`)
//! and pure-virtual Reader/Writer interfaces. Whether the Rust port realises the
//! hierarchy as a trait (the `*Reader`/`*Writer` virtuals) or as an enum (the
//! marker family bases) is deferred to the W6 reconcile pass; for the struct-def
//! wave each is a distinct zero-field struct so the names exist and the family
//! tree is documented. See each `// [api] was-abstract` note.

#![allow(dead_code)]

// ===========================================================================
// The 6 generic cache family bases (`CCache` + 5 markers).
// ===========================================================================

/// Port of `CCache`.
///
/// [api] was-abstract — empty abstract base (virtual dtor only); the root of the
/// whole cache hierarchy. No member variables.
#[derive(Debug, Default, Clone)]
pub struct Cache;

impl Cache {
    /// Port of `CCache::CCache()`.
    pub fn new() -> Self {
        Cache
    }
    // [api] no methods to port: `CCache` declares only an (empty) constructor and a
    // virtual destructor; it is a pure type-hierarchy anchor with no behaviour.
}

/// Port of `CSatisfiableCache : public CCache`.
///
/// [api] was-abstract — marker base for the satisfiable-label caches
/// (signature-satisfiable expander; also the parent of `CSaturationCache`).
/// No member variables of its own.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCache {
    /// Inlined `CCache` base. KONCLUDE-PORT-NOTE[api]: C++ `: public CCache`.
    pub base: Cache,
}

impl SatisfiableCache {
    /// Port of `CSatisfiableCache::CSatisfiableCache()` (`: CCache()`).
    pub fn new() -> Self {
        SatisfiableCache::default()
    }
    // [api] no methods to port: empty marker base (ctor / virtual dtor only).
}

/// Port of `CUnsatisfiableCache : public CCache`.
///
/// [api] was-abstract — marker base for the occurrence-unsatisfiable cache.
/// No member variables of its own.
#[derive(Debug, Default, Clone)]
pub struct UnsatisfiableCache {
    /// Inlined `CCache` base. KONCLUDE-PORT-NOTE[api]: C++ `: public CCache`.
    pub base: Cache,
}

impl UnsatisfiableCache {
    /// Port of `CUnsatisfiableCache::CUnsatisfiableCache()` (`: CCache()`).
    pub fn new() -> Self {
        UnsatisfiableCache::default()
    }
    // [api] no methods to port: empty marker base (ctor / virtual dtor only).
}

/// Port of `CSaturationCache : public CSatisfiableCache`.
///
/// [api] was-abstract — marker base for the saturation-node associated-expansion
/// cache. Derives from `CSatisfiableCache`, not `CCache`. No member variables of
/// its own.
#[derive(Debug, Default, Clone)]
pub struct SaturationCache {
    /// Inlined `CSatisfiableCache` base.
    /// KONCLUDE-PORT-NOTE[api]: C++ `: public CSatisfiableCache`.
    pub base: SatisfiableCache,
}

impl SaturationCache {
    /// Port of `CSaturationCache::CSaturationCache()` (`: CSatisfiableCache()`).
    pub fn new() -> Self {
        SaturationCache::default()
    }
    // [api] no methods to port: empty marker base (ctor / virtual dtor only).
}

/// Port of `CCompletionGraphCache : public CCache`.
///
/// [api] was-abstract — marker base for the reuse-completion-graph cache.
/// No member variables of its own.
#[derive(Debug, Default, Clone)]
pub struct CompletionGraphCache {
    /// Inlined `CCache` base. KONCLUDE-PORT-NOTE[api]: C++ `: public CCache`.
    pub base: Cache,
}

impl CompletionGraphCache {
    /// Port of `CCompletionGraphCache::CCompletionGraphCache()` (`: CCache()`).
    pub fn new() -> Self {
        CompletionGraphCache::default()
    }
    // [api] no methods to port: empty marker base (ctor / virtual dtor only).
}

/// Port of `CBackendCache : public CCache`.
///
/// [api] was-abstract — marker base for the backend representative-memory
/// association cache. No member variables of its own.
#[derive(Debug, Default, Clone)]
pub struct BackendCache {
    /// Inlined `CCache` base. KONCLUDE-PORT-NOTE[api]: C++ `: public CCache`.
    pub base: Cache,
}

impl BackendCache {
    /// Port of `CBackendCache::CBackendCache()` (`: CCache()`).
    pub fn new() -> Self {
        BackendCache::default()
    }
    // [api] no methods to port: empty marker base (ctor / virtual dtor only).
}

// ===========================================================================
// Per-cache Reader / Writer abstract bases.
//
// KONCLUDE-PORT-NOTE[api]: in C++ these declare ONLY pure-virtual methods
// (`isSatisfiable`/`getSatisfiableOutcome`, `setSatisfiable`,
// `isUnsatisfiable`/`getUnsatisfiableItems`, `setUnsatisfiable`) and hold no
// data. Kept as zero-field structs for the struct wave; the virtuals become a
// trait at the W6 reconcile (the concrete `*Reader`/`*Writer` in F2/F3 will
// implement it). The method signatures are recorded in the doc-comments for the
// reconcile (they take `QVector<CCacheValue>` item/outcome/clash vectors with
// explicit counts — `&[CacheValue]` + `Cint64` count in the port).
// ===========================================================================

/// Port of `CSatisfiableCacheReader`.
///
/// [api] was-abstract — pure-virtual reader interface. No member variables.
/// Virtuals (W6 method-batch): `is_satisfiable(item_vec: &[CacheValue], count)`,
/// `get_satisfiable_outcome(item_vec, item_count, outcome_list)`.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCacheReader;

impl SatisfiableCacheReader {
    /// Port of `CSatisfiableCacheReader::CSatisfiableCacheReader()`.
    pub fn new() -> Self {
        SatisfiableCacheReader
    }
    // [api] no method BODIES to port: `isSatisfiable` / `getSatisfiableOutcome` are
    // pure-virtual (`= 0`) — the interface only. The concrete bodies live in the F2
    // `SignatureSatisfiableExpanderCacheReader`; these virtuals become a trait at
    // the W6 reconcile (signatures recorded in the struct doc above).
}

/// Port of `CSatisfiableCacheWriter`.
///
/// [api] was-abstract — pure-virtual writer interface. No member variables.
/// Virtuals (W6 method-batch):
/// `set_satisfiable(item_vec, item_count, outcome_vec, out_count)`.
#[derive(Debug, Default, Clone)]
pub struct SatisfiableCacheWriter;

impl SatisfiableCacheWriter {
    /// Port of `CSatisfiableCacheWriter::CSatisfiableCacheWriter()`.
    pub fn new() -> Self {
        SatisfiableCacheWriter
    }
    // [api] no method BODIES to port: `setSatisfiable` is pure-virtual (`= 0`) — the
    // interface only. The concrete body lives in the F2 writer; this virtual becomes
    // a trait at the W6 reconcile (signature recorded in the struct doc above).
}

/// Port of `CUnsatisfiableCacheReader`.
///
/// [api] was-abstract — pure-virtual reader interface. No member variables.
/// Virtuals (W6 method-batch): `is_unsatisfiable(item_vec, count)`,
/// `get_unsatisfiable_items(item_vec, count) -> Vec<CacheValue>`.
#[derive(Debug, Default, Clone)]
pub struct UnsatisfiableCacheReader;

impl UnsatisfiableCacheReader {
    /// Port of `CUnsatisfiableCacheReader::CUnsatisfiableCacheReader()`.
    pub fn new() -> Self {
        UnsatisfiableCacheReader
    }
    // [api] no method BODIES to port: `isUnsatisfiable` / `getUnsatisfiableItems` are
    // pure-virtual (`= 0`) — the interface only. The concrete bodies live in the F3
    // `OccurrenceUnsatisfiableCacheReader`; these virtuals become a trait at the W6
    // reconcile (signatures recorded in the struct doc above).
}

/// Port of `CUnsatisfiableCacheWriter`.
///
/// [api] was-abstract — pure-virtual writer interface. No member variables.
/// Virtuals (W6 method-batch):
/// `set_unsatisfiable(item_vec, count, clash_vec, clash_count)`.
#[derive(Debug, Default, Clone)]
pub struct UnsatisfiableCacheWriter;

impl UnsatisfiableCacheWriter {
    /// Port of `CUnsatisfiableCacheWriter::CUnsatisfiableCacheWriter()`.
    pub fn new() -> Self {
        UnsatisfiableCacheWriter
    }
    // [api] no method BODIES to port: `setUnsatisfiable` is pure-virtual (`= 0`) — the
    // interface only. The concrete body lives in the F3 writer; this virtual becomes
    // a trait at the W6 reconcile (signature recorded in the struct doc above).
}
