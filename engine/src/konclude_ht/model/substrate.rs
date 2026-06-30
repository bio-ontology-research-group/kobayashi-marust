//! Shared port substrate — the ONE global `[ownership]` decision for the whole
//! `konclude_ht` port. Every other ported file builds on these primitives.
//!
//! Konclude stores raw `CXxx*` pointers everywhere and allocates objects from
//! per-task bump pools (`CMemoryAllocationManager`) that are never individually
//! freed — they die when the task pool is reset, and backtracking restores state
//! by rewinding to a saved watermark. Stable `cint64` ids already accompany most
//! objects. The port standardises on that id model:
//!
//!   * each object kind lives in an arena `Vec<T>` owned by the task context;
//!   * a `CXxx*` becomes a typed id (`ConceptId`, `NodeId`, …) indexing that arena;
//!   * "allocate" = `arena.push`; backtrack = truncate to a watermark + replay a
//!     trail of in-place mutations (see `Trail`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: this replaces the raw-pointer + pool model. It
//! is the single deviation referenced by all per-site `[ownership]` notes; those
//! notes point here rather than re-explaining. Behaviour is identical: an id
//! dereferences to the same object the C++ pointer would.

#![allow(dead_code)]

use std::marker::PhantomData;

/// Konclude's ubiquitous `cint64`. Kept as a named alias so ported signatures
/// read like the original (`cint64 mTag` → `tag: Cint64`).
pub type Cint64 = i64;

/// Sentinel for a null `CXxx*` / unset `cint64` id. Konclude uses `nullptr` and,
/// for id fields, frequently `-1`.
pub const INVALID: Cint64 = -1;

/// A typed arena id. `Id<T>` replaces `T*`. `PhantomData` keeps the kinds
/// distinct at compile time (a `ConceptId` cannot be used where a `NodeId` is
/// expected) at zero runtime cost.
///
/// KONCLUDE-PORT-NOTE[ownership]: the marker is `PhantomData<fn() -> T>`, so an
/// `Id<T>` carries no `T` value and is `Copy`/`Eq`/`Hash` regardless of whether
/// `T` is. `#[derive]` would wrongly add `T: Copy`/`T: Clone`/`T: Eq` bounds
/// (an id into a non-`Copy` arena object like `Concept` would then itself stop
/// being `Copy`), so these are hand-implemented without any bound on `T`.
pub struct Id<T> {
    pub raw: Cint64,
    _k: PhantomData<fn() -> T>,
}

impl<T> Clone for Id<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Id<T> {}
impl<T> PartialEq for Id<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl<T> Eq for Id<T> {}
impl<T> std::hash::Hash for Id<T> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<T> Id<T> {
    #[inline]
    pub const fn new(raw: Cint64) -> Self { Id { raw, _k: PhantomData } }
    /// The null/unset id (== a `nullptr` back-pointer).
    pub const NONE: Self = Id { raw: INVALID, _k: PhantomData };
    #[inline]
    pub fn is_none(self) -> bool { self.raw < 0 }
    #[inline]
    pub fn is_some(self) -> bool { self.raw >= 0 }
    #[inline]
    pub fn index(self) -> usize { self.raw as usize }
}

impl<T> std::fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.raw)
    }
}

/// An append-mostly arena. `push` returns a stable `Id`; objects are addressed by
/// id for the object's whole life. `truncate_to` rewinds allocation on backtrack
/// (the pool-reset analogue) — callers must ensure no live id past the watermark
/// survives, exactly as Konclude relies on the branch structure to guarantee.
pub struct Arena<T> {
    items: Vec<T>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self { Arena { items: Vec::new() } }
}

impl<T> Arena<T> {
    pub fn new() -> Self { Self::default() }
    #[inline]
    pub fn push(&mut self, v: T) -> Id<T> {
        let id = Id::new(self.items.len() as Cint64);
        self.items.push(v);
        id
    }
    #[inline]
    pub fn get(&self, id: Id<T>) -> &T { &self.items[id.index()] }
    #[inline]
    pub fn get_mut(&mut self, id: Id<T>) -> &mut T { &mut self.items[id.index()] }
    #[inline]
    pub fn len(&self) -> usize { self.items.len() }
    #[inline]
    pub fn watermark(&self) -> usize { self.items.len() }
    /// Backtrack: drop everything allocated since `mark`.
    #[inline]
    pub fn truncate_to(&mut self, mark: usize) { self.items.truncate(mark); }
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, T> { self.items.iter() }
}

/// KONCLUDE-PORT-NOTE[ownership]: Konclude's intrusive linker chains
/// (`CLinker`/`CXLinker`/`CSortedNegLinker` with `getNext()/setNext()`) become a
/// plain `Vec` of entries here. `CSortedNegLinker<CConcept*>` (an operand list
/// where each entry carries a negation bit) maps to `Vec<NegLink<ConceptId>>`.
/// Iteration order is preserved (Konclude keeps these sorted by id; the port
/// keeps insertion/sorted order to match).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NegLink<I> {
    pub target: I,
    pub negated: bool,
}

/// Save/restore stack for the `mX` / `mUseX` / `mPrevX` triple-buffer pattern
/// Konclude uses on queues and label sets for branch save/restore. A ported
/// component that mutates in place registers an undo closure-equivalent here.
/// (Kept deliberately small; concrete trail entry kinds are added as the data
/// model lands in W2.)
#[derive(Default)]
pub struct Trail {
    marks: Vec<usize>,
}

impl Trail {
    pub fn new() -> Self { Trail::default() }
    /// Open a backtrack scope; returns the level to restore to.
    pub fn push_mark(&mut self, len: usize) { self.marks.push(len); }
    pub fn pop_mark(&mut self) -> Option<usize> { self.marks.pop() }
}
