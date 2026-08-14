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
    pub const fn new(raw: Cint64) -> Self {
        Id {
            raw,
            _k: PhantomData,
        }
    }
    /// The null/unset id (== a `nullptr` back-pointer).
    pub const NONE: Self = Id {
        raw: INVALID,
        _k: PhantomData,
    };
    #[inline]
    pub fn is_none(self) -> bool {
        self.raw < 0
    }
    #[inline]
    pub fn is_some(self) -> bool {
        self.raw >= 0
    }
    #[inline]
    pub fn index(self) -> usize {
        self.raw as usize
    }
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
    /// Branch-epoch watermarks (in-process COW): allocation lengths at each
    /// open epoch; `pop_epoch*` truncates back. Empty when no epoch is open —
    /// all epoch machinery is then zero-cost.
    wm_stack: Vec<usize>,
    /// Journal frames (one per open epoch, for journal-enabled pushes): the
    /// first in-place mutation of a slot BELOW the frame's watermark saves a
    /// clone; `pop_epoch` replays the saves in reverse. Slots at/above the
    /// watermark die on truncate and are never saved.
    journal_stack: Vec<EpochJournalFrame<T>>,
}

/// One epoch's first-touch save frame (see [`Arena::get_mut_journaled`]).
pub struct EpochJournalFrame<T> {
    watermark: usize,
    saved_keys: std::collections::HashSet<usize>,
    saves: Vec<(usize, T)>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Arena {
            items: Vec::new(),
            wm_stack: Vec::new(),
            journal_stack: Vec::new(),
        }
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self::default()
    }
    #[inline]
    pub fn push(&mut self, v: T) -> Id<T> {
        let id = Id::new(self.items.len() as Cint64);
        self.items.push(v);
        id
    }
    #[inline]
    pub fn get(&self, id: Id<T>) -> &T {
        &self.items[id.index()]
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.items.len()
    }
    /// Allocated object slots available before the arena's outer vector grows.
    #[cfg(test)]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.items.capacity()
    }
    #[inline]
    pub fn watermark(&self) -> usize {
        self.items.len()
    }
    /// Plain mutate path WITHOUT epoch journaling (no `Clone` bound):
    /// immutable-model arenas (ontology concepts/roles), the task layer, and
    /// cross-task shared cache state, whose mutations must persist across
    /// branch rollbacks by design.
    #[inline]
    pub fn get_mut(&mut self, id: Id<T>) -> &mut T {
        &mut self.items[id.index()]
    }
    /// Alias (cache substrate call sites).
    #[inline]
    pub fn get_mut_raw(&mut self, id: Id<T>) -> &mut T {
        &mut self.items[id.index()]
    }
    /// Backtrack: drop everything allocated since `mark`.
    #[inline]
    pub fn truncate_to(&mut self, mark: usize) {
        self.items.truncate(mark);
    }
    /// End one calculation task while retaining this arena's backing storage
    /// for the next task. All object ids and every open branch epoch become
    /// invalid, exactly as if the arena had been dropped and reconstructed.
    ///
    /// The epoch vectors are cleared as logical state too. Their outer
    /// allocations remain available, but journal frames (and the saved object
    /// clones owned by them) are dropped rather than carried across tasks.
    #[inline]
    pub fn clear_preserving_capacity(&mut self) {
        self.items.clear();
        self.wm_stack.clear();
        self.journal_stack.clear();
    }
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.items.iter()
    }

    // --- branch-epoch COW (the in-process stand-in for Konclude's per-task
    // --- memory pools + copy-on-write databox referencing) ---

    /// Open a watermark-ONLY epoch: allocations since it are dropped on pop,
    /// but in-place mutations of older slots PERSIST across the pop. Used for
    /// the dependency track-point / branch-node arenas, whose clash markings
    /// are branch-SHARED state in Konclude (the DDB learning must survive the
    /// death of the alternative that produced it).
    #[inline]
    pub fn push_epoch_watermark(&mut self) {
        self.wm_stack.push(self.items.len());
    }
    /// Close a watermark-only epoch.
    #[inline]
    pub fn pop_epoch_watermark(&mut self) {
        if let Some(wm) = self.wm_stack.pop() {
            self.items.truncate(wm);
        }
    }
    /// True when any epoch is open (journaled or watermark-only).
    #[inline]
    pub fn epoch_open(&self) -> bool {
        !self.wm_stack.is_empty()
    }
}

impl<T: Clone> Arena<T> {
    /// Open a JOURNALED epoch: allocations are dropped on pop AND in-place
    /// mutations of pre-epoch slots are rolled back (first-touch clone).
    #[inline]
    pub fn push_epoch(&mut self) {
        let wm = self.items.len();
        self.wm_stack.push(wm);
        self.journal_stack.push(EpochJournalFrame {
            watermark: wm,
            saved_keys: std::collections::HashSet::new(),
            saves: Vec::new(),
        });
    }
    /// Close a journaled epoch: replay the saves in reverse, then truncate.
    pub fn pop_epoch(&mut self) {
        if let Some(frame) = self.journal_stack.pop() {
            // truncate FIRST (frees slots the saves may index past? saves are
            // all below the watermark by construction, so order is free; do
            // saves last so restored content is final).
            if let Some(wm) = self.wm_stack.pop() {
                self.items.truncate(wm);
            }
            for (ix, v) in frame.saves.into_iter().rev() {
                self.items[ix] = v;
            }
        } else if let Some(wm) = self.wm_stack.pop() {
            self.items.truncate(wm);
        }
    }
    /// The mutate path under branch epochs: the first mutation of a
    /// pre-epoch slot in the CURRENT epoch saves a rollback clone (zero-cost
    /// when no journaled epoch is open). The `ProcessContext` accessor macro
    /// routes every branch-state arena through this; arenas holding
    /// immutable-model / cross-task state keep the raw `get_mut`.
    #[inline]
    pub fn get_mut_journaled(&mut self, id: Id<T>) -> &mut T {
        if let Some(frame) = self.journal_stack.last_mut() {
            let ix = id.index();
            if ix < frame.watermark && frame.saved_keys.insert(ix) {
                let clone = self.items[ix].clone();
                frame.saves.push((ix, clone));
            }
        }
        &mut self.items[id.index()]
    }
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
    pub fn new() -> Self {
        Trail::default()
    }
    /// Open a backtrack scope; returns the level to restore to.
    pub fn push_mark(&mut self, len: usize) {
        self.marks.push(len);
    }
    pub fn pop_mark(&mut self) -> Option<usize> {
        self.marks.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::Arena;

    #[test]
    fn arena_clear_preserves_storage_but_invalidates_objects_and_epochs() {
        let mut arena = Arena::new();
        for value in 0..32 {
            arena.push(value);
        }
        let items_capacity = arena.items.capacity();
        let items_ptr = arena.items.as_ptr();

        arena.push_epoch();
        *arena.get_mut_journaled(super::Id::new(0)) = 99;
        arena.push(32);
        assert!(arena.epoch_open());
        assert!(!arena.journal_stack.is_empty());

        arena.clear_preserving_capacity();

        assert_eq!(arena.len(), 0);
        assert!(!arena.epoch_open());
        assert!(arena.journal_stack.is_empty());
        assert_eq!(arena.items.capacity(), items_capacity);
        assert_eq!(arena.items.as_ptr(), items_ptr);

        let id = arena.push(7);
        assert_eq!(id.index(), 0, "reused arenas restart their id space");
        assert_eq!(*arena.get(id), 7, "no old object content survives");
    }
}
