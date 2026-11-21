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
    items: ChunkStore<T>,
    /// Use bounded geometric growth for exceptionally large append-only pools.
    /// `Vec` normally doubles at capacity, which can request multiple GiB at
    /// once for saturation arenas containing tens of millions of records.
    tight_growth: bool,
    /// Watermark-ONLY epochs (eager): allocation lengths at each open
    /// watermark-only epoch; `pop_epoch_watermark` truncates back.
    wm_stack: Vec<usize>,
    /// Number of open JOURNALED epochs. Opening one is O(1): its frame is
    /// materialized lazily, on the first allocation, removal, truncation or
    /// journaled mutation inside it (see `materialize_epoch_frame`).
    open_depth: usize,
    /// Materialized journal frames, ordered by depth. One frame covers the
    /// contiguous run of open depths `lo..=hi` that were opened while the arena
    /// was untouched; all of them share one watermark, exactly as the eager
    /// scheme (one frame pushed per opened epoch) would have recorded.
    journal_stack: Vec<EpochJournalFrame<T>>,
}

/// Elements per chunk of `ChunkStore` beyond the first (2^16).
const CHUNK_SHIFT: usize = 16;
const CHUNK_LEN: usize = 1 << CHUNK_SHIFT;

/// Arena backing store: chunk 0 grows like a `Vec` up to `CHUNK_LEN`
/// elements, every later chunk is allocated once with exactly `CHUNK_LEN`
/// slots and never moves. Element `i` lives at `chunks[i >> CHUNK_SHIFT]
/// [i & (CHUNK_LEN - 1)]`; every chunk below the one holding the last element
/// is full. A single `Vec` reallocated and copied the whole pool on every
/// growth step: on ore_ont_7361 that memmove was a third of the HT worker's
/// CPU (the 1.2 GB successor-record arena growing by 25 % at a time), and it
/// briefly held the old and new pool together.
pub struct ChunkStore<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
}

impl<T> ChunkStore<T> {
    pub fn new() -> Self {
        ChunkStore { chunks: Vec::new(), len: 0 }
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }
    #[inline]
    pub fn push(&mut self, v: T) {
        let chunk = self.len >> CHUNK_SHIFT;
        if chunk == self.chunks.len() {
            self.chunks.push(if chunk == 0 { Vec::new() } else { Vec::with_capacity(CHUNK_LEN) });
        }
        self.chunks[chunk].push(v);
        self.len += 1;
    }
    /// Bounded growth for the first chunk, which grows like a `Vec`: at most
    /// 25 % (at least 4,096 slots, never beyond `CHUNK_LEN`). Later chunks are
    /// allocated at their full size once, so at most one chunk is unused.
    #[inline]
    pub fn reserve_tight_for_push(&mut self) {
        if self.len < CHUNK_LEN {
            if self.chunks.is_empty() {
                self.chunks.push(Vec::new());
            }
            let first = &mut self.chunks[0];
            if first.len() == first.capacity() {
                let additional = (first.capacity() / 4).max(4_096).min(CHUNK_LEN - first.len());
                first.reserve_exact(additional);
            }
        }
    }
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        self.chunks[self.len >> CHUNK_SHIFT].pop()
    }
    /// Keep the first `len` elements. Emptied chunks keep their allocation, as
    /// `Vec::truncate` keeps its capacity.
    pub fn truncate(&mut self, len: usize) {
        if len >= self.len {
            return;
        }
        for chunk in (len >> CHUNK_SHIFT)..self.chunks.len() {
            let keep = len.saturating_sub(chunk << CHUNK_SHIFT).min(CHUNK_LEN);
            self.chunks[chunk].truncate(keep);
        }
        self.len = len;
    }
    pub fn clear(&mut self) {
        self.truncate(0);
    }
    pub fn capacity(&self) -> usize {
        self.chunks.iter().map(Vec::capacity).sum()
    }
    #[inline]
    pub fn get(&self, index: usize) -> &T {
        &self.chunks[index >> CHUNK_SHIFT][index & (CHUNK_LEN - 1)]
    }
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> &mut T {
        &mut self.chunks[index >> CHUNK_SHIFT][index & (CHUNK_LEN - 1)]
    }
    pub fn iter(&self) -> ChunkIter<'_, T> {
        ChunkIter { store: self, front: 0, back: self.len }
    }
    #[cfg(test)]
    fn first_chunk_ptr(&self) -> *const T {
        self.chunks.first().map_or(std::ptr::null(), |chunk| chunk.as_ptr())
    }
}

impl<T> Default for ChunkStore<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> std::ops::Index<usize> for ChunkStore<T> {
    type Output = T;
    #[inline]
    fn index(&self, index: usize) -> &T {
        self.get(index)
    }
}

impl<T> std::ops::IndexMut<usize> for ChunkStore<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index)
    }
}

/// In-order iterator over a `ChunkStore`.
pub struct ChunkIter<'a, T> {
    store: &'a ChunkStore<T>,
    front: usize,
    back: usize,
}

impl<'a, T> Iterator for ChunkIter<'a, T> {
    type Item = &'a T;
    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        if self.front == self.back {
            return None;
        }
        let item = self.store.get(self.front);
        self.front += 1;
        Some(item)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.back - self.front;
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for ChunkIter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        if self.front == self.back {
            return None;
        }
        self.back -= 1;
        Some(self.store.get(self.back))
    }
}

impl<'a, T> ExactSizeIterator for ChunkIter<'a, T> {}

/// One run of open epochs' first-touch save frame (see
/// [`Arena::get_mut_journaled`]). Only the innermost depth `hi` of the run can
/// receive saves: the shallower depths of the run were never touched while
/// they were innermost.
pub struct EpochJournalFrame<T> {
    lo: usize,
    hi: usize,
    watermark: usize,
    saved_keys: crate::fxhash::FxHashSet<usize>,
    saves: Vec<(usize, T)>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Arena {
            items: ChunkStore::new(),
            tight_growth: false,
            wm_stack: Vec::new(),
            open_depth: 0,
            journal_stack: Vec::new(),
        }
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self::default()
    }
    /// Construct an arena whose backing vector grows by at most 25% at a time.
    /// IDs, indexing, epoch rollback, and object lifetime are identical to
    /// `new`; only unused capacity and reallocation granularity differ.
    pub fn new_tight() -> Self {
        Arena {
            tight_growth: true,
            ..Self::default()
        }
    }
    #[inline]
    pub fn push(&mut self, v: T) -> Id<T> {
        self.materialize_epoch_frame();
        let id = Id::new(self.items.len() as Cint64);
        if self.tight_growth {
            self.items.reserve_tight_for_push();
        }
        self.items.push(v);
        id
    }
    /// Reclaim a just-allocated object that was rejected before publication.
    /// This is valid only for the current tail id; published ids remain stable.
    #[inline]
    pub fn pop_last_if(&mut self, id: Id<T>) -> bool {
        if id.is_some() && id.index().checked_add(1) == Some(self.items.len()) {
            self.materialize_epoch_frame();
            self.items.pop();
            true
        } else {
            false
        }
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
    #[inline]
    pub fn capacity(&self) -> usize {
        self.items.capacity()
    }
    /// Bytes reserved by the arena's primary item vector. Nested allocations
    /// owned by individual items are intentionally excluded and reported by
    /// their subsystem-specific census.
    #[inline]
    pub fn reserved_item_bytes(&self) -> usize {
        self.items
            .capacity()
            .saturating_mul(std::mem::size_of::<T>())
    }
    #[inline]
    pub fn item_size(&self) -> usize {
        std::mem::size_of::<T>()
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
        self.materialize_epoch_frame();
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
        self.open_depth = 0;
        self.journal_stack.clear();
    }
    /// Drop every object and return the backing allocations to the allocator.
    ///
    /// Use this only at a task boundary where no arena id can remain live.
    /// Most resets deliberately retain capacity for reuse; exceptionally large
    /// one-shot saturation pools must instead be released before a different
    /// completion phase starts, or their empty backing vectors dominate RSS.
    #[inline]
    pub fn clear_releasing_capacity(&mut self) {
        let tight_growth = self.tight_growth;
        *self = if tight_growth {
            Self::new_tight()
        } else {
            Self::new()
        };
    }
    #[inline]
    pub fn iter(&self) -> ChunkIter<'_, T> {
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
        self.open_depth > 0 || !self.wm_stack.is_empty()
    }
    /// Number of open journaled epochs.
    #[inline]
    pub fn open_depth(&self) -> usize {
        self.open_depth
    }
    /// True if any item below `watermark` has been saved (mutated in place)
    /// in any journal frame opened after `base_open_depth`.
    #[inline]
    pub fn has_saves_below_since_depth(&self, watermark: usize, base_open_depth: usize) -> bool {
        self.journal_stack
            .iter()
            .rev()
            .take_while(|frame| frame.hi > base_open_depth)
            .any(|frame| frame.saves.iter().any(|&(ix, _)| ix < watermark))
    }
    /// True if any item below `watermark` saved in a journal frame opened
    /// after `base_open_depth` satisfies `predicate(index, saved_original, current)`.
    #[inline]
    pub fn has_matching_save_below_since_depth(
        &self,
        watermark: usize,
        base_open_depth: usize,
        mut predicate: impl FnMut(usize, &T, &T) -> bool,
    ) -> bool {
        self.journal_stack
            .iter()
            .rev()
            .take_while(|frame| frame.hi > base_open_depth)
            .any(|frame| {
                frame
                    .saves
                    .iter()
                    .any(|(ix, orig)| *ix < watermark && predicate(*ix, orig, &self.items[*ix]))
            })
    }
    /// Materialize the frame of the innermost open journaled epoch before the
    /// first change of this arena inside it. Every open depth above the last
    /// materialized frame was opened while the arena was untouched, so the
    /// current length is the allocation length at each of their openings —
    /// the watermark the eager scheme recorded for every one of them.
    #[inline]
    fn materialize_epoch_frame(&mut self) {
        let depth = self.open_depth;
        if depth == 0 {
            return;
        }
        let lo = self.journal_stack.last().map_or(1, |frame| frame.hi + 1);
        if lo <= depth {
            self.journal_stack.push(EpochJournalFrame {
                lo,
                hi: depth,
                watermark: self.items.len(),
                saved_keys: crate::fxhash::FxHashSet::default(),
                saves: Vec::new(),
            });
        }
    }
}

impl<T: Clone> Arena<T> {
    /// Open a JOURNALED epoch: allocations are dropped on pop AND in-place
    /// mutations of pre-epoch slots are rolled back (first-touch clone).
    #[inline]
    pub fn push_epoch(&mut self) {
        self.open_depth += 1;
    }
    /// Close a journaled epoch: replay the saves in reverse, then truncate.
    pub fn pop_epoch(&mut self) {
        let depth = self.open_depth;
        if depth == 0 {
            return;
        }
        self.open_depth = depth - 1;
        let Some(frame) = self.journal_stack.last_mut() else {
            return;
        };
        if frame.hi != depth {
            // Untouched during the closed epoch: nothing to roll back.
            return;
        }
        self.items.truncate(frame.watermark);
        if frame.lo == depth {
            let frame = self.journal_stack.pop().expect("checked above");
            for (ix, v) in frame.saves.into_iter().rev() {
                self.items[ix] = v;
            }
        } else {
            // The shallower depths of the run keep the same watermark and,
            // never touched while innermost, have no saves of their own.
            frame.hi = depth - 1;
            frame.saved_keys.clear();
            let saves = std::mem::take(&mut frame.saves);
            for (ix, v) in saves.into_iter().rev() {
                self.items[ix] = v;
            }
        }
    }
    /// Merge all open journaled epochs above `target_depth` into `target_depth`
    /// without rolling back their mutations. When `target_depth == 0`, all open
    /// journaled epochs are committed permanently into depth 0 and their saved
    /// rollback clones are released. When `target_depth > 0`, epochs
    /// `target_depth..=open_depth` collapse into a single epoch at
    /// `target_depth` that retains only the earliest pre-`target_depth` clone
    /// per slot below `target_depth`'s watermark.
    pub fn coalesce_epochs_to(&mut self, target_depth: usize) {
        if self.open_depth <= target_depth {
            return;
        }
        self.open_depth = target_depth;
        if target_depth == 0 {
            self.journal_stack.clear();
            self.journal_stack.shrink_to_fit();
            return;
        }
        let first_idx = self
            .journal_stack
            .partition_point(|frame| frame.hi < target_depth);
        if first_idx >= self.journal_stack.len() {
            return;
        }
        let watermark = self.journal_stack[first_idx].watermark;
        let tail: Vec<EpochJournalFrame<T>> = self.journal_stack.drain((first_idx + 1)..).collect();
        let target_frame = &mut self.journal_stack[first_idx];
        target_frame.hi = target_depth;
        for frame in tail {
            for (ix, val) in frame.saves {
                if ix < watermark && target_frame.saved_keys.insert(ix) {
                    target_frame.saves.push((ix, val));
                }
            }
        }
        target_frame.saves.shrink_to_fit();
    }
    /// The mutate path under branch epochs: the first mutation of a
    /// pre-epoch slot in the CURRENT epoch saves a rollback clone (zero-cost
    /// when no journaled epoch is open). The `ProcessContext` accessor macro
    /// routes every branch-state arena through this; arenas holding
    /// immutable-model / cross-task state keep the raw `get_mut`.
    #[inline]
    pub fn get_mut_journaled(&mut self, id: Id<T>) -> &mut T {
        if self.open_depth > 0 {
            self.materialize_epoch_frame();
            let frame = self.journal_stack.last_mut().expect("materialized");
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
        let _test_env = crate::test_env::read();
        let mut arena = Arena::new();
        for value in 0..32 {
            arena.push(value);
        }
        arena.push_epoch();
        *arena.get_mut_journaled(super::Id::new(0)) = 99;
        arena.push(32);
        assert!(arena.epoch_open());
        assert!(!arena.journal_stack.is_empty());
        let items_capacity = arena.items.capacity();
        let items_ptr = arena.items.first_chunk_ptr();

        arena.clear_preserving_capacity();

        assert_eq!(arena.len(), 0);
        assert!(!arena.epoch_open());
        assert!(arena.journal_stack.is_empty());
        assert_eq!(arena.items.capacity(), items_capacity);
        assert_eq!(arena.items.first_chunk_ptr(), items_ptr);

        let id = arena.push(7);
        assert_eq!(id.index(), 0, "reused arenas restart their id space");
        assert_eq!(*arena.get(id), 7, "no old object content survives");
    }

    #[test]
    fn arena_releasing_clear_drops_storage_and_preserves_growth_policy() {
        let _test_env = crate::test_env::read();
        let mut arena = Arena::new_tight();
        for value in 0..32_768 {
            arena.push(value);
        }
        assert!(arena.capacity() > 0);
        arena.push_epoch();

        arena.clear_releasing_capacity();

        assert_eq!(arena.len(), 0);
        assert_eq!(arena.capacity(), 0);
        assert!(!arena.epoch_open());
        assert!(arena.tight_growth);
        let id = arena.push(7);
        assert_eq!(id.index(), 0);
        assert!(arena.capacity() <= 4_096);
    }

    /// Chunked storage must behave as one `Vec` across chunk boundaries:
    /// push, pop, truncate (inside and across chunks), journaled rollback and
    /// iteration in both directions, for tight and ordinary arenas.
    #[test]
    fn chunked_arena_matches_vec_across_chunk_boundaries() {
        let _test_env = crate::test_env::read();
        let chunk = super::CHUNK_LEN;
        for tight in [false, true] {
            let mut arena: Arena<usize> = if tight { Arena::new_tight() } else { Arena::new() };
            let mut model: Vec<usize> = Vec::new();
            for value in 0..(3 * chunk + 17) {
                assert_eq!(arena.push(value).index(), value);
                model.push(value);
            }
            assert!(arena.iter().copied().eq(model.iter().copied()));
            assert!(arena.iter().rev().copied().eq(model.iter().rev().copied()));
            assert_eq!(arena.iter().len(), model.len());
            for cut in [3 * chunk, 2 * chunk + 1, chunk - 1, chunk + 5] {
                if cut < model.len() {
                    arena.truncate_to(cut);
                    model.truncate(cut);
                } else {
                    while model.len() < cut {
                        let v = model.len() * 3;
                        arena.push(v);
                        model.push(v);
                    }
                }
                assert_eq!(arena.len(), model.len());
                assert!(arena.iter().copied().eq(model.iter().copied()), "cut {cut}");
            }
            let last = super::Id::new((model.len() - 1) as super::Cint64);
            assert!(arena.pop_last_if(last));
            model.pop();
            arena.push_epoch();
            *arena.get_mut_journaled(super::Id::new(chunk as super::Cint64 + 2)) = 1;
            *arena.get_mut_journaled(super::Id::new(3)) = 2;
            for v in 0..(2 * chunk) {
                arena.push(v);
            }
            arena.pop_epoch();
            assert!(arena.iter().copied().eq(model.iter().copied()));
            assert!(arena.capacity() >= arena.len());
        }
    }
    #[test]
    fn tight_arena_bounds_capacity_without_changing_ids_or_epoch_rollback() {
        let _test_env = crate::test_env::read();
        let mut arena = Arena::new_tight();
        for value in 0..10_000 {
            let id = arena.push(value);
            assert_eq!(id.index(), value);
        }
        assert!(arena.capacity() <= 12_500);
        assert_eq!(*arena.get(super::Id::new(9_999)), 9_999);

        arena.push_epoch();
        *arena.get_mut_journaled(super::Id::new(7)) = 77_777;
        let transient = arena.push(10_000);
        assert_eq!(transient.index(), 10_000);
        arena.pop_epoch();

        assert_eq!(arena.len(), 10_000);
        assert_eq!(*arena.get(super::Id::new(7)), 7);
        let reused = arena.push(10_001);
        assert_eq!(reused.index(), transient.index());
    }
    /// The lazily materialized journal must be observationally identical to
    /// the eager one-frame-per-epoch scheme. Reference model: an explicit
    /// stack of (length, full snapshot) per open epoch.
    #[test]
    fn lazy_epoch_frames_match_eager_snapshots_under_random_operations() {
        let _test_env = crate::test_env::read();
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        for _round in 0..200 {
            let mut arena: Arena<u64> = Arena::new();
            let mut model: Vec<u64> = Vec::new();
            let mut snapshots: Vec<Vec<u64>> = Vec::new();
            for _ in 0..(next(8) as usize) {
                let v = next(1000);
                arena.push(v);
                model.push(v);
            }
            for _step in 0..400 {
                match next(7) {
                    0 | 1 => {
                        arena.push_epoch();
                        snapshots.push(model.clone());
                    }
                    2 => {
                        if let Some(snapshot) = snapshots.pop() {
                            arena.pop_epoch();
                            model = snapshot;
                        }
                    }
                    3 => {
                        let v = next(1000);
                        let id = arena.push(v);
                        assert_eq!(id.index(), model.len());
                        model.push(v);
                    }
                    4 | 5 => {
                        if !model.is_empty() {
                            let ix = next(model.len() as u64) as usize;
                            let v = next(1000);
                            *arena.get_mut_journaled(super::Id::new(ix as i64)) = v;
                            model[ix] = v;
                        }
                    }
                    _ => {
                        // `pop_last_if` reclaims a just-allocated tail object:
                        // only objects allocated inside the innermost epoch.
                        let floor = snapshots.last().map_or(0, |snapshot| snapshot.len());
                        if model.len() > floor {
                            let last = super::Id::new(model.len() as i64 - 1);
                            assert!(arena.pop_last_if(last));
                            model.pop();
                        }
                    }
                }
                assert_eq!(arena.len(), model.len());
                assert!(arena.iter().copied().eq(model.iter().copied()));
                assert_eq!(arena.epoch_open(), !snapshots.is_empty());
            }
            while let Some(snapshot) = snapshots.pop() {
                arena.pop_epoch();
                assert!(arena.iter().copied().eq(snapshot.iter().copied()));
            }
        }
    }

    #[test]
    fn coalesce_epochs_to_preserves_earliest_pre_target_saves_and_watermark() {
        let _test_env = crate::test_env::read();
        let mut arena: Arena<String> = Arena::new();
        let id0 = arena.push("a0".to_string());
        let id1 = arena.push("b0".to_string());

        // Epoch 1: mutate slot 0 ("a0" -> "a1") and allocate slot 2 ("c1").
        arena.push_epoch();
        *arena.get_mut_journaled(id0) = "a1".to_string();
        let id2 = arena.push("c1".to_string());

        // Epoch 2: mutate slot 0 again ("a1" -> "a2"), mutate slot 1 for the
        // first time ("b0" -> "b2"), and allocate slot 3 ("d2").
        arena.push_epoch();
        *arena.get_mut_journaled(id0) = "a2".to_string();
        *arena.get_mut_journaled(id1) = "b2".to_string();
        let id3 = arena.push("d2".to_string());

        // Epoch 3: mutate slot 1 again ("b2" -> "b3") and mutate slot 2 ("c1" -> "c3").
        arena.push_epoch();
        *arena.get_mut_journaled(id1) = "b3".to_string();
        *arena.get_mut_journaled(id2) = "c3".to_string();
        assert_eq!(arena.open_depth(), 3);

        // Coalesce epochs 1..=3 into target_depth = 1. Current live values must
        // remain unchanged while the open depth collapses to 1.
        arena.coalesce_epochs_to(1);
        assert_eq!(arena.open_depth(), 1);
        assert_eq!(arena.len(), 4);
        assert_eq!(arena.get(id0), "a2");
        assert_eq!(arena.get(id1), "b3");
        assert_eq!(arena.get(id2), "c3");
        assert_eq!(arena.get(id3), "d2");

        // Popping the single coalesced epoch 1 must restore the exact pre-epoch-1
        // state: length 2 with ["a0", "b0"] (not the intermediate "a1" or "b2").
        arena.pop_epoch();
        assert_eq!(arena.open_depth(), 0);
        assert_eq!(arena.len(), 2);
        assert_eq!(arena.get(id0), "a0");
        assert_eq!(arena.get(id1), "b0");
    }
}
