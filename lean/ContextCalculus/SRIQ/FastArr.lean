import ContextCalculus.SRIQ.FastBasic

/-!
# Certificate check for the fast SHIQ procedure: array candidate sets (stage C1d)

The check of `FastDefs.lean` works on finsets, whose operations cost time
quadratic in the set sizes. This file introduces candidate sets on sorted
arrays of naturals (`CandA`), the finset candidate set they denote
(`CandA.view`), and the array operations the fast check uses:

- strictly sorted arrays (`SortedA`, checked by `sortedB`), binary search
  (`bsA`, exact on sorted arrays), canonical sorted arrays of a list
  (`canon`);
- the finsets an array denotes (`absTy`, `absLab`) and their membership;
- the accessors of `CandA` and their agreement with the accessors of the
  view (`nd_view`, `keyOf_view`, `memb_view`, ...).

Nothing here is trusted: the theorems relate every array computation to
the finset definitions of `FastDefs.lean`.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-! ## Sorted arrays -/

/-- Strictly increasing. -/
def SortedA (a : Array Nat) : Prop := a.toList.Pairwise (· < ·)

/-- Strictly increasing, by neighbours. -/
def ascL : List Nat → Bool
  | x :: y :: l => decide (x < y) && ascL (y :: l)
  | _ => true

theorem ascL_pairwise : ∀ l : List Nat, ascL l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: l, h => by
    simp only [ascL, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := ascL_pairwise (y :: l) h.2
    refine List.Pairwise.cons (fun z hz => ?_) ih
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hz)

def sortedB (a : Array Nat) : Bool := ascL a.toList

theorem sortedB_sound {a : Array Nat} (h : sortedB a = true) : SortedA a := ascL_pairwise _ h

theorem SortedA.lt {a : Array Nat} (h : SortedA a) {i j : Nat} (hij : i < j) (hj : j < a.size) :
    a[i]'(by omega) < a[j] := by
  have := List.pairwise_iff_getElem.1 h i j (by simp; omega) (by simpa using hj) hij
  simpa using this

/-- Binary search between `lo` and `hi`. -/
def bsGo (a : Array Nat) (x : Nat) (lo hi : Nat) : Bool :=
  if lo < hi then
    let mid := (lo + hi) / 2
    match a[mid]? with
    | none => false
    | some v => if v = x then true else if v < x then bsGo a x (mid + 1) hi else bsGo a x lo mid
  else false
termination_by hi - lo

/-- Membership by binary search. -/
def bsA (a : Array Nat) (x : Nat) : Bool := bsGo a x 0 a.size

theorem bsGo_sound {a : Array Nat} {x : Nat} (lo hi : Nat) (h : bsGo a x lo hi = true) : x ∈ a := by
  rw [bsGo] at h
  split at h
  · next hlt =>
    dsimp only at h
    split at h
    · simp at h
    · next v hm =>
      by_cases hv : v = x
      · subst hv; exact Array.mem_of_getElem? hm
      · rw [if_neg hv] at h
        split at h
        · exact bsGo_sound _ _ h
        · exact bsGo_sound _ _ h
  · simp at h
termination_by hi - lo
decreasing_by all_goals omega

theorem bsGo_complete {a : Array Nat} (hs : SortedA a) {x : Nat} (lo hi : Nat) (hhi : hi ≤ a.size)
    (k : Nat) (hk : k < a.size) (hlo : lo ≤ k) (hkh : k < hi) (hkx : a[k] = x) :
    bsGo a x lo hi = true := by
  rw [bsGo]
  have hlt : lo < hi := by omega
  have hmid : (lo + hi) / 2 < a.size := by omega
  rw [if_pos hlt]
  dsimp only
  rw [Array.getElem?_eq_getElem hmid]
  dsimp only
  by_cases hv : a[(lo + hi) / 2] = x
  · rw [if_pos hv]
  · rw [if_neg hv]
    split
    · next hvx =>
      refine bsGo_complete hs _ _ hhi k hk ?_ hkh hkx
      by_contra hc
      have : a[k] ≤ a[(lo + hi) / 2] := by
        rcases Nat.lt_or_eq_of_le (show k ≤ (lo + hi) / 2 by omega) with h | h
        · exact le_of_lt (hs.lt h hmid)
        · simp only [h]; exact le_refl _
      omega
    · next hvx =>
      refine bsGo_complete hs _ _ (by omega) k hk hlo ?_ hkx
      by_contra hc
      have : a[(lo + hi) / 2] ≤ a[k] := by
        rcases Nat.lt_or_eq_of_le (show (lo + hi) / 2 ≤ k by omega) with h | h
        · exact le_of_lt (hs.lt h hk)
        · simp only [← h]; exact le_refl _
      omega
termination_by hi - lo
decreasing_by all_goals omega

theorem bsA_iff {a : Array Nat} (hs : SortedA a) {x : Nat} : bsA a x = true ↔ x ∈ a := by
  constructor
  · exact bsGo_sound _ _
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact bsGo_complete hs 0 a.size (le_refl _) k hk (Nat.zero_le _) hk rfl

theorem bsA_sound {a : Array Nat} {x : Nat} (h : bsA a x = true) : x ∈ a := bsGo_sound _ _ h

/-! ## Canonical arrays -/

/-- Drop adjacent duplicates. -/
def dedupAdj : List Nat → List Nat
  | x :: y :: l => if x = y then dedupAdj (y :: l) else x :: dedupAdj (y :: l)
  | l => l

theorem mem_dedupAdj : ∀ (l : List Nat) (z : Nat), z ∈ dedupAdj l ↔ z ∈ l
  | [], _ => by simp [dedupAdj]
  | [_], _ => by simp [dedupAdj]
  | x :: y :: l, z => by
    simp only [dedupAdj]
    split
    · next h => subst h; rw [mem_dedupAdj]; simp
    · rw [List.mem_cons, mem_dedupAdj]; simp

theorem dedupAdj_pairwise : ∀ l : List Nat, l.Pairwise (· ≤ ·) → (dedupAdj l).Pairwise (· < ·)
  | [], _ => by simp [dedupAdj]
  | [_], _ => by simp [dedupAdj]
  | x :: y :: l, h => by
    simp only [dedupAdj]
    have ih := dedupAdj_pairwise (y :: l) (List.Pairwise.of_cons h)
    split
    · exact ih
    · next hxy =>
      refine List.Pairwise.cons (fun z hz => ?_) ih
      rw [mem_dedupAdj] at hz
      have := List.rel_of_pairwise_cons h hz
      have := List.rel_of_pairwise_cons h List.mem_cons_self
      rcases List.mem_cons.1 hz with rfl | hz
      · omega
      · have := List.rel_of_pairwise_cons (List.Pairwise.of_cons h) hz
        omega

/-- The sorted array without duplicates of the members of a list. -/
def canon (l : List Nat) : Array Nat := (dedupAdj (l.mergeSort fun a b => decide (a ≤ b))).toArray

theorem mem_canon {l : List Nat} {x : Nat} : x ∈ canon l ↔ x ∈ l := by
  simp only [canon, List.mem_toArray, mem_dedupAdj, List.mem_mergeSort]

theorem sorted_canon (l : List Nat) : SortedA (canon l) := by
  unfold SortedA canon
  refine dedupAdj_pairwise _ ?_
  have := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  simpa using this

/-- Merge of two lists: on sorted lists, the sorted union. -/
def mergeL : List Nat → List Nat → List Nat
  | [], l => l
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x < y then x :: mergeL xs (y :: ys)
    else if y < x then y :: mergeL (x :: xs) ys
    else x :: mergeL xs ys

theorem mem_mergeL : ∀ (a b : List Nat) (z : Nat), z ∈ mergeL a b ↔ z ∈ a ∨ z ∈ b
  | [], l, z => by simp [mergeL]
  | x :: xs, [], z => by simp [mergeL]
  | x :: xs, y :: ys, z => by
    simp only [mergeL]
    split
    · rw [List.mem_cons, mem_mergeL]; simp only [List.mem_cons]; tauto
    · split
      · rw [List.mem_cons, mem_mergeL]; simp only [List.mem_cons]; tauto
      · next h1 h2 =>
        have : x = y := by omega
        subst this
        rw [List.mem_cons, mem_mergeL]; simp only [List.mem_cons]; tauto

theorem mergeL_pairwise : ∀ (a b : List Nat), a.Pairwise (· < ·) → b.Pairwise (· < ·) →
    (mergeL a b).Pairwise (· < ·)
  | [], l, _, hb => by simpa [mergeL] using hb
  | x :: xs, [], ha, _ => by simpa [mergeL] using ha
  | x :: xs, y :: ys, ha, hb => by
    simp only [mergeL]
    have hxs := List.Pairwise.of_cons ha
    have hys := List.Pairwise.of_cons hb
    split
    · next h =>
      refine List.Pairwise.cons (fun z hz => ?_) (mergeL_pairwise _ _ hxs hb)
      rcases (mem_mergeL _ _ z).1 hz with hz | hz
      · exact List.rel_of_pairwise_cons ha hz
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact h
        · exact lt_trans h (List.rel_of_pairwise_cons hb hz)
    · split
      · next h1 h =>
        refine List.Pairwise.cons (fun z hz => ?_) (mergeL_pairwise _ _ ha hys)
        rcases (mem_mergeL _ _ z).1 hz with hz | hz
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact h
          · exact lt_trans h (List.rel_of_pairwise_cons ha hz)
        · exact List.rel_of_pairwise_cons hb hz
      · next h1 h2 =>
        refine List.Pairwise.cons (fun z hz => ?_) (mergeL_pairwise _ _ hxs hys)
        rcases (mem_mergeL _ _ z).1 hz with hz | hz
        · exact List.rel_of_pairwise_cons ha hz
        · have := List.rel_of_pairwise_cons hb hz; omega

/-- The union of two sorted arrays, sorted. -/
def unionA (a b : Array Nat) : Array Nat := (mergeL a.toList b.toList).toArray

theorem mem_unionA {a b : Array Nat} {z : Nat} : z ∈ unionA a b ↔ z ∈ a ∨ z ∈ b := by
  simp only [unionA, List.mem_toArray, mem_mergeL, Array.mem_def]

theorem sorted_unionA {a b : Array Nat} (ha : SortedA a) (hb : SortedA b) : SortedA (unionA a b) := by
  unfold SortedA unionA
  exact mergeL_pairwise _ _ ha hb

/-! ## The finsets of arrays -/

/-- The names below `n` of a list. -/
def finL (n : Nat) (l : List Nat) : List (Fin n) :=
  l.filterMap fun x => if h : x < n then some ⟨x, h⟩ else none

theorem mem_finL {l : List Nat} {y : Fin n} : y ∈ finL n l ↔ y.val ∈ l := by
  simp only [finL, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, he⟩
    split at he
    · simp only [Option.some.injEq] at he; subst he; exact hx
    · simp at he
  · intro h
    exact ⟨y.val, h, by simp [y.isLt]⟩

theorem finL_pairwise {l : List Nat} (h : l.Pairwise (· < ·)) : (finL n l).Pairwise (· < ·) := by
  refine List.Pairwise.filterMap _ (fun a a' haa b hb b' hb' => ?_) h
  split at hb <;> split at hb' <;> simp only [Option.some.injEq, reduceCtorEq] at hb hb'
  subst hb; subst hb'
  exact haa

def absTy (n : Nat) (a : Array Nat) : Ty n := (finL n a.toList).toFinset

theorem mem_absTy {a : Array Nat} {y : Fin n} : y ∈ absTy n a ↔ y.val ∈ a := by
  simp [absTy, mem_finL]

/-- Role terms of codes. -/
def toRT (m : Nat) (c : Nat) : Option (RoleT (Fin m)) :=
  if h : c < 2 * m then some (ofRc c h) else none

def absLab (m : Nat) (a : Array Nat) : Lab m := (a.toList.filterMap (toRT m)).toFinset

theorem mem_absLab {a : Array Nat} {R : RoleT (Fin m)} : R ∈ absLab m a ↔ rc R ∈ a := by
  simp only [absLab, List.mem_toFinset, List.mem_filterMap, toRT]
  constructor
  · rintro ⟨c, hc, he⟩
    split at he
    · next h => simp only [Option.some.injEq] at he; subst he; rw [rc_ofRc]; exact Array.mem_def.2 hc
    · simp at he
  · intro h
    exact ⟨rc R, Array.mem_def.1 h, by simp [rc_lt R, ofRc_rc]⟩

/-- Equal sorted arrays of names below `n` have equal finsets, and conversely. -/
theorem absTy_inj {a b : Array Nat} (ha : SortedA a) (hb : SortedA b) (hna : ∀ x ∈ a, x < n)
    (hnb : ∀ x ∈ b, x < n) (h : absTy n a = absTy n b) : a = b := by
  have hl : a.toList = b.toList := by
    refine List.Pairwise.eq_of_mem_iff ha hb fun x => ?_
    constructor
    · intro hx
      have := (mem_absTy (y := ⟨x, hna x (Array.mem_def.2 hx)⟩)).2 (Array.mem_def.2 hx)
      rw [h] at this
      exact Array.mem_def.1 (mem_absTy.1 this)
    · intro hx
      have := (mem_absTy (y := ⟨x, hnb x (Array.mem_def.2 hx)⟩)).2 (Array.mem_def.2 hx)
      rw [← h] at this
      exact Array.mem_def.1 (mem_absTy.1 this)
  exact Array.ext' hl

theorem absLab_inj {a b : Array Nat} (ha : SortedA a) (hb : SortedA b) (hna : ∀ x ∈ a, x < 2 * m)
    (hnb : ∀ x ∈ b, x < 2 * m) (h : absLab m a = absLab m b) : a = b := by
  have hl : a.toList = b.toList := by
    refine List.Pairwise.eq_of_mem_iff ha hb fun x => ?_
    constructor
    · intro hx
      have hx' := hna x (Array.mem_def.2 hx)
      have := (mem_absLab (R := ofRc x hx')).2 (by rw [rc_ofRc]; exact Array.mem_def.2 hx)
      rw [h, mem_absLab, rc_ofRc] at this
      exact Array.mem_def.1 this
    · intro hx
      have hx' := hnb x (Array.mem_def.2 hx)
      have := (mem_absLab (R := ofRc x hx')).2 (by rw [rc_ofRc]; exact Array.mem_def.2 hx)
      rw [← h, mem_absLab, rc_ofRc] at this
      exact Array.mem_def.1 this
  exact Array.ext' hl

/-- The sorted list of a sorted array's finset is the array. -/
theorem sort_absTy {a : Array Nat} (ha : SortedA a) :
    (absTy n a).sort (· ≤ ·) = finL n a.toList := by
  have hp : (finL n a.toList).Pairwise (· < ·) := finL_pairwise ha
  have hnd : (finL n a.toList).Nodup := hp.nodup
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
    (hp.imp le_of_lt) ?_
  rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnd]
  intro y
  rw [Finset.mem_sort, absTy, List.mem_toFinset]

theorem absTy_empty : absTy n #[] = ∅ := by
  ext y; simp [mem_absTy]

theorem absLab_empty : absLab m #[] = ∅ := by
  ext R; simp [mem_absLab]

theorem absTy_single (a : Fin n) : absTy n #[a.val] = {a} := by
  ext y; simp [mem_absTy, Fin.ext_iff]

theorem absTy_unionA (a b : Array Nat) : absTy n (unionA a b) = absTy n a ∪ absTy n b := by
  ext y; rw [Finset.mem_union, mem_absTy, mem_absTy, mem_absTy, mem_unionA]

theorem absLab_unionA (a b : Array Nat) : absLab m (unionA a b) = absLab m a ∪ absLab m b := by
  ext R; rw [Finset.mem_union, mem_absLab, mem_absLab, mem_absLab, mem_unionA]

theorem absTy_canon {l : List Nat} {s : Ty n} (h : ∀ y : Fin n, y ∈ s ↔ y.val ∈ l) :
    absTy n (canon l) = s := by
  ext y; rw [mem_absTy, mem_canon, h]

/-! ## Role codes -/

/-- The code of the inverse role. -/
def flipC (c : Nat) : Nat := if c % 2 = 0 then c + 1 else c - 1

theorem rc_flip (R : RoleT (Fin m)) : rc R.flip = flipC (rc R) := by
  cases R <;> simp only [RoleT.flip, rc, flipC] <;> split <;> omega

theorem flipC_flipC (c : Nat) : flipC (flipC c) = c := by
  unfold flipC; split <;> split <;> omega

/-- The flipped label. -/
def flipA (L : Array Nat) : Array Nat := canon (L.toList.map flipC)

theorem absLab_flipA (L : Array Nat) : absLab m (flipA L) = flipL (absLab m L) := by
  ext R
  rw [mem_absLab, mem_flipL, mem_absLab, flipA, mem_canon, List.mem_map, rc_flip]
  constructor
  · rintro ⟨c, hc, he⟩
    rw [← he, flipC_flipC]; exact Array.mem_def.2 hc
  · intro h
    exact ⟨_, Array.mem_def.1 h, flipC_flipC _⟩

/-! ## Array candidate sets -/

structure EntryA where
  lab : Array Nat
  fill : Array Nat
  kid : Nat
deriving Inhabited, DecidableEq

structure KeyA where
  seed : Array Nat
  lab : Array Nat
  pi : Array Nat
deriving Inhabited, DecidableEq

structure NodeA where
  ctx : Nat
  ty : Array Nat
  pool : List EntryA
deriving Inhabited

/-- A candidate set on sorted arrays: as `Cand`, with names as naturals and
roles as their codes. -/
structure CandA where
  keys : Array KeyA
  nodes : Array NodeA
  members : Array (Array Nat)
  roots : List Nat
  bk : Array (Array Nat)
  uni : Array (Array Nat)
  /-- a hint for the branch covers: (context, type) ↦ (node, position of the
  node in the context's members); the check verifies every lookup -/
  idx : Std.HashMap (Nat × Array Nat) (Nat × Nat) := ∅

def viewSpec (n m : Nat) (σ : Array Nat × Array Nat) : Spec n m := ⟨absLab m σ.1, absTy n σ.2⟩

def viewEntry (n m : Nat) (e : EntryA) : Entry n m := ⟨⟨absLab m e.lab, absTy n e.fill⟩, e.kid⟩

def viewKey (n m : Nat) (k : KeyA) : Key n m := ⟨absTy n k.seed, absLab m k.lab, absTy n k.pi⟩

def viewNode (n m : Nat) (v : NodeA) : FNode n m :=
  ⟨v.ctx, absTy n v.ty, v.pool.map (viewEntry n m)⟩

/-- The finset candidate set an array candidate set denotes. -/
def CandA.view (C : CandA) (n m : Nat) : Cand n m :=
  { keys := C.keys.map (viewKey n m)
    nodes := C.nodes.map (viewNode n m)
    members := C.members
    roots := C.roots
    bk := C.bk.map (absTy n)
    uni := C.uni.map (absTy n) }

theorem default_nodeA : (default : NodeA) = ⟨0, #[], []⟩ := rfl
theorem default_keyA : (default : KeyA) = ⟨#[], #[], #[]⟩ := rfl

section Acc

variable (C : CandA)

def ndA (i : Nat) : NodeA := C.nodes[i]?.getD default
def keyA (k : Nat) : KeyA := C.keys[k]?.getD default
def bkA (j : Nat) : Array Nat := C.bk[j]?.getD #[]
def uniA (k : Nat) : Array Nat := C.uni[k]?.getD #[]

def membA (k : Nat) : List Nat :=
  (C.members[k]?.getD #[]).toList.filter fun i => decide (i < C.nodes.size ∧ (ndA C i).ctx = k)

variable {C}

@[simp] theorem view_nodes_size : (C.view n m).nodes.size = C.nodes.size := by simp [CandA.view]
@[simp] theorem view_keys_size : (C.view n m).keys.size = C.keys.size := by simp [CandA.view]
@[simp] theorem view_roots : (C.view n m).roots = C.roots := rfl

theorem nd_view (i : Nat) : nd (C.view n m) i = viewNode n m (ndA C i) := by
  simp only [nd, ndA, CandA.view, Array.getElem?_map]
  cases C.nodes[i]? with
  | none =>
    rw [Option.map_none, Option.getD_none, Option.getD_none, default_nodeA]
    simp only [viewNode, absTy_empty, List.map_nil]
    rfl
  | some v => rfl

theorem keyOf_view (k : Nat) : keyOf (C.view n m) k = viewKey n m (keyA C k) := by
  simp only [keyOf, keyA, CandA.view, Array.getElem?_map]
  cases C.keys[k]? with
  | none =>
    rw [Option.map_none, Option.getD_none, Option.getD_none, default_keyA]
    simp only [viewKey, absTy_empty, absLab_empty]
    rfl
  | some v => rfl

theorem bkOf_view (j : Nat) : bkOf (C.view n m) j = absTy n (bkA C j) := by
  simp only [bkOf, bkA, CandA.view, Array.getElem?_map]
  cases C.bk[j]? with
  | none => simp [absTy_empty]
  | some v => rfl

theorem uniOf_view (k : Nat) : uniOf (C.view n m) k = absTy n (uniA C k) := by
  simp only [uniOf, uniA, CandA.view, Array.getElem?_map]
  cases C.uni[k]? with
  | none => simp [absTy_empty]
  | some v => rfl

theorem memb_view (k : Nat) : memb (C.view n m) k = membA C k := by
  simp only [memb, membA, view_nodes_size, nd_view, viewNode]
  rfl

theorem mem_membA {k j : Nat} (h : j ∈ membA C k) : j < C.nodes.size ∧ (ndA C j).ctx = k := by
  simp only [membA, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

end Acc

/-! ## The fast index -/

/-- Indexes for the array check: for each name, the codes of the roles whose
relevant fillers (`relBy`) contain it; for each role code, the sorted codes
of its super-roles. -/
structure IxF where
  relRev : Array (List Nat)
  upA : Array (Array Nat)

def mkIxF (O : Ontology (Fin n) (Fin m)) (ix : Ix n m) : IxF where
  relRev := buildIdx n (fun p => some (p.2.val, p.1)) (relSrc O)
  upA := ix.upArr.map fun L => canon (Multiset.sort (L.val.map rc) (· ≤ ·))

/-- The super-roles of a role, sorted. -/
def upSA (ixf : IxF) (R : RoleT (Fin m)) : Array Nat := (ixf.upA[rc R]?).getD #[rc R]

theorem absLab_upSA {O : Ontology (Fin n) (Fin m)} {ix : Ix n m} (R : RoleT (Fin m)) :
    absLab m (upSA (mkIxF O ix) R) = upS ix R := by
  simp only [upSA, upS, mkIxF, Array.getElem?_map]
  cases ix.upArr[rc R]? with
  | none =>
    ext S
    rw [Option.map_none, Option.getD_none, Option.getD_none, mem_absLab, Finset.mem_singleton,
      Array.mem_singleton]
    exact ⟨rc_inj, fun h => h ▸ rfl⟩
  | some L =>
    ext S
    simp only [Option.map_some, Option.getD_some, mem_absLab, Array.mem_def]
    rw [← Array.mem_def, mem_canon, Multiset.mem_sort, Multiset.mem_map]
    constructor
    · rintro ⟨S', hS', he⟩; rw [← rc_inj he]; exact hS'
    · intro h; exact ⟨S, h, rfl⟩

theorem sorted_upSA {O : Ontology (Fin n) (Fin m)} {ix : Ix n m} (R : RoleT (Fin m)) :
    SortedA (upSA (mkIxF O ix) R) := by
  simp only [upSA, mkIxF, Array.getElem?_map]
  cases ix.upArr[rc R]? with
  | none => simp [SortedA]
  | some L => exact sorted_canon _

theorem bnd_upSA {O : Ontology (Fin n) (Fin m)} {ix : Ix n m} (R : RoleT (Fin m)) :
    ∀ x ∈ upSA (mkIxF O ix) R, x < 2 * m := by
  simp only [upSA, mkIxF, Array.getElem?_map]
  cases ix.upArr[rc R]? with
  | none => simp only [Option.map_none, Option.getD_none]; intro x hx; simp at hx; rw [hx]; exact rc_lt R
  | some L =>
    simp only [Option.map_some, Option.getD_some]
    intro x hx
    rw [mem_canon, Multiset.mem_sort, Multiset.mem_map] at hx
    obtain ⟨S, -, rfl⟩ := hx
    exact rc_lt S

/-- Some role of the sorted label `L` has `a` among its relevant fillers. -/
def relHitA (ixf : IxF) (a : Nat) (L : Array Nat) : Bool := (getL ixf.relRev a).any (bsA L)

theorem relHitA_iff {O : Ontology (Fin n) (Fin m)} {L : Array Nat} (hL : SortedA L) (a : Fin n) :
    relHitA (mkIxF O (mkIx O)) a.val L = true ↔ a ∈ relI (mkIx O) (absLab m L) := by
  simp only [relHitA, mkIxF, List.any_eq_true, bsA_iff hL, relI, Finset.mem_biUnion,
    List.mem_toFinset, mem_absLab, mem_relBy]
  constructor
  · rintro ⟨c, hcm, hc⟩
    obtain ⟨x, hx, he⟩ := (mem_buildIdx a.isLt).1 hcm
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    have hx' : x = (x.1, a) := Prod.ext rfl (Fin.ext h1)
    have : ∃ S : RoleT (Fin m), rc S = x.1 := by
      simp only [relSrc, List.mem_append, List.mem_filterMap, List.mem_map] at hx
      rcases hx with ⟨q, -, hq⟩ | ⟨q, -, rfl⟩
      · split at hq
        · simp only [Option.some.injEq] at hq; exact ⟨_, congrArg Prod.fst hq⟩
        · simp at hq
      · exact ⟨_, rfl⟩
    obtain ⟨S, hS⟩ := this
    refine ⟨S, ?_, ?_⟩
    · rw [hS]; exact hc
    · rw [hS, ← hx']; exact hx
  · rintro ⟨S, hS, hx⟩
    exact ⟨rc S, (mem_buildIdx a.isLt).2 ⟨(rc S, a), hx, rfl⟩, hS⟩

end ContextCalculus.SRIQ.Fast

#print axioms ContextCalculus.SRIQ.Fast.bsA_iff
#print axioms ContextCalculus.SRIQ.Fast.absTy_inj
#print axioms ContextCalculus.SRIQ.Fast.sort_absTy
#print axioms ContextCalculus.SRIQ.Fast.nd_view
#print axioms ContextCalculus.SRIQ.Fast.absLab_upSA
#print axioms ContextCalculus.SRIQ.Fast.relHitA_iff
