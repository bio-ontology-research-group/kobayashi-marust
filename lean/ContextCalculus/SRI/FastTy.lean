import ContextCalculus.SRI.Procedure
import Mathlib.Data.Finset.Sort

/-!
# Fast operations on types (v1.6.3, P2d)

A type is a `Finset (Fin n)`, which the compiler stores as a list in no
fixed order. Union, insertion and subset on such lists cost quadratic
time, and `Finset.sort` sorts on every call. This file gives operations
that keep the stored list strictly increasing and work on it in linear
time:

- `toL`: the members in increasing order. It returns the stored list
  when that list is already increasing (one linear check), and sorts it
  otherwise. It equals `Finset.sort`.
- `uni`, `ins`, `sub`, `ofL`: union, insertion, subset and the type of a
  list, by merging sorted lists. Each equals its `Finset` counterpart
  (`uni_eq`, `ins_eq`, `sub_eq`, `ofL_eq`), and the types they build
  store increasing lists, so later calls of `toL` take the fast path.

The proofs of the procedure rewrite with these equations and keep
working with `Finset`.
-/

namespace ContextCalculus.SRI.Proc

variable {n : Nat}

/-! ## Increasing lists -/

/-- Each name is smaller than the next. -/
def sortedB : List (Fin n) → Bool
  | a :: b :: l => decide (a < b) && sortedB (b :: l)
  | _ => true

theorem pairwise_of_sortedB : ∀ {l : List (Fin n)}, sortedB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_sortedB h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.1 ih).1 x hx)

/-- The stored list if it is increasing, else the sorted list. -/
def toLRaw (l : List (Fin n)) : List (Fin n) :=
  if sortedB l then l else l.mergeSort (fun a b => decide (a ≤ b))

theorem toLRaw_eq (l : List (Fin n)) : toLRaw l = l.mergeSort (fun a b => decide (a ≤ b)) := by
  unfold toLRaw
  split
  · next h =>
    exact (List.mergeSort_eq_self (r := (· ≤ ·)) ((pairwise_of_sortedB h).imp le_of_lt)).symm
  · rfl

/-- The members of a type in increasing order. -/
def toL (t : Ty n) : List (Fin n) :=
  Quot.liftOn t.val toLRaw fun a b h => by
    rw [toLRaw_eq, toLRaw_eq]
    exact congrArg (fun s : Multiset (Fin n) => Multiset.sort s (· ≤ ·)) (Quot.sound h)

theorem toL_eq_sort (t : Ty n) : toL t = t.sort (· ≤ ·) := by
  rcases t with ⟨s, hs⟩
  induction s using Quot.ind
  exact toLRaw_eq _

theorem mem_toL {t : Ty n} {a : Fin n} : a ∈ toL t ↔ a ∈ t := by
  rw [toL_eq_sort]; exact Finset.mem_sort _

theorem toL_sorted (t : Ty n) : (toL t).Pairwise (· < ·) := by
  rw [toL_eq_sort]
  exact ((Finset.pairwise_sort t _).and (Finset.sort_nodup t _)).imp
    fun h => lt_of_le_of_ne h.1 h.2

theorem toL_inj {K K' : Ty n} (h : toL K = toL K') : K = K' := by
  ext x; rw [← mem_toL, h, mem_toL]

/-- The type of an increasing list. It stores the list as it is. -/
def ofSorted (l : List (Fin n)) (h : l.Pairwise (· < ·)) : Ty n :=
  ⟨l, h.imp ne_of_lt⟩

theorem mem_ofSorted {l : List (Fin n)} {h : l.Pairwise (· < ·)} {a : Fin n} :
    a ∈ ofSorted l h ↔ a ∈ l :=
  Multiset.mem_coe

/-! ## Merging -/

/-- The union of two increasing lists. -/
def unionL : List (Fin n) → List (Fin n) → List (Fin n)
  | [], l => l
  | a :: l, [] => a :: l
  | a :: l, b :: l' =>
    if a < b then a :: unionL l (b :: l')
    else if b < a then b :: unionL (a :: l) l'
    else a :: unionL l l'
termination_by l l' => l.length + l'.length

theorem mem_unionL {x : Fin n} : ∀ l l' : List (Fin n), x ∈ unionL l l' ↔ x ∈ l ∨ x ∈ l'
  | [], l => by simp [unionL]
  | a :: l, [] => by simp [unionL]
  | a :: l, b :: l' => by
    rw [unionL]
    split_ifs with h1 h2
    · simp only [List.mem_cons, mem_unionL l (b :: l')]; tauto
    · simp only [List.mem_cons, mem_unionL (a :: l) l']; tauto
    · have hab : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst hab
      simp only [List.mem_cons, mem_unionL l l']; tauto
termination_by l l' => l.length + l'.length

theorem unionL_sorted : ∀ {l l' : List (Fin n)}, l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (unionL l l').Pairwise (· < ·)
  | [], _, _, h' => by rw [unionL]; exact h'
  | _ :: _, [], h, _ => by rw [unionL]; exact h
  | a :: l, b :: l', h, h' => by
    have ha := List.pairwise_cons.1 h
    have hb := List.pairwise_cons.1 h'
    rw [unionL]
    split_ifs with h1 h2
    · refine List.pairwise_cons.2 ⟨fun x hx => ?_, unionL_sorted ha.2 h'⟩
      rcases (mem_unionL _ _).1 hx with hx | hx
      · exact ha.1 x hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact h1
        · exact h1.trans (hb.1 x hx)
    · refine List.pairwise_cons.2 ⟨fun x hx => ?_, unionL_sorted h hb.2⟩
      rcases (mem_unionL _ _).1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact h2
        · exact h2.trans (ha.1 x hx)
      · exact hb.1 x hx
    · have hab : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst hab
      refine List.pairwise_cons.2 ⟨fun x hx => ?_, unionL_sorted ha.2 hb.2⟩
      rcases (mem_unionL _ _).1 hx with hx | hx
      · exact ha.1 x hx
      · exact hb.1 x hx
termination_by l l' => l.length + l'.length

/-- Whether every member of the first increasing list is in the second. -/
def subL : List (Fin n) → List (Fin n) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: l' =>
    if a < b then false
    else if b < a then subL (a :: l) l'
    else subL l l'
termination_by l l' => l.length + l'.length

theorem subL_iff : ∀ {l l' : List (Fin n)}, l.Pairwise (· < ·) → l'.Pairwise (· < ·) →
    (subL l l' = true ↔ ∀ x ∈ l, x ∈ l')
  | [], _, _, _ => by simp [subL]
  | a :: l, [], _, _ => by
    rw [subL]
    constructor
    · intro h; cases h
    · intro h; exact absurd (h a (List.mem_cons_self ..)) List.not_mem_nil
  | a :: l, b :: l', h, h' => by
    have ha := List.pairwise_cons.1 h
    have hb := List.pairwise_cons.1 h'
    rw [subL]
    split_ifs with h1 h2
    · simp only [false_iff, not_forall]
      refine ⟨a, List.mem_cons_self .., fun hm => ?_⟩
      rcases List.mem_cons.1 hm with rfl | hm
      · exact lt_irrefl _ h1
      · exact lt_asymm h1 (hb.1 a hm)
    · rw [subL_iff h hb.2]
      constructor
      · intro hs x hx; exact List.mem_cons_of_mem _ (hs x hx)
      · intro hs x hx
        rcases List.mem_cons.1 (hs x hx) with rfl | hm
        · exfalso
          rcases List.mem_cons.1 hx with rfl | hx
          · exact lt_irrefl _ h2
          · exact lt_asymm h2 (ha.1 _ hx)
        · exact hm
    · have hab : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst hab
      rw [subL_iff ha.2 hb.2]
      constructor
      · intro hs x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hs x hx)
      · intro hs x hx
        rcases List.mem_cons.1 (hs x (List.mem_cons_of_mem _ hx)) with rfl | hm
        · exact absurd (ha.1 _ hx) (lt_irrefl _)
        · exact hm
termination_by l l' => l.length + l'.length

/-- The increasing list of the members of a list: sort the halves and
merge them. -/
def sortL : List (Fin n) → List (Fin n)
  | [] => []
  | [a] => [a]
  | a :: b :: l =>
    unionL (sortL ((a :: b :: l).take ((l.length + 2) / 2)))
      (sortL ((a :: b :: l).drop ((l.length + 2) / 2)))
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

theorem mem_sortL {x : Fin n} : ∀ l : List (Fin n), x ∈ sortL l ↔ x ∈ l
  | [] => by simp [sortL]
  | [a] => by simp [sortL]
  | a :: b :: l => by
    rw [sortL, mem_unionL, mem_sortL, mem_sortL, ← List.mem_append, List.take_append_drop]
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

theorem sortL_sorted : ∀ l : List (Fin n), (sortL l).Pairwise (· < ·)
  | [] => by simp [sortL]
  | [a] => by simp [sortL]
  | a :: b :: l => by
    rw [sortL]
    exact unionL_sorted (sortL_sorted _) (sortL_sorted _)
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-! ## The operations on types -/

/-- Union. -/
def uni (s t : Ty n) : Ty n :=
  ofSorted (unionL (toL s) (toL t)) (unionL_sorted (toL_sorted s) (toL_sorted t))

theorem uni_eq (s t : Ty n) : uni s t = s ∪ t := by
  ext x
  simp only [uni, mem_ofSorted, mem_unionL, mem_toL, Finset.mem_union]

/-- Insertion. -/
def ins (a : Fin n) (s : Ty n) : Ty n := uni {a} s

theorem ins_eq (a : Fin n) (s : Ty n) : ins a s = insert a s := by
  rw [ins, uni_eq, Finset.insert_eq]

/-- Subset. -/
def sub (s t : Ty n) : Bool := subL (toL s) (toL t)

theorem sub_eq (s t : Ty n) : sub s t = decide (s ⊆ t) := by
  rw [Bool.eq_iff_iff, sub, subL_iff (toL_sorted s) (toL_sorted t), decide_eq_true_iff]
  simp only [mem_toL]
  exact Iff.rfl

/-- The type of a list. -/
def ofL (L : List (Fin n)) : Ty n := ofSorted (sortL L) (sortL_sorted L)

theorem ofL_eq (L : List (Fin n)) : ofL L = L.toFinset := by
  ext x
  simp only [ofL, mem_ofSorted, mem_sortL, List.mem_toFinset]

theorem toL_ofSorted {l : List (Fin n)} (h : l.Pairwise (· < ·)) : toL (ofSorted l h) = l := by
  show toLRaw l = l
  rw [toLRaw_eq]
  exact List.mergeSort_eq_self (r := (· ≤ ·)) (h.imp le_of_lt)

end ContextCalculus.SRI.Proc
