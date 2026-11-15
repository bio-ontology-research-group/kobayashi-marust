import ContextCalculus.OWLFrontend.SHOIQC2aReference
import ContextCalculus.SRIQN.HintFast

/-!
# The text format read into a sparse hint (stage H2)

`RawHint.toHintN` (`SHOIQC2aReference.lean`) reads a hint into the core of
`SRIQN.Proc.HintN`, whose types and labels are folds over all `ty` and
`lab` lines. `RawHint.toHintS` reads the same lines into the sparse hint
`HF.HintS` (an array of types, the `lab` lines as edges, the `kid` lines as
a list) and `toHintS_map` proves that it denotes the same core:

```
(h.toHintS n m).map HF.HintS.toN = h.toHintN n m
```

so the hint route can check the sparse form (`HF.hintPartsS_eq`) with no
change in meaning. The text format is unchanged.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (flipL)
open ContextCalculus.SRIQN.HF (HintS RecS labOf mem_foldl_union)

/-! ## Types read in linear time (stage H4)

`List.toFinset` removes duplicates by a quadratic scan; a type of a
hint lists hundreds of names. `dedupH` removes them with a hash set, and
`finsOf_eq_F` registers the equal definition for compiled code. -/

/-- One step of the hash-set deduplication. -/
def dedupStep {α : Type} [BEq α] [Hashable α] (a : Std.HashSet α × List α) (x : α) :
    Std.HashSet α × List α :=
  if a.1.contains x then a else (a.1.insert x, x :: a.2)

theorem dedupStep_inv {α : Type} [DecidableEq α] [Hashable α] :
    ∀ (l : List α) (a : Std.HashSet α × List α), a.2.Nodup → (∀ y, y ∈ a.1 ↔ y ∈ a.2) →
      (l.foldl dedupStep a).2.Nodup ∧
        (∀ y, y ∈ (l.foldl dedupStep a).1 ↔ y ∈ (l.foldl dedupStep a).2) ∧
        ∀ y, y ∈ (l.foldl dedupStep a).2 ↔ y ∈ a.2 ∨ y ∈ l
  | [], a, h1, h2 => ⟨h1, h2, fun y => by simp⟩
  | x :: l, a, h1, h2 => by
    rw [List.foldl_cons]
    by_cases hx : a.1.contains x = true
    · have hs : dedupStep a x = a := by simp [dedupStep, hx]
      rw [hs]
      obtain ⟨g1, g2, g3⟩ := dedupStep_inv l a h1 h2
      refine ⟨g1, g2, fun y => ?_⟩
      rw [g3 y, List.mem_cons]
      have hxa : x ∈ a.2 := (h2 x).1 (Std.HashSet.contains_iff_mem.1 hx)
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hxa
        · exact Or.inr h
    · have hs : dedupStep a x = (a.1.insert x, x :: a.2) := by simp [dedupStep, hx]
      rw [hs]
      have hxa : x ∉ a.2 := fun h => hx (Std.HashSet.contains_iff_mem.2 ((h2 x).2 h))
      obtain ⟨g1, g2, g3⟩ := dedupStep_inv l (a.1.insert x, x :: a.2) (List.nodup_cons.2 ⟨hxa, h1⟩)
        (fun y => by
          rw [Std.HashSet.mem_insert, List.mem_cons, h2 y, beq_iff_eq]
          exact or_congr eq_comm Iff.rfl)
      refine ⟨g1, g2, fun y => ?_⟩
      rw [g3 y]
      simp only [List.mem_cons]
      tauto

/-- The elements of a list without duplicates, through a hash set. -/
def dedupH {α : Type} [BEq α] [Hashable α] (l : List α) : List α :=
  (l.foldl dedupStep ({}, [])).2

theorem dedupH_spec {α : Type} [DecidableEq α] [Hashable α] (l : List α) :
    (dedupH l).Nodup ∧ ∀ y, y ∈ dedupH l ↔ y ∈ l := by
  obtain ⟨g1, -, g3⟩ := dedupStep_inv l (({} : Std.HashSet α), []) List.nodup_nil
    (fun y => by simp)
  exact ⟨g1, fun y => by rw [dedupH, g3 y]; simp⟩

/-- `List.toFinset` through the hash set. -/
def toFinsetH {n : Nat} (l : List (Fin n)) : Finset (Fin n) :=
  ⟨dedupH l, (dedupH_spec l).1⟩

theorem toFinsetH_eq {n : Nat} (l : List (Fin n)) : toFinsetH l = l.toFinset := by
  ext y
  simp only [toFinsetH, Finset.mem_mk, Multiset.mem_coe, List.mem_toFinset]
  exact (dedupH_spec l).2 y

def finsOfF (n : Nat) (xs : List Nat) : Option (Finset (Fin n)) :=
  (xs.mapM (RawHint.finOf n)).map toFinsetH

@[csimp] theorem finsOf_eq_F : @RawHint.finsOf = @finsOfF := by
  funext n xs
  simp only [RawHint.finsOf, finsOfF]
  congr 1
  funext l
  exact (toFinsetH_eq l).symm

/-- A certificate record as a sparse row (its core entries as a list). -/
def RawRec.toRecS (n m k : Nat) (x : RawRec) : Option (RecS n m k) :=
  match RawHint.finsOf n x.ty, RawHint.rtsOf m x.plab,
    x.ce.mapM (fun e => (RawHint.finOf k e.1).bind fun d => (RawHint.rtsOf m e.2).map (d, ·)),
    x.kids.mapM (fun e => (RawHint.rtsOf m e.1).bind fun L => (RawHint.finsOf n e.2).map (L, ·))
  with
  | some t, some L, some ces, some ks =>
    let par : Option (SRIQ.Nbr (Fin n) (Fin m) ⊕ (Fin k × Finset (RoleT (Fin m)))) :=
      match x.anchor with
      | some b => (RawHint.finOf k b).map fun b' => .inr (b', L)
      | none => (RawHint.finsOf n x.pty).map fun s => .inl (L, s)
    par.map fun p => { ty := t, par := p, ce := ces, kids := ks }
  | _, _, _, _ => none

theorem toRecS_map (n m k : Nat) (x : RawRec) :
    (x.toRecS n m k).map RecS.toN = x.toRec n m k := by
  unfold RawRec.toRecS RawRec.toRec
  generalize RawHint.finsOf n x.ty = a1
  generalize RawHint.rtsOf m x.plab = a2
  generalize x.ce.mapM (fun e => (RawHint.finOf k e.1).bind fun d => (RawHint.rtsOf m e.2).map (d, ·)) = a3
  generalize x.kids.mapM (fun e => (RawHint.rtsOf m e.1).bind fun L =>
    (RawHint.finsOf n e.2).map (L, ·)) = a4
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> simp only [Option.map_map] <;> rfl

theorem mapM_map_of {α β γ : Type} (f : α → Option β) (g : α → Option γ) (φ : β → γ)
    (hfg : ∀ x, (f x).map φ = g x) : ∀ l : List α, (l.mapM f).map (List.map φ) = l.mapM g
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, List.mapM_cons, ← hfg x, ← mapM_map_of f g φ hfg l]
    cases f x <;> cases l.mapM f <;> rfl

/-- The core types as an array. -/
def tyArr {n : Nat} (nb : Nat) (ty : List (Nat × Finset (Fin n))) : Array (Finset (Fin n)) :=
  ty.foldl (fun A e => A.modify e.1 (· ∪ e.2)) (Array.replicate nb ∅)

theorem tyArr_aux {n : Nat} {nb : Nat} {b : Nat} (hb : b < nb) (x : Fin n) :
    ∀ (l : List (Nat × Finset (Fin n))) (A : Array (Finset (Fin n))), A.size = nb →
      (x ∈ (l.foldl (fun A e => A.modify e.1 (· ∪ e.2)) A)[b]?.getD ∅ ↔
        x ∈ A[b]?.getD ∅ ∨ ∃ e ∈ l, e.1 = b ∧ x ∈ e.2)
  | [], A, _ => by simp
  | e :: l, A, hA => by
    rw [List.foldl_cons, tyArr_aux hb x l _ (by simpa using hA)]
    rw [Array.getElem?_modify]
    by_cases he : e.1 = b
    · subst he
      have : e.1 < A.size := hA ▸ hb
      simp only [if_true, List.mem_cons, exists_eq_or_imp, true_and]
      rw [Array.getElem?_eq_getElem this]
      simp only [Option.map_some, Option.getD_some, Finset.mem_union]
      tauto
    · simp [he]

theorem tyArr_get {n : Nat} {nb : Nat} (ty : List (Nat × Finset (Fin n))) (b : Fin nb) :
    (tyArr nb ty)[b.val]?.getD ∅ = ty.foldl (fun acc e => if e.1 = b.val then acc ∪ e.2 else acc) ∅ := by
  ext x
  unfold tyArr
  rw [tyArr_aux b.isLt x ty _ (by simp),
    mem_foldl_union (fun e : Nat × Finset (Fin n) => e.1 = b.val) (·.2)]
  simp [b.isLt]

/-- The `lab` lines inside the core. -/
def labIn {m : Nat} (nb : Nat) (lab : List (Nat × Nat × Finset (RoleT (Fin m)))) :
    List (Fin nb × Fin nb × Finset (RoleT (Fin m))) :=
  lab.filterMap fun e => if h : e.1 < nb ∧ e.2.1 < nb then some (⟨e.1, h.1⟩, ⟨e.2.1, h.2⟩, e.2.2) else none

/-- The `kid` lines inside the core. -/
def kidsIn {n m : Nat} (nb : Nat) (kids : List (Nat × Finset (RoleT (Fin m)) × Finset (Fin n))) :
    List (Fin nb × SRIQ.Proc.QNbr n m) :=
  kids.filterMap fun e => if h : e.1 < nb then some (⟨e.1, h⟩, (e.2.1, e.2.2)) else none

/-- **The text format as a sparse hint**; `none` exactly when `toHintN`
gives `none`. -/
def RawHint.toHintS (h : RawHint) (n m : Nat) : Option (HintS n m) :=
  match h.ty.mapM (fun e => (RawHint.finsOf n e.2).map (e.1, ·)),
    h.lab.mapM (fun e => (RawHint.rtsOf m e.2.2).map (e.1, e.2.1, ·)),
    h.kids.mapM (fun e => ((RawHint.rtsOf m e.2.1).bind fun L =>
      (RawHint.finsOf n e.2.2).map (e.1, L, ·))),
    h.recs.mapM (fun x => x.2.toRecS n m h.nb)
  with
  | some ty, some lab, some kids, some recs =>
    some { k := h.nb, ty := tyArr h.nb ty, lab := labIn h.nb lab, kids := kidsIn h.nb kids,
           recs := recs, part := h.part, partNamed := h.partNamed, dstar := h.dstar,
           dgiven := h.dgiven }
  | _, _, _, _ => none

theorem half_labIn {m nb : Nat} (lab : List (Nat × Nat × Finset (RoleT (Fin m)))) (b c : Fin nb) :
    (labIn nb lab).foldl (fun acc e => if e.1 = b ∧ e.2.1 = c then acc ∪ e.2.2 else acc) ∅ =
      lab.foldl (fun acc e => if e.1 = b.val ∧ e.2.1 = c.val then acc ∪ e.2.2 else acc) ∅ := by
  ext x
  rw [mem_foldl_union (fun e : Fin nb × Fin nb × Finset (RoleT (Fin m)) => e.1 = b ∧ e.2.1 = c)
      (·.2.2),
    mem_foldl_union (fun e : Nat × Nat × Finset (RoleT (Fin m)) => e.1 = b.val ∧ e.2.1 = c.val)
      (·.2.2)]
  simp only [Finset.notMem_empty, false_or, labIn, List.mem_filterMap]
  constructor
  · rintro ⟨e', ⟨e, he, hif⟩, ⟨rfl, rfl⟩, hx⟩
    split at hif
    · simp only [Option.some.injEq] at hif
      subst hif
      exact ⟨e, he, ⟨rfl, rfl⟩, hx⟩
    · cases hif
  · rintro ⟨e, he, ⟨h1, h2⟩, hx⟩
    have hlt : e.1 < nb ∧ e.2.1 < nb := ⟨h1 ▸ b.isLt, h2 ▸ c.isLt⟩
    refine ⟨_, ⟨e, he, dif_pos hlt⟩, ⟨Fin.ext h1, Fin.ext h2⟩, hx⟩

theorem kids_kidsIn {n m nb : Nat} (kids : List (Nat × Finset (RoleT (Fin m)) × Finset (Fin n)))
    (b : Fin nb) :
    ((kidsIn nb kids).filter fun e => e.1 = b).map (·.2) =
      (kids.filter fun e => e.1 = b.val).map fun e => (e.2.1, e.2.2) := by
  induction kids with
  | nil => rfl
  | cons e l ih =>
    by_cases he : e.1 = b.val
    · have hlt : e.1 < nb := he ▸ b.isLt
      have hk : kidsIn nb (e :: l) = (⟨e.1, hlt⟩, (e.2.1, e.2.2)) :: kidsIn nb l := by
        simp [kidsIn, List.filterMap_cons, hlt]
      rw [hk]
      have hb : (⟨e.1, hlt⟩ : Fin nb) = b := Fin.ext he
      simp [List.filter_cons, hb, he, ih]
    · by_cases hlt : e.1 < nb
      · have hk : kidsIn nb (e :: l) = (⟨e.1, hlt⟩, (e.2.1, e.2.2)) :: kidsIn nb l := by
          simp [kidsIn, List.filterMap_cons, hlt]
        rw [hk]
        have hb : ¬ (⟨e.1, hlt⟩ : Fin nb) = b := fun h => he (by rw [← h])
        simp [List.filter_cons, hb, he, ih]
      · have hk : kidsIn nb (e :: l) = kidsIn nb l := by
          simp [kidsIn, List.filterMap_cons, hlt]
        rw [hk]
        simp [List.filter_cons, he, ih]

/-- **The sparse hint denotes the hint of `toHintN`.** -/
theorem toHintS_map (h : RawHint) (n m : Nat) : (h.toHintS n m).map HintS.toN = h.toHintN n m := by
  unfold RawHint.toHintS RawHint.toHintN
  rw [← mapM_map_of (fun x : Nat × RawRec => x.2.toRecS n m h.nb)
    (fun x : Nat × RawRec => x.2.toRec n m h.nb) RecS.toN (fun x => toRecS_map n m h.nb x.2) h.recs]
  cases h.ty.mapM (fun e => (RawHint.finsOf n e.2).map (e.1, ·)) with
  | none => rfl
  | some ty =>
    cases h.lab.mapM (fun e => (RawHint.rtsOf m e.2.2).map (e.1, e.2.1, ·)) with
    | none => rfl
    | some lab =>
      cases h.kids.mapM (fun e => ((RawHint.rtsOf m e.2.1).bind fun L =>
          (RawHint.finsOf n e.2.2).map (e.1, L, ·))) with
      | none => rfl
      | some kids =>
        cases h.recs.mapM (fun x => x.2.toRecS n m h.nb) with
        | none => rfl
        | some recs =>
          simp only [Option.map_some, Option.some.injEq]
          unfold HintS.toN HintS.tyF HintS.half
          simp only [tyArr_get, half_labIn, kids_kidsIn]

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.toHintS_map
