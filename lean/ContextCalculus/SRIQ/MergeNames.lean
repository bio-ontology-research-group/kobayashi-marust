import ContextCalculus.SRIQ.FastDefs

/-!
# Merging fresh names with one definition (stage C1e)

The translation gives every occurrence of a restriction on the left of an
axiom its own fresh name. On ore_ont_10140, `∃R.C ⊑ x` for one `R` and
`C` occurs 19 158 times: `C ⊑ ∀R⁻.xᵢ` with 19 158 names `xᵢ` that occur
only in gci bodies. A node with `C` then pushes 19 158 names to its
parent, and every parent type has as many.

A name `x` whose positive occurrences are universal fillers only
(`a ⊑ ∀S.x`) and whose other occurrences are negative (gci bodies, the
left of clauses, the filler of an at-most clause) is determined from
below by its universal clauses. Two such names with the same universal
clauses can be identified: renaming one into the other (`renO`) keeps
the models up to the interpretation of the renamed names
(`models_renO_meet`: interpret the target as the intersection of its
class; `models_of_renO`: interpret a renamed name as its target), so the
subsumptions between the other names are unchanged (`entailsSub_renO`).

The renaming is a hint (`mergeHint`, unproved) that `mergeOK` checks.
-/

namespace ContextCalculus.SRIQ.Merge

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ
open ContextCalculus.SRIQ.Fast (buildIdx getL mem_buildIdx)

variable {n m : Nat}

/-- The target of each name (the name itself when it stays). -/
def tgt (ρ : Array Nat) (x : Fin n) : Fin n :=
  if h : ρ[x.val]?.getD x.val < n then ⟨ρ[x.val]?.getD x.val, h⟩ else x

def renC (f : Fin n → Fin n) : Clause (Fin n) (Fin m) → Clause (Fin n) (Fin m)
  | .gci B H => .gci (B.map f) (H.map f)
  | .exRight a R b => .exRight (f a) R (f b)
  | .allRight a R b => .allRight (f a) R (f b)
  | .atLeast a k R b => .atLeast (f a) k R (f b)
  | .atMost a k R b => .atMost (f a) k R (f b)
  | .chain b S => .chain b S

/-- **The renaming.** -/
def renO (f : Fin n → Fin n) (O : Ontology (Fin n) (Fin m)) : Ontology (Fin n) (Fin m) :=
  O.map (renC f)

/-- The universal clauses `a ⊑ ∀S.x` by filler `x`. -/
def defIdx (O : Ontology (Fin n) (Fin m)) : Array (List (Fin n × RoleT (Fin m))) :=
  buildIdx n (fun c => match c with
    | .allRight a S x => some (x.val, (a, S))
    | _ => none) O

/-- The names that move or receive others (`M`) occur positively only as
universal fillers. -/
def clauseOK (M : Array Bool) : Clause (Fin n) (Fin m) → Bool
  | .gci _ H => H.all fun h => !(M[h.val]?.getD false)
  | .exRight _ _ b => !(M[b.val]?.getD false)
  | .atLeast _ _ _ b => !(M[b.val]?.getD false)
  | _ => true

def sameSet {α : Type} [DecidableEq α] (l1 l2 : List α) : Bool := l1.all (l2.contains ·) && l2.all (l1.contains ·)

/-- A name and its target: the target stays; a moved name and its target
are in `M`, at least `bound`, and have the same universal clauses. -/
def nameOK (D : Array (List (Fin n × RoleT (Fin m)))) (bound : Nat) (ρ : Array Nat) (M : Array Bool)
    (x : Fin n) : Bool :=
  let y := tgt ρ x
  decide (tgt ρ y = y) && (decide (x = y) || ((M[x.val]?.getD false) && (M[y.val]?.getD false) &&
    decide (bound ≤ x.val) && decide (bound ≤ y.val) && sameSet (getL D x.val) (getL D y.val)))

/-- **The hint check.** -/
def mergeOK (O : Ontology (Fin n) (Fin m)) (bound : Nat) (ρ : Array Nat) (M : Array Bool) : Bool :=
  (List.finRange n).all (nameOK (defIdx O) bound ρ M) && O.all (clauseOK M)

/-! ## The hint (unproved) -/

/-- Names at least `bound` whose positive occurrences are universal
fillers only, grouped by their universal clauses; each group goes to its
first name. -/
def mergeHint (O : Ontology (Fin n) (Fin m)) (bound : Nat) : Array Nat × Array Bool := Id.run do
  let mut bad : Array Bool := Array.replicate n false
  for cl in O do
    match cl with
    | .gci _ H => for h in H do bad := bad.set! h.val true
    | .exRight _ _ b => bad := bad.set! b.val true
    | .atLeast _ _ _ b => bad := bad.set! b.val true
    | _ => pure ()
  let D := defIdx O
  let mut first : Std.HashMap (List (Nat × Nat × Bool)) Nat := ∅
  let mut ρ : Array Nat := Array.range n
  let mut M : Array Bool := Array.replicate n false
  for i in [bound:n] do
    if bad[i]?.getD true then continue
    let key := ((getL D i).map fun p => (p.1.val, match p.2 with | .pos r => r.val | .inv r => r.val, p.2 matches .inv _)).mergeSort
      (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ (a.2.2 = false ∨ b.2.2 = true))))))
    let key := key.eraseDups
    match first.get? key with
    | some j => ρ := ρ.set! i j; M := (M.set! i true).set! j true
    | none => first := first.insert key i
  return (ρ, M)

/-- The renaming when the hint passes the check, else the ontology. -/
def mergeChecked (O : Ontology (Fin n) (Fin m)) (bound : Nat) : Ontology (Fin n) (Fin m) :=
  let h := mergeHint O bound
  if mergeOK O bound h.1 h.2 then renO (tgt h.1) O else O

/-! ## Correctness -/

section Proofs

variable {D : Type} {O : Ontology (Fin n) (Fin m)} {bound : Nat} {ρ : Array Nat} {M : Array Bool}

def inM (M : Array Bool) (x : Fin n) : Prop := M[x.val]?.getD false = true

theorem nameOK_of (h : mergeOK O bound ρ M = true) (x : Fin n) :
    nameOK (defIdx O) bound ρ M x = true := by
  unfold mergeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 x (List.mem_finRange x)

theorem clauseOK_of (h : mergeOK O bound ρ M = true) {cl : Clause (Fin n) (Fin m)} (hc : cl ∈ O) :
    clauseOK M cl = true := by
  unfold mergeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 cl hc

theorem tgt_tgt (h : mergeOK O bound ρ M = true) (x : Fin n) : tgt ρ (tgt ρ x) = tgt ρ x := by
  have := nameOK_of h x
  unfold nameOK at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- A moved name and its target are in `M`, the target at least `bound`. -/
theorem moved (h : mergeOK O bound ρ M = true) {x : Fin n} (hx : tgt ρ x ≠ x) :
    inM M x ∧ inM M (tgt ρ x) ∧ bound ≤ (tgt ρ x).val ∧
      sameSet (getL (defIdx O) x.val) (getL (defIdx O) (tgt ρ x).val) = true ∧ bound ≤ x.val := by
  have := nameOK_of h x
  unfold nameOK at this
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at this
  rcases this.2 with h1 | h1
  · exact absurd h1.symm hx
  · exact ⟨h1.1.1.1.1, h1.1.1.1.2, h1.1.2, h1.2, h1.1.1.2⟩

/-- A name outside `M` is its own class. -/
theorem class_of_notM (h : mergeOK O bound ρ M = true) {y : Fin n} (hy : ¬ inM M y) (x : Fin n) :
    tgt ρ x = y ↔ x = y := by
  constructor
  · intro hx
    by_contra hne
    have : tgt ρ x ≠ x := fun he => hne (he.symm.trans hx)
    exact hy (hx ▸ (moved h this).2.1)
  · intro hx
    subst hx
    by_contra hne
    exact hy (moved h hne).1

theorem notM_of_clause {M : Array Bool} {x : Fin n} (h : (!(M[x.val]?.getD false)) = true) : ¬ inM M x := by
  unfold inM; simpa using h

/-- Names below the bound are their own class. -/
theorem class_of_lt (h : mergeOK O bound ρ M = true) {y : Fin n} (hy : y.val < bound) (x : Fin n) :
    tgt ρ x = y ↔ x = y := by
  constructor
  · intro hx
    by_contra hne
    have : tgt ρ x ≠ x := fun he => hne (he.symm.trans hx)
    have := (moved h this).2.2.1
    rw [hx] at this
    omega
  · intro hx
    subst hx
    by_contra hne
    have := (moved h hne).2.2.2.2
    omega

theorem mem_defIdx {x : Fin n} {p : Fin n × RoleT (Fin m)} :
    p ∈ getL (defIdx O) x.val ↔ Clause.allRight p.1 p.2 x ∈ O := by
  unfold defIdx
  rw [mem_buildIdx x.isLt]
  constructor
  · rintro ⟨c, hc, he⟩
    cases c with
    | allRight a S y =>
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨h1, rfl⟩ := he
      have : y = x := Fin.ext h1
      subst this
      exact hc
    | _ => simp at he
  · intro hc
    exact ⟨_, hc, rfl⟩

theorem sameSet_mem {α : Type} [DecidableEq α] {l1 l2 : List α} (h : sameSet l1 l2 = true) {a : α} :
    a ∈ l1 ↔ a ∈ l2 := by
  unfold sameSet at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun ha => h.1 a ha, fun ha => h.2 a ha⟩

/-- Every name of a class has the universal clauses of its target. -/
theorem def_class (h : mergeOK O bound ρ M = true) {x : Fin n} {p : Fin n × RoleT (Fin m)} :
    Clause.allRight p.1 p.2 x ∈ O ↔ Clause.allRight p.1 p.2 (tgt ρ x) ∈ O := by
  by_cases hx : tgt ρ x = x
  · rw [hx]
  · rw [← mem_defIdx, ← mem_defIdx]
    exact sameSet_mem (moved h hx).2.2.2.1

/-- The meet interpretation: a target holds where every name of its class holds. -/
def meet (ρ : Array Nat) (I : Interp D (Fin n) (Fin m)) : Interp D (Fin n) (Fin m) where
  c y z := ∀ x : Fin n, tgt ρ x = y → I.c x z
  r := I.r

/-- The renamed-back interpretation. -/
def back (ρ : Array Nat) (I : Interp D (Fin n) (Fin m)) : Interp D (Fin n) (Fin m) where
  c x z := I.c (tgt ρ x) z
  r := I.r

theorem meet_rt (I : Interp D (Fin n) (Fin m)) (R : RoleT (Fin m)) : (meet ρ I).rt R = I.rt R := by
  cases R <;> rfl

theorem back_rt (I : Interp D (Fin n) (Fin m)) (R : RoleT (Fin m)) : (back ρ I).rt R = I.rt R := by
  cases R <;> rfl

theorem meet_path (I : Interp D (Fin n) (Fin m)) :
    ∀ body : List (RoleT (Fin m)), (meet ρ I).path body = I.path body
  | [] => rfl
  | R :: Rs => by funext x z; simp only [Interp.path, meet_rt, meet_path I Rs]

theorem back_path (I : Interp D (Fin n) (Fin m)) :
    ∀ body : List (RoleT (Fin m)), (back ρ I).path body = I.path body
  | [] => rfl
  | R :: Rs => by funext x z; simp only [Interp.path, back_rt, back_path I Rs]

theorem meet_self {I : Interp D (Fin n) (Fin m)} {x : Fin n} {z : D} (h : (meet ρ I).c (tgt ρ x) z) :
    I.c x z := h x rfl

theorem meet_notM (hS : mergeOK O bound ρ M = true) {I : Interp D (Fin n) (Fin m)} {y : Fin n}
    (hy : ¬ inM M y) (z : D) : (meet ρ I).c (tgt ρ y) z ↔ I.c y z := by
  have ht : tgt ρ y = y := (class_of_notM hS hy y).2 rfl
  rw [ht]
  constructor
  · intro h; exact h y ht
  · intro h x hx
    rw [(class_of_notM hS hy x).1 hx]; exact h

/-- **Every model of the ontology gives a model of the renaming.** -/
theorem models_renO_meet (hS : mergeOK O bound ρ M = true) {I : Interp D (Fin n) (Fin m)}
    (hI : models I O) : models (meet ρ I) (renO (tgt ρ) O) := by
  intro cl hcl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcl
  have hok := clauseOK_of hS hc
  cases c with
  | gci B H =>
    simp only [clauseOK, List.all_eq_true] at hok
    intro z hz
    obtain ⟨b, hb, hbz⟩ := hI _ hc z fun a ha => meet_self (hz _ (List.mem_map.2 ⟨a, ha, rfl⟩))
    exact ⟨tgt ρ b, List.mem_map.2 ⟨b, hb, rfl⟩, (meet_notM hS (notM_of_clause (hok b hb)) z).2 hbz⟩
  | exRight a R b =>
    simp only [clauseOK] at hok
    intro z hz
    obtain ⟨w, hw1, hw2⟩ := hI _ hc z (meet_self hz)
    exact ⟨w, by rw [meet_rt]; exact hw1, (meet_notM hS (notM_of_clause hok) w).2 hw2⟩
  | allRight a S x =>
    intro z hz w hw
    rw [meet_rt] at hw
    intro x' hx'
    have h1 : Clause.allRight a S (tgt ρ x) ∈ O := (def_class hS (p := (a, S))).1 hc
    rw [← hx'] at h1
    have h2 : Clause.allRight a S x' ∈ O := (def_class hS (p := (a, S))).2 h1
    exact hI _ h2 z (meet_self hz) w hw
  | atLeast a k R b =>
    simp only [clauseOK] at hok
    intro z hz
    obtain ⟨l, hl1, hl2, hl3⟩ := hI _ hc z (meet_self hz)
    exact ⟨l, hl1, hl2, fun w hw => ⟨by rw [meet_rt]; exact (hl3 w hw).1,
      (meet_notM hS (notM_of_clause hok) w).2 (hl3 w hw).2⟩⟩
  | atMost a k R b =>
    intro z hz l hl hs
    exact hI _ hc z (meet_self hz) l hl fun w hw =>
      ⟨by rw [← meet_rt (ρ := ρ)]; exact (hs w hw).1, meet_self (hs w hw).2⟩
  | chain body S =>
    intro x y hxy
    rw [meet_path] at hxy
    rw [meet_rt]
    exact hI _ hc x y hxy

/-- **A model of the renaming gives a model of the ontology.** -/
theorem models_of_renO {I : Interp D (Fin n) (Fin m)} (hI : models I (renO (tgt ρ) O)) :
    models (back ρ I) O := by
  intro c hc
  have h := hI _ (List.mem_map.2 ⟨c, hc, rfl⟩)
  cases c with
  | gci B H =>
    intro z hz
    obtain ⟨b, hb, hbz⟩ := h z fun a ha => by
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      exact hz a' ha'
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact ⟨b', hb', hbz⟩
  | exRight a R b =>
    intro z hz
    obtain ⟨w, hw1, hw2⟩ := h z hz
    exact ⟨w, by rw [back_rt]; exact hw1, hw2⟩
  | allRight a S x =>
    intro z hz w hw
    rw [back_rt] at hw
    exact h z hz w hw
  | atLeast a k R b =>
    intro z hz
    obtain ⟨l, hl1, hl2, hl3⟩ := h z hz
    exact ⟨l, hl1, hl2, fun w hw => ⟨by rw [back_rt]; exact (hl3 w hw).1, (hl3 w hw).2⟩⟩
  | atMost a k R b =>
    intro z hz l hl hs
    exact h z hz l hl fun w hw => ⟨by rw [← back_rt (ρ := ρ)]; exact (hs w hw).1, (hs w hw).2⟩
  | chain body S =>
    intro x y hxy
    rw [back_path] at hxy
    rw [back_rt]
    exact h x y hxy

/-- **Subsumptions between names below the bound are unchanged.** -/
theorem entailsSub_renO (hS : mergeOK O bound ρ M = true) {a b : Fin n} (ha : a.val < bound)
    (hb : b.val < bound) : EntailsSub (renO (tgt ρ) O) a b ↔ EntailsSub O a b := by
  have hta : tgt ρ a = a := (class_of_lt hS ha a).2 rfl
  have htb : tgt ρ b = b := (class_of_lt hS hb b).2 rfl
  constructor
  · intro h D _ I hI x hx
    have := h D (meet ρ I) (models_renO_meet hS hI) x (fun y hy => by
      rw [(class_of_lt hS ha y).1 hy]; exact hx)
    exact this b htb
  · intro h D _ I hI x hx
    have := h D (back ρ I) (models_of_renO hI) x (show I.c (tgt ρ a) x by rw [hta]; exact hx)
    simpa [back, htb] using this

theorem isALCHIQ_renO {f : Fin n → Fin n} (h : IsALCHIQ O) : IsALCHIQ (renO f O) := by
  intro body S hcl
  obtain ⟨c, hc, he⟩ := List.mem_map.1 hcl
  cases c with
  | chain body' S' =>
    simp only [renC, Clause.chain.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h _ _ hc
  | _ => simp [renC] at he

theorem entailsSub_mergeChecked {a b : Fin n} (ha : a.val < bound) (hb : b.val < bound) :
    EntailsSub (mergeChecked O bound) a b ↔ EntailsSub O a b := by
  unfold mergeChecked
  dsimp only
  split
  · next h => exact entailsSub_renO h ha hb
  · exact Iff.rfl

theorem isALCHIQ_mergeChecked (h : IsALCHIQ O) : IsALCHIQ (mergeChecked O bound) := by
  unfold mergeChecked
  dsimp only
  split
  · exact isALCHIQ_renO h
  · exact h

end Proofs

end ContextCalculus.SRIQ.Merge

#print axioms ContextCalculus.SRIQ.Merge.entailsSub_mergeChecked
#print axioms ContextCalculus.SRIQ.Merge.isALCHIQ_mergeChecked
