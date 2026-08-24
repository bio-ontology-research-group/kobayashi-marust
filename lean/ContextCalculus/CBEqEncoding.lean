import ContextCalculus.CBALCEncoding
import ContextCalculus.CBClauseShape
import ContextCalculus.CompletenessEq
import Mathlib.Data.Nat.Pairing

/-!
# Exact equational ontology to CB nested-term encoding

This module connects the normalized equational ontology language used by the
Herbrand quotient completeness proof to the nested-term first-order semantics
used by CB certificates. It covers disjunctive GCIs, existential and universal
restrictions, role inclusions, inverse-role bridges, functionality, nominals,
and qualified at-most restrictions.
-/

namespace ContextCalculus.CBEqEncoding

open ContextCalculus CheckerTerm Eqv

private abbrev x : FTerm := CBALCEncoding.x
private abbrev y : FTerm := CBALCEncoding.y
private def z : FTerm := .var (-2)

private abbrev con (concept : Fin conceptCount) (term : FTerm) : FLit :=
  CBALCEncoding.con concept term

private abbrev rol (role : Fin roleCount) (source target : FTerm) : FLit :=
  CBALCEncoding.rol role source target

private def individual (name : Fin individualCount) : FTerm :=
  .const name.val

/-- Variable used for the `i`th qualified-successor slot. Slot variables are
    negative and therefore disjoint from the central variable `0`. -/
private def slot (i : Nat) : FTerm :=
  .var (-(Int.ofNat (i + 2)))

private def atMostBodyL (n : Nat) (role : Fin roleCount)
    (concept : Fin conceptCount) : List FLit :=
  (List.range (n + 1)).map (fun i => rol role x (slot i)) ++
  (List.range (n + 1)).map (fun i => con concept (slot i))

private def atMostHeadL (n : Nat) : List FLit :=
  (List.range (n + 1)).flatMap (fun i =>
    (List.range (n + 1)).flatMap (fun j =>
      if i < j then [.eq (slot i) (slot j)] else []))

private def atLeastWitness (index slot : Nat) : FTerm :=
  .app (Nat.pair index slot) x

private def atLeastRoleClauses (index : Nat) (source : Fin conceptCount)
    (n : Nat) (role : Fin roleCount) : List FCL :=
  (List.range n).map fun i =>
    ⟨[con source x], [rol role x (atLeastWitness index i)]⟩

private def atLeastConceptClauses (index : Nat) (source : Fin conceptCount)
    (n : Nat) (concept : Fin conceptCount) : List FCL :=
  (List.range n).map fun i =>
    ⟨[con source x], [con concept (atLeastWitness index i)]⟩

private def atLeastDistinctClauses (index : Nat) (source : Fin conceptCount)
    (n : Nat) : List FCL :=
  (List.range n).flatMap fun i =>
    (List.range n).flatMap fun j =>
      if i < j then
        [⟨[con source x],
          [.ineq (atLeastWitness index j) (atLeastWitness index i)]⟩]
      else []

private def guardedAtLeastClauses (index : Nat) (source : Fin conceptCount)
    (n : Nat) (role : Fin roleCount) (concept : Fin conceptCount) : List FCL :=
  atLeastRoleClauses index source n role ++
    atLeastConceptClauses index source n concept ++
    atLeastDistinctClauses index source n

private theorem mem_atLeastRoleClauses {clause : FCL} :
    clause ∈ atLeastRoleClauses index source n role ↔
      ∃ i : Fin n, clause =
        ⟨[con source x], [rol role x (atLeastWitness index i)]⟩ := by
  simp only [atLeastRoleClauses, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩

private theorem mem_atLeastConceptClauses {clause : FCL} :
    clause ∈ atLeastConceptClauses index source n concept ↔
      ∃ i : Fin n, clause =
        ⟨[con source x], [con concept (atLeastWitness index i)]⟩ := by
  simp only [atLeastConceptClauses, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩

private theorem mem_atLeastDistinctClauses {clause : FCL} :
    clause ∈ atLeastDistinctClauses index source n ↔
      ∃ i j : Fin n, i < j ∧ clause =
        ⟨[con source x],
          [.ineq (atLeastWitness index j) (atLeastWitness index i)]⟩ := by
  simp only [atLeastDistinctClauses, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, hmem⟩
    by_cases hlt : i < j
    · simp only [hlt, if_true, List.mem_singleton] at hmem
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩, hlt, hmem⟩
    · simp only [hlt, if_false, List.not_mem_nil] at hmem
  · rintro ⟨i, j, hlt, rfl⟩
    exact ⟨i.val, i.isLt, j.val, j.isLt,
      by simp only [show i.val < j.val from hlt, if_true, List.mem_singleton]⟩

private theorem mem_atMostBodyL {n : Nat} {role : Fin roleCount}
    {concept : Fin conceptCount} {literal : FLit} :
    literal ∈ atMostBodyL n role concept ↔
      (∃ i : Fin (n + 1), literal = rol role x (slot i)) ∨
      (∃ i : Fin (n + 1), literal = con concept (slot i)) := by
  simp only [atMostBodyL, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨⟨i, hi⟩, rfl⟩
    · exact Or.inr ⟨⟨i, hi⟩, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl ⟨i.val, i.isLt, rfl⟩
    · exact Or.inr ⟨i.val, i.isLt, rfl⟩

private theorem mem_atMostHeadL {n : Nat} {literal : FLit} :
    literal ∈ atMostHeadL n ↔
      ∃ i j : Fin (n + 1), i < j ∧ literal = .eq (slot i) (slot j) := by
  simp only [atMostHeadL, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, hij⟩
    by_cases h : i < j
    · simp only [h, if_true, List.mem_singleton] at hij
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩, h, hij⟩
    · simp only [h, if_false, List.not_mem_nil] at hij
  · rintro ⟨i, j, hlt, rfl⟩
    exact ⟨i.val, i.isLt, j.val, j.isLt,
      by simp only [show i.val < j.val from hlt, if_true, List.mem_singleton]⟩

private noncomputable def slotAssignment {n : Nat} (source : D)
    (values : Fin (n + 1) → D) (id : Int) : D :=
  if h : ∃ i : Fin (n + 1), id = -(Int.ofNat (i.val + 2)) then
    values (Classical.choose h)
  else source

@[simp] private theorem slotAssignment_slot {n : Nat} (source : D)
    (values : Fin (n + 1) → D) (i : Fin (n + 1)) :
    slotAssignment source values (-(Int.ofNat (i.val + 2))) = values i := by
  classical
  have hexists : ∃ j : Fin (n + 1),
      -(Int.ofNat (i.val + 2)) = -(Int.ofNat (j.val + 2)) := ⟨i, rfl⟩
  rw [slotAssignment, dif_pos hexists]
  congr 1
  apply Fin.ext
  have hchosen := Classical.choose_spec hexists
  have hnat : i.val + 2 = (Classical.choose hexists).val + 2 :=
    Int.ofNat_injective (neg_injective hchosen)
  omega

@[simp] private theorem slotAssignment_zero {n : Nat} (source : D)
    (values : Fin (n + 1) → D) :
    slotAssignment source values 0 = source := by
  rw [slotAssignment, dif_neg]
  intro hexists
  rcases hexists with ⟨i, hi⟩
  have hzero : Int.ofNat (i.val + 2) = 0 := neg_eq_zero.mp hi.symm
  have hnat : i.val + 2 = 0 :=
    Int.ofNat_injective (show Int.ofNat (i.val + 2) = Int.ofNat 0 from hzero)
  omega

/-- Encode one normalized source clause. Canonical Skolem identifiers pair the
    source-clause index with a constructor-local witness slot. -/
def encodeClause (index : Nat) :
    OClause (Fin conceptCount) (Fin roleCount) (Fin individualCount) → List FCL
  | .gci body head =>
      [⟨body.map (con · x), head.map (con · x)⟩]
  | .exR source role filler =>
      [ ⟨[con source x], [rol role x (.app (Nat.pair index 0) x)]⟩
      , ⟨[con source x], [con filler (.app (Nat.pair index 0) x)]⟩ ]
  | .allR source role filler =>
      [⟨[con source x, rol role x y], [con filler y]⟩]
  | .exL role filler conclusion =>
      [⟨[con filler y, rol role x y], [con conclusion x]⟩]
  | .subR sub sup =>
      [⟨[rol sub x y], [rol sup x y]⟩]
  | .inv role inverse =>
      [ ⟨[rol role x y], [rol inverse y x]⟩
      , ⟨[rol inverse x y], [rol role y x]⟩ ]
  | .func role =>
      [⟨[rol role x y, rol role x z], [.eq y z]⟩]
  | .nom concept name =>
      [ ⟨[con concept x], [.eq x (individual name)]⟩
      , ⟨[], [con concept (individual name)]⟩ ]
  | .atMost n role concept =>
      [⟨atMostBodyL n role concept, atMostHeadL n⟩]
  | .guardedAtMost source n role concept =>
      [⟨con source x :: atMostBodyL n role concept, atMostHeadL n⟩]
  | .guardedAtLeast source n role concept =>
      guardedAtLeastClauses index source n role concept

def encodeFrom (index : Nat) :
    Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount) → List FCL
  | [] => []
  | clause :: rest => encodeClause index clause ++ encodeFrom (index + 1) rest

def encode
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    List FCL :=
  encodeFrom 0 ontology

open ContextCalculus.CBClauseShape

/-- Exact source encoding invariant: equality and disequality never occur in
clause bodies. -/
theorem encodeClause_predicateBody
    (index : Nat)
    (clause : OClause (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    ∀ encoded ∈ encodeClause index clause, PredicateBody encoded := by
  cases clause <;>
    simp [encodeClause, PredicateBody, con, rol, CBALCEncoding.con,
      CBALCEncoding.rol, atMostBodyL,
      guardedAtLeastClauses, atLeastRoleClauses, atLeastConceptClauses,
      atLeastDistinctClauses] <;> aesop

theorem encodeFrom_predicateBody
    (index : Nat)
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    ∀ clause ∈ encodeFrom index ontology, PredicateBody clause := by
  induction ontology generalizing index with
  | nil => simp [encodeFrom]
  | cons source rest ih =>
      intro clause hclause
      simp only [encodeFrom, List.mem_append] at hclause
      exact hclause.elim
        (encodeClause_predicateBody index source clause)
        (ih (index + 1) clause)

theorem encode_predicateBody
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    ∀ clause ∈ encode ontology, PredicateBody clause := by
  simpa [encode] using encodeFrom_predicateBody 0 ontology

/-- Restrict a nested-term model to the exact bounded source signature. -/
def restrictModel (model : TModel D) :
    Eqv.Interp D (Fin conceptCount) (Fin roleCount) (Fin individualCount) where
  c concept := model.conc concept.val
  r role := model.rol role.val
  nm name := model.const name.val

/-! ### Semantic clauses for the equational features -/

theorem valid_subR_iff (model : TModel D) (sub sup : Fin roleCount) :
    valid model ⟨[rol sub x y], [rol sup x y]⟩ ↔
      ∀ source target, model.rol sub.val source target →
        model.rol sup.val source target := by
  constructor
  · intro hvalid source target hsub
    let assignment : Int → D := fun id => if id = -1 then target else source
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [List.mem_singleton] at hliteral
      subst literal
      simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using hsub) with
      ⟨literal, hliteral, htrue⟩
    simp only [List.mem_singleton] at hliteral
    subst literal
    simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using htrue
  · intro hsemantic assignment hbody
    exact ⟨rol sup x y, by simp,
      hsemantic (assignment 0) (assignment (-1))
        (hbody (rol sub x y) (by simp))⟩

theorem valid_inv_iff (model : TModel D) (role inverse : Fin roleCount) :
    (valid model ⟨[rol role x y], [rol inverse y x]⟩ ∧
      valid model ⟨[rol inverse x y], [rol role y x]⟩) ↔
      ∀ source target, model.rol role.val source target ↔
        model.rol inverse.val target source := by
  constructor
  · rintro ⟨hforward, hbackward⟩ source target
    let assignment : Int → D := fun id => if id = -1 then target else source
    constructor
    · intro hrole
      rcases hforward assignment (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using hrole) with
        ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using htrue
    · intro hinverse
      let reverseAssignment : Int → D := fun id =>
        if id = -1 then source else target
      rcases hbackward reverseAssignment (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        simpa [reverseAssignment, rol, x, y, TModel.evalL, TModel.evalT] using hinverse) with
        ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      simpa [reverseAssignment, rol, x, y, TModel.evalL, TModel.evalT] using htrue
  · intro hsemantic
    constructor
    · intro assignment hbody
      exact ⟨rol inverse y x, by simp,
        (hsemantic (assignment 0) (assignment (-1))).1
          (hbody (rol role x y) (by simp))⟩
    · intro assignment hbody
      exact ⟨rol role y x, by simp,
        (hsemantic (assignment (-1)) (assignment 0)).2
          (hbody (rol inverse x y) (by simp))⟩

theorem valid_func_iff (model : TModel D) (role : Fin roleCount) :
    valid model ⟨[rol role x y, rol role x z], [.eq y z]⟩ ↔
      ∀ source first second, model.rol role.val source first →
        model.rol role.val source second → first = second := by
  constructor
  · intro hvalid source first second hfirst hsecond
    let assignment : Int → D := fun id =>
      if id = -1 then first else if id = -2 then second else source
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl
      · simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using hfirst
      · simpa [assignment, rol, x, z, TModel.evalL, TModel.evalT] using hsecond) with
      ⟨literal, hliteral, htrue⟩
    simp only [List.mem_singleton] at hliteral
    subst literal
    simpa [assignment, y, z, TModel.evalL, TModel.evalT] using htrue
  · intro hsemantic assignment hbody
    exact ⟨.eq y z, by simp,
      hsemantic (assignment 0) (assignment (-1)) (assignment (-2))
        (hbody (rol role x y) (by simp))
        (hbody (rol role x z) (by simp))⟩

theorem valid_nom_iff (model : TModel D) (concept : Fin conceptCount)
    (name : Fin individualCount) :
    (valid model ⟨[con concept x], [.eq x (individual name)]⟩ ∧
      valid model ⟨[], [con concept (individual name)]⟩) ↔
      ∀ element, model.conc concept.val element ↔ element = model.const name.val := by
  constructor
  · rintro ⟨hto, hfrom⟩ element
    constructor
    · intro hconcept
      rcases hto (fun _ => element) (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        exact hconcept) with ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      exact htrue
    · intro heq
      subst element
      rcases hfrom (fun _ => model.const name.val) (by
        intro literal hliteral
        simp only [List.not_mem_nil] at hliteral) with ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      exact htrue
  · intro hsemantic
    constructor
    · intro assignment hbody
      exact ⟨.eq x (individual name), by simp,
        (hsemantic (assignment 0)).1 (hbody (con concept x) (by simp))⟩
    · intro assignment _
      exact ⟨con concept (individual name), by simp,
        (hsemantic (model.const name.val)).2 rfl⟩

theorem valid_atMost_iff (model : TModel D) (n : Nat) (role : Fin roleCount)
    (concept : Fin conceptCount) :
    valid model ⟨atMostBodyL n role concept, atMostHeadL n⟩ ↔
      ∀ source, ∀ values : Fin (n + 1) → D,
        (∀ i, model.rol role.val source (values i) ∧
          model.conc concept.val (values i)) →
        ∃ i j, i ≠ j ∧ values i = values j := by
  constructor
  · intro hvalid source values hvalues
    let assignment : Int → D := slotAssignment source values
    rcases hvalid assignment (by
      intro literal hliteral
      rw [mem_atMostBodyL] at hliteral
      rcases hliteral with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · change model.rol role.val (slotAssignment source values 0)
          (slotAssignment source values (-(Int.ofNat (i.val + 2))))
        simpa only [slotAssignment_zero, slotAssignment_slot] using (hvalues i).1
      · change model.conc concept.val
          (slotAssignment source values (-(Int.ofNat (i.val + 2))))
        simpa only [slotAssignment_slot] using (hvalues i).2) with
      ⟨literal, hliteral, htrue⟩
    rw [mem_atMostHeadL] at hliteral
    rcases hliteral with ⟨i, j, hlt, rfl⟩
    refine ⟨i, j, ne_of_lt hlt, ?_⟩
    change slotAssignment source values (-(Int.ofNat (i.val + 2))) =
      slotAssignment source values (-(Int.ofNat (j.val + 2))) at htrue
    simpa only [slotAssignment_slot] using htrue
  · intro hsemantic assignment hbody
    let values : Fin (n + 1) → D := fun i => assignment (-(Int.ofNat (i.val + 2)))
    rcases hsemantic (assignment 0) values (by
      intro i
      constructor
      · exact hbody (rol role x (slot i))
          (mem_atMostBodyL.mpr (Or.inl ⟨i, rfl⟩))
      · exact hbody (con concept (slot i))
          (mem_atMostBodyL.mpr (Or.inr ⟨i, rfl⟩))) with
      ⟨i, j, hne, heq⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨.eq (slot i) (slot j),
        mem_atMostHeadL.mpr ⟨i, j, hlt, rfl⟩, heq⟩
    · exact ⟨.eq (slot j) (slot i),
        mem_atMostHeadL.mpr ⟨j, i, hgt, rfl⟩, heq.symm⟩

theorem valid_guardedAtMost_iff (model : TModel D)
    (source : Fin conceptCount) (n : Nat) (role : Fin roleCount)
    (concept : Fin conceptCount) :
    valid model ⟨con source x :: atMostBodyL n role concept, atMostHeadL n⟩ ↔
      ∀ element, model.conc source.val element →
        ∀ values : Fin (n + 1) → D,
          (∀ i, model.rol role.val element (values i) ∧
            model.conc concept.val (values i)) →
          ∃ i j, i ≠ j ∧ values i = values j := by
  constructor
  · intro hvalid element hsource values hvalues
    let assignment : Int → D := slotAssignment element values
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [List.mem_cons] at hliteral
      rcases hliteral with rfl | hliteral
      · change model.conc source.val (slotAssignment element values 0)
        simpa only [slotAssignment_zero] using hsource
      · rw [mem_atMostBodyL] at hliteral
        rcases hliteral with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · change model.rol role.val (slotAssignment element values 0)
            (slotAssignment element values (-(Int.ofNat (i.val + 2))))
          simpa only [slotAssignment_zero, slotAssignment_slot] using (hvalues i).1
        · change model.conc concept.val
            (slotAssignment element values (-(Int.ofNat (i.val + 2))))
          simpa only [slotAssignment_slot] using (hvalues i).2) with
      ⟨literal, hliteral, htrue⟩
    rw [mem_atMostHeadL] at hliteral
    rcases hliteral with ⟨i, j, hlt, rfl⟩
    refine ⟨i, j, ne_of_lt hlt, ?_⟩
    change slotAssignment element values (-(Int.ofNat (i.val + 2))) =
      slotAssignment element values (-(Int.ofNat (j.val + 2))) at htrue
    simpa only [slotAssignment_slot] using htrue
  · intro hsemantic assignment hbody
    let values : Fin (n + 1) → D := fun i => assignment (-(Int.ofNat (i.val + 2)))
    rcases hsemantic (assignment 0)
      (hbody (con source x) (by simp)) values (by
        intro i
        constructor
        · apply hbody (rol role x (slot i))
          simp only [List.mem_cons]
          exact Or.inr (mem_atMostBodyL.mpr (Or.inl ⟨i, rfl⟩))
        · apply hbody (con concept (slot i))
          simp only [List.mem_cons]
          exact Or.inr (mem_atMostBodyL.mpr (Or.inr ⟨i, rfl⟩))) with
      ⟨i, j, hne, heq⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨.eq (slot i) (slot j),
        mem_atMostHeadL.mpr ⟨i, j, hlt, rfl⟩, heq⟩
    · exact ⟨.eq (slot j) (slot i),
        mem_atMostHeadL.mpr ⟨j, i, hgt, rfl⟩, heq.symm⟩

theorem guardedAtLeast_of_valid (model : TModel D) (index : Nat)
    (source : Fin conceptCount) (n : Nat) (role : Fin roleCount)
    (concept : Fin conceptCount)
    (hvalid : ∀ clause ∈ guardedAtLeastClauses index source n role concept,
      valid model clause) :
    ∀ element, model.conc source.val element →
      ∃ values : Fin n → D,
        (∀ i, model.rol role.val element (values i) ∧
          model.conc concept.val (values i)) ∧ Function.Injective values := by
  intro element hsource
  let values : Fin n → D := fun i => model.fn (Nat.pair index i.val) element
  refine ⟨values, ?_, ?_⟩
  · intro i
    constructor
    · have hclause := hvalid _ (by
        simp only [guardedAtLeastClauses, List.mem_append]
        exact Or.inl (Or.inl (mem_atLeastRoleClauses.mpr ⟨i, rfl⟩)))
      rcases hclause (fun _ => element) (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        exact hsource) with ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      simpa [values, atLeastWitness, x, TModel.evalL, TModel.evalT] using htrue
    · have hclause := hvalid _ (by
        simp only [guardedAtLeastClauses, List.mem_append]
        exact Or.inl (Or.inr (mem_atLeastConceptClauses.mpr ⟨i, rfl⟩)))
      rcases hclause (fun _ => element) (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        exact hsource) with ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      simpa [values, atLeastWitness, x, TModel.evalL, TModel.evalT] using htrue
  · intro i j hequal
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hclause := hvalid _ (by
        simp only [guardedAtLeastClauses, List.mem_append]
        exact Or.inr (mem_atLeastDistinctClauses.mpr ⟨i, j, hij, rfl⟩))
      obtain ⟨literal, hliteral, hnequal⟩ := hclause (fun _ => element) (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        exact hsource)
      simp only [List.mem_singleton] at hliteral
      subst literal
      exact (hnequal (by
        simpa [values, atLeastWitness, x, TModel.evalL, TModel.evalT] using hequal.symm)).elim
    · have hclause := hvalid _ (by
        simp only [guardedAtLeastClauses, List.mem_append]
        exact Or.inr (mem_atLeastDistinctClauses.mpr ⟨j, i, hji, rfl⟩))
      obtain ⟨literal, hliteral, hnequal⟩ := hclause (fun _ => element) (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        exact hsource)
      simp only [List.mem_singleton] at hliteral
      subst literal
      exact (hnequal (by
        simpa [values, atLeastWitness, x, TModel.evalL, TModel.evalT] using hequal)).elim

/-! ### Restriction from encoded term models -/

theorem models_restrict
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (model : TModel D) (hmodels : ∀ clause ∈ encode ontology, valid model clause) :
    Eqv.models (restrictModel model) ontology := by
  have go : ∀ (index : Nat)
      (rest : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)),
      (∀ encoded ∈ encodeFrom index rest, valid model encoded) →
      Eqv.models (restrictModel model) rest := by
    intro index rest
    induction rest generalizing index with
    | nil => simp [Eqv.models]
    | cons clause rest ih =>
        intro hall candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with hhead | hrest
        · subst candidate
          have hencoded : ∀ encoded ∈ encodeClause index clause,
              valid model encoded := by
            intro encoded hmem
            exact hall encoded (by simp [encodeFrom, hmem])
          cases clause with
          | gci body head =>
              exact (CBALCEncoding.valid_gci_iff model body head).1
                (hencoded _ (by simp [encodeClause]))
          | exR source role filler =>
              intro element hsource
              let target := model.fn (Nat.pair index 0) element
              refine ⟨target, ?_, ?_⟩
              · have hvalid := hencoded
                  ⟨[con source x], [rol role x (.app (Nat.pair index 0) x)]⟩
                  (by simp [encodeClause])
                rcases hvalid (fun _ => element) (by
                  intro literal hliteral
                  simp only [List.mem_singleton] at hliteral
                  subst literal
                  exact hsource) with ⟨literal, hliteral, htrue⟩
                simp only [List.mem_singleton] at hliteral
                subst literal
                exact htrue
              · have hvalid := hencoded
                  ⟨[con source x], [con filler (.app (Nat.pair index 0) x)]⟩
                  (by simp [encodeClause])
                rcases hvalid (fun _ => element) (by
                  intro literal hliteral
                  simp only [List.mem_singleton] at hliteral
                  subst literal
                  exact hsource) with ⟨literal, hliteral, htrue⟩
                simp only [List.mem_singleton] at hliteral
                subst literal
                exact htrue
          | allR source role filler =>
              exact (CBALCEncoding.valid_allRight_iff model source role filler).1
                (hencoded _ (by simp [encodeClause]))
          | exL role filler conclusion =>
              exact (CBALCEncoding.valid_exLeft_iff model role filler conclusion).1
                (hencoded _ (by simp [encodeClause]))
          | subR sub sup =>
              exact (valid_subR_iff model sub sup).1
                (hencoded _ (by simp [encodeClause]))
          | inv role inverse =>
              exact (valid_inv_iff model role inverse).1 ⟨
                hencoded _ (by simp [encodeClause]),
                hencoded _ (by simp [encodeClause])⟩
          | func role =>
              exact (valid_func_iff model role).1
                (hencoded _ (by simp [encodeClause]))
          | nom concept name =>
              exact (valid_nom_iff model concept name).1 ⟨
                hencoded _ (by simp [encodeClause]),
                hencoded _ (by simp [encodeClause])⟩
          | atMost n role concept =>
              exact (valid_atMost_iff model n role concept).1
                (hencoded _ (by simp [encodeClause]))
          | guardedAtMost source n role concept =>
              exact (valid_guardedAtMost_iff model source n role concept).1
                (hencoded _ (by simp [encodeClause]))
          | guardedAtLeast source n role concept =>
              exact guardedAtLeast_of_valid model index source n role concept (by
                intro encoded hmem
                exact hencoded encoded (by simpa [encodeClause] using hmem))
        · apply ih (index := index + 1)
          · intro encoded hencoded
            exact hall encoded (by simp [encodeFrom, hencoded])
          · exact hrest
  exact go 0 ontology (by simpa [encode] using hmodels)

/-! ### Extension to encoded term models -/

noncomputable def witnessFor
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    (index : Nat) (element : D) : D := by
  classical
  exact match hclause : ontology[index]? with
    | some (.exR source role filler) =>
        if hsource : interpretation.c source element then
          Classical.choose (hmodels _ (List.mem_of_getElem? hclause) element hsource)
        else default
    | _ => default

theorem witnessFor_spec
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    {index : Nat} {source : Fin conceptCount} {role : Fin roleCount}
    {filler : Fin conceptCount}
    (hclause : ontology[index]? = some (.exR source role filler))
    (element : D) (hsource : interpretation.c source element) :
    interpretation.r role element
        (witnessFor ontology interpretation hmodels default index element) ∧
      interpretation.c filler
        (witnessFor ontology interpretation hmodels default index element) := by
  have hspec := Classical.choose_spec
    (hmodels _ (List.mem_of_getElem? hclause) element hsource)
  rw [witnessFor]
  split
  next source' role' filler' hlookup =>
    have hinj : OClause.exR source' role' filler' =
        OClause.exR source role filler :=
      Option.some.inj (hlookup.symm.trans hclause)
    injection hinj with hsource' hrole' hfiller'
    subst source'
    subst role'
    subst filler'
    simpa only [hsource, dite_true] using hspec
  next hlookup => exact (hlookup source role filler hclause).elim

noncomputable def atLeastWitnessFor
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    (index slot : Nat) (element : D) : D := by
  classical
  exact match hclause : ontology[index]? with
    | some (.guardedAtLeast source n role concept) =>
        if hslot : slot < n then
          if hsource : interpretation.c source element then
            (Classical.choose
              (hmodels _ (List.mem_of_getElem? hclause) element hsource)) ⟨slot, hslot⟩
          else default
        else default
    | _ => default

theorem atLeastWitnessFor_spec
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    {index : Nat} {source : Fin conceptCount} {n : Nat}
    {role : Fin roleCount} {concept : Fin conceptCount}
    (hclause : ontology[index]? = some (.guardedAtLeast source n role concept))
    (element : D) (hsource : interpretation.c source element) :
    (∀ i : Fin n,
      interpretation.r role element
          (atLeastWitnessFor ontology interpretation hmodels default index i element) ∧
        interpretation.c concept
          (atLeastWitnessFor ontology interpretation hmodels default index i element)) ∧
      Function.Injective (fun i : Fin n =>
        atLeastWitnessFor ontology interpretation hmodels default index i element) := by
  have hsemantic := hmodels _ (List.mem_of_getElem? hclause) element hsource
  let family : Fin n → D := Classical.choose hsemantic
  have hspec := Classical.choose_spec hsemantic
  have heq : ∀ i : Fin n,
      atLeastWitnessFor ontology interpretation hmodels default index i element =
        family i := by
    intro i
    rw [atLeastWitnessFor]
    split
    next source' n' role' concept' hlookup =>
      have hinj : OClause.guardedAtLeast source' n' role' concept' =
          OClause.guardedAtLeast source n role concept :=
        Option.some.inj (hlookup.symm.trans hclause)
      injection hinj with hsource' hn' hrole' hconcept'
      subst source'
      subst n'
      subst role'
      subst concept'
      simp only [i.isLt, hsource, dite_true]
      rfl
    next hlookup => exact (hlookup source n role concept hclause).elim
  constructor
  · intro i
    rw [heq i]
    exact hspec.1 i
  · intro i j hij
    change atLeastWitnessFor ontology interpretation hmodels default index i element =
      atLeastWitnessFor ontology interpretation hmodels default index j element at hij
    rw [heq i, heq j] at hij
    exact hspec.2 hij

noncomputable def functionInterpretation
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    (canonical : Nat) (element : D) : D :=
  let owner := Nat.unpair canonical
  match ontology[owner.1]? with
  | some (.guardedAtLeast _ _ _ _) =>
      atLeastWitnessFor ontology interpretation hmodels default owner.1 owner.2 element
  | _ =>
      if owner.2 = 0 then
        witnessFor ontology interpretation hmodels default owner.1 element
      else default

noncomputable def extendModel
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D) : TModel D where
  conc id element := if h : id < conceptCount then interpretation.c ⟨id, h⟩ element
    else False
  rol id source target := if h : id < roleCount then
    interpretation.r ⟨id, h⟩ source target else False
  const id := if h : id < individualCount then interpretation.nm ⟨id, h⟩ else default
  fn := functionInterpretation ontology interpretation hmodels default

@[simp] theorem extendModel_conc
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    (concept : Fin conceptCount) (element : D) :
    (extendModel ontology interpretation hmodels default).conc concept.val element ↔
      interpretation.c concept element := by
  simp [extendModel, concept.isLt]

@[simp] theorem extendModel_rol
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    (role : Fin roleCount) (source target : D) :
    (extendModel ontology interpretation hmodels default).rol role.val source target ↔
      interpretation.r role source target := by
  simp [extendModel, role.isLt]

@[simp] theorem extendModel_const
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    (name : Fin individualCount) :
    (extendModel ontology interpretation hmodels default).const name.val =
      interpretation.nm name := by
  simp [extendModel, name.isLt]

theorem valid_guardedAtLeast_extend
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D)
    {index : Nat} {source : Fin conceptCount} {n : Nat}
    {role : Fin roleCount} {concept : Fin conceptCount}
    (hclause : ontology[index]? = some (.guardedAtLeast source n role concept)) :
    ∀ encoded ∈ guardedAtLeastClauses index source n role concept,
      valid (extendModel ontology interpretation hmodels default) encoded := by
  let model := extendModel ontology interpretation hmodels default
  intro encoded hencoded
  simp only [guardedAtLeastClauses, List.mem_append] at hencoded
  rcases hencoded with (hrole | hconcept) | hdistinct
  · rw [mem_atLeastRoleClauses] at hrole
    obtain ⟨i, rfl⟩ := hrole
    intro assignment hbody
    have hsource : interpretation.c source (assignment 0) := by
      have hm : model.conc source.val (assignment 0) := by
        simpa [con, x, TModel.evalL, TModel.evalT] using
          hbody (con source x) (by simp)
      simpa only [model, extendModel_conc] using hm
    have hspec := (atLeastWitnessFor_spec ontology interpretation hmodels default
      hclause (assignment 0) hsource).1 i
    exact ⟨rol role x (atLeastWitness index i), by simp, by
      change model.rol role.val (assignment 0)
        (model.fn (Nat.pair index i.val) (assignment 0))
      simpa [model, extendModel, functionInterpretation, hclause, role.isLt,
        atLeastWitness] using hspec.1⟩
  · rw [mem_atLeastConceptClauses] at hconcept
    obtain ⟨i, rfl⟩ := hconcept
    intro assignment hbody
    have hsource : interpretation.c source (assignment 0) := by
      have hm : model.conc source.val (assignment 0) := by
        simpa [con, x, TModel.evalL, TModel.evalT] using
          hbody (con source x) (by simp)
      simpa only [model, extendModel_conc] using hm
    have hspec := (atLeastWitnessFor_spec ontology interpretation hmodels default
      hclause (assignment 0) hsource).1 i
    exact ⟨con concept (atLeastWitness index i), by simp, by
      change model.conc concept.val
        (model.fn (Nat.pair index i.val) (assignment 0))
      simpa [model, extendModel, functionInterpretation, hclause, concept.isLt,
        atLeastWitness] using hspec.2⟩
  · rw [mem_atLeastDistinctClauses] at hdistinct
    obtain ⟨i, j, hij, rfl⟩ := hdistinct
    intro assignment hbody
    have hsource : interpretation.c source (assignment 0) := by
      have hm : model.conc source.val (assignment 0) := by
        simpa [con, x, TModel.evalL, TModel.evalT] using
          hbody (con source x) (by simp)
      simpa only [model, extendModel_conc] using hm
    have hinjective := (atLeastWitnessFor_spec ontology interpretation hmodels default
      hclause (assignment 0) hsource).2
    exact ⟨.ineq (atLeastWitness index j) (atLeastWitness index i), by simp, by
      intro hequal
      apply ne_of_gt hij
      apply hinjective
      simpa [model, extendModel, functionInterpretation, hclause, atLeastWitness,
        TModel.evalL, TModel.evalT] using hequal⟩

theorem models_extend
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount))
    (hmodels : Eqv.models interpretation ontology) (default : D) :
    ∀ encoded ∈ encode ontology,
      valid (extendModel ontology interpretation hmodels default) encoded := by
  let model := extendModel ontology interpretation hmodels default
  have go : ∀ (index : Nat)
      (rest : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)),
      (∀ clause ∈ rest, clause ∈ ontology) →
      (∀ offset clause, rest[offset]? = some clause →
        ontology[index + offset]? = some clause) →
      ∀ encoded ∈ encodeFrom index rest, valid model encoded := by
    intro index rest hsubset hlookup
    induction rest generalizing index with
    | nil => simp [encodeFrom]
    | cons clause rest ih =>
        intro encoded hencoded
        simp only [encodeFrom, List.mem_append] at hencoded
        rcases hencoded with hhead | htail
        · have hclauseOntology : clause ∈ ontology := hsubset clause (by simp)
          have hsemantic := hmodels clause hclauseOntology
          cases clause with
          | gci body head =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (CBALCEncoding.valid_gci_iff model body head).2
              intro element hbody
              rcases hsemantic element (by
                intro concept hconcept
                simpa only [model, extendModel_conc] using hbody concept hconcept) with
                ⟨concept, hconcept, htrue⟩
              exact ⟨concept, hconcept, by
                simpa only [model, extendModel_conc] using htrue⟩
          | exR source role filler =>
              simp only [encodeClause, List.mem_cons, List.not_mem_nil, or_false] at hhead
              have hindex : ontology[index]? = some (.exR source role filler) := by
                simpa using hlookup 0 (.exR source role filler) rfl
              rcases hhead with rfl | rfl
              · intro assignment hbody
                have hsource : interpretation.c source (assignment 0) := by
                  have hm : model.conc source.val (assignment 0) := by
                    simpa [con, x, TModel.evalL, TModel.evalT] using
                      hbody (con source x) (by simp)
                  simpa only [model, extendModel_conc] using hm
                exact ⟨rol role x (.app (Nat.pair index 0) x), by simp,
                  by
                    have hw := (witnessFor_spec ontology interpretation hmodels default
                      hindex (assignment 0) hsource).1
                    change model.rol role.val (assignment 0)
                      (model.fn (Nat.pair index 0) (assignment 0))
                    simpa [model, extendModel, functionInterpretation, hindex,
                      role.isLt] using hw⟩
              · intro assignment hbody
                have hsource : interpretation.c source (assignment 0) := by
                  have hm : model.conc source.val (assignment 0) := by
                    simpa [con, x, TModel.evalL, TModel.evalT] using
                      hbody (con source x) (by simp)
                  simpa only [model, extendModel_conc] using hm
                exact ⟨con filler (.app (Nat.pair index 0) x), by simp,
                  by
                    have hw := (witnessFor_spec ontology interpretation hmodels default
                      hindex (assignment 0) hsource).2
                    change model.conc filler.val
                      (model.fn (Nat.pair index 0) (assignment 0))
                    simpa [model, extendModel, functionInterpretation, hindex,
                      filler.isLt] using hw⟩
          | allR source role filler =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (CBALCEncoding.valid_allRight_iff model source role filler).2
              intro element hsource target hrole
              have hresult := hsemantic element
                (by simpa only [model, extendModel_conc] using hsource) target
                (by simpa only [model, extendModel_rol] using hrole)
              simpa only [model, extendModel_conc] using hresult
          | exL role filler conclusion =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (CBALCEncoding.valid_exLeft_iff model role filler conclusion).2
              intro source hexists
              rcases hexists with ⟨target, hrole, hfiller⟩
              have hresult := hsemantic source ⟨target,
                by simpa only [model, extendModel_rol] using hrole,
                by simpa only [model, extendModel_conc] using hfiller⟩
              simpa only [model, extendModel_conc] using hresult
          | subR sub sup =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (valid_subR_iff model sub sup).2
              intro source target hsub
              have hresult := hsemantic source target
                (by simpa only [model, extendModel_rol] using hsub)
              simpa only [model, extendModel_rol] using hresult
          | inv role inverse =>
              simp only [encodeClause, List.mem_cons, List.not_mem_nil, or_false] at hhead
              apply hhead.elim <;> intro heq <;> subst encoded
              · exact (valid_inv_iff model role inverse).2 (by
                  intro source target
                  simpa only [model, extendModel_rol] using hsemantic source target) |>.1
              · exact (valid_inv_iff model role inverse).2 (by
                  intro source target
                  simpa only [model, extendModel_rol] using hsemantic source target) |>.2
          | func role =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (valid_func_iff model role).2
              intro source first second hfirst hsecond
              exact hsemantic source first second
                (by simpa only [model, extendModel_rol] using hfirst)
                (by simpa only [model, extendModel_rol] using hsecond)
          | nom concept name =>
              simp only [encodeClause, List.mem_cons, List.not_mem_nil, or_false] at hhead
              apply hhead.elim <;> intro heq <;> subst encoded
              · exact (valid_nom_iff model concept name).2 (by
                  intro element
                  simpa only [model, extendModel_conc, extendModel_const] using
                    hsemantic element) |>.1
              · exact (valid_nom_iff model concept name).2 (by
                  intro element
                  simpa only [model, extendModel_conc, extendModel_const] using
                    hsemantic element) |>.2
          | atMost n role concept =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (valid_atMost_iff model n role concept).2
              intro source values hvalues
              apply hsemantic source values
              intro i
              exact ⟨by simpa only [model, extendModel_rol] using (hvalues i).1,
                by simpa only [model, extendModel_conc] using (hvalues i).2⟩
          | guardedAtMost source n role concept =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (valid_guardedAtMost_iff model source n role concept).2
              intro element hsource values hvalues
              apply hsemantic element
              · simpa only [model, extendModel_conc] using hsource
              · intro i
                exact ⟨by simpa only [model, extendModel_rol] using (hvalues i).1,
                  by simpa only [model, extendModel_conc] using (hvalues i).2⟩
          | guardedAtLeast source n role concept =>
              have hindex : ontology[index]? =
                  some (.guardedAtLeast source n role concept) := by
                simpa using hlookup 0 (.guardedAtLeast source n role concept) rfl
              exact valid_guardedAtLeast_extend ontology interpretation hmodels default
                hindex encoded (by simpa [encodeClause] using hhead)
        · apply ih (index := index + 1)
          · intro candidate hcand
            exact hsubset candidate (by simp [hcand])
          · intro offset candidate hcandidate
            have hshift := hlookup (offset + 1) candidate (by simpa using hcandidate)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
          · exact htail
  apply go 0 ontology (by simp)
  · intro offset clause hclause
    simpa using hclause

/-! ### Exact source semantics -/

def EntailsSub
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (sub sup : Fin conceptCount) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ encode ontology, valid model clause) →
      ∀ element, model.conc sub.val element → model.conc sup.val element

theorem entailsSub_iff_source
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (sub sup : Fin conceptCount) :
    EntailsSub ontology sub sup ↔
      ∀ (D : Type)
        (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
          (Fin individualCount)),
        Eqv.models interpretation ontology → ∀ element,
          interpretation.c sub element → interpretation.c sup element := by
  constructor
  · intro hentails D interpretation hmodels element hsub
    let model := extendModel ontology interpretation hmodels element
    have hsup := hentails D model
      (models_extend ontology interpretation hmodels element) element
      (by simpa only [model, extendModel_conc] using hsub)
    simpa only [model, extendModel_conc] using hsup
  · intro hentails D model hmodels element hsub
    exact hentails D (restrictModel model) (models_restrict ontology model hmodels)
      element hsub

/-- Source satisfiability uses the standard nonempty-domain convention. -/
def SourceSatisfiable
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    Prop :=
  ∃ (D : Type) (_ : Nonempty D)
    (interpretation : Eqv.Interp D (Fin conceptCount) (Fin roleCount)
      (Fin individualCount)),
    Eqv.models interpretation ontology

def EncodedSatisfiable
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    Prop :=
  ∃ (D : Type) (model : TModel D),
    ∀ clause ∈ encode ontology, valid model clause

theorem satisfiable_iff_source
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    EncodedSatisfiable ontology ↔ SourceSatisfiable ontology := by
  constructor
  · rintro ⟨D, model, hmodel⟩
    let inhabitant : D := model.const 0
    exact ⟨D, ⟨inhabitant⟩, restrictModel model,
      models_restrict ontology model hmodel⟩
  · rintro ⟨D, hnonempty, interpretation, hmodel⟩
    let default : D := Classical.choice hnonempty
    exact ⟨D, extendModel ontology interpretation hmodel default,
      models_extend ontology interpretation hmodel default⟩

#print axioms models_restrict
#print axioms models_extend
#print axioms entailsSub_iff_source
#print axioms satisfiable_iff_source

end ContextCalculus.CBEqEncoding
