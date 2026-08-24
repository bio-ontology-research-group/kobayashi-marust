import ContextCalculus.CBALCEncoding
import ContextCalculus.CompletenessEq

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
  .var (-(Int.ofNat (i + 1)))

private def atMostBodyL (n : Nat) (role : Fin roleCount)
    (concept : Fin conceptCount) : List FLit :=
  (List.range (n + 1)).map (fun i => rol role x (slot i)) ++
  (List.range (n + 1)).map (fun i => con concept (slot i))

private def atMostHeadL (n : Nat) : List FLit :=
  (List.range (n + 1)).flatMap (fun i =>
    (List.range (n + 1)).flatMap (fun j =>
      if i < j then [.eq (slot i) (slot j)] else []))

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
  if h : ∃ i : Fin (n + 1), id = -(Int.ofNat (i.val + 1)) then
    values (Classical.choose h)
  else source

@[simp] private theorem slotAssignment_slot {n : Nat} (source : D)
    (values : Fin (n + 1) → D) (i : Fin (n + 1)) :
    slotAssignment source values (-(Int.ofNat (i.val + 1))) = values i := by
  classical
  have hexists : ∃ j : Fin (n + 1),
      -(Int.ofNat (i.val + 1)) = -(Int.ofNat (j.val + 1)) := ⟨i, rfl⟩
  rw [slotAssignment, dif_pos hexists]
  congr 1
  apply Fin.ext
  have hchosen := Classical.choose_spec hexists
  have hnat : i.val + 1 = (Classical.choose hexists).val + 1 :=
    Int.ofNat_injective (neg_injective hchosen)
  omega

@[simp] private theorem slotAssignment_zero {n : Nat} (source : D)
    (values : Fin (n + 1) → D) :
    slotAssignment source values 0 = source := by
  rw [slotAssignment, dif_neg]
  intro hexists
  rcases hexists with ⟨i, hi⟩
  have hzero : Int.ofNat (i.val + 1) = 0 := neg_eq_zero.mp hi.symm
  have hnat : i.val + 1 = 0 :=
    Int.ofNat_injective (show Int.ofNat (i.val + 1) = Int.ofNat 0 from hzero)
  omega

/-- Encode one normalized source clause. Existential-right clauses use their
    source-list index as the Skolem function identifier. -/
def encodeClause (index : Nat) :
    OClause (Fin conceptCount) (Fin roleCount) (Fin individualCount) → List FCL
  | .gci body head =>
      [⟨body.map (con · x), head.map (con · x)⟩]
  | .exR source role filler =>
      [ ⟨[con source x], [rol role x (.app index x)]⟩
      , ⟨[con source x], [con filler (.app index x)]⟩ ]
  | .allR source role filler =>
      [⟨[con source x, rol role x y], [con filler y]⟩]
  | .exL role filler conclusion =>
      [⟨[con filler y, rol role x y], [con conclusion x]⟩]
  | .subR sub sup =>
      [⟨[rol sub x y], [rol sup x y]⟩]
  | .inv role inverse =>
      [ ⟨[rol role x y], [rol inverse y x]⟩
      , ⟨[rol inverse y x], [rol role x y]⟩ ]
  | .func role =>
      [⟨[rol role x y, rol role x z], [.eq y z]⟩]
  | .nom concept name =>
      [ ⟨[con concept x], [.eq x (individual name)]⟩
      , ⟨[], [con concept (individual name)]⟩ ]
  | .atMost n role concept =>
      [⟨atMostBodyL n role concept, atMostHeadL n⟩]

def encodeFrom (index : Nat) :
    Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount) → List FCL
  | [] => []
  | clause :: rest => encodeClause index clause ++ encodeFrom (index + 1) rest

def encode
    (ontology : Ontology (Fin conceptCount) (Fin roleCount) (Fin individualCount)) :
    List FCL :=
  encodeFrom 0 ontology

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
      valid model ⟨[rol inverse y x], [rol role x y]⟩) ↔
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
      rcases hbackward assignment (by
        intro literal hliteral
        simp only [List.mem_singleton] at hliteral
        subst literal
        simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using hinverse) with
        ⟨literal, hliteral, htrue⟩
      simp only [List.mem_singleton] at hliteral
      subst literal
      simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using htrue
  · intro hsemantic
    constructor
    · intro assignment hbody
      exact ⟨rol inverse y x, by simp,
        (hsemantic (assignment 0) (assignment (-1))).1
          (hbody (rol role x y) (by simp))⟩
    · intro assignment hbody
      exact ⟨rol role x y, by simp,
        (hsemantic (assignment 0) (assignment (-1))).2
          (hbody (rol inverse y x) (by simp))⟩

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
          (slotAssignment source values (-(Int.ofNat (i.val + 1))))
        simpa only [slotAssignment_zero, slotAssignment_slot] using (hvalues i).1
      · change model.conc concept.val
          (slotAssignment source values (-(Int.ofNat (i.val + 1))))
        simpa only [slotAssignment_slot] using (hvalues i).2) with
      ⟨literal, hliteral, htrue⟩
    rw [mem_atMostHeadL] at hliteral
    rcases hliteral with ⟨i, j, hlt, rfl⟩
    refine ⟨i, j, ne_of_lt hlt, ?_⟩
    change slotAssignment source values (-(Int.ofNat (i.val + 1))) =
      slotAssignment source values (-(Int.ofNat (j.val + 1))) at htrue
    simpa only [slotAssignment_slot] using htrue
  · intro hsemantic assignment hbody
    let values : Fin (n + 1) → D := fun i => assignment (-(Int.ofNat (i.val + 1)))
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
              let target := model.fn index element
              refine ⟨target, ?_, ?_⟩
              · have hvalid := hencoded
                  ⟨[con source x], [rol role x (.app index x)]⟩
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
                  ⟨[con source x], [con filler (.app index x)]⟩
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
  fn := witnessFor ontology interpretation hmodels default

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
                exact ⟨rol role x (.app index x), by simp,
                  by
                    have hw := (witnessFor_spec ontology interpretation hmodels default
                      hindex (assignment 0) hsource).1
                    change model.rol role.val (assignment 0) (model.fn index (assignment 0))
                    simpa [model, extendModel, role.isLt] using hw⟩
              · intro assignment hbody
                have hsource : interpretation.c source (assignment 0) := by
                  have hm : model.conc source.val (assignment 0) := by
                    simpa [con, x, TModel.evalL, TModel.evalT] using
                      hbody (con source x) (by simp)
                  simpa only [model, extendModel_conc] using hm
                exact ⟨con filler (.app index x), by simp,
                  by
                    have hw := (witnessFor_spec ontology interpretation hmodels default
                      hindex (assignment 0) hsource).2
                    change model.conc filler.val (model.fn index (assignment 0))
                    simpa [model, extendModel, filler.isLt] using hw⟩
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
