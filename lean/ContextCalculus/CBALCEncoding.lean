import ContextCalculus.CheckerTerm
import ContextCalculus.CompletenessContext

/-!
# Exact ALC to CB nested-term encoding

This module connects the complete finite-type ALC calculus to the first-order
term semantics used by CB certificates. Each existential-right clause receives
its source-list index as a unique unary Skolem function and is encoded by the
production pair of role and filler clauses.
-/

namespace ContextCalculus.CBALCEncoding

open ContextCalculus CheckerTerm
open ContextCalculus.Ctx

def x : FTerm := .var 0
def y : FTerm := .var (-1)
def con (concept : Fin conceptCount) (term : FTerm) : FLit :=
  .P (.concept concept.val term)
def rol (role : Fin roleCount) (source target : FTerm) : FLit :=
  .P (.role role.val source target)

def encodeClause (index : Nat) : Ctx.Clause (Fin conceptCount) (Fin roleCount) → List FCL
  | .gci body head =>
      [⟨body.map (con · x), head.map (con · x)⟩]
  | .exRight source role filler =>
      [ ⟨[con source x], [rol role x (.app index x)]⟩
      , ⟨[con source x], [con filler (.app index x)]⟩ ]
  | .exLeft role filler conclusion =>
      [⟨[con filler y, rol role x y], [con conclusion x]⟩]
  | .allRight source role filler =>
      [⟨[con source x, rol role x y], [con filler y]⟩]

def encodeFrom (index : Nat) :
    Ontology (Fin conceptCount) (Fin roleCount) → List FCL
  | [] => []
  | clause :: rest => encodeClause index clause ++ encodeFrom (index + 1) rest

def encode (ontology : Ontology (Fin conceptCount) (Fin roleCount)) : List FCL :=
  encodeFrom 0 ontology

def restrictModel (model : TModel D) : Interp D (Fin conceptCount) (Fin roleCount) where
  c concept := model.conc concept.val
  r role := model.rol role.val

theorem valid_gci_iff (model : TModel D) (body head : List (Fin conceptCount)) :
    valid model ⟨body.map (con · x), head.map (con · x)⟩ ↔
      ∀ element, (∀ concept ∈ body, model.conc concept.val element) →
        ∃ concept ∈ head, model.conc concept.val element := by
  constructor
  · intro hvalid element hbody
    let assignment : Int → D := fun _ => element
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [List.mem_map] at hliteral
      rcases hliteral with ⟨concept, hconcept, rfl⟩
      exact hbody concept hconcept) with ⟨literal, hliteral, htrue⟩
    simp only [List.mem_map] at hliteral
    rcases hliteral with ⟨concept, hconcept, rfl⟩
    exact ⟨concept, hconcept, htrue⟩
  · intro hsemantic assignment hbody
    rcases hsemantic (assignment 0) (by
      intro concept hconcept
      exact hbody (con concept x)
        (List.mem_map.mpr ⟨concept, hconcept, rfl⟩)) with
      ⟨concept, hconcept, htrue⟩
    exact ⟨con concept x, List.mem_map.mpr ⟨concept, hconcept, rfl⟩, htrue⟩

theorem valid_exLeft_iff (model : TModel D) (role : Fin roleCount)
    (filler conclusion : Fin conceptCount) :
    valid model ⟨[con filler y, rol role x y], [con conclusion x]⟩ ↔
      ∀ source, (∃ target, model.rol role.val source target ∧
        model.conc filler.val target) → model.conc conclusion.val source := by
  constructor
  · intro hvalid source hexists
    rcases hexists with ⟨target, hrole, hfiller⟩
    let assignment : Int → D := fun id => if id = -1 then target else source
    have hresult := hvalid assignment
    have hhead := hresult (by
      intro literal hliteral
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl
      · simpa [assignment, con, y, TModel.evalL, TModel.evalT] using hfiller
      · simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using hrole)
    rcases hhead with ⟨literal, hliteral, htrue⟩
    simp only [List.mem_singleton] at hliteral
    subst literal
    simpa [assignment, con, x, TModel.evalL, TModel.evalT] using htrue
  · intro hsemantic assignment hbody
    refine ⟨con conclusion x, by simp, ?_⟩
    apply hsemantic (assignment 0)
    exact ⟨assignment (-1),
      hbody (rol role x y) (by simp), hbody (con filler y) (by simp)⟩

theorem valid_allRight_iff (model : TModel D) (source : Fin conceptCount)
    (role : Fin roleCount) (filler : Fin conceptCount) :
    valid model ⟨[con source x, rol role x y], [con filler y]⟩ ↔
      ∀ element, model.conc source.val element →
        ∀ target, model.rol role.val element target → model.conc filler.val target := by
  constructor
  · intro hvalid element hsource target hrole
    let assignment : Int → D := fun id => if id = -1 then target else element
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl
      · simpa [assignment, con, x, TModel.evalL, TModel.evalT] using hsource
      · simpa [assignment, rol, x, y, TModel.evalL, TModel.evalT] using hrole) with
      ⟨literal, hliteral, htrue⟩
    simp only [List.mem_singleton] at hliteral
    subst literal
    simpa [assignment, con, y, TModel.evalL, TModel.evalT] using htrue
  · intro hsemantic assignment hbody
    exact ⟨con filler y, by simp,
      hsemantic (assignment 0) (hbody (con source x) (by simp))
        (assignment (-1)) (hbody (rol role x y) (by simp))⟩

theorem models_restrict (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (model : TModel D) (hmodels : ∀ clause ∈ encode ontology, valid model clause) :
    models (restrictModel model) ontology := by
  have go : ∀ (index : Nat) (rest : Ontology (Fin conceptCount) (Fin roleCount)),
      (∀ encoded ∈ encodeFrom index rest, valid model encoded) →
      models (restrictModel model) rest := by
    intro index rest
    induction rest generalizing index with
    | nil => simp [models]
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
              exact (valid_gci_iff model body head).1
                (hencoded _ (by simp [encodeClause]))
          | exRight source role filler =>
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
          | exLeft role filler conclusion =>
              exact (valid_exLeft_iff model role filler conclusion).1
                (hencoded _ (by simp [encodeClause]))
          | allRight source role filler =>
              exact (valid_allRight_iff model source role filler).1
                (hencoded _ (by simp [encodeClause]))
        · apply ih (index := index + 1)
          · intro encoded hencoded
            exact hall encoded (by simp [encodeFrom, hencoded])
          · exact hrest
  exact go 0 ontology (by simpa [encode] using hmodels)

noncomputable def witnessFor
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (interpretation : Interp D (Fin conceptCount) (Fin roleCount))
    (hmodels : models interpretation ontology) (default : D)
    (index : Nat) (element : D) : D := by
  classical
  exact match hclause : ontology[index]? with
    | some (.exRight source role filler) =>
        if hsource : interpretation.c source element then
          Classical.choose (hmodels _ (List.mem_of_getElem? hclause)
            element hsource)
        else default
    | _ => default

theorem witnessFor_spec
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (interpretation : Interp D (Fin conceptCount) (Fin roleCount))
    (hmodels : models interpretation ontology) (default : D)
    {index : Nat} {source : Fin conceptCount} {role : Fin roleCount}
    {filler : Fin conceptCount}
    (hclause : ontology[index]? = some (.exRight source role filler))
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
    have hinj : Clause.exRight source' role' filler' =
        Clause.exRight source role filler :=
      Option.some.inj (hlookup.symm.trans hclause)
    injection hinj with hsource' hrole' hfiller'
    subst source'
    subst role'
    subst filler'
    simpa only [hsource, dite_true] using hspec
  next hlookup => exact (hlookup source role filler hclause).elim

noncomputable def extendModel
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (interpretation : Interp D (Fin conceptCount) (Fin roleCount))
    (hmodels : models interpretation ontology) (default : D) : TModel D where
  conc id element := if h : id < conceptCount then interpretation.c ⟨id, h⟩ element
    else False
  rol id source target := if h : id < roleCount then
    interpretation.r ⟨id, h⟩ source target else False
  const _ := default
  fn := witnessFor ontology interpretation hmodels default

@[simp] theorem extendModel_conc
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (interpretation : Interp D (Fin conceptCount) (Fin roleCount))
    (hmodels : models interpretation ontology) (default : D)
    (concept : Fin conceptCount) (element : D) :
    (extendModel ontology interpretation hmodels default).conc concept.val element ↔
      interpretation.c concept element := by
  simp [extendModel, concept.isLt]

@[simp] theorem extendModel_rol
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (interpretation : Interp D (Fin conceptCount) (Fin roleCount))
    (hmodels : models interpretation ontology) (default : D)
    (role : Fin roleCount) (source target : D) :
    (extendModel ontology interpretation hmodels default).rol role.val source target ↔
      interpretation.r role source target := by
  simp [extendModel, role.isLt]

theorem models_extend
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (interpretation : Interp D (Fin conceptCount) (Fin roleCount))
    (hmodels : models interpretation ontology) (default : D) :
    ∀ encoded ∈ encode ontology,
      valid (extendModel ontology interpretation hmodels default) encoded := by
  let model := extendModel ontology interpretation hmodels default
  have go : ∀ (index : Nat) (rest : Ontology (Fin conceptCount) (Fin roleCount)),
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
              apply (valid_gci_iff model body head).2
              intro element hbody
              rcases hsemantic element (by
                intro concept hconcept
                simpa only [model, extendModel_conc] using hbody concept hconcept) with
                ⟨concept, hconcept, htrue⟩
              exact ⟨concept, hconcept, by
                simpa only [model, extendModel_conc] using htrue⟩
          | exRight source role filler =>
              simp only [encodeClause, List.mem_cons,
                List.not_mem_nil, or_false] at hhead
              have hindex : ontology[index]? = some (.exRight source role filler) := by
                simpa using hlookup 0 (.exRight source role filler) rfl
              rcases hhead with rfl | rfl
              · intro assignment hbody
                have hsource : interpretation.c source (assignment 0) := by
                  simpa only [model, con, x, TModel.evalL, TModel.evalT,
                    extendModel_conc] using hbody (con source x) (by simp)
                exact ⟨rol role x (.app index x), by simp,
                  by simpa [model, rol, x, TModel.evalL, TModel.evalT,
                    extendModel, role.isLt] using
                    (witnessFor_spec ontology interpretation hmodels default hindex
                      (assignment 0) hsource).1⟩
              · intro assignment hbody
                have hsource : interpretation.c source (assignment 0) := by
                  simpa only [model, con, x, TModel.evalL, TModel.evalT,
                    extendModel_conc] using hbody (con source x) (by simp)
                exact ⟨con filler (.app index x), by simp,
                  by simpa [model, con, x, TModel.evalL, TModel.evalT,
                    extendModel, filler.isLt] using
                    (witnessFor_spec ontology interpretation hmodels default hindex
                      (assignment 0) hsource).2⟩
          | exLeft role filler conclusion =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (valid_exLeft_iff model role filler conclusion).2
              intro source hexists
              rcases hexists with ⟨target, hrole, hfiller⟩
              have hresult := hsemantic source ⟨target,
                by simpa only [model, extendModel_rol] using hrole,
                by simpa only [model, extendModel_conc] using hfiller⟩
              simpa only [model, extendModel_conc] using hresult
          | allRight source role filler =>
              simp only [encodeClause, List.mem_singleton] at hhead
              subst encoded
              apply (valid_allRight_iff model source role filler).2
              intro element hsource target hrole
              have hresult := hsemantic element
                (by simpa only [model, extendModel_conc] using hsource) target
                (by simpa only [model, extendModel_rol] using hrole)
              simpa only [model, extendModel_conc] using hresult
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

/-! ### Semantic equivalence for atomic subsumption -/

/-- Atomic subsumption in the nested-term semantics consumed by the CB
    certificate checker. -/
def EntailsSub (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (sub sup : Fin conceptCount) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ encode ontology, valid model clause) →
      ∀ element, model.conc sub.val element → model.conc sup.val element

/-- The indexed Skolem encoding preserves and reflects atomic subsumption. -/
theorem entailsSub_iff_ctx
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (sub sup : Fin conceptCount) :
    EntailsSub ontology sub sup ↔
      ∀ (D : Type) (interpretation : Interp D (Fin conceptCount) (Fin roleCount)),
        models interpretation ontology → ∀ element,
          interpretation.c sub element → interpretation.c sup element := by
  constructor
  · intro hentails D interpretation hmodels element hsub
    let model := extendModel ontology interpretation hmodels element
    have hsup := hentails D model
      (models_extend ontology interpretation hmodels element) element
      (by simpa only [model, extendModel_conc] using hsub)
    simpa only [model, extendModel_conc] using hsup
  · intro hentails D model hmodels element hsub
    have hsup := hentails D (restrictModel model)
      (models_restrict ontology model hmodels) element hsub
    exact hsup

/-- ALC good-type elimination decides exactly the same atomic subsumptions as
    the nested-term CB encoding. -/
theorem entailsSub_iff_good
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (sub sup : Fin conceptCount) :
    EntailsSub ontology sub sup ↔
      ∀ context, Good ontology context → sub ∈ context → sup ∈ context := by
  rw [entailsSub_iff_ctx, Ctx.subsumption_complete ontology sub sup]

/-- The canonical good-type domain used below is finite independently of the
    query outcome. -/
theorem goodType_domain_finite
    (ontology : Ontology (Fin conceptCount) (Fin roleCount)) :
    Finite {context : Finset (Fin conceptCount) // Good ontology context} := by
  infer_instance

/-- Every failed encoded ALC subsumption has a concrete finite canonical
    countermodel. The domain is the finite subtype of good ALC types. -/
theorem finite_countermodel_of_not_entailsSub
    (ontology : Ontology (Fin conceptCount) (Fin roleCount))
    (sub sup : Fin conceptCount) (hnot : ¬ EntailsSub ontology sub sup) :
    ∃ (context : Finset (Fin conceptCount)) (hgood : Good ontology context),
      sub ∈ context ∧ sup ∉ context ∧
      let root : {candidate : Finset (Fin conceptCount) // Good ontology candidate} :=
        ⟨context, hgood⟩
      let model := extendModel ontology (canon ontology) (canon_models ontology) root
      (∀ clause ∈ encode ontology, valid model clause) ∧
        model.conc sub.val root ∧ ¬model.conc sup.val root := by
  classical
  rw [entailsSub_iff_good] at hnot
  push Not at hnot
  rcases hnot with ⟨context, hgood, hsub, hsup⟩
  refine ⟨context, hgood, hsub, hsup, ?_⟩
  dsimp only
  refine ⟨models_extend ontology (canon ontology) (canon_models ontology)
    ⟨context, hgood⟩, ?_, ?_⟩
  · simpa only [extendModel_conc] using hsub
  · simpa only [extendModel_conc] using hsup

#print axioms witnessFor_spec
#print axioms models_extend
#print axioms entailsSub_iff_ctx
#print axioms entailsSub_iff_good
#print axioms goodType_domain_finite
#print axioms finite_countermodel_of_not_entailsSub

#print axioms models_restrict

end ContextCalculus.CBALCEncoding
