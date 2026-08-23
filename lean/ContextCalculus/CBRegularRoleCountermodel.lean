import ContextCalculus.CBRegularALCCountermodel
import ContextCalculus.CBRoleChainEncoding

/-!
# Equality-free CB regular models with role structure

This extends the ALC regular bridge with the equality-free RBox forms supported
directly by the HT unravelling: subroles, inverse-role equivalences, and binary
role chains.  Source clause order is retained, so existential Skolem function
indices remain the exact CB production indices.
-/

namespace ContextCalculus.CBRegularRoleCountermodel

open ContextCalculus CheckerTerm Eqv
open ContextCalculus.Ctx
open ContextCalculus.CBRegularALCCountermodel
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau

inductive SafeClause (Concept Role : Type) where
  | gci (body head : List Concept)
  | exR (source : Concept) (role : Role) (filler : Concept)
  | allR (source : Concept) (role : Role) (filler : Concept)
  | exL (role : Role) (filler conclusion : Concept)
  | subR (premise conclusion : Role)
  | inv (role inverse : Role)
deriving DecidableEq, Repr

def SafeClause.toOClause : SafeClause Concept Role → OClause Concept Role Individual
  | .gci body head => .gci body head
  | .exR source role filler => .exR source role filler
  | .allR source role filler => .allR source role filler
  | .exL role filler conclusion => .exL role filler conclusion
  | .subR premise conclusion => .subR premise conclusion
  | .inv role inverse => .inv role inverse

def SafeClause.toCtx? : SafeClause Concept Role → Option (Ctx.Clause Concept Role)
  | .gci body head => some (.gci body head)
  | .exR source role filler => some (.exRight source role filler)
  | .allR source role filler => some (.allRight source role filler)
  | .exL role filler conclusion => some (.exLeft role filler conclusion)
  | .subR _ _ => none
  | .inv _ _ => none

structure BinaryChain (Role : Type) where
  first : Role
  second : Role
  conclusion : Role
deriving DecidableEq, Repr

def BinaryChain.toRoleChain (chain : BinaryChain Role) : RoleChain Role :=
  ⟨[chain.first, chain.second], chain.conclusion⟩

structure SafeSource (Concept Role Individual : Type) where
  clauses : List (SafeClause Concept Role)
  chains : List (BinaryChain Role)

def SafeSource.toSource (source : SafeSource Concept Role Individual) :
    SourceOntology Concept Role Individual where
  clauses := source.clauses.map SafeClause.toOClause
  chains := source.chains.map BinaryChain.toRoleChain

def residual (source target : Fin variableCount)
    (clauses : List (SafeClause (Fin conceptCount) (Fin roleCount))) :
    List (Hypertableau.Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :=
  clauses.filterMap fun clause =>
    (clause.toCtx?).map (htClause source target)

def roleClauses (source middle target : Fin variableCount)
    (safe : SafeSource (Fin conceptCount) (Fin roleCount) Individual) :
    List (NormalizedRoleClause (Fin variableCount) (Fin roleCount)) :=
  (safe.clauses.flatMap fun clause => match clause with
    | .subR premise conclusion => [.subRole premise conclusion source target]
    | .inv role inverse =>
        [.inverseRole role inverse source target,
         .inverseRole inverse role source target]
    | _ => [])
  ++ safe.chains.map fun chain =>
    .chain chain.first chain.second chain.conclusion source middle target

def restrictHT (interpretation : Hypertableau.Interp D Concept Role)
    (name : Individual → D) : Eqv.Interp D Concept Role Individual where
  c := interpretation.concept
  r := interpretation.role
  nm := name

private theorem ctxClause_models_of_residual
    (interpretation : Hypertableau.Interp D (Fin conceptCount) (Fin roleCount))
    (source target : Fin variableCount) (hne : source ≠ target)
    (safe : SafeClause (Fin conceptCount) (Fin roleCount))
    (ctx : Ctx.Clause (Fin conceptCount) (Fin roleCount))
    (hctx : safe.toCtx? = some ctx)
    (clauses : List (SafeClause (Fin conceptCount) (Fin roleCount)))
    (hsafe : safe ∈ clauses)
    (hmodels : interpretation.models (residual source target clauses)) :
    Ctx.satClause (CBRegularALCCountermodel.restrictHT interpretation) ctx := by
  have htranslated : interpretation.modelsClause (htClause source target ctx) := by
    apply hmodels
    simp only [residual, List.mem_filterMap]
    exact ⟨safe, hsafe, by simp [hctx]⟩
  have hsingle : interpretation.models (htOntology source target [ctx]) := by
    intro clause hclause
    simp only [htOntology, List.map_singleton, List.mem_singleton] at hclause
    exact hclause ▸ htranslated
  exact models_ctx_of_models_ht interpretation source target hne [ctx] hsingle ctx (by simp)

private theorem subRole_models
    [DecidableEq Variable]
    (interpretation : Hypertableau.Interp D Concept Role)
    (source target : Variable) (hne : source ≠ target) (premise conclusion : Role)
    (hmodels : interpretation.modelsClause
      ((NormalizedRoleClause.subRole premise conclusion source target).toClause
        (Concept := Concept))) :
    ∀ x y, interpretation.role premise x y → interpretation.role conclusion x y := by
  intro x y hedge
  let assignment : Variable → D := fun node =>
    if node = target then y else x
  rcases hmodels assignment (by
    intro atom hatom
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simp [Hypertableau.Interp.satAtom, assignment, hne, hedge]) with
    ⟨atom, hatom, hsat⟩
  simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
  subst atom
  simpa [Hypertableau.Interp.satAtom, assignment, hne] using hsat

private theorem inverse_models
    [DecidableEq Variable]
    (interpretation : Hypertableau.Interp D Concept Role)
    (source target : Variable) (hne : source ≠ target) (role inverse : Role)
    (hforward : interpretation.modelsClause
      ((NormalizedRoleClause.inverseRole role inverse source target).toClause
        (Concept := Concept)))
    (hbackward : interpretation.modelsClause
      ((NormalizedRoleClause.inverseRole inverse role source target).toClause
        (Concept := Concept))) :
    ∀ x y, interpretation.role role x y ↔ interpretation.role inverse y x := by
  intro x y
  constructor
  · intro hedge
    let assignment : Variable → D := fun node =>
      if node = target then y else x
    rcases hforward assignment (by
      intro atom hatom
      simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
      subst atom
      simpa [Hypertableau.Interp.satAtom, assignment, hne] using hedge) with
      ⟨atom, hatom, hsat⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [Hypertableau.Interp.satAtom, assignment, hne] using hsat
  · intro hedge
    let assignment : Variable → D := fun node =>
      if node = target then x else y
    rcases hbackward assignment (by
      intro atom hatom
      simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
      subst atom
      simpa [Hypertableau.Interp.satAtom, assignment, hne] using hedge) with
      ⟨atom, hatom, hsat⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [Hypertableau.Interp.satAtom, assignment, hne] using hsat

theorem models_source_of_models_ht
    (interpretation : Hypertableau.Interp D (Fin conceptCount) (Fin roleCount))
    (name : Individual → D)
    (source middle target : Fin variableCount)
    (hsourceTarget : source ≠ target)
    (hmiddleSource : middle ≠ source) (hmiddleTarget : middle ≠ target)
    (safe : SafeSource (Fin conceptCount) (Fin roleCount) Individual)
    (hresidual : interpretation.models (residual source target safe.clauses))
    (hroles : interpretation.models
      ((roleClauses source middle target safe).map
        (NormalizedRoleClause.toClause (Concept := Fin conceptCount)))) :
    CBRoleChainEncoding.models (restrictHT interpretation name) safe.toSource := by
  constructor
  · intro clause hclause
    simp only [SafeSource.toSource, List.mem_map] at hclause
    rcases hclause with ⟨sourceClause, hsourceClause, rfl⟩
    cases sourceClause with
    | gci body head =>
        simpa [SafeClause.toOClause, restrictHT,
          CBRegularALCCountermodel.restrictHT, Ctx.satClause, Eqv.satO] using
          ctxClause_models_of_residual interpretation source target hsourceTarget
            (.gci body head) (.gci body head) rfl safe.clauses hsourceClause hresidual
    | exR trigger role filler =>
        simpa [SafeClause.toOClause, restrictHT,
          CBRegularALCCountermodel.restrictHT, Ctx.satClause, Eqv.satO] using
          ctxClause_models_of_residual interpretation source target hsourceTarget
            (.exR trigger role filler) (.exRight trigger role filler) rfl
            safe.clauses hsourceClause hresidual
    | allR trigger role filler =>
        simpa [SafeClause.toOClause, restrictHT,
          CBRegularALCCountermodel.restrictHT, Ctx.satClause, Eqv.satO] using
          ctxClause_models_of_residual interpretation source target hsourceTarget
            (.allR trigger role filler) (.allRight trigger role filler) rfl
            safe.clauses hsourceClause hresidual
    | exL role filler conclusion =>
        simpa [SafeClause.toOClause, restrictHT,
          CBRegularALCCountermodel.restrictHT, Ctx.satClause, Eqv.satO] using
          ctxClause_models_of_residual interpretation source target hsourceTarget
            (.exL role filler conclusion) (.exLeft role filler conclusion) rfl
            safe.clauses hsourceClause hresidual
    | subR premise conclusion =>
        have hroleClause : interpretation.modelsClause
            ((NormalizedRoleClause.subRole premise conclusion source target).toClause
              (Concept := Fin conceptCount)) := by
          apply hroles
          apply List.mem_map.mpr
          refine ⟨NormalizedRoleClause.subRole premise conclusion source target, ?_, rfl⟩
          simp only [roleClauses, List.mem_append]
          exact Or.inl (List.mem_flatMap.mpr
            ⟨SafeClause.subR premise conclusion, hsourceClause, by simp⟩)
        simpa [SafeClause.toOClause, Eqv.satO, restrictHT] using
          subRole_models interpretation source target hsourceTarget premise conclusion
            hroleClause
    | inv role inverse =>
        have hforward : interpretation.modelsClause
            ((NormalizedRoleClause.inverseRole role inverse source target).toClause
              (Concept := Fin conceptCount)) := by
          apply hroles
          apply List.mem_map.mpr
          refine ⟨NormalizedRoleClause.inverseRole role inverse source target, ?_, rfl⟩
          simp only [roleClauses, List.mem_append]
          exact Or.inl (List.mem_flatMap.mpr
            ⟨SafeClause.inv role inverse, hsourceClause, by simp⟩)
        have hbackward : interpretation.modelsClause
            ((NormalizedRoleClause.inverseRole inverse role source target).toClause
              (Concept := Fin conceptCount)) := by
          apply hroles
          apply List.mem_map.mpr
          refine ⟨NormalizedRoleClause.inverseRole inverse role source target, ?_, rfl⟩
          simp only [roleClauses, List.mem_append]
          exact Or.inl (List.mem_flatMap.mpr
            ⟨SafeClause.inv role inverse, hsourceClause, by simp⟩)
        simpa [SafeClause.toOClause, Eqv.satO, restrictHT] using
          inverse_models interpretation source target hsourceTarget role inverse
            hforward hbackward
  · intro chain hchain
    simp only [SafeSource.toSource, List.mem_map] at hchain
    rcases hchain with ⟨binary, hbinary, rfl⟩
    intro values hedges
    have hclause := hroles
      ((NormalizedRoleClause.chain binary.first binary.second binary.conclusion
        source middle target).toClause (Concept := Fin conceptCount)) (by
          apply List.mem_map.mpr
          refine ⟨NormalizedRoleClause.chain binary.first binary.second
            binary.conclusion source middle target, ?_, rfl⟩
          simp only [roleClauses, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨binary, hbinary, rfl⟩))
    let assignment : Fin variableCount → D := fun node =>
      if node = source then values 0
      else if node = middle then values 1
      else values 2
    rcases hclause assignment (by
      intro atom hatom
      simp only [NormalizedRoleClause.toClause, List.mem_cons,
        List.not_mem_nil, or_false] at hatom
      rcases hatom with rfl | rfl
      · simpa [Hypertableau.Interp.satAtom, assignment, hmiddleSource,
          Ne.symm hmiddleSource] using
          hedges ⟨0, by simp [BinaryChain.toRoleChain]⟩
      · simpa [Hypertableau.Interp.satAtom, assignment, hmiddleTarget,
          hsourceTarget, Ne.symm hsourceTarget, Ne.symm hmiddleTarget,
          hmiddleSource, Ne.symm hmiddleSource] using
          hedges ⟨1, by simp [BinaryChain.toRoleChain]⟩) with
      ⟨atom, hatom, hsat⟩
    simp only [NormalizedRoleClause.toClause, List.mem_singleton] at hatom
    subst atom
    simpa [Hypertableau.Interp.satAtom, assignment, hsourceTarget,
      Ne.symm hsourceTarget, hmiddleTarget, Ne.symm hmiddleTarget,
      BinaryChain.toRoleChain, restrictHT] using hsat

/-- A checked equality-free regular certificate over the exact residual and
RBox translations yields a nested-term CB countermodel. -/
theorem checked_regular_role_countermodel
    [NeZero nodeCount]
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (source middle target : Fin variableCount)
    (hsourceTarget : source ≠ target)
    (hmiddleSource : middle ≠ source) (hmiddleTarget : middle ≠ target)
    (safe : SafeSource (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (sub sup : Fin conceptCount)
    (hroleClauses : certificate.roleClauses =
      roleClauses source middle target safe)
    (hresidual : certificate.residual = residual source target safe.clauses)
    (hsub : certificate.state.label 0 (.pos sub))
    (hnotSup : certificate.state.label 0 (.negated sup))
    (hcheck : certificate.check = true) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ CBRoleChainEncoding.encode safe.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  let htModel := certificate.state.regularUnravelling certificate.redirect
    (fun _ _ _ _ => True) 0 certificate.rules
  let element : UnravellingDomain certificate.state certificate.redirect
      (fun _ _ _ _ => True) 0 := ⟨0, .root⟩
  have hmodels := certificate.check_models hcheck
  have hroles : htModel.models
      ((roleClauses source middle target safe).map
        (NormalizedRoleClause.toClause (Concept := Fin conceptCount))) := by
    intro clause hclause
    apply hmodels clause
    simp only [FiniteRegularCertificate.ontology, List.mem_append]
    left
    simpa [hroleClauses] using hclause
  have hresidualModels : htModel.models (residual source target safe.clauses) := by
    intro clause hclause
    apply hmodels clause
    simp only [FiniteRegularCertificate.ontology, List.mem_append]
    right
    simpa [hresidual] using hclause
  let name : Fin individualCount →
      UnravellingDomain certificate.state certificate.redirect
        (fun _ _ _ _ => True) 0 := fun _ => element
  have hsourceModels : CBRoleChainEncoding.models
      (restrictHT htModel name) safe.toSource :=
    models_source_of_models_ht htModel name source middle target
      hsourceTarget hmiddleSource hmiddleTarget safe hresidualModels hroles
  let model := CBRoleChainEncoding.extendModel safe.toSource
    (restrictHT htModel name) hsourceModels element
  refine ⟨_, model, element,
    CBRoleChainEncoding.models_extend safe.toSource
      (restrictHT htModel name) hsourceModels element, ?_, ?_⟩
  · simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      restrictHT, htModel, Hypertableau.Interp.satLit, Lit.pos] using
      certificate.state.regularUnravelling_sat_label certificate.redirect
        (fun _ _ _ _ => True) 0 certificate.rules
        (certificate.check_sound hcheck).2.2.2.1 element (.pos sub) hsub
  · simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      restrictHT, htModel, Hypertableau.Interp.satLit, Lit.negated] using
      certificate.state.regularUnravelling_sat_label certificate.redirect
        (fun _ _ _ _ => True) 0 certificate.rules
        (certificate.check_sound hcheck).2.2.2.1 element (.negated sup) hnotSup

#print axioms models_source_of_models_ht
#print axioms checked_regular_role_countermodel

end ContextCalculus.CBRegularRoleCountermodel
