import ContextCalculus.ELCheckerTermEmbedding
import Mathlib.Data.List.Enum

/-!
# ELC normal forms in the common proper-term source

NF1–NF7 and reflexive-role clauses are encoded directly. NF3 uses a function
symbol tagged separately from every residual frontend function, so the two
complete source families can share one model without aliasing witnesses.
-/

namespace ContextCalculus.ELNormalCheckerTermEmbedding

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.ELCompletion
open ContextCalculus.ELCheckerTermEmbedding

private def x : FTerm := .var 0
private def y : FTerm := .var 1
private def z : FTerm := .var 2

private def concept (name : Nat) (term : FTerm) : FLit :=
  .P (.concept name term)

private def role (name : Nat) (source target : FTerm) : FLit :=
  .P (.role name source target)

def encodeNormalClause (slot : Nat) : ELCompletion.Clause Nat Nat → List FCL
  | .nf1 sub sup => [⟨[concept sub x], [concept sup x]⟩]
  | .nf2 left right sup =>
      [⟨[concept left x, concept right x], [concept sup x]⟩]
  | .nf3 sub roleName filler =>
      let witness := FTerm.app (normalFunctionCode slot) x
      [⟨[concept sub x], [role roleName x witness]⟩,
       ⟨[concept sub x], [concept filler witness]⟩]
  | .nf4 roleName filler sup =>
      [⟨[role roleName x y, concept filler y], [concept sup x]⟩]
  | .nf5 sub => [⟨[concept sub x], []⟩]
  | .nf6 sub sup => [⟨[role sub x y], [role sup x y]⟩]
  | .nf7 first second sup =>
      [⟨[role first x y, role second y z], [role sup x z]⟩]
  | .reflexive roleName => [⟨[], [role roleName x x]⟩]

def FixedNormalClauseModels (model : TModel Domain) (slot : Nat) :
    ELCompletion.Clause Nat Nat → Prop
  | .nf1 sub sup => ∀ value, model.conc sub value → model.conc sup value
  | .nf2 left right sup => ∀ value,
      model.conc left value → model.conc right value → model.conc sup value
  | .nf3 sub roleName filler => ∀ value, model.conc sub value →
      model.rol roleName value (model.fn (normalFunctionCode slot) value) ∧
      model.conc filler (model.fn (normalFunctionCode slot) value)
  | .nf4 roleName filler sup => ∀ source,
      (∃ target, model.rol roleName source target ∧ model.conc filler target) →
        model.conc sup source
  | .nf5 sub => ∀ value, model.conc sub value → False
  | .nf6 sub sup => ∀ source target,
      model.rol sub source target → model.rol sup source target
  | .nf7 first second sup => ∀ source middle target,
      model.rol first source middle → model.rol second middle target →
        model.rol sup source target
  | .reflexive roleName => ∀ value, model.rol roleName value value

theorem models_encodeNormalClause_iff (model : TModel Domain) (slot : Nat)
    (clause : ELCompletion.Clause Nat Nat) :
    (∀ encoded ∈ encodeNormalClause slot clause, valid model encoded) ↔
      FixedNormalClauseModels model slot clause := by
  cases clause <;>
    simp [encodeNormalClause, FixedNormalClauseModels, valid, sat,
      concept, role, x, y, z, TModel.evalL, TModel.evalT] <;>
    constructor
  · intro h value hsub
    exact h (fun _ => value) hsub
  · intro h ρ
    exact h (ρ 0)
  · intro h value hleft hright
    exact h (fun _ => value) hleft hright
  · intro h ρ
    exact h (ρ 0)
  · rintro ⟨hrole, hfiller⟩ value hsub
    exact ⟨hrole (fun _ => value) hsub, hfiller (fun _ => value) hsub⟩
  · intro h
    constructor <;> intro ρ hsub
    · exact (h (ρ 0) hsub).1
    · exact (h (ρ 0) hsub).2
  · intro h source target hrole hfiller
    simpa using h (fun index => if index = 0 then source else target) hrole hfiller
  · intro h ρ
    exact h (ρ 0) (ρ 1)
  · intro h value hsub
    exact h (fun _ => value) hsub
  · intro h ρ
    exact h (ρ 0)
  · intro h source target hrole
    simpa using h (fun index => if index = 0 then source else target) hrole
  · intro h ρ
    exact h (ρ 0) (ρ 1)
  · intro h source middle target hfirst hsecond
    let ρ : Int → Domain := fun index =>
      if index = 0 then source else if index = 1 then middle else target
    simpa [ρ] using h ρ hfirst hsecond
  · intro h ρ
    exact h (ρ 0) (ρ 1) (ρ 2)
  · intro h value
    exact h (fun _ => value)
  · intro h ρ
    exact h (ρ 0)

def encodeNormalEntry
    (entry : ELCompletion.Clause Nat Nat × Nat) : List FCL :=
  encodeNormalClause entry.2 entry.1

def encodeNormalOntology
    (ontology : ELCompletion.Ontology Nat Nat) : List FCL :=
  ontology.zipIdx.flatMap encodeNormalEntry

theorem models_encodeNormalOntology_fixed_iff (model : TModel Domain)
    (ontology : ELCompletion.Ontology Nat Nat) :
    (∀ encoded ∈ encodeNormalOntology ontology, valid model encoded) ↔
      ∀ entry ∈ ontology.zipIdx,
        FixedNormalClauseModels model entry.2 entry.1 := by
  constructor
  · intro hmodels entry hentry
    apply (models_encodeNormalClause_iff model entry.2 entry.1).1
    intro encoded hencoded
    exact hmodels encoded (by
      simp only [encodeNormalOntology, List.mem_flatMap]
      exact ⟨entry, hentry, hencoded⟩)
  · intro hfixed encoded hencoded
    simp only [encodeNormalOntology, List.mem_flatMap] at hencoded
    rcases hencoded with ⟨entry, hentry, hencoded⟩
    exact (models_encodeNormalClause_iff model entry.2 entry.1).2
      (hfixed entry hentry) encoded hencoded

def interpOfModel (model : TModel Domain) (top bottom : Nat)
    (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value) :
    ELCompletion.Interp Domain Nat Nat top bottom :=
  ELCheckerTermEmbedding.elInterp model top bottom topTrue bottomFalse

theorem models_encodeNormalOntology_implies_models
    (model : TModel Domain) (ontology : ELCompletion.Ontology Nat Nat)
    (top bottom : Nat) (topTrue : ∀ value, model.conc top value)
    (bottomFalse : ∀ value, ¬ model.conc bottom value)
    (hmodels : ∀ encoded ∈ encodeNormalOntology ontology,
      valid model encoded) :
    ELCompletion.models
      (interpOfModel model top bottom topTrue bottomFalse) ontology := by
  intro clause hclause
  rw [List.mem_iff_getElem] at hclause
  rcases hclause with ⟨slot, hslot, rfl⟩
  have hentry : (ontology[slot], slot) ∈ ontology.zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨slot, by simpa using hslot, by simp⟩
  have hfixed : FixedNormalClauseModels model slot ontology[slot] := by
    simpa using
      (models_encodeNormalOntology_fixed_iff model ontology).1 hmodels
        (ontology[slot], slot) hentry
  cases hkind : ontology[slot] with
  | nf1 sub sup =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed
  | nf2 left right sup =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed
  | nf3 sub roleName filler =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      intro value hsub
      exact ⟨model.fn (normalFunctionCode slot) value, hfixed value hsub⟩
  | nf4 roleName filler sup =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed
  | nf5 sub =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed
  | nf6 sub sup =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed
  | nf7 first second sup =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed
  | reflexive roleName =>
      simp only [hkind, FixedNormalClauseModels] at hfixed
      exact hfixed

noncomputable def witnessForClause
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (clause : ELCompletion.Clause Nat Nat)
    (hsat : ELCompletion.satClause I clause) (fallback : Domain)
    (source : Domain) : Domain := by
  classical
  cases clause with
  | nf3 sub roleName filler =>
      if hsub : I.concept sub source then
        exact Classical.choose (hsat source hsub)
      else exact fallback
  | _ => exact fallback

theorem witnessForClause_spec
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (clause : ELCompletion.Clause Nat Nat)
    (hsat : ELCompletion.satClause I clause) (fallback : Domain)
    (sub roleName filler : Nat)
    (hclause : clause = .nf3 sub roleName filler)
    (source : Domain) (hsub : I.concept sub source) :
    I.role roleName source (witnessForClause I clause hsat fallback source) ∧
      I.concept filler (witnessForClause I clause hsat fallback source) := by
  subst clause
  simpa [witnessForClause, hsub] using
    (Classical.choose_spec (hsat source hsub))

noncomputable def normalWitness
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology) (fallback : Domain)
    (slot : Nat) (source : Domain) : Domain := by
  if hslot : slot < ontology.length then
    exact witnessForClause I ontology[slot]
      (hmodels ontology[slot] (List.getElem_mem hslot)) fallback source
  else exact fallback

theorem normalWitness_spec
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology) (fallback : Domain)
    (slot : Nat) (hslot : slot < ontology.length)
    (sub roleName filler : Nat)
    (hclause : ontology[slot] = .nf3 sub roleName filler)
    (source : Domain) (hsub : I.concept sub source) :
    I.role roleName source
        (normalWitness I ontology hmodels fallback slot source) ∧
      I.concept filler
        (normalWitness I ontology hmodels fallback slot source) := by
  simp only [normalWitness, dif_pos hslot]
  exact witnessForClause_spec I ontology[slot]
    (hmodels ontology[slot] (List.getElem_mem hslot)) fallback
    sub roleName filler hclause source hsub

noncomputable def modelOfNormalAndRaw
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology)
    (terms : RawTermInterp Domain) (fallback : Domain) : TModel Domain where
  conc := I.concept
  rol := I.role
  const := decodedConstant terms fallback
  fn code :=
    if (Nat.unpair code).1 = 0 then
      terms.function (Nat.unpair code).2
    else if (Nat.unpair code).1 = 1 then
      normalWitness I ontology hmodels fallback (Nat.unpair code).2
    else fun _ => fallback

@[simp] theorem modelOfNormalAndRaw_residualFunction
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology)
    (terms : RawTermInterp Domain) (fallback : Domain) (function : Nat) :
    (modelOfNormalAndRaw I ontology hmodels terms fallback).fn
        (residualFunctionCode function) = terms.function function := by
  simp [modelOfNormalAndRaw, residualFunctionCode]

@[simp] theorem modelOfNormalAndRaw_normalFunction
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology)
    (terms : RawTermInterp Domain) (fallback : Domain) (slot : Nat) :
    (modelOfNormalAndRaw I ontology hmodels terms fallback).fn
        (normalFunctionCode slot) =
      normalWitness I ontology hmodels fallback slot := by
  simp [modelOfNormalAndRaw, normalFunctionCode]

@[simp] theorem rawTermInterp_modelOfNormalAndRaw
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology)
    (terms : RawTermInterp Domain) (fallback : Domain) :
    rawTermInterp (modelOfNormalAndRaw I ontology hmodels terms fallback) =
      terms := by
  rcases terms with ⟨individuals, auxiliaries, functions⟩
  simp [rawTermInterp, modelOfNormalAndRaw, residualFunctionCode]

theorem models_encodeNormalOntology_modelOfNormalAndRaw
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (ontology : ELCompletion.Ontology Nat Nat)
    (hmodels : ELCompletion.models I ontology)
    (terms : RawTermInterp Domain) (fallback : Domain) :
    ∀ encoded ∈ encodeNormalOntology ontology,
      valid (modelOfNormalAndRaw I ontology hmodels terms fallback) encoded := by
  apply (models_encodeNormalOntology_fixed_iff
    (modelOfNormalAndRaw I ontology hmodels terms fallback) ontology).2
  rw [List.forall_mem_zipIdx']
  intro slot hslotOntology
  cases hclause : ontology[slot] with
  | nf1 sub sup =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs
  | nf2 left right sup =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs
  | nf3 sub roleName filler =>
      simp only [FixedNormalClauseModels]
      intro source hsub
      simpa [modelOfNormalAndRaw, normalFunctionCode] using
        normalWitness_spec I ontology hmodels fallback slot hslotOntology
          sub roleName filler hclause source hsub
  | nf4 roleName filler sup =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs
  | nf5 sub =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs
  | nf6 sub sup =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs
  | nf7 first second sup =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs
  | reflexive roleName =>
      have hs := hmodels ontology[slot] (List.getElem_mem hslotOntology)
      rw [hclause] at hs
      exact hs

def encodeCombinedSource (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (RawResidualClause Nat Nat)) : List FCL :=
  encodeNormalOntology ontology ++ residual.map encodeResidualClause

theorem models_encodeCombinedSource_iff (model : TModel Domain)
    (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (RawResidualClause Nat Nat)) :
    (∀ clause ∈ encodeCombinedSource ontology residual, valid model clause) ↔
      (∀ clause ∈ encodeNormalOntology ontology, valid model clause) ∧
        ∀ clause ∈ residual, valid model (encodeResidualClause clause) := by
  constructor
  · intro hmodels
    constructor
    · intro clause hclause
      exact hmodels clause (by
        simp only [encodeCombinedSource, List.mem_append]
        exact Or.inl hclause)
    · intro clause hclause
      exact hmodels (encodeResidualClause clause) (by
        simp only [encodeCombinedSource, List.mem_append, List.mem_map]
        exact Or.inr ⟨clause, hclause, rfl⟩)
  · rintro ⟨hnormal, hresidual⟩ clause hclause
    simp only [encodeCombinedSource, List.mem_append] at hclause
    rcases hclause with hnormalClause | hresidualClause
    · exact hnormal clause hnormalClause
    · rcases List.mem_map.mp hresidualClause with ⟨source, hsource, rfl⟩
      exact hresidual source hsource

def CommonCombinedEntails (top bottom : Nat)
    (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (RawResidualClause Nat Nat))
    (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ value, model.conc top value) →
    (∀ value, ¬model.conc bottom value) →
    (∀ clause ∈ encodeCombinedSource ontology residual,
      valid model clause) →
    ∀ value, model.conc sub value → model.conc sup value

def ELCSourceEntails (top bottom : Nat)
    (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (RawResidualClause Nat Nat))
    (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (terms : RawTermInterp Domain),
    ELCompletion.models I ontology →
    modelsRawResidual I terms residual →
    ∀ value, I.concept sub value → I.concept sup value

theorem commonCombinedEntails_iff_elcSource (top bottom : Nat)
    (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (RawResidualClause Nat Nat))
    (sub sup : Nat) :
    CommonCombinedEntails top bottom ontology residual sub sup ↔
      ELCSourceEntails top bottom ontology residual sub sup := by
  constructor
  · intro hcommon Domain I terms hnormal hresidual value hsub
    let model := modelOfNormalAndRaw I ontology hnormal terms value
    have hnormalEncoded : ∀ clause ∈ encodeNormalOntology ontology,
        valid model clause := by
      simpa [model] using
        models_encodeNormalOntology_modelOfNormalAndRaw
          I ontology hnormal terms value
    have hresidualEncoded : ∀ clause ∈ residual,
        valid model (encodeResidualClause clause) := by
      apply (models_encodeResidual_iff model top bottom I.top_true
        I.bottom_false residual).2
      simpa [model] using hresidual
    have hcombined : ∀ clause ∈ encodeCombinedSource ontology residual,
        valid model clause :=
      (models_encodeCombinedSource_iff model ontology residual).2
        ⟨hnormalEncoded, hresidualEncoded⟩
    exact hcommon Domain model
      (by simpa [model, modelOfNormalAndRaw] using I.top_true)
      (by simpa [model, modelOfNormalAndRaw] using I.bottom_false)
      hcombined value (by simpa [model, modelOfNormalAndRaw] using hsub)
  · intro hsource Domain model htop hbottom hcombined value hsub
    have hparts :=
      (models_encodeCombinedSource_iff model ontology residual).1 hcombined
    let I := interpOfModel model top bottom htop hbottom
    have hnormal : ELCompletion.models I ontology := by
      exact models_encodeNormalOntology_implies_models model ontology top bottom
        htop hbottom hparts.1
    have hresidual : modelsRawResidual I (rawTermInterp model) residual := by
      exact (models_encodeResidual_iff model top bottom htop hbottom residual).1
        hparts.2
    exact hsource Domain I (rawTermInterp model) hnormal hresidual value hsub

#print axioms models_encodeNormalClause_iff
#print axioms models_encodeNormalOntology_fixed_iff
#print axioms models_encodeNormalOntology_implies_models
#print axioms models_encodeNormalOntology_modelOfNormalAndRaw
#print axioms models_encodeCombinedSource_iff
#print axioms commonCombinedEntails_iff_elcSource

end ContextCalculus.ELNormalCheckerTermEmbedding
