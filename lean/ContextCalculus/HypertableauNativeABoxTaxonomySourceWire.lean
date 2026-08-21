import ContextCalculus.HypertableauNativeABoxTaxonomyMatrixWire
import ContextCalculus.HypertableauNativeABoxSourceDecisionWire

/-!
# Source-composed native-ABox taxonomy decisions

The direct source wrapper binds one taxonomy query to the exact source clauses
whose projection, together with checked negative-role guards, is the ontology
inside the finite model or refutation.  Query semantics are therefore proved
for the source problem rather than only for the normalized target.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireDirectNativeABoxTaxonomyDecision where
  version : Nat
  source : List WireDirectSourceClause
  decision : WireNativeABoxTaxonomyDecision
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxTaxonomySat where
  taxonomy : DecodedNativeABoxTaxonomySat
  variable_ge_two : 2 ≤ taxonomy.certificate.seed.variableCount
  source : List (Clause (Fin taxonomy.certificate.seed.variableCount)
    (Fin taxonomy.certificate.seed.abox.concepts.length)
    (Fin taxonomy.certificate.seed.abox.roles.length))
  exact_projection : source ++
      taxonomy.certificate.seed.abox.negativeRoleClausesAt
        taxonomy.certificate.seed.variableCount variable_ge_two =
      taxonomy.certificate.seed.state.base.base.ontology

structure DecodedDirectNativeABoxTaxonomyUnsat where
  taxonomy : DecodedNativeABoxTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  source : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length))
  exact_projection : source ++ taxonomy.initial.abox.negativeRoleClausesAt
      taxonomy.initial.variableCount variable_ge_two =
    taxonomy.initial.state.base.base.ontology

inductive DecodedDirectNativeABoxTaxonomyDecision where
  | sat (decoded : DecodedDirectNativeABoxTaxonomySat)
  | unsat (decoded : DecodedDirectNativeABoxTaxonomyUnsat)

def WireDirectNativeABoxTaxonomyDecision.decode
    (wire : WireDirectNativeABoxTaxonomyDecision) :
    Except String DecodedDirectNativeABoxTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox taxonomy source version {wire.version}"
  match ← wire.decision.decode with
  | .sat taxonomy =>
      let variableWitness ← requireAtLeastTwoVariables
        taxonomy.certificate.seed.variableCount
      let hvariables := variableWitness.proof
      let source ← wire.source.mapM (WireDirectSourceClause.decode
        taxonomy.certificate.seed.variableCount
        taxonomy.certificate.seed.abox.concepts
        taxonomy.certificate.seed.abox.roles)
      if hequal : source ++ taxonomy.certificate.seed.abox.negativeRoleClausesAt
          taxonomy.certificate.seed.variableCount hvariables =
          taxonomy.certificate.seed.state.base.base.ontology then
        return .sat {
          taxonomy
          variable_ge_two := hvariables
          source
          exact_projection := hequal
        }
      else throw "direct source conversion differs from the native ABox taxonomy model"
  | .unsat taxonomy =>
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      let source ← wire.source.mapM (WireDirectSourceClause.decode
        taxonomy.initial.variableCount taxonomy.initial.abox.concepts
        taxonomy.initial.abox.roles)
      if hequal : source ++ taxonomy.initial.abox.negativeRoleClausesAt
          taxonomy.initial.variableCount hvariables =
          taxonomy.initial.state.base.base.ontology then
        return .unsat {
          taxonomy
          variable_ge_two := hvariables
          source
          exact_projection := hequal
        }
      else throw "direct source conversion differs from the native ABox taxonomy refutation"

def WireDirectNativeABoxTaxonomyDecision.check
    (wire : WireDirectNativeABoxTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectNativeABoxTaxonomySat.source_satisfiable
    (decoded : DecodedDirectNativeABoxTaxonomySat) :
    decoded.taxonomy.certificate.seed.abox.abox.SatisfiableWithQuery
      decoded.source decoded.taxonomy.query.literals := by
  rcases decoded.taxonomy.certificate.satisfiable_with_query
      decoded.taxonomy.query.root decoded.taxonomy.query.literals
      decoded.taxonomy.query_present with
    ⟨Domain, I, value, element, hdomain, htarget, habox, hquery⟩
  have happended : I.models (decoded.source ++
      decoded.taxonomy.certificate.seed.abox.negativeRoleClausesAt
        decoded.taxonomy.certificate.seed.variableCount decoded.variable_ge_two) := by
    simpa only [decoded.exact_projection] using htarget
  have hsource : I.models decoded.source := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  exact ⟨Domain, I, value, element, hdomain, hsource, habox, hquery⟩

theorem DecodedDirectNativeABoxTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedDirectNativeABoxTaxonomyUnsat) :
    ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithQuery
      decoded.source decoded.taxonomy.query.literals := by
  rintro ⟨Domain, I, value, element, hdomain, hsource, habox, hquery⟩
  apply decoded.taxonomy.unsatisfiable
  refine ⟨Domain, I, value, element, hdomain, ?_, habox, hquery⟩
  rw [← decoded.exact_projection]
  exact (decoded.taxonomy.initial.abox.models_append_negativeRoleClausesAt_iff
    I value habox.1 decoded.variable_ge_two decoded.source).2
      ⟨hsource, habox.2.2.2.2⟩

def DecodedDirectNativeABoxTaxonomyDecision.SemanticallyValid :
    DecodedDirectNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      decoded.taxonomy.certificate.seed.abox.abox.SatisfiableWithQuery
        decoded.source decoded.taxonomy.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithQuery
        decoded.source decoded.taxonomy.query.literals

theorem DecodedDirectNativeABoxTaxonomyDecision.semantic_valid
    (decoded : DecodedDirectNativeABoxTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

/-! ## Complete direct-source matrix -/

structure WireDirectNativeABoxTaxonomyMatrix where
  version : Nat
  source : List WireDirectSourceClause
  matrix : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxTaxonomyMatrix where
  matrix : DecodedNativeABoxTaxonomyMatrix
  concepts : List DecodedDirectNativeABoxTaxonomyDecision
  subsumptions : List (List DecodedDirectNativeABoxTaxonomyDecision)

def WireDirectNativeABoxTaxonomyMatrix.decode
    (wire : WireDirectNativeABoxTaxonomyMatrix) :
    Except String DecodedDirectNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    source := wire.source
    decision
  } : WireDirectNativeABoxTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireDirectNativeABoxTaxonomyMatrix.check
    (wire : WireDirectNativeABoxTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectNativeABoxTaxonomyMatrix.allDecisions
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    List DecodedDirectNativeABoxTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedDirectNativeABoxTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧
  decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedDirectNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

/-! ## Mixed direct/Skolem-pair source projection -/

def NativeABox.SatisfiableWithMixedQuery
    (abox : NativeABox Individual Concept Role)
    (direct : List (Clause Variable Concept Role))
    (pairs : List (SkolemPairSpec Variable Concept Role Function))
    (query : List (Lit Concept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain) (element : Domain),
    Nonempty Domain ∧ abox.models I value ∧ I.RealizesLiterals query element ∧
      ∃ functions : SkolemInterp Domain Function,
        I.models direct ∧ ModelsSkolemPairs I functions pairs

structure WireMixedNativeABoxTaxonomyDecision where
  version : Nat
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  decision : WireNativeABoxTaxonomyDecision
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxTaxonomySat where
  projection : DecodedMixedNativeABoxSatCertificate
  query : DecodedNativeABoxTaxonomyQuery projection.certificate.seed.nodeCount
    projection.certificate.seed.abox.concepts.length
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈ projection.certificate.seed.state.base.base.labels

structure DecodedMixedNativeABoxTaxonomyUnsat where
  taxonomy : DecodedNativeABoxTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  functions : List String
  direct : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length))
  pairs : List (SkolemPairSpec (Fin taxonomy.initial.variableCount)
    (Fin taxonomy.initial.abox.concepts.length)
    (Fin taxonomy.initial.abox.roles.length) (Fin functions.length))
  unique_functions : (skolemPairFunctions pairs).Nodup
  exact_projection :
    (skolemProjectionOntology direct pairs ++
      taxonomy.initial.abox.negativeRoleClausesAt taxonomy.initial.variableCount
        variable_ge_two).toFinset =
      taxonomy.initial.state.base.base.ontology.toFinset

inductive DecodedMixedNativeABoxTaxonomyDecision where
  | sat (decoded : DecodedMixedNativeABoxTaxonomySat)
  | unsat (decoded : DecodedMixedNativeABoxTaxonomyUnsat)

def WireMixedNativeABoxTaxonomyDecision.decode
    (wire : WireMixedNativeABoxTaxonomyDecision) :
    Except String DecodedMixedNativeABoxTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox taxonomy source version {wire.version}"
  match wire.decision.evidence with
  | .sat certificateWire =>
      let projection ← ({
        functions := wire.functions
        direct := wire.direct
        pairs := wire.pairs
        certificate := certificateWire
      } : WireMixedNativeABoxSatCertificate).decode
      let query ← wire.decision.query.decode projection.certificate.seed.nodeCount
        projection.certificate.seed.abox.concepts.length
      if hquery : query.labelsPresentB
          projection.certificate.seed.state.base.base.labels = true then
        return .sat {
          projection
          query
          query_present := query.labelsPresentB_sound _ hquery
        }
      else throw "mixed source taxonomy countermodel omits its query literals"
  | .unsat _ _ =>
      let taxonomyDecision ← wire.decision.decode
      let taxonomy ← match taxonomyDecision with
        | .unsat result => pure result
        | .sat _ => throw "internal mixed taxonomy evidence mismatch"
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      if _hfunctions : wire.functions.Nodup then
        let direct ← wire.direct.mapM (WireDirectSourceClause.decode
          taxonomy.initial.variableCount taxonomy.initial.abox.concepts
          taxonomy.initial.abox.roles)
        let pairs ← wire.pairs.mapM (WireSkolemPair.decode
          taxonomy.initial.variableCount taxonomy.initial.abox.concepts
          taxonomy.initial.abox.roles wire.functions)
        if hunique : (skolemPairFunctions pairs).Nodup then
          if hequal : (skolemProjectionOntology direct pairs ++
              taxonomy.initial.abox.negativeRoleClausesAt
                taxonomy.initial.variableCount hvariables).toFinset =
              taxonomy.initial.state.base.base.ontology.toFinset then
            return .unsat {
              taxonomy
              variable_ge_two := hvariables
              functions := wire.functions
              direct
              pairs
              unique_functions := hunique
              exact_projection := hequal
            }
          else throw "mixed source conversion differs from the native ABox taxonomy refutation"
        else throw "mixed native ABox taxonomy projection reuses a Skolem function"
      else throw "mixed native ABox taxonomy function-name table contains duplicates"

def WireMixedNativeABoxTaxonomyDecision.check
    (wire : WireMixedNativeABoxTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedMixedNativeABoxTaxonomySat.source_satisfiable
    (decoded : DecodedMixedNativeABoxTaxonomySat) :
    decoded.projection.certificate.seed.abox.abox.SatisfiableWithMixedQuery
      decoded.projection.direct decoded.projection.pairs decoded.query.literals := by
  rcases decoded.projection.certificate.satisfiable_with_query decoded.query.root
      decoded.query.literals decoded.query_present with
    ⟨Domain, I, value, element, hdomain, htarget, habox, hquery⟩
  have happended : I.models
      (skolemProjectionOntology decoded.projection.direct decoded.projection.pairs ++
        decoded.projection.certificate.seed.abox.negativeRoleClausesAt
          decoded.projection.certificate.seed.variableCount
          decoded.projection.variable_ge_two) :=
    (models_iff_of_toFinset_eq I _ _ decoded.projection.exact_projection).2 htarget
  have hprojected : I.models
      (skolemProjectionOntology decoded.projection.direct decoded.projection.pairs) := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  let fallback : Domain := Classical.choice hdomain
  let base : SkolemInterp Domain (Fin decoded.projection.functions.length) :=
    { app := fun _ _ => fallback }
  rcases (mixedSkolemProjection_sat_iff I base decoded.projection.direct
      decoded.projection.pairs decoded.projection.unique_functions).2 hprojected with
    ⟨functions, hdirect, hpairs⟩
  exact ⟨Domain, I, value, element, hdomain, habox, hquery,
    functions, hdirect, hpairs⟩

theorem DecodedMixedNativeABoxTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedMixedNativeABoxTaxonomyUnsat) :
    ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithMixedQuery
      decoded.direct decoded.pairs decoded.taxonomy.query.literals := by
  rintro ⟨Domain, I, value, element, hdomain, habox, hquery,
    functions, hdirect, hpairs⟩
  letI : Nonempty Domain := hdomain
  let base : SkolemInterp Domain (Fin decoded.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  have hprojected : I.models (skolemProjectionOntology decoded.direct decoded.pairs) :=
    (mixedSkolemProjection_sat_iff I base decoded.direct decoded.pairs
      decoded.unique_functions).1 ⟨functions, hdirect, hpairs⟩
  have happended : I.models (skolemProjectionOntology decoded.direct decoded.pairs ++
      decoded.taxonomy.initial.abox.negativeRoleClausesAt
        decoded.taxonomy.initial.variableCount decoded.variable_ge_two) :=
    (decoded.taxonomy.initial.abox.models_append_negativeRoleClausesAt_iff
      I value habox.1 decoded.variable_ge_two
      (skolemProjectionOntology decoded.direct decoded.pairs)).2
        ⟨hprojected, habox.2.2.2.2⟩
  have htarget : I.models decoded.taxonomy.initial.state.base.base.ontology :=
    (models_iff_of_toFinset_eq I _ _ decoded.exact_projection).1 happended
  exact decoded.taxonomy.unsatisfiable
    ⟨Domain, I, value, element, hdomain, htarget, habox, hquery⟩

def DecodedMixedNativeABoxTaxonomyDecision.SemanticallyValid :
    DecodedMixedNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      decoded.projection.certificate.seed.abox.abox.SatisfiableWithMixedQuery
        decoded.projection.direct decoded.projection.pairs decoded.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithMixedQuery
        decoded.direct decoded.pairs decoded.taxonomy.query.literals

theorem DecodedMixedNativeABoxTaxonomyDecision.semantic_valid
    (decoded : DecodedMixedNativeABoxTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

structure WireMixedNativeABoxTaxonomyMatrix where
  version : Nat
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  matrix : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxTaxonomyMatrix where
  matrix : DecodedNativeABoxTaxonomyMatrix
  concepts : List DecodedMixedNativeABoxTaxonomyDecision
  subsumptions : List (List DecodedMixedNativeABoxTaxonomyDecision)

def WireMixedNativeABoxTaxonomyMatrix.decode
    (wire : WireMixedNativeABoxTaxonomyMatrix) :
    Except String DecodedMixedNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    functions := wire.functions
    direct := wire.direct
    pairs := wire.pairs
    decision
  } : WireMixedNativeABoxTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireMixedNativeABoxTaxonomyMatrix.check
    (wire : WireMixedNativeABoxTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedNativeABoxTaxonomyMatrix.allDecisions
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    List DecodedMixedNativeABoxTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedMixedNativeABoxTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧ decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedMixedNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

#print axioms DecodedDirectNativeABoxTaxonomySat.source_satisfiable
#print axioms DecodedDirectNativeABoxTaxonomyUnsat.source_unsatisfiable
#print axioms DecodedDirectNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedDirectNativeABoxTaxonomyMatrix.semantic_valid
#print axioms DecodedMixedNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedMixedNativeABoxTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
