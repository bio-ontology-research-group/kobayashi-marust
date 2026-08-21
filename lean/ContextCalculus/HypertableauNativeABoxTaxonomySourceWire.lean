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

def DecodedDirectNativeABoxTaxonomyDecision.wireQuery :
    DecodedDirectNativeABoxTaxonomyDecision → WireNativeABoxTaxonomyQuery
  | .sat decoded => decoded.taxonomy.wireQuery
  | .unsat decoded => decoded.taxonomy.wireQuery

def DecodedDirectNativeABoxTaxonomyDecision.CoordinatesExact
    (expected : WireNativeABoxTaxonomyQuery) :
    DecodedDirectNativeABoxTaxonomyDecision → Prop
  | .sat decoded => DecodedNativeABoxTaxonomyQuery.MatchesWire
      decoded.taxonomy.query expected
  | .unsat decoded => DecodedNativeABoxTaxonomyQuery.MatchesWire
      decoded.taxonomy.query expected

theorem DecodedDirectNativeABoxTaxonomyDecision.coordinates_exact
    (decoded : DecodedDirectNativeABoxTaxonomyDecision)
    {expected : WireNativeABoxTaxonomyQuery}
    (haligned : decoded.wireQuery = expected) :
    decoded.CoordinatesExact expected := by
  cases decoded with
  | sat result => exact haligned ▸ result.taxonomy.exactCoordinates
  | unsat result => exact haligned ▸ result.taxonomy.exactCoordinates

def WireDirectNativeABoxTaxonomyDecision.decodeExact
    (wire : WireDirectNativeABoxTaxonomyDecision) :
    Except String { decoded : DecodedDirectNativeABoxTaxonomyDecision //
      decoded.wireQuery = wire.decision.query } := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox taxonomy source version {wire.version}"
  let exactTaxonomy ← wire.decision.decodeExact
  match htaxonomy : exactTaxonomy.val with
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
        return ⟨.sat {
          taxonomy
          variable_ge_two := hvariables
          source
          exact_projection := hequal
        }, by simpa [DecodedDirectNativeABoxTaxonomyDecision.wireQuery,
          htaxonomy] using exactTaxonomy.property⟩
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
        return ⟨.unsat {
          taxonomy
          variable_ge_two := hvariables
          source
          exact_projection := hequal
        }, by simpa [DecodedDirectNativeABoxTaxonomyDecision.wireQuery,
          htaxonomy] using exactTaxonomy.property⟩
      else throw "direct source conversion differs from the native ABox taxonomy refutation"

def WireDirectNativeABoxTaxonomyDecision.decode
    (wire : WireDirectNativeABoxTaxonomyDecision) :
    Except String DecodedDirectNativeABoxTaxonomyDecision := do
  return (← wire.decodeExact).val

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

def DecodedDirectNativeABoxTaxonomyDecision.positive :
    DecodedDirectNativeABoxTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedDirectNativeABoxTaxonomyDecision.QueryEntailed :
    DecodedDirectNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      ¬decoded.taxonomy.certificate.seed.abox.abox.SatisfiableWithQuery
        decoded.source decoded.taxonomy.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithQuery
        decoded.source decoded.taxonomy.query.literals

theorem DecodedDirectNativeABoxTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedDirectNativeABoxTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := decoded.source_satisfiable
      change (false = true ↔
        ¬decoded.taxonomy.certificate.seed.abox.abox.SatisfiableWithQuery
          decoded.source decoded.taxonomy.query.literals)
      constructor
      · intro hfalse; contradiction
      · intro hnot; exact False.elim (hnot hsemantic)
  | unsat decoded =>
      have hsemantic := decoded.source_unsatisfiable
      change (true = true ↔
        ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithQuery
          decoded.source decoded.taxonomy.query.literals)
      exact ⟨fun _ => hsemantic, fun _ => rfl⟩

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
  concepts_exact : List.Forall₂
    (fun concept decoded => decoded.wireQuery = .concept 0 concept)
    matrix.named concepts
  subsumptions_exact : List.Forall₂
    (fun sub row => List.Forall₂
      (fun sup decoded => decoded.wireQuery = .subsumption 0 sub sup)
      matrix.named row)
    matrix.named subsumptions

private def decodeDirectNativeTaxonomyDecisionAt
    (source : List WireDirectSourceClause)
    (expected : WireNativeABoxTaxonomyQuery)
    (wire : WireNativeABoxTaxonomyDecision) :
    Except String { decoded : DecodedDirectNativeABoxTaxonomyDecision //
      decoded.wireQuery = expected } := do
  if hquery : wire.query = expected then
    let decoded ← ({ version := 1, source, decision := wire } :
      WireDirectNativeABoxTaxonomyDecision).decodeExact
    return ⟨decoded.val, decoded.property.trans hquery⟩
  else throw "direct native ABox taxonomy cell is in the wrong matrix position"

private def decodeDirectNativeTaxonomyConceptsExact
    (source : List WireDirectSourceClause) :
    (named : List Nat) → (wires : List WireNativeABoxTaxonomyDecision) →
    Except String { decoded : List DecodedDirectNativeABoxTaxonomyDecision //
      List.Forall₂
        (fun concept decision => decision.wireQuery = .concept 0 concept)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | concept :: named, wire :: wires => do
      let decision ← decodeDirectNativeTaxonomyDecisionAt source
        (.concept 0 concept) wire
      let tail ← decodeDirectNativeTaxonomyConceptsExact source named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "direct native ABox taxonomy concept row is incomplete"

private def decodeDirectNativeTaxonomySubsumptionRowExact
    (source : List WireDirectSourceClause) (sub : Nat) :
    (named : List Nat) → (wires : List WireNativeABoxTaxonomyDecision) →
    Except String { decoded : List DecodedDirectNativeABoxTaxonomyDecision //
      List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sup :: named, wire :: wires => do
      let decision ← decodeDirectNativeTaxonomyDecisionAt source
        (.subsumption 0 sub sup) wire
      let tail ← decodeDirectNativeTaxonomySubsumptionRowExact source sub named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "direct native ABox taxonomy subsumption row is incomplete"

private def decodeDirectNativeTaxonomyRowsExact
    (source : List WireDirectSourceClause) (allNamed : List Nat) :
    (named : List Nat) → (rows : List (List WireNativeABoxTaxonomyDecision)) →
    Except String { decoded : List (List DecodedDirectNativeABoxTaxonomyDecision) //
      List.Forall₂
        (fun sub row => List.Forall₂
          (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
          allNamed row)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sub :: named, row :: rows => do
      let decodedRow ← decodeDirectNativeTaxonomySubsumptionRowExact
        source sub allNamed row
      let decodedRows ← decodeDirectNativeTaxonomyRowsExact source allNamed named rows
      return ⟨decodedRow.val :: decodedRows.val,
        .cons decodedRow.property decodedRows.property⟩
  | _, _ => .error "direct native ABox taxonomy subsumption matrix is incomplete"

def WireDirectNativeABoxTaxonomyMatrix.decode
    (wire : WireDirectNativeABoxTaxonomyMatrix) :
    Except String DecodedDirectNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported direct native ABox taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let concepts ← decodeDirectNativeTaxonomyConceptsExact wire.source
    matrix.named wire.matrix.concepts
  let subsumptions ← decodeDirectNativeTaxonomyRowsExact wire.source matrix.named
    matrix.named wire.matrix.subsumptions
  return {
    matrix
    concepts := concepts.val
    subsumptions := subsumptions.val
    concepts_exact := concepts.property
    subsumptions_exact := subsumptions.property
  }

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

private theorem directConceptAlignment_coordinates_exact
    {named : List Nat} {decisions : List DecodedDirectNativeABoxTaxonomyDecision}
    (haligned : List.Forall₂
      (fun concept decision => decision.wireQuery = .concept 0 concept)
      named decisions) :
    List.Forall₂
      (fun concept decision => decision.CoordinatesExact (.concept 0 concept))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      apply List.Forall₂.cons
      · exact DecodedDirectNativeABoxTaxonomyDecision.coordinates_exact _ haligned
      · exact ih

private theorem directSubsumptionRowAlignment_coordinates_exact
    (sub : Nat) {named : List Nat}
    {decisions : List DecodedDirectNativeABoxTaxonomyDecision}
    (haligned : List.Forall₂
      (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
      named decisions) :
    List.Forall₂
      (fun sup decision => decision.CoordinatesExact (.subsumption 0 sub sup))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      apply List.Forall₂.cons
      · exact DecodedDirectNativeABoxTaxonomyDecision.coordinates_exact _ haligned
      · exact ih

private theorem directSubsumptionAlignment_coordinates_exact
    (allNamed : List Nat) {named : List Nat}
    {rows : List (List DecodedDirectNativeABoxTaxonomyDecision)}
    (haligned : List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        allNamed row)
      named rows) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.CoordinatesExact (.subsumption 0 sub sup))
        allNamed row)
      named rows := by
  induction haligned with
  | nil => exact .nil
  | cons hrow _ ih =>
      exact .cons (directSubsumptionRowAlignment_coordinates_exact _ hrow) ih

theorem DecodedDirectNativeABoxTaxonomyMatrix.concept_coordinates_exact
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => decision.CoordinatesExact (.concept 0 concept))
      decoded.matrix.named decoded.concepts :=
  directConceptAlignment_coordinates_exact decoded.concepts_exact

theorem DecodedDirectNativeABoxTaxonomyMatrix.subsumption_coordinates_exact
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.CoordinatesExact (.subsumption 0 sub sup))
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  directSubsumptionAlignment_coordinates_exact decoded.matrix.named
    decoded.subsumptions_exact

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
  wireQuery : WireNativeABoxTaxonomyQuery
  exactCoordinates : DecodedNativeABoxTaxonomyQuery.MatchesWire query wireQuery
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

def DecodedMixedNativeABoxTaxonomyDecision.wireQuery :
    DecodedMixedNativeABoxTaxonomyDecision → WireNativeABoxTaxonomyQuery
  | .sat decoded => decoded.wireQuery
  | .unsat decoded => decoded.taxonomy.wireQuery

def DecodedMixedNativeABoxTaxonomyDecision.CoordinatesExact
    (expected : WireNativeABoxTaxonomyQuery) :
    DecodedMixedNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      DecodedNativeABoxTaxonomyQuery.MatchesWire decoded.query expected
  | .unsat decoded =>
      DecodedNativeABoxTaxonomyQuery.MatchesWire decoded.taxonomy.query expected

theorem DecodedMixedNativeABoxTaxonomyDecision.coordinates_exact
    (decoded : DecodedMixedNativeABoxTaxonomyDecision)
    {expected : WireNativeABoxTaxonomyQuery}
    (haligned : decoded.wireQuery = expected) :
    decoded.CoordinatesExact expected := by
  cases decoded with
  | sat result => exact haligned ▸ result.exactCoordinates
  | unsat result => exact haligned ▸ result.taxonomy.exactCoordinates

def WireMixedNativeABoxTaxonomyDecision.decodeExact
    (wire : WireMixedNativeABoxTaxonomyDecision) :
    Except String { decoded : DecodedMixedNativeABoxTaxonomyDecision //
      decoded.wireQuery = wire.decision.query } := do
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
      let exactQuery ← wire.decision.query.decodeExact
        projection.certificate.seed.nodeCount
        projection.certificate.seed.abox.concepts.length
      let query := exactQuery.query
      if hquery : query.labelsPresentB
          projection.certificate.seed.state.base.base.labels = true then
        return ⟨.sat {
          projection
          query
          wireQuery := wire.decision.query
          exactCoordinates := exactQuery.exactCoordinates
          query_present := query.labelsPresentB_sound _ hquery
        }, rfl⟩
      else throw "mixed source taxonomy countermodel omits its query literals"
  | .unsat _ _ =>
      let exactTaxonomyDecision ← wire.decision.decodeExact
      match htaxonomy : exactTaxonomyDecision.val with
      | .sat _ => throw "internal mixed taxonomy evidence mismatch"
      | .unsat taxonomy =>
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
                return ⟨.unsat {
                  taxonomy
                  variable_ge_two := hvariables
                  functions := wire.functions
                  direct
                  pairs
                  unique_functions := hunique
                  exact_projection := hequal
                }, by simpa [DecodedMixedNativeABoxTaxonomyDecision.wireQuery,
                    DecodedNativeABoxTaxonomyDecision.wireQuery, htaxonomy]
                  using exactTaxonomyDecision.property⟩
              else throw "mixed source conversion differs from the native ABox taxonomy refutation"
            else throw "mixed native ABox taxonomy projection reuses a Skolem function"
          else throw "mixed native ABox taxonomy function-name table contains duplicates"

def WireMixedNativeABoxTaxonomyDecision.decode
    (wire : WireMixedNativeABoxTaxonomyDecision) :
    Except String DecodedMixedNativeABoxTaxonomyDecision := do
  return (← wire.decodeExact).val

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

def DecodedMixedNativeABoxTaxonomyDecision.positive :
    DecodedMixedNativeABoxTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedMixedNativeABoxTaxonomyDecision.QueryEntailed :
    DecodedMixedNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      ¬decoded.projection.certificate.seed.abox.abox.SatisfiableWithMixedQuery
        decoded.projection.direct decoded.projection.pairs decoded.query.literals
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithMixedQuery
        decoded.direct decoded.pairs decoded.taxonomy.query.literals

theorem DecodedMixedNativeABoxTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedMixedNativeABoxTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := decoded.source_satisfiable
      change (false = true ↔
        ¬decoded.projection.certificate.seed.abox.abox.SatisfiableWithMixedQuery
          decoded.projection.direct decoded.projection.pairs decoded.query.literals)
      exact ⟨fun hfalse => by contradiction,
        fun hnot => False.elim (hnot hsemantic)⟩
  | unsat decoded =>
      have hsemantic := decoded.source_unsatisfiable
      change (true = true ↔
        ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithMixedQuery
          decoded.direct decoded.pairs decoded.taxonomy.query.literals)
      exact ⟨fun _ => hsemantic, fun _ => rfl⟩

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
  concepts_exact : List.Forall₂
    (fun concept decoded => decoded.wireQuery = .concept 0 concept)
    matrix.named concepts
  subsumptions_exact : List.Forall₂
    (fun sub row => List.Forall₂
      (fun sup decoded => decoded.wireQuery = .subsumption 0 sub sup)
      matrix.named row)
    matrix.named subsumptions

private def decodeMixedNativeTaxonomyDecisionAt
    (functions : List String) (direct : List WireDirectSourceClause)
    (pairs : List WireSkolemPair) (expected : WireNativeABoxTaxonomyQuery)
    (wire : WireNativeABoxTaxonomyDecision) :
    Except String { decoded : DecodedMixedNativeABoxTaxonomyDecision //
      decoded.wireQuery = expected } := do
  if hquery : wire.query = expected then
    let decoded ← ({ version := 1, functions, direct, pairs, decision := wire } :
      WireMixedNativeABoxTaxonomyDecision).decodeExact
    return ⟨decoded.val, decoded.property.trans hquery⟩
  else throw "mixed native ABox taxonomy cell is in the wrong matrix position"

private def decodeMixedNativeTaxonomyConceptsExact
    (functions : List String) (direct : List WireDirectSourceClause)
    (pairs : List WireSkolemPair) :
    (named : List Nat) → (wires : List WireNativeABoxTaxonomyDecision) →
    Except String { decoded : List DecodedMixedNativeABoxTaxonomyDecision //
      List.Forall₂
        (fun concept decision => decision.wireQuery = .concept 0 concept)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | concept :: named, wire :: wires => do
      let decision ← decodeMixedNativeTaxonomyDecisionAt functions direct pairs
        (.concept 0 concept) wire
      let tail ← decodeMixedNativeTaxonomyConceptsExact functions direct pairs named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "mixed native ABox taxonomy concept row is incomplete"

private def decodeMixedNativeTaxonomySubsumptionRowExact
    (functions : List String) (direct : List WireDirectSourceClause)
    (pairs : List WireSkolemPair) (sub : Nat) :
    (named : List Nat) → (wires : List WireNativeABoxTaxonomyDecision) →
    Except String { decoded : List DecodedMixedNativeABoxTaxonomyDecision //
      List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sup :: named, wire :: wires => do
      let decision ← decodeMixedNativeTaxonomyDecisionAt functions direct pairs
        (.subsumption 0 sub sup) wire
      let tail ← decodeMixedNativeTaxonomySubsumptionRowExact
        functions direct pairs sub named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "mixed native ABox taxonomy subsumption row is incomplete"

private def decodeMixedNativeTaxonomyRowsExact
    (functions : List String) (direct : List WireDirectSourceClause)
    (pairs : List WireSkolemPair) (allNamed : List Nat) :
    (named : List Nat) → (rows : List (List WireNativeABoxTaxonomyDecision)) →
    Except String { decoded : List (List DecodedMixedNativeABoxTaxonomyDecision) //
      List.Forall₂
        (fun sub row => List.Forall₂
          (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
          allNamed row)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sub :: named, row :: rows => do
      let decodedRow ← decodeMixedNativeTaxonomySubsumptionRowExact
        functions direct pairs sub allNamed row
      let decodedRows ← decodeMixedNativeTaxonomyRowsExact
        functions direct pairs allNamed named rows
      return ⟨decodedRow.val :: decodedRows.val,
        .cons decodedRow.property decodedRows.property⟩
  | _, _ => .error "mixed native ABox taxonomy subsumption matrix is incomplete"

def WireMixedNativeABoxTaxonomyMatrix.decode
    (wire : WireMixedNativeABoxTaxonomyMatrix) :
    Except String DecodedMixedNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported mixed native ABox taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let concepts ← decodeMixedNativeTaxonomyConceptsExact wire.functions wire.direct
    wire.pairs matrix.named wire.matrix.concepts
  let subsumptions ← decodeMixedNativeTaxonomyRowsExact wire.functions wire.direct
    wire.pairs matrix.named matrix.named wire.matrix.subsumptions
  return {
    matrix
    concepts := concepts.val
    subsumptions := subsumptions.val
    concepts_exact := concepts.property
    subsumptions_exact := subsumptions.property
  }

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

private theorem mixedConceptAlignment_coordinates_exact
    {named : List Nat} {decisions : List DecodedMixedNativeABoxTaxonomyDecision}
    (haligned : List.Forall₂
      (fun concept decision => decision.wireQuery = .concept 0 concept)
      named decisions) :
    List.Forall₂
      (fun concept decision => decision.CoordinatesExact (.concept 0 concept))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      exact .cons
        (DecodedMixedNativeABoxTaxonomyDecision.coordinates_exact _ haligned) ih

private theorem mixedSubsumptionRowAlignment_coordinates_exact
    (sub : Nat) {named : List Nat}
    {decisions : List DecodedMixedNativeABoxTaxonomyDecision}
    (haligned : List.Forall₂
      (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
      named decisions) :
    List.Forall₂
      (fun sup decision => decision.CoordinatesExact (.subsumption 0 sub sup))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      exact .cons
        (DecodedMixedNativeABoxTaxonomyDecision.coordinates_exact _ haligned) ih

private theorem mixedSubsumptionAlignment_coordinates_exact
    (allNamed : List Nat) {named : List Nat}
    {rows : List (List DecodedMixedNativeABoxTaxonomyDecision)}
    (haligned : List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        allNamed row)
      named rows) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.CoordinatesExact (.subsumption 0 sub sup))
        allNamed row)
      named rows := by
  induction haligned with
  | nil => exact .nil
  | cons hrow _ ih =>
      exact .cons (mixedSubsumptionRowAlignment_coordinates_exact _ hrow) ih

theorem DecodedMixedNativeABoxTaxonomyMatrix.concept_coordinates_exact
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => decision.CoordinatesExact (.concept 0 concept))
      decoded.matrix.named decoded.concepts :=
  mixedConceptAlignment_coordinates_exact decoded.concepts_exact

theorem DecodedMixedNativeABoxTaxonomyMatrix.subsumption_coordinates_exact
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.CoordinatesExact (.subsumption 0 sub sup))
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  mixedSubsumptionAlignment_coordinates_exact decoded.matrix.named
    decoded.subsumptions_exact

theorem DecodedMixedNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

/-! ## Bundle query transport -/

def DecodedBundleProjection.sourceQueryEmbedding
    (decoded : DecodedBundleProjection) :
    Fin decoded.sourceConcepts.length → Fin decoded.concepts.length :=
  fun source => bundleConceptEmbedding decoded.sourceTargets decoded.bundles (.inr source)

theorem DecodedBundleProjection.target_model_to_source_model_preserving_nativeABox_query
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      decoded.sourceQueryEmbedding (sourceOf concept) = concept)
    (query : List (Lit (Fin decoded.sourceConcepts.length)))
    (J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (base : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain) (element : Domain)
    (htarget : J.models decoded.target)
    (habox : abox.models J value)
    (hquery : J.RealizesLiterals
      (query.map (renameLit decoded.sourceQueryEmbedding)) element) :
    ∃ I : Interp Domain (Fin decoded.sourceConcepts.length)
        (Fin decoded.roles.length),
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧
        ModelsBundles I functions (decodedBundleSpecs decoded.bundles) ∧
        (abox.mapConcepts sourceOf).models I value ∧
        I.RealizesLiterals query element := by
  let embedding := bundleConceptEmbedding decoded.sourceTargets decoded.bundles
  let combined := indexedBundleOntology decoded.direct
      (decodedBundleSpecs decoded.bundles) ++
    indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
      decoded.domainExtras
  have hrenamed : J.models (renameOntology embedding combined) :=
    (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).2 htarget
  let K := pullbackConcepts embedding J
  have hcombined : K.models combined :=
    (models_rename_pullback_iff embedding J combined).1 hrenamed
  have hcore : K.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles)) := by
    intro clause hclause
    exact hcombined clause (List.mem_append_left _ hclause)
  rcases indexedBundleProjection_complete K base decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.uniqueFunctions hcore with
    ⟨functions, hdirect, hbundles⟩
  let I := indexedRestrict K
  have haboxSource : (abox.mapConcepts sourceOf).models I value :=
    abox.mapConcepts_models_of sourceOf I J value
      (by
        intro individual concept hused
        change J.concept concept = J.concept (embedding (.inr (sourceOf concept)))
        simpa [DecodedBundleProjection.sourceQueryEmbedding, embedding] using
          congrArg J.concept (hembedded individual concept hused).symm)
      rfl habox
  have hquerySource : I.RealizesLiterals query element := by
    intro literal hliteral
    have htargetLiteral := hquery (renameLit decoded.sourceQueryEmbedding literal)
      (List.mem_map.mpr ⟨literal, hliteral, rfl⟩)
    change K.satLit (indexedLiftLit literal) element
    rw [← satLit_rename_pullback_iff embedding J]
    simpa [DecodedBundleProjection.sourceQueryEmbedding, embedding,
      indexedLiftLit, renameLit] using htargetLiteral
  exact ⟨I, functions, hdirect, hbundles, haboxSource, hquerySource⟩

theorem DecodedBundleProjection.source_model_to_target_model_preserving_nativeABox_query
    (decoded : DecodedBundleProjection)
    (abox : NativeABox Individual (Fin decoded.concepts.length)
      (Fin decoded.roles.length))
    (sourceOf : Fin decoded.concepts.length → Fin decoded.sourceConcepts.length)
    (hembedded : ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      decoded.sourceQueryEmbedding (sourceOf concept) = concept)
    (query : List (Lit (Fin decoded.sourceConcepts.length)))
    (I : Interp Domain (Fin decoded.sourceConcepts.length)
      (Fin decoded.roles.length))
    (functions : SkolemInterp Domain (Fin decoded.functions.length))
    (value : Individual → Domain) (element : Domain)
    (hdirect : I.models decoded.direct)
    (hbundles : ModelsBundles I functions (decodedBundleSpecs decoded.bundles))
    (habox : (abox.mapConcepts sourceOf).models I value)
    (hquery : I.RealizesLiterals query element) :
    ∃ J : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length),
      J.models decoded.target ∧ abox.models J value ∧
      J.RealizesLiterals
        (query.map (renameLit decoded.sourceQueryEmbedding)) element := by
  have hpositive : 0 < decoded.bundles.length :=
    List.length_pos_of_ne_nil decoded.nonemptyBundles
  letI : Nonempty
      (Sum (Fin decoded.bundles.length) (Fin decoded.sourceConcepts.length)) :=
    ⟨.inl ⟨0, hpositive⟩⟩
  obtain ⟨inverse, hleft⟩ := decoded.embeddingInjective.hasLeftInverse
  let embedding := bundleConceptEmbedding decoded.sourceTargets decoded.bundles
  let extended := indexedBundleExtension I (decodedBundleSpecs decoded.bundles)
  have hcore : extended.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles)) :=
    indexedBundleProjection_sound I functions decoded.direct
      (decodedBundleSpecs decoded.bundles) hdirect hbundles
  have hdomains : extended.models
      (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
          decoded.domainExtras) :=
    (add_indexedBundleDomainOntology_of_direct_iff extended decoded.direct
      (decodedBundleSpecs decoded.bundles) decoded.domainExtras
      decoded.rboxSource decoded.rboxTarget decoded.rboxDistinct
      decoded.pathPremises decoded.domainPremises).2 hcore
  let J := pushforwardConcepts inverse extended
  have hrenamed : J.models
      (renameOntology embedding
        (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
          indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
            decoded.domainExtras)) :=
    (models_rename_pushforward_iff embedding inverse hleft extended _).2 hdomains
  have haboxTarget : abox.models J value := by
    apply abox.models_of_mapConcepts sourceOf I J value
    · intro individual concept hused
      have hembed := hembedded individual concept hused
      have hinverse : inverse concept = .inr (sourceOf concept) := by
        calc
          inverse concept = inverse (embedding (.inr (sourceOf concept))) :=
            congrArg inverse hembed.symm
          _ = .inr (sourceOf concept) := hleft _
      simp [J, pushforwardConcepts, hinverse, extended, indexedBundleExtension]
    · rfl
    · exact habox
  have hqueryTarget : J.RealizesLiterals
      (query.map (renameLit decoded.sourceQueryEmbedding)) element := by
    intro targetLiteral htargetLiteral
    rcases List.mem_map.mp htargetLiteral with ⟨literal, hliteral, rfl⟩
    have hsourceLiteral := hquery literal hliteral
    have hinverse : inverse (embedding (.inr literal.concept)) =
        .inr literal.concept := by
      exact hleft _
    rw [satLit_rename_pullback_iff]
    cases literal <;>
      simpa [pullbackConcepts, DecodedBundleProjection.sourceQueryEmbedding,
        embedding, J, pushforwardConcepts, extended, indexedBundleExtension,
        renameLit, hinverse, Interp.satLit] using hsourceLiteral
  exact ⟨J, (models_iff_of_toFinset_eq J _ _ decoded.exactProjection).1 hrenamed,
    haboxTarget, hqueryTarget⟩

/-! ## Bundle source taxonomy wire -/

def NativeABox.SatisfiableWithBundleQuery
    (abox : NativeABox Individual TargetConcept Role)
    (sourceOf : TargetConcept → SourceConcept)
    (direct : List (Clause Variable SourceConcept Role))
    (bundles : Fin n → BundleSpec Variable SourceConcept Role Function)
    (query : List (Lit SourceConcept)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain SourceConcept Role)
      (functions : SkolemInterp Domain Function) (value : Individual → Domain)
      (element : Domain),
    Nonempty Domain ∧ I.models direct ∧ ModelsBundles I functions bundles ∧
      (abox.mapConcepts sourceOf).models I value ∧ I.RealizesLiterals query element

def queryConceptsEmbeddedB
    (query : List (Lit TargetConcept)) [DecidableEq TargetConcept]
    (sourceOf : TargetConcept → SourceConcept)
    (embedding : SourceConcept → TargetConcept) : Bool :=
  query.all fun literal => decide (embedding (sourceOf literal.concept) = literal.concept)

theorem queryConceptsEmbeddedB_sound
    (query : List (Lit TargetConcept)) [DecidableEq TargetConcept]
    (sourceOf : TargetConcept → SourceConcept)
    (embedding : SourceConcept → TargetConcept)
    (hcheck : queryConceptsEmbeddedB query sourceOf embedding = true) :
    ∀ literal ∈ query, embedding (sourceOf literal.concept) = literal.concept := by
  simpa only [queryConceptsEmbeddedB, List.all_eq_true, decide_eq_true_eq] using hcheck

theorem map_source_query_roundtrip
    (query : List (Lit TargetConcept))
    (sourceOf : TargetConcept → SourceConcept)
    (embedding : SourceConcept → TargetConcept)
    (hembedded : ∀ literal ∈ query,
      embedding (sourceOf literal.concept) = literal.concept) :
    (query.map (renameLit sourceOf)).map (renameLit embedding) = query := by
  induction query with
  | nil => rfl
  | cons literal tail ih =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · cases literal
        simp [renameLit, hembedded _ (List.mem_cons_self)]
      · exact ih (fun candidate hcandidate =>
          hembedded candidate (List.mem_cons_of_mem _ hcandidate))

structure WireBundleNativeABoxTaxonomyDecision where
  version : Nat
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  abox_source_map : List Nat
  decision : WireNativeABoxTaxonomyDecision
deriving FromJson, ToJson, Repr

structure DecodedBundleNativeABoxTaxonomySat where
  projection : DecodedBundleNativeABoxSatCertificate
  query : DecodedNativeABoxTaxonomyQuery projection.certificate.seed.nodeCount
    projection.certificate.seed.abox.concepts.length
  query_present : ∀ literal ∈ query.literals,
    (query.root, literal) ∈ projection.certificate.seed.state.base.base.labels
  query_embedded : ∀ literal ∈ query.literals,
    bundleConceptEmbedding projection.sourceTargets projection.bundles
      (.inr (projection.sourceOf literal.concept)) = literal.concept

structure DecodedBundleNativeABoxTaxonomyUnsat where
  taxonomy : DecodedNativeABoxTaxonomyUnsat
  variable_ge_two : 2 ≤ taxonomy.initial.variableCount
  sourceConcepts : List String
  functions : List String
  sourceTargets : Fin sourceConcepts.length → Fin taxonomy.initial.abox.concepts.length
  direct : List (Clause (Fin taxonomy.initial.variableCount)
    (Fin sourceConcepts.length) (Fin taxonomy.initial.abox.roles.length))
  bundles : List (DecodedWireBundle (Fin taxonomy.initial.variableCount)
    (Fin sourceConcepts.length) (Fin taxonomy.initial.abox.roles.length)
    (Fin functions.length) (Fin taxonomy.initial.abox.concepts.length))
  domainExtras : List (IndexedBundleDomainSpec (Fin sourceConcepts.length)
    (Fin taxonomy.initial.abox.roles.length) bundles.length)
  nonemptyBundles : bundles ≠ []
  uniqueFunctions :
    (skolemPairFunctions (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup
  embeddingInjective : Function.Injective
    (bundleConceptEmbedding sourceTargets bundles)
  rboxSource : Fin taxonomy.initial.variableCount
  rboxTarget : Fin taxonomy.initial.variableCount
  rboxDistinct : rboxSource ≠ rboxTarget
  pathPremises : ∀ spec ∈ domainExtras, ∀ clause ∈
    roleInclusionPathClauses (decodedBundleSpecs bundles spec.bundle).role
      spec.path rboxSource rboxTarget, clause ∈ direct
  domainPremises : ∀ spec ∈ domainExtras,
    roleDomainClause (spec.superRole (decodedBundleSpecs bundles)) spec.domain
      rboxSource rboxTarget ∈ direct
  sourceOf : Fin taxonomy.initial.abox.concepts.length → Fin sourceConcepts.length
  abox_embedded : ∀ individual concept,
    concept ∈ taxonomy.initial.abox.abox.proxies individual ++
      taxonomy.initial.abox.abox.assertions individual →
    bundleConceptEmbedding sourceTargets bundles (.inr (sourceOf concept)) = concept
  query_embedded : ∀ literal ∈ taxonomy.query.literals,
    bundleConceptEmbedding sourceTargets bundles (.inr (sourceOf literal.concept)) =
      literal.concept
  exact_ontology :
    (renameOntology (bundleConceptEmbedding sourceTargets bundles)
      (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs bundles) domainExtras) ++
      taxonomy.initial.abox.negativeRoleClausesAt taxonomy.initial.variableCount
        variable_ge_two).toFinset =
      taxonomy.initial.state.base.base.ontology.toFinset

inductive DecodedBundleNativeABoxTaxonomyDecision where
  | sat (decoded : DecodedBundleNativeABoxTaxonomySat)
  | unsat (decoded : DecodedBundleNativeABoxTaxonomyUnsat)

def WireBundleNativeABoxTaxonomyDecision.decode
    (wire : WireBundleNativeABoxTaxonomyDecision) :
    Except String DecodedBundleNativeABoxTaxonomyDecision := do
  if wire.version != 1 then
    throw s!"unsupported bundle native ABox taxonomy source version {wire.version}"
  match wire.decision.evidence with
  | .sat certificateWire =>
      let projection ← ({
        source_concepts := wire.source_concepts
        functions := wire.functions
        direct := wire.direct
        bundles := wire.bundles
        domain_extras := wire.domain_extras
        abox_source_map := wire.abox_source_map
        certificate := certificateWire
      } : WireBundleNativeABoxSatCertificate).decode
      let query ← wire.decision.query.decode projection.certificate.seed.nodeCount
        projection.certificate.seed.abox.concepts.length
      if hquery : query.labelsPresentB
          projection.certificate.seed.state.base.base.labels = true then
        if hembedded : queryConceptsEmbeddedB query.literals projection.sourceOf
            (fun source => bundleConceptEmbedding projection.sourceTargets
              projection.bundles (.inr source)) = true then
          return .sat {
            projection
            query
            query_present := query.labelsPresentB_sound _ hquery
            query_embedded := queryConceptsEmbeddedB_sound _ _ _ hembedded
          }
        else throw "bundle taxonomy query is not an embedded source concept"
      else throw "bundle source taxonomy countermodel omits its query literals"
  | .unsat initial tree =>
      let taxonomyDecision ← wire.decision.decode
      let taxonomy ← match taxonomyDecision with
        | .unsat result => pure result
        | .sat _ => throw "internal bundle taxonomy evidence mismatch"
      let variableWitness ← requireAtLeastTwoVariables taxonomy.initial.variableCount
      let hvariables := variableWitness.proof
      if _hsourceConcepts : wire.source_concepts.Nodup then
        if _hfunctions : wire.functions.Nodup then
          let sourceTargets ← checkedNameEmbedding "source concept in target"
            wire.source_concepts taxonomy.initial.abox.concepts
          let direct ← wire.direct.mapM (WireDirectSourceClause.decode
            taxonomy.initial.variableCount wire.source_concepts
            taxonomy.initial.abox.roles)
          let bundles ← wire.bundles.mapM (WireSkolemBundle.decode
            taxonomy.initial.variableCount wire.source_concepts
            taxonomy.initial.abox.concepts taxonomy.initial.abox.roles wire.functions)
          if hnonempty : bundles ≠ [] then
            let rboxSource : Fin taxonomy.initial.variableCount :=
              ⟨0, lt_of_lt_of_le Nat.zero_lt_two hvariables⟩
            let rboxTarget : Fin taxonomy.initial.variableCount := ⟨1, hvariables⟩
            have hrboxDistinct : rboxSource ≠ rboxTarget := by
              intro hequal
              have hval := congrArg Fin.val hequal
              simp [rboxSource, rboxTarget] at hval
            let domainExtras ← wire.domain_extras.mapM
              (WireBundleDomainExtra.decode wire.source_concepts
                taxonomy.initial.abox.roles bundles.length)
            if hunique : (skolemPairFunctions
                (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup then
              if hinjective : (bundleEmbeddingValues sourceTargets bundles).Nodup then
                if hpaths : ∀ spec ∈ domainExtras, ∀ clause ∈
                    roleInclusionPathClauses
                      (decodedBundleSpecs bundles spec.bundle).role spec.path
                        rboxSource rboxTarget, clause ∈ direct then
                  if hdomains : ∀ spec ∈ domainExtras,
                      roleDomainClause
                        (spec.superRole (decodedBundleSpecs bundles)) spec.domain
                          rboxSource rboxTarget ∈ direct then
                    let sourceOf ← decodeConceptMap "native ABox source concept"
                      wire.source_concepts.length taxonomy.initial.abox.concepts.length
                      wire.abox_source_map
                    let embedding := fun source =>
                      bundleConceptEmbedding sourceTargets bundles (.inr source)
                    if haboxEmbedded : taxonomy.initial.abox.abox.conceptsEmbeddedB
                        sourceOf embedding = true then
                      if hqueryEmbedded : queryConceptsEmbeddedB taxonomy.query.literals
                          sourceOf embedding = true then
                        if hequal :
                            (renameOntology (bundleConceptEmbedding sourceTargets bundles)
                              (indexedBundleOntology direct
                                  (decodedBundleSpecs bundles) ++
                                indexedBundleDomainOntology
                                  (decodedBundleSpecs bundles) domainExtras) ++
                              taxonomy.initial.abox.negativeRoleClausesAt
                                taxonomy.initial.variableCount hvariables).toFinset =
                              taxonomy.initial.state.base.base.ontology.toFinset then
                          return .unsat {
                            taxonomy
                            variable_ge_two := hvariables
                            sourceConcepts := wire.source_concepts
                            functions := wire.functions
                            sourceTargets
                            direct
                            bundles
                            domainExtras
                            nonemptyBundles := hnonempty
                            uniqueFunctions := hunique
                            embeddingInjective :=
                              bundleConceptEmbedding_injective_of_nodup
                                sourceTargets bundles hinjective
                            rboxSource
                            rboxTarget
                            rboxDistinct := hrboxDistinct
                            pathPremises := hpaths
                            domainPremises := hdomains
                            sourceOf
                            abox_embedded :=
                              taxonomy.initial.abox.abox.conceptsEmbeddedB_sound
                                sourceOf embedding haboxEmbedded
                            query_embedded := queryConceptsEmbeddedB_sound _ _ _
                              hqueryEmbedded
                            exact_ontology := hequal
                          }
                        else throw "bundle source conversion differs from the native ABox taxonomy refutation ontology"
                      else throw "bundle taxonomy query is not an embedded source concept"
                    else throw "native ABox concept is not an embedded bundle source concept"
                  else throw "bundle domain premise is absent from the source ontology"
                else throw "bundle role-inclusion path is absent from the source ontology"
              else throw "bundle definers collide with each other or source concepts"
            else throw "bundle native ABox taxonomy projection reuses a Skolem function"
          else throw "bundle native ABox taxonomy projection contains no bundles"
        else throw "bundle native ABox taxonomy function-name table contains duplicates"
      else throw "bundle native ABox taxonomy source concept-name table contains duplicates"

def WireBundleNativeABoxTaxonomyDecision.check
    (wire : WireBundleNativeABoxTaxonomyDecision) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleNativeABoxTaxonomySat.source_satisfiable
    (decoded : DecodedBundleNativeABoxTaxonomySat) :
    decoded.projection.certificate.seed.abox.abox.SatisfiableWithBundleQuery
      decoded.projection.sourceOf decoded.projection.direct
      (decodedBundleSpecs decoded.projection.bundles)
      (decoded.query.literals.map (renameLit decoded.projection.sourceOf)) := by
  rcases decoded.projection.certificate.satisfiable_with_query decoded.query.root
      decoded.query.literals decoded.query_present with
    ⟨Domain, J, value, element, hdomain, htarget, habox, hquery⟩
  let targetCore := renameOntology
    (bundleConceptEmbedding decoded.projection.sourceTargets decoded.projection.bundles)
    (indexedBundleOntology decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.projection.bundles)
        decoded.projection.domainExtras)
  have happended : J.models (targetCore ++
      decoded.projection.certificate.seed.abox.negativeRoleClausesAt
        decoded.projection.certificate.seed.variableCount
        decoded.projection.variable_ge_two) :=
    (models_iff_of_toFinset_eq J _ _ decoded.projection.exact_ontology).2 htarget
  have hcore : J.models targetCore := by
    intro clause hclause
    exact happended clause (List.mem_append_left _ hclause)
  let projection : DecodedBundleProjection := {
    variableCount := decoded.projection.certificate.seed.variableCount
    sourceConcepts := decoded.projection.sourceConcepts
    concepts := decoded.projection.certificate.seed.abox.concepts
    roles := decoded.projection.certificate.seed.abox.roles
    functions := decoded.projection.functions
    sourceTargets := decoded.projection.sourceTargets
    direct := decoded.projection.direct
    bundles := decoded.projection.bundles
    domainExtras := decoded.projection.domainExtras
    target := targetCore
    nonemptyBundles := decoded.projection.nonemptyBundles
    uniqueFunctions := decoded.projection.uniqueFunctions
    embeddingInjective := decoded.projection.embeddingInjective
    rboxSource := decoded.projection.rboxSource
    rboxTarget := decoded.projection.rboxTarget
    rboxDistinct := decoded.projection.rboxDistinct
    pathPremises := decoded.projection.pathPremises
    domainPremises := decoded.projection.domainPremises
    exactProjection := rfl
  }
  have hroundtrip :
      (decoded.query.literals.map (renameLit decoded.projection.sourceOf)).map
          (renameLit projection.sourceQueryEmbedding) = decoded.query.literals := by
    exact map_source_query_roundtrip _ _ _ decoded.query_embedded
  have hqueryMapped : J.RealizesLiterals
      ((decoded.query.literals.map (renameLit decoded.projection.sourceOf)).map
        (renameLit projection.sourceQueryEmbedding)) element := by
    rw [hroundtrip]
    exact hquery
  let fallback : Domain := Classical.choice hdomain
  let base : SkolemInterp Domain (Fin decoded.projection.functions.length) :=
    { app := fun _ _ => fallback }
  rcases projection.target_model_to_source_model_preserving_nativeABox_query
      decoded.projection.certificate.seed.abox.abox decoded.projection.sourceOf
      decoded.projection.abox_embedded
      (decoded.query.literals.map (renameLit decoded.projection.sourceOf))
      J base value element hcore habox hqueryMapped with
    ⟨I, functions, hdirect, hbundles, haboxSource, hquerySource⟩
  exact ⟨Domain, I, functions, value, element, hdomain, hdirect, hbundles,
    haboxSource, hquerySource⟩

theorem DecodedBundleNativeABoxTaxonomyUnsat.source_unsatisfiable
    (decoded : DecodedBundleNativeABoxTaxonomyUnsat) :
    ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithBundleQuery
      decoded.sourceOf decoded.direct (decodedBundleSpecs decoded.bundles)
      (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf)) := by
  rintro ⟨Domain, I, functions, value, element, hdomain, hdirect, hbundles,
    habox, hquery⟩
  let targetCore := renameOntology
    (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
    (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
        decoded.domainExtras)
  let projection : DecodedBundleProjection := {
    variableCount := decoded.taxonomy.initial.variableCount
    sourceConcepts := decoded.sourceConcepts
    concepts := decoded.taxonomy.initial.abox.concepts
    roles := decoded.taxonomy.initial.abox.roles
    functions := decoded.functions
    sourceTargets := decoded.sourceTargets
    direct := decoded.direct
    bundles := decoded.bundles
    domainExtras := decoded.domainExtras
    target := targetCore
    nonemptyBundles := decoded.nonemptyBundles
    uniqueFunctions := decoded.uniqueFunctions
    embeddingInjective := decoded.embeddingInjective
    rboxSource := decoded.rboxSource
    rboxTarget := decoded.rboxTarget
    rboxDistinct := decoded.rboxDistinct
    pathPremises := decoded.pathPremises
    domainPremises := decoded.domainPremises
    exactProjection := rfl
  }
  obtain ⟨J, hcore, haboxTarget, hqueryMapped⟩ :=
    projection.source_model_to_target_model_preserving_nativeABox_query
      decoded.taxonomy.initial.abox.abox decoded.sourceOf decoded.abox_embedded
      (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf))
      I functions value element hdirect hbundles habox hquery
  have hroundtrip :
      (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf)).map
          (renameLit projection.sourceQueryEmbedding) =
        decoded.taxonomy.query.literals := by
    exact map_source_query_roundtrip _ _ _ decoded.query_embedded
  have hqueryTarget : J.RealizesLiterals decoded.taxonomy.query.literals element := by
    rw [← hroundtrip]
    exact hqueryMapped
  have happended : J.models (targetCore ++
      decoded.taxonomy.initial.abox.negativeRoleClausesAt
        decoded.taxonomy.initial.variableCount decoded.variable_ge_two) :=
    (decoded.taxonomy.initial.abox.models_append_negativeRoleClausesAt_iff
      J value haboxTarget.1 decoded.variable_ge_two targetCore).2
        ⟨hcore, haboxTarget.2.2.2.2⟩
  have htarget : J.models decoded.taxonomy.initial.state.base.base.ontology :=
    (models_iff_of_toFinset_eq J _ _ decoded.exact_ontology).1 happended
  exact decoded.taxonomy.unsatisfiable
    ⟨Domain, J, value, element, hdomain, htarget, haboxTarget, hqueryTarget⟩

def DecodedBundleNativeABoxTaxonomyDecision.SemanticallyValid :
    DecodedBundleNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      decoded.projection.certificate.seed.abox.abox.SatisfiableWithBundleQuery
        decoded.projection.sourceOf decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles)
        (decoded.query.literals.map (renameLit decoded.projection.sourceOf))
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithBundleQuery
        decoded.sourceOf decoded.direct (decodedBundleSpecs decoded.bundles)
        (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf))

theorem DecodedBundleNativeABoxTaxonomyDecision.semantic_valid
    (decoded : DecodedBundleNativeABoxTaxonomyDecision) :
    decoded.SemanticallyValid := by
  cases decoded with
  | sat result => exact result.source_satisfiable
  | unsat result => exact result.source_unsatisfiable

def DecodedBundleNativeABoxTaxonomyDecision.positive :
    DecodedBundleNativeABoxTaxonomyDecision → Bool
  | .sat _ => false
  | .unsat _ => true

def DecodedBundleNativeABoxTaxonomyDecision.QueryEntailed :
    DecodedBundleNativeABoxTaxonomyDecision → Prop
  | .sat decoded =>
      ¬decoded.projection.certificate.seed.abox.abox.SatisfiableWithBundleQuery
        decoded.projection.sourceOf decoded.projection.direct
        (decodedBundleSpecs decoded.projection.bundles)
        (decoded.query.literals.map (renameLit decoded.projection.sourceOf))
  | .unsat decoded =>
      ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithBundleQuery
        decoded.sourceOf decoded.direct (decodedBundleSpecs decoded.bundles)
        (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf))

theorem DecodedBundleNativeABoxTaxonomyDecision.positive_eq_true_iff
    (decision : DecodedBundleNativeABoxTaxonomyDecision) :
    decision.positive = true ↔ decision.QueryEntailed := by
  cases decision with
  | sat decoded =>
      have hsemantic := decoded.source_satisfiable
      change (false = true ↔
        ¬decoded.projection.certificate.seed.abox.abox.SatisfiableWithBundleQuery
          decoded.projection.sourceOf decoded.projection.direct
          (decodedBundleSpecs decoded.projection.bundles)
          (decoded.query.literals.map (renameLit decoded.projection.sourceOf)))
      exact ⟨fun hfalse => by contradiction,
        fun hnot => False.elim (hnot hsemantic)⟩
  | unsat decoded =>
      have hsemantic := decoded.source_unsatisfiable
      change (true = true ↔
        ¬decoded.taxonomy.initial.abox.abox.SatisfiableWithBundleQuery
          decoded.sourceOf decoded.direct (decodedBundleSpecs decoded.bundles)
          (decoded.taxonomy.query.literals.map (renameLit decoded.sourceOf)))
      exact ⟨fun _ => hsemantic, fun _ => rfl⟩

structure WireBundleNativeABoxTaxonomyMatrix where
  version : Nat
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  abox_source_map : List Nat
  matrix : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedBundleNativeABoxTaxonomyMatrix where
  matrix : DecodedNativeABoxTaxonomyMatrix
  concepts : List DecodedBundleNativeABoxTaxonomyDecision
  subsumptions : List (List DecodedBundleNativeABoxTaxonomyDecision)

def WireBundleNativeABoxTaxonomyMatrix.decode
    (wire : WireBundleNativeABoxTaxonomyMatrix) :
    Except String DecodedBundleNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported bundle native ABox taxonomy matrix version {wire.version}"
  let matrix ← wire.matrix.decode
  let wrap := fun decision => ({
    version := 1
    source_concepts := wire.source_concepts
    functions := wire.functions
    direct := wire.direct
    bundles := wire.bundles
    domain_extras := wire.domain_extras
    abox_source_map := wire.abox_source_map
    decision
  } : WireBundleNativeABoxTaxonomyDecision)
  let concepts ← wire.matrix.concepts.mapM fun decision => (wrap decision).decode
  let subsumptions ← wire.matrix.subsumptions.mapM fun row =>
    row.mapM fun decision => (wrap decision).decode
  return { matrix, concepts, subsumptions }

def WireBundleNativeABoxTaxonomyMatrix.check
    (wire : WireBundleNativeABoxTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleNativeABoxTaxonomyMatrix.allDecisions
    (decoded : DecodedBundleNativeABoxTaxonomyMatrix) :
    List DecodedBundleNativeABoxTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedBundleNativeABoxTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedBundleNativeABoxTaxonomyMatrix) : Prop :=
  decoded.matrix.wire.shapeB = true ∧ decoded.matrix.wire.queriesB = true ∧
  decoded.matrix.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedBundleNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedBundleNativeABoxTaxonomyMatrix) :
    decoded.SemanticallyValid := by
  refine ⟨decoded.matrix.complete_shape, decoded.matrix.exact_queries,
    decoded.matrix.shared_problem, ?_⟩
  intro decision _
  exact decision.semantic_valid

#print axioms DecodedDirectNativeABoxTaxonomySat.source_satisfiable
#print axioms DecodedDirectNativeABoxTaxonomyUnsat.source_unsatisfiable
#print axioms DecodedDirectNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedDirectNativeABoxTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedDirectNativeABoxTaxonomyMatrix.concept_coordinates_exact
#print axioms DecodedDirectNativeABoxTaxonomyMatrix.subsumption_coordinates_exact
#print axioms DecodedDirectNativeABoxTaxonomyMatrix.semantic_valid
#print axioms DecodedMixedNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedMixedNativeABoxTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedMixedNativeABoxTaxonomyMatrix.concept_coordinates_exact
#print axioms DecodedMixedNativeABoxTaxonomyMatrix.subsumption_coordinates_exact
#print axioms DecodedMixedNativeABoxTaxonomyMatrix.semantic_valid
#print axioms DecodedBundleNativeABoxTaxonomyDecision.semantic_valid
#print axioms DecodedBundleNativeABoxTaxonomyDecision.positive_eq_true_iff
#print axioms DecodedBundleNativeABoxTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
