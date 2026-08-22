import ContextCalculus.HypertableauProductionBlockingWire
import ContextCalculus.HypertableauEqualityBlocking
import ContextCalculus.HypertableauEqualityBlockingCertificate
import ContextCalculus.HypertableauEqualityWire
import ContextCalculus.HypertableauCardinalityWire
import ContextCalculus.HypertableauNativeABoxModelWire
import ContextCalculus.HypertableauFiniteProductionTerminalWire

/-!
# Equality-quotient production-blocking control wire

Equality, cardinality, and native-ABox production searches use the same
predecessor forest as the equality-free route, but compare pairwise signatures
after closing labels, obligations, and role endpoints under the checked node
equivalence.  This module reconstructs that exact table in Lean before Rust may
learn the union of an exhausted Cartesian assignment family.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireProductionNativeABoxContext where
  abox : WireNativeABox
  roots : List Nat
  apart : List WireApart
deriving FromJson, ToJson, Repr

structure WireEqProductionBlockingTable where
  version : Nat
  base : WireEqCertificate
  /-- `node_count` is the sentinel for no predecessor. -/
  parents : List Nat
  forbidden : List WireNodePair
  options : List WireFoldOption
  rejected : List (List WireNodePair)
  /-- Cardinality search retains every node having a blocker. Ordinary
  equality search retains precisely raw unwitnessed sources. -/
  all_blockable_sources : Bool
  /-- Ontology-only routes can replay every rejected finite candidate exactly.
  Native-ABox routes require the separate joint source payload. -/
  validate_rejections : Bool := false
  definitions : List WireCardinalityDef := []
  exact_definitions : List Nat := []
  /-- The exact candidate-independent ABox seed used by native-ABox routes.
  Its equality state must equal `base` before folds are materialized. -/
  native_seed : Option WireProductionNativeABoxContext := none
deriving FromJson, ToJson, Repr

structure FiniteEqProductionBlockingTable
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteEqCertificate nodeCount conceptCount roleCount variableCount
  parent : Fin nodeCount → Option (Fin nodeCount)
  forbidden : Finset (Fin nodeCount × Fin nodeCount)
  options : List (Fin nodeCount × List (Fin nodeCount))
  allBlockableSources : Bool

def FiniteEqProductionBlockingTable.ParentEarlier
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) : Prop :=
  ∀ node predecessor, table.parent node = some predecessor →
    predecessor.val < node.val

/-- Dimension-indexed part of the native-ABox seed needed to replay a folded
candidate. Names are checked by the decoder but do not enter model validity. -/
structure FiniteProductionNativeABoxContext
    (nodeCount conceptCount roleCount : Nat) where
  individualCount : Nat
  roots : Fin individualCount → Fin nodeCount
  proxies : Fin individualCount → List (Fin conceptCount)
  assertions : Fin individualCount → List (Fin conceptCount)
  different : List (Fin individualCount × Fin individualCount)
  roleAssertions : List (Fin roleCount × Fin individualCount × Fin individualCount)
  negativeRoleAssertions :
    List (Fin roleCount × Fin individualCount × Fin individualCount)
  apart : List (Fin nodeCount × Fin nodeCount)

structure DecodedEqProductionBlockingTable where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  table : FiniteEqProductionBlockingTable
    nodeCount conceptCount roleCount variableCount
  rejected : Finset (FoldAssignment (Fin nodeCount))
  rejectedList : List (FoldAssignment (Fin nodeCount))
  validateRejections : Bool
  definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))
  exactDefinitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))
  nativeContext : Option (FiniteProductionNativeABoxContext
    nodeCount conceptCount roleCount) := none

/-- A production SAT terminal carries both the exact blocked-state table and
the Cartesian fold assignment accepted for that state. -/
structure WireEqProductionTerminal where
  version : Nat
  table : WireEqProductionBlockingTable
  assignment : List WireNodePair
  result : WireEqCertificate
deriving FromJson, ToJson, Repr

structure DecodedEqProductionTerminal where
  table : DecodedEqProductionBlockingTable
  assignment : FoldAssignment (Fin table.nodeCount)
  result : FiniteEqCertificate table.nodeCount table.conceptCount
    table.roleCount table.variableCount

def WireProductionNativeABoxContext.decode
    (wire : WireProductionNativeABoxContext)
    (nodeCount conceptCount roleCount : Nat) :
    Except String (FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount) := do
  unless wire.abox.complete do
    throw "incomplete production native ABox payload"
  unless wire.abox.concepts.length = conceptCount do
    throw "production native ABox concept count differs from the blocker state"
  unless wire.abox.roles.length = roleCount do
    throw "production native ABox role count differs from the blocker state"
  unless wire.abox.concepts.Nodup do
    throw "production native ABox concept-name table contains duplicates"
  unless wire.abox.roles.Nodup do
    throw "production native ABox role-name table contains duplicates"
  let individuals ← wire.abox.individuals.mapM fun individual => do
    let proxies ← individual.proxies.mapM
      (checkedFin "production native ABox proxy" conceptCount)
    if proxies.isEmpty then
      throw "production native ABox individual has no singleton proxy"
    let assertions ← individual.assertions.mapM
      (checkedFin "production native ABox assertion" conceptCount)
    return (proxies, assertions)
  let individualCount := individuals.length
  let roots ← wire.roots.mapM
    (checkedFin "production native ABox root" nodeCount)
  if hroots : roots.length = individualCount then
    if _hrootUnique : roots.Nodup then
      let different ← wire.abox.different.mapM
        (decodeNativePair individualCount)
      let roleAssertions ← wire.abox.role_assertions.mapM
        (decodeNativeRoleAssertion roleCount individualCount)
      let negativeRoleAssertions ← wire.abox.negative_role_assertions.mapM
        (decodeNativeRoleAssertion roleCount individualCount)
      let apart ← wire.apart.mapM fun pair => do
        return (← checkedFin "production native ABox apart node" nodeCount pair.left,
          ← checkedFin "production native ABox apart node" nodeCount pair.right)
      let nominals ← wire.abox.nominals.mapM
        (checkedFin "production native ABox nominal" conceptCount)
      let allProxies := individuals.flatMap (·.1)
      unless allProxies.Nodup do
        throw "production native ABox proxy has duplicate ownership"
      unless allProxies.all (· ∈ nominals) do
        throw "production native ABox proxy is absent from nominals"
      return {
        individualCount
        roots := fun index => roots.get (hroots.symm ▸ index)
        proxies := fun index => (individuals.get index).1
        assertions := fun index => (individuals.get index).2
        different
        roleAssertions
        negativeRoleAssertions
        apart
      }
    else throw "production native ABox roots must be pairwise distinct"
  else throw s!"production native ABox root map has {roots.length} entries, expected {individualCount}"

/-! ## Executable equality-closed facts -/

def FiniteEqCertificate.computableClosedLabelB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (node : Fin nodeCount) (literal : Lit (Fin conceptCount)) : Bool :=
  (List.finRange nodeCount).any fun source =>
    certificate.closedRelatedB source node &&
      decide ((source, literal) ∈ certificate.base.labels)

theorem FiniteEqCertificate.computableClosedLabelB_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hclosure : certificate.equalityClosureValidB = true)
    (node : Fin nodeCount) (literal : Lit (Fin conceptCount)) :
    certificate.computableClosedLabelB node literal = true ↔
      certificate.state.closedLabel node literal := by
  simp only [FiniteEqCertificate.computableClosedLabelB, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, EqState.closedLabel]
  constructor
  · rintro ⟨source, _, hrelated, hlabel⟩
    exact ⟨source,
      (certificate.closedRelatedB_eq_true hclosure source node).mp hrelated,
      hlabel⟩
  · rintro ⟨source, hrelated, hlabel⟩
    exact ⟨source, List.mem_finRange source,
      (certificate.closedRelatedB_eq_true hclosure source node).mpr hrelated,
      hlabel⟩

def FiniteEqCertificate.computableClosedObligationB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (node : Fin nodeCount) (role : Fin roleCount)
    (literal : Lit (Fin conceptCount)) : Bool :=
  (List.finRange nodeCount).any fun source =>
    certificate.closedRelatedB source node &&
      decide ((role, literal, source) ∈ certificate.base.obligations)

theorem FiniteEqCertificate.computableClosedObligationB_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hclosure : certificate.equalityClosureValidB = true)
    (node : Fin nodeCount) (role : Fin roleCount)
    (literal : Lit (Fin conceptCount)) :
    certificate.computableClosedObligationB node role literal = true ↔
      certificate.state.closedObligation role literal node := by
  simp only [FiniteEqCertificate.computableClosedObligationB, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, EqState.closedObligation]
  constructor
  · rintro ⟨source, _, hrelated, hobligation⟩
    exact ⟨source,
      (certificate.closedRelatedB_eq_true hclosure source node).mp hrelated,
      hobligation⟩
  · rintro ⟨source, hrelated, hobligation⟩
    exact ⟨source, List.mem_finRange source,
      (certificate.closedRelatedB_eq_true hclosure source node).mpr hrelated,
      hobligation⟩

def FiniteEqCertificate.computableClosedEdgeB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (role : Fin roleCount) (source target : Fin nodeCount) : Bool :=
  (List.finRange nodeCount).any fun edgeSource =>
    (List.finRange nodeCount).any fun edgeTarget =>
      certificate.closedRelatedB edgeSource source &&
      certificate.closedRelatedB edgeTarget target &&
      decide ((role, edgeSource, edgeTarget) ∈ certificate.base.edges)

theorem FiniteEqCertificate.computableClosedEdgeB_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hclosure : certificate.equalityClosureValidB = true)
    (role : Fin roleCount) (source target : Fin nodeCount) :
    certificate.computableClosedEdgeB role source target = true ↔
      certificate.state.closedEdge role source target := by
  simp only [FiniteEqCertificate.computableClosedEdgeB, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, EqState.closedEdge]
  constructor
  · rintro ⟨edgeSource, _, edgeTarget, _, ⟨hsource, htarget⟩, hedge⟩
    exact ⟨edgeSource, edgeTarget,
      (certificate.closedRelatedB_eq_true hclosure edgeSource source).mp hsource,
      (certificate.closedRelatedB_eq_true hclosure edgeTarget target).mp htarget,
      hedge⟩
  · rintro ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
    exact ⟨edgeSource, List.mem_finRange edgeSource,
      edgeTarget, List.mem_finRange edgeTarget,
      ⟨(certificate.closedRelatedB_eq_true hclosure edgeSource source).mpr hsource,
        (certificate.closedRelatedB_eq_true hclosure edgeTarget target).mpr htarget⟩,
      hedge⟩

def FiniteEqCertificate.computableClosedLocalBlockingFacts
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (node : Fin nodeCount) : LocalBlockingFacts (Fin conceptCount) (Fin roleCount) :=
  (((finiteLiterals conceptCount).filter fun literal =>
      certificate.computableClosedLabelB node literal).toFinset,
    (((List.finRange roleCount).flatMap fun role =>
      (finiteLiterals conceptCount).map fun literal => (role, literal)).filter
        fun obligation => certificate.computableClosedObligationB node
          obligation.1 obligation.2).toFinset)

theorem FiniteEqCertificate.computableClosedLocalBlockingFacts_eq
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hclosure : certificate.equalityClosureValidB = true)
    (node : Fin nodeCount) :
    certificate.computableClosedLocalBlockingFacts node =
      certificate.state.closedLocalBlockingFacts node := by
  apply Prod.ext
  · ext literal
    simp [FiniteEqCertificate.computableClosedLocalBlockingFacts,
      EqState.closedLocalBlockingFacts, EqState.closedLabelSet,
      certificate.computableClosedLabelB_eq_true_iff hclosure]
  · ext obligation
    rcases obligation with ⟨role, literal⟩
    simp [FiniteEqCertificate.computableClosedLocalBlockingFacts,
      EqState.closedLocalBlockingFacts, EqState.closedObligationSet,
      certificate.computableClosedObligationB_eq_true_iff hclosure]

def FiniteEqCertificate.computableQuotientRoleBlockingSignature
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (parent : Fin nodeCount → Option (Fin nodeCount)) (node : Fin nodeCount) :
    RoleBlockingSignature (Fin conceptCount) (Fin roleCount) :=
  (certificate.computableClosedLocalBlockingFacts node,
    (parent node).map fun predecessor =>
      (certificate.computableClosedLocalBlockingFacts predecessor,
        ((List.finRange roleCount).filter fun role =>
          certificate.computableClosedEdgeB role predecessor node).toFinset,
        ((List.finRange roleCount).filter fun role =>
          certificate.computableClosedEdgeB role node predecessor).toFinset))

theorem FiniteEqCertificate.computableQuotientRoleBlockingSignature_eq
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hclosure : certificate.equalityClosureValidB = true)
    (parent : Fin nodeCount → Option (Fin nodeCount)) (node : Fin nodeCount) :
    certificate.computableQuotientRoleBlockingSignature parent node =
      certificate.state.quotientRoleBlockingSignature parent node := by
  unfold FiniteEqCertificate.computableQuotientRoleBlockingSignature
    EqState.quotientRoleBlockingSignature
  rw [certificate.computableClosedLocalBlockingFacts_eq hclosure]
  cases hparent : parent node with
  | none => simp
  | some predecessor =>
      simp only [Option.map_some]
      congr 3
      · exact certificate.computableClosedLocalBlockingFacts_eq hclosure predecessor
      · apply Prod.ext <;> ext role <;>
          simp [EqState.closedForwardParentRoles,
            EqState.closedBackwardParentRoles,
            certificate.computableClosedEdgeB_eq_true_iff hclosure]

/-! ## Exact option reconstruction -/

def FiniteEqProductionBlockingTable.quotientFold
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount)
    (source blocker : Fin nodeCount) : Prop :=
  blocker ∈ ancestorChain table.parent nodeCount source ∧
    table.base.state.quotientRoleBlockingSignature table.parent blocker =
      table.base.state.quotientRoleBlockingSignature table.parent source ∧
    (source, blocker) ∉ table.forbidden

noncomputable def FiniteEqProductionBlockingTable.candidateSources
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) : List (Fin nodeCount) := by
  classical
  exact if table.allBlockableSources then
      List.finRange nodeCount
    else
      (List.finRange nodeCount).filter fun source =>
        decide (∃ role filler, table.base.base.state.obligation role filler source ∧
          ∀ witness, ¬(table.base.base.state.edge role source witness ∧
            table.base.base.state.label witness filler))

noncomputable def FiniteEqProductionBlockingTable.expectedOptions
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) :
    List (Fin nodeCount × List (Fin nodeCount)) := by
  classical
  let options := table.candidateSources.map fun source =>
    (source, (ancestorChain table.parent nodeCount source).filter fun blocker =>
      decide (table.quotientFold source blocker))
  exact if table.allBlockableSources then
      options.filter fun option => !option.2.isEmpty
    else
      options

def FiniteEqProductionBlockingTable.computableFoldB
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount)
    (source blocker : Fin nodeCount) : Bool := by
  letI : DecidableEq
      (Option (LocalBlockingFacts (Fin conceptCount) (Fin roleCount) ×
        Finset (Fin roleCount) × Finset (Fin roleCount))) := decidableEqOption
  letI : DecidableEq
      (RoleBlockingSignature (Fin conceptCount) (Fin roleCount)) := inferInstance
  exact decide (blocker ∈ ancestorChain table.parent nodeCount source) &&
    decide (table.base.computableQuotientRoleBlockingSignature table.parent blocker =
      table.base.computableQuotientRoleBlockingSignature table.parent source) &&
    decide ((source, blocker) ∉ table.forbidden)

theorem FiniteEqProductionBlockingTable.computableFoldB_eq_true_iff
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount)
    (hclosure : table.base.equalityClosureValidB = true)
    (source blocker : Fin nodeCount) :
    table.computableFoldB source blocker = true ↔
      table.quotientFold source blocker := by
  simp only [FiniteEqProductionBlockingTable.computableFoldB,
    FiniteEqProductionBlockingTable.quotientFold, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [table.base.computableQuotientRoleBlockingSignature_eq hclosure,
    table.base.computableQuotientRoleBlockingSignature_eq hclosure]
  tauto

def FiniteEqProductionBlockingTable.computableCandidateSources
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) : List (Fin nodeCount) :=
  if table.allBlockableSources then
    List.finRange nodeCount
  else
    (List.finRange nodeCount).filter fun source =>
      table.base.base.state.unwitnessedB source

def FiniteEqProductionBlockingTable.computableExpectedOptions
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) :
    List (Fin nodeCount × List (Fin nodeCount)) :=
  let options := table.computableCandidateSources.map fun source =>
    (source, (ancestorChain table.parent nodeCount source).filter fun blocker =>
      table.computableFoldB source blocker)
  if table.allBlockableSources then
    options.filter fun option => !option.2.isEmpty
  else
    options

theorem FiniteEqProductionBlockingTable.computableCandidateSources_eq
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) :
    table.computableCandidateSources = table.candidateSources := by
  classical
  unfold FiniteEqProductionBlockingTable.computableCandidateSources
    FiniteEqProductionBlockingTable.candidateSources
  split <;> rename_i hmode
  · rfl
  · apply List.filter_congr
    intro source _
    rw [Bool.eq_iff_iff]
    simpa only [decide_eq_true_eq] using
      table.base.base.state.unwitnessedB_eq_true_iff source

theorem FiniteEqProductionBlockingTable.computableExpectedOptions_eq
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount)
    (hclosure : table.base.equalityClosureValidB = true) :
    table.computableExpectedOptions = table.expectedOptions := by
  classical
  have hmap :
      table.computableCandidateSources.map (fun source =>
        (source, (ancestorChain table.parent nodeCount source).filter fun blocker =>
          table.computableFoldB source blocker)) =
      table.candidateSources.map (fun source =>
        (source, (ancestorChain table.parent nodeCount source).filter fun blocker =>
          decide (table.quotientFold source blocker))) := by
    rw [table.computableCandidateSources_eq]
    apply List.map_congr_left
    intro source _
    congr 1
    apply List.filter_congr
    intro blocker _
    rw [Bool.eq_iff_iff]
    simpa only [decide_eq_true_eq] using
      table.computableFoldB_eq_true_iff hclosure source blocker
  unfold FiniteEqProductionBlockingTable.computableExpectedOptions
    FiniteEqProductionBlockingTable.expectedOptions
  rw [hmap]

def FiniteEqProductionBlockingTable.computableCheck
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount) : Bool :=
  table.base.equalityClosureValidB &&
  ((List.finRange nodeCount).all fun node =>
    match table.parent node with
    | none => true
    | some predecessor => decide (predecessor.val < node.val)) &&
  decide (table.options = table.computableExpectedOptions)

theorem FiniteEqProductionBlockingTable.computableCheck_sound
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount)
    (hcheck : table.computableCheck = true) :
    table.base.equalityClosureValidB = true ∧ table.ParentEarlier ∧
      table.options = table.expectedOptions := by
  unfold FiniteEqProductionBlockingTable.computableCheck at hcheck
  have houter :
      (table.base.equalityClosureValidB &&
        ((List.finRange nodeCount).all fun node =>
          match table.parent node with
          | none => true
          | some predecessor => decide (predecessor.val < node.val))) = true ∧
      decide (table.options = table.computableExpectedOptions) = true := by
    simpa only [Bool.and_eq_true] using hcheck
  have hinner : table.base.equalityClosureValidB = true ∧
      ((List.finRange nodeCount).all fun node =>
        match table.parent node with
        | none => true
        | some predecessor => decide (predecessor.val < node.val)) = true := by
    simpa only [Bool.and_eq_true] using houter.1
  have hclosure := hinner.1
  have hparents := hinner.2
  have hoptions := of_decide_eq_true houter.2
  refine ⟨hclosure, ?_, ?_⟩
  · intro node predecessor hparent
    have hnode : (match table.parent node with
        | none => true
        | some predecessor => decide (predecessor.val < node.val)) = true :=
      (List.all_eq_true.mp hparents) node (List.mem_finRange node)
    rw [hparent] at hnode
    simpa using hnode
  · exact hoptions.trans (table.computableExpectedOptions_eq hclosure)

def DecodedEqProductionBlockingTable.assignmentsExhausted
    (decoded : DecodedEqProductionBlockingTable) : Bool :=
  (enumerateFoldAssignments decoded.table.options).all fun assignment =>
    decide (assignment ∈ decoded.rejected)

theorem DecodedEqProductionBlockingTable.assignmentsExhausted_eq_true_iff
    (decoded : DecodedEqProductionBlockingTable) :
    decoded.assignmentsExhausted = true ↔
      ∀ assignment ∈ enumerateFoldAssignments decoded.table.options,
        assignment ∈ decoded.rejected := by
  simp [DecodedEqProductionBlockingTable.assignmentsExhausted]

def DecodedEqProductionBlockingTable.optionsNonempty
    (decoded : DecodedEqProductionBlockingTable) : Bool :=
  decoded.table.options.all fun option => !option.2.isEmpty

theorem DecodedEqProductionBlockingTable.optionsNonempty_eq_true_iff
    (decoded : DecodedEqProductionBlockingTable) :
    decoded.optionsNonempty = true ↔
      ∀ option ∈ decoded.table.options, option.2 ≠ [] := by
  simp [DecodedEqProductionBlockingTable.optionsNonempty]

def finiteFoldPairs (nodeCount : Nat) : List (Fin nodeCount × Fin nodeCount) :=
  (List.finRange nodeCount).flatMap fun source =>
    (List.finRange nodeCount).map fun blocker => (source, blocker)

def DecodedEqProductionBlockingTable.assignmentFoldCertificate
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount)) :
    FiniteEqFoldCertificate decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount := {
  base := decoded.table.base
  folds := (finiteFoldPairs decoded.nodeCount).filter fun pair =>
    decide (pair ∈ assignment)
}

def DecodedEqProductionBlockingTable.materializeAssignment
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount)) :
    FiniteEqCertificate decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount :=
  (decoded.assignmentFoldCertificate assignment).materialize

def DecodedEqProductionBlockingTable.assignmentCandidateValidB
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount)) : Bool :=
  if decoded.table.allBlockableSources then
    let materialized := decoded.materializeAssignment assignment
    materialized.checkEqSatWithCardinality decoded.definitions &&
      materialized.checkCardinalityDefsExact decoded.exactDefinitions
  else
    (decoded.materializeAssignment assignment).checkEqSat

/-- In the equality-only mode, assignment acceptance is exactly acceptance of
the concrete fold certificate reconstructed from the decoded production
state. -/
theorem DecodedEqProductionBlockingTable.assignmentCandidateValidB_eq_foldCheck
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount))
    (hmode : decoded.table.allBlockableSources = false) :
    decoded.assignmentCandidateValidB assignment =
      (decoded.assignmentFoldCertificate assignment).check := by
  simp [DecodedEqProductionBlockingTable.assignmentCandidateValidB,
    DecodedEqProductionBlockingTable.assignmentFoldCertificate,
    DecodedEqProductionBlockingTable.materializeAssignment,
    FiniteEqFoldCertificate.check, hmode]

def FiniteProductionNativeABoxContext.seededB
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount)
    (state : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  ((List.finRange context.individualCount).all fun individual =>
    ((context.proxies individual ++ context.assertions individual).all
      fun concept => decide
        ((context.roots individual, Lit.pos concept) ∈ state.base.base.labels))) &&
  (context.roleAssertions.all fun assertion => decide
    ((assertion.1, context.roots assertion.2.1,
      context.roots assertion.2.2) ∈ state.base.base.edges)) &&
  (context.different.all fun pair => decide
    ((context.roots pair.1, context.roots pair.2) ∈ state.apart))

def FiniteProductionNativeABoxContext.abox
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount) :
    NativeABox (Fin context.individualCount) (Fin conceptCount) (Fin roleCount) where
  proxies := context.proxies
  assertions := context.assertions
  different := context.different
  roleAssertions := context.roleAssertions
  negativeRoleAssertions := context.negativeRoleAssertions

theorem FiniteProductionNativeABoxContext.seededB_eq_true_iff
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount)
    (state : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    context.seededB state = true ↔
      context.abox.SeededIn state.state context.roots := by
  simp only [FiniteProductionNativeABoxContext.seededB, Bool.and_eq_true,
    List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq,
    NativeABox.SeededIn, FiniteProductionNativeABoxContext.abox,
    FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
    FiniteSatCertificate.state]
  tauto

def FiniteProductionNativeABoxContext.proxySingletonsB
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount)
    (state : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  (List.finRange context.individualCount).all fun individual =>
    (context.proxies individual).all fun proxy =>
      (List.finRange nodeCount).all fun node =>
        state.quotientPositiveB node proxy ==
          state.closedRelatedB node (context.roots individual)

theorem FiniteProductionNativeABoxContext.proxySingletonsB_sound
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount)
    (state : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : state.equalityClosureValidB = true)
    (hcheck : context.proxySingletonsB state = true) :
    context.abox.ProxySingletons state.state.quotientCanonical
      (fun individual => Quotient.mk state.state.nodeSetoid
        (context.roots individual)) := by
  simp only [FiniteProductionNativeABoxContext.proxySingletonsB,
    List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hcheck
  intro individual proxy hproxy candidate
  refine Quotient.inductionOn candidate fun node => ?_
  have hnode := hcheck individual proxy hproxy node
  rw [Bool.eq_iff_iff] at hnode
  rw [state.quotientPositiveB_eq_true hvalid node proxy,
    state.closedRelatedB_eq_true hvalid node (context.roots individual)] at hnode
  simpa only [Quotient.eq] using hnode

def FiniteProductionNativeABoxContext.negativeRolesB
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount)
    (state : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  context.negativeRoleAssertions.all fun assertion =>
    !state.quotientRoleB assertion.1
      (context.roots assertion.2.1) (context.roots assertion.2.2)

theorem FiniteProductionNativeABoxContext.negativeRolesB_sound
    (context : FiniteProductionNativeABoxContext
      nodeCount conceptCount roleCount)
    (state : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : state.equalityClosureValidB = true)
    (hcheck : context.negativeRolesB state = true) :
    context.abox.NegativeRoles state.state.quotientCanonical
      (fun individual => Quotient.mk state.state.nodeSetoid
        (context.roots individual)) := by
  simp only [FiniteProductionNativeABoxContext.negativeRolesB,
    List.all_eq_true] at hcheck
  intro assertion hassertion
  have hfalse := hcheck assertion hassertion
  intro hrole
  have htrue := (state.quotientRoleB_eq_true hvalid assertion.1
    (context.roots assertion.2.1) (context.roots assertion.2.2)).mpr hrole
  simp [htrue] at hfalse

def DecodedEqProductionBlockingTable.nativeAssignmentCandidateValidB
    (decoded : DecodedEqProductionBlockingTable)
    (context : FiniteProductionNativeABoxContext
      decoded.nodeCount decoded.conceptCount decoded.roleCount)
    (assignment : FoldAssignment (Fin decoded.nodeCount)) : Bool :=
  let materialized := decoded.materializeAssignment assignment
  let distinct : FiniteDistinctEqCertificate decoded.nodeCount
      decoded.conceptCount decoded.roleCount decoded.variableCount := {
    base := materialized
    apart := context.apart
  }
  decoded.assignmentCandidateValidB assignment &&
    distinct.apartSeparatedB && context.seededB distinct &&
    context.proxySingletonsB materialized &&
    context.negativeRolesB materialized

def DecodedEqProductionBlockingTable.NativeCandidateSemanticallyValid
    (decoded : DecodedEqProductionBlockingTable)
    (context : FiniteProductionNativeABoxContext
      decoded.nodeCount decoded.conceptCount decoded.roleCount)
    (assignment : FoldAssignment (Fin decoded.nodeCount)) : Prop :=
  let materialized := decoded.materializeAssignment assignment
  if decoded.table.allBlockableSources then
    context.abox.SatisfiableWithCardinality
      materialized.base.ontology decoded.definitions
  else
    context.abox.SatisfiableWith materialized.base.ontology

theorem DecodedEqProductionBlockingTable.nativeAssignmentCandidateValidB_sound
    (decoded : DecodedEqProductionBlockingTable)
    [Nonempty (Fin decoded.nodeCount)]
    (context : FiniteProductionNativeABoxContext
      decoded.nodeCount decoded.conceptCount decoded.roleCount)
    (assignment : FoldAssignment (Fin decoded.nodeCount))
    (hcheck : decoded.nativeAssignmentCandidateValidB context assignment = true) :
    decoded.NativeCandidateSemanticallyValid context assignment := by
  simp only [DecodedEqProductionBlockingTable.nativeAssignmentCandidateValidB,
    Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hcandidate, hapart⟩, hseeded⟩, hsingletons⟩, hnegative⟩
  let materialized := decoded.materializeAssignment assignment
  let distinct : FiniteDistinctEqCertificate decoded.nodeCount
      decoded.conceptCount decoded.roleCount decoded.variableCount := {
    base := materialized
    apart := context.apart
  }
  have hseeded' : context.abox.SeededIn distinct.state context.roots :=
    (context.seededB_eq_true_iff distinct).mp hseeded
  by_cases hmode : decoded.table.allBlockableSources = true
  · simp only [DecodedEqProductionBlockingTable.NativeCandidateSemanticallyValid,
      hmode]
    have hcardinality : materialized.checkEqSatWithCardinality
        decoded.definitions = true := by
      simp [DecodedEqProductionBlockingTable.assignmentCandidateValidB,
        hmode] at hcandidate
      simpa [materialized] using hcandidate.1
    have hparts := hcardinality
    simp only [FiniteEqCertificate.checkEqSatWithCardinality,
      Bool.and_eq_true, FiniteEqCertificate.checkEqSat] at hparts
    have hvalid : materialized.equalityClosureValidB = true :=
      hparts.1.1.1.1.1
    exact distinct.checkEqSatWithCardinality_native_satisfiable
      decoded.definitions context.abox context.roots hseeded' hcardinality
      hapart (context.proxySingletonsB_sound materialized hvalid hsingletons)
      (context.negativeRolesB_sound materialized hvalid hnegative)
  · have hmodeFalse : decoded.table.allBlockableSources = false :=
      Bool.eq_false_of_not_eq_true hmode
    simp only [DecodedEqProductionBlockingTable.NativeCandidateSemanticallyValid,
      hmodeFalse, Bool.false_eq]
    have hsat : materialized.checkEqSat = true := by
      simpa [DecodedEqProductionBlockingTable.assignmentCandidateValidB,
        hmodeFalse, materialized] using hcandidate
    have hparts := hsat
    simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hparts
    have hvalid : materialized.equalityClosureValidB = true := hparts.1.1.1.1
    exact distinct.checkEqSat_native_satisfiable context.abox context.roots
      hseeded' hsat hapart
      (context.proxySingletonsB_sound materialized hvalid hsingletons)
      (context.negativeRolesB_sound materialized hvalid hnegative)

def DecodedEqProductionBlockingTable.rejectedCandidatesInvalid
    (decoded : DecodedEqProductionBlockingTable) : Bool :=
  decoded.rejectedList.all fun assignment =>
    !(match decoded.nativeContext with
      | none => decoded.assignmentCandidateValidB assignment
      | some context => decoded.nativeAssignmentCandidateValidB context assignment)

theorem DecodedEqProductionBlockingTable.rejectedCandidatesInvalid_eq_true_iff
    (decoded : DecodedEqProductionBlockingTable) :
    decoded.rejectedCandidatesInvalid = true ↔
      ∀ assignment ∈ decoded.rejectedList,
        (match decoded.nativeContext with
          | none => decoded.assignmentCandidateValidB assignment
          | some context =>
              decoded.nativeAssignmentCandidateValidB context assignment) = false := by
  simp [DecodedEqProductionBlockingTable.rejectedCandidatesInvalid]

theorem FiniteEqProductionBlockingTable.expectedOptions_filtered
    (table : FiniteEqProductionBlockingTable
      nodeCount conceptCount roleCount variableCount)
    {source blockers blocker}
    (hoption : (source, blockers) ∈ table.expectedOptions)
    (hblocker : blocker ∈ blockers) :
    (source, blocker) ∉ table.forbidden := by
  classical
  unfold FiniteEqProductionBlockingTable.expectedOptions at hoption
  dsimp only at hoption
  split at hoption
  · replace hoption := (List.mem_filter.mp hoption).1
    rcases List.mem_map.mp hoption with ⟨candidate, _, heq⟩
    cases heq
    have hfold : table.quotientFold source blocker := by
      exact of_decide_eq_true (List.mem_filter.mp hblocker).2
    exact hfold.2.2
  · rcases List.mem_map.mp hoption with ⟨candidate, _, heq⟩
    cases heq
    have hfold : table.quotientFold source blocker := by
      exact of_decide_eq_true (List.mem_filter.mp hblocker).2
    exact hfold.2.2

theorem DecodedEqProductionBlockingTable.checked_foldOptionPairs_has_fresh
    (decoded : DecodedEqProductionBlockingTable)
    (hoptions : decoded.table.options = decoded.table.expectedOptions)
    (hnonempty : decoded.table.options ≠ [])
    (hrows : ∀ option ∈ decoded.table.options, option.2 ≠ []) :
    ∃ pair ∈ foldOptionPairs decoded.table.options,
      pair ∉ decoded.table.forbidden := by
  apply foldOptionPairs_has_fresh_of_filtered hnonempty hrows
  intro source blockers hoption blocker hblocker
  apply decoded.table.expectedOptions_filtered
  · simpa [hoptions] using hoption
  · exact hblocker

/-! ## Bounded decoder and semantic capstone -/

def WireEqProductionBlockingTable.decode
    (wire : WireEqProductionBlockingTable) :
    Except String DecodedEqProductionBlockingTable := do
  if wire.version != 1 && wire.version != 2 then
    throw s!"unsupported equality production blocker table version {wire.version}"
  let decodedBase ← wire.base.decode
  match decodedBase.evidence with
  | .sat certificate =>
      let definitions ← wire.definitions.mapM
        (WireCardinalityDef.decode decodedBase.conceptCount decodedBase.roleCount)
      let exactDefinitions ← wire.exact_definitions.mapM fun index =>
        match definitions[index]? with
        | some definition => pure definition
        | none => throw s!"exact production cardinality definition index {index} is out of range"
      let parent ← decodeProductionParents decodedBase.nodeCount wire.parents
      let forbidden ← wire.forbidden.mapM fun pair => do
        return (← checkedFin "forbidden source" decodedBase.nodeCount pair.source,
          ← checkedFin "forbidden blocker" decodedBase.nodeCount pair.target)
      let options ← wire.options.mapM fun option => do
        let source ← checkedFin "option source" decodedBase.nodeCount option.source
        let blockers ← option.blockers.mapM
          (checkedFin "option blocker" decodedBase.nodeCount)
        return (source, blockers)
      let rejected ← wire.rejected.mapM fun assignment => do
        let pairs ← assignment.mapM fun pair => do
          return (← checkedFin "rejected source" decodedBase.nodeCount pair.source,
            ← checkedFin "rejected blocker" decodedBase.nodeCount pair.target)
        return pairs.toFinset
      let nativeContext ← wire.native_seed.mapM fun native =>
        native.decode decodedBase.nodeCount decodedBase.conceptCount
          decodedBase.roleCount
      return {
        nodeCount := decodedBase.nodeCount
        conceptCount := decodedBase.conceptCount
        roleCount := decodedBase.roleCount
        variableCount := decodedBase.variableCount
        table := {
          base := certificate
          parent := parent
          forbidden := forbidden.toFinset
          options := options
          allBlockableSources := wire.all_blockable_sources
        }
        rejected := rejected.toFinset
        rejectedList := rejected
        validateRejections := wire.validate_rejections
        definitions := definitions
        exactDefinitions := exactDefinitions
        nativeContext := nativeContext
      }
  | _ => throw "equality production blocker base is not a SAT-state payload"

private def decodeEqTerminalResult
    (wire : WireEqCertificate) (base : DecodedEqProductionBlockingTable) :
    Except String (FiniteEqCertificate base.nodeCount base.conceptCount
      base.roleCount base.variableCount) := do
  let decoded ← wire.decode
  if hnodes : decoded.nodeCount = base.nodeCount then
    if hconcepts : decoded.conceptCount = base.conceptCount then
      if hroles : decoded.roleCount = base.roleCount then
        if hvariables : decoded.variableCount = base.variableCount then
          match decoded.evidence with
          | .sat certificate =>
              return hvariables ▸ hroles ▸ hconcepts ▸ hnodes ▸ certificate
          | _ => throw "equality production result is not a SAT payload"
        else throw "equality production result variable count differs from blocked state"
      else throw "equality production result role count differs from blocked state"
    else throw "equality production result concept count differs from blocked state"
  else throw "equality production result node count differs from blocked state"

def FiniteEqCertificate.productionMatchesB
    (left right : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  left.base.matchesB right.base &&
    listMembershipEqB left.equalities right.equalities

theorem FiniteEqCertificate.productionMatchesB_eq_true_iff
    (left right : FiniteEqCertificate nodeCount conceptCount roleCount variableCount) :
    left.productionMatchesB right = true ↔
      left.base.ontology = right.base.ontology ∧
      left.base.state = right.base.state ∧
      (∀ pair, pair ∈ left.equalities ↔ pair ∈ right.equalities) := by
  simp [FiniteEqCertificate.productionMatchesB,
    FiniteSatCertificate.matchesB_eq_true_iff,
    listMembershipEqB_eq_true_iff, and_assoc]

theorem FiniteEqCertificate.productionMatchesB_state
    (left right : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hmatch : left.productionMatchesB right = true) :
    left.base.ontology = right.base.ontology ∧ left.state = right.state := by
  have parts := (left.productionMatchesB_eq_true_iff right).mp hmatch
  refine ⟨parts.1, EqState.ext parts.2.1 ?_⟩
  funext source target
  apply propext
  simp only [FiniteEqCertificate.state]
  constructor
  · intro related
    induction related with
    | rel leftNode rightNode member =>
        exact Relation.EqvGen.rel _ _
          ((parts.2.2 (leftNode, rightNode)).mp member)
    | refl node => exact Relation.EqvGen.refl node
    | symm leftNode rightNode _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans leftNode middle rightNode _ _ leftIH rightIH =>
        exact Relation.EqvGen.trans _ _ _ leftIH rightIH
  · intro related
    induction related with
    | rel leftNode rightNode member =>
        exact Relation.EqvGen.rel _ _
          ((parts.2.2 (leftNode, rightNode)).mpr member)
    | refl node => exact Relation.EqvGen.refl node
    | symm leftNode rightNode _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans leftNode middle rightNode _ _ leftIH rightIH =>
        exact Relation.EqvGen.trans _ _ _ leftIH rightIH

def WireEqProductionTerminal.decode
    (wire : WireEqProductionTerminal) :
    Except String DecodedEqProductionTerminal := do
  unless wire.version == 1 do
    throw s!"unsupported equality production terminal version {wire.version}"
  let decoded ← wire.table.decode
  let pairs ← wire.assignment.mapM fun pair => do
    return (← checkedFin "terminal fold source" decoded.nodeCount pair.source,
      ← checkedFin "terminal fold blocker" decoded.nodeCount pair.target)
  let result ← decodeEqTerminalResult wire.result decoded
  return ⟨decoded, pairs.toFinset, result⟩

/-- Check exact terminal provenance independently of the final materialized
SAT document.  The table must reconstruct its computed blocker options, the
assignment must be one member of that Cartesian product, and materializing the
assignment must pass the equality fold checker. -/
def WireEqProductionTerminal.check
    (wire : WireEqProductionTerminal) : Except String Bool := do
  let decoded ← wire.decode
  return decoded.table.table.allBlockableSources == false &&
    decoded.table.table.computableCheck &&
    decide (decoded.assignment ∈
      enumerateFoldAssignments decoded.table.table.options) &&
    decoded.table.assignmentCandidateValidB decoded.assignment &&
    decoded.result.productionMatchesB
      (decoded.table.materializeAssignment decoded.assignment) &&
    decoded.result.checkEqSat

theorem WireEqProductionTerminal.check_sound
    (wire : WireEqProductionTerminal)
    (decoded : DecodedEqProductionTerminal)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true) :
    decoded.table.table.allBlockableSources = false ∧
      decoded.table.table.computableCheck = true ∧
      decoded.assignment ∈
        enumerateFoldAssignments decoded.table.table.options ∧
      decoded.table.assignmentCandidateValidB decoded.assignment = true ∧
      decoded.result.productionMatchesB
        (decoded.table.materializeAssignment decoded.assignment) = true ∧
      decoded.result.checkEqSat = true := by
  have hbool :
      ((decoded.table.table.allBlockableSources == false) &&
        decoded.table.table.computableCheck &&
        decide (decoded.assignment ∈
          enumerateFoldAssignments decoded.table.table.options) &&
        decoded.table.assignmentCandidateValidB decoded.assignment &&
        decoded.result.productionMatchesB
          (decoded.table.materializeAssignment decoded.assignment) &&
        decoded.result.checkEqSat) = true := by
    simpa [WireEqProductionTerminal.check, hdecode] using hcheck
  have checks :
      (decoded.table.table.allBlockableSources == false) = true ∧
      decoded.table.table.computableCheck = true ∧
      decide (decoded.assignment ∈
        enumerateFoldAssignments decoded.table.table.options) = true ∧
      decoded.table.assignmentCandidateValidB decoded.assignment = true ∧
      decoded.result.productionMatchesB
        (decoded.table.materializeAssignment decoded.assignment) = true ∧
      decoded.result.checkEqSat = true := by
    simpa only [Bool.and_eq_true, and_assoc] using hbool
  exact ⟨beq_iff_eq.mp checks.1, checks.2.1,
    of_decide_eq_true checks.2.2.1, checks.2.2.2.1,
    checks.2.2.2.2.1, checks.2.2.2.2.2⟩

def WireEqProductionBlockingTable.check
    (wire : WireEqProductionBlockingTable) : Except String Bool := do
  let decoded ← wire.decode
  return decoded.table.computableCheck && decoded.assignmentsExhausted &&
    decoded.optionsNonempty &&
    decide (decoded.rejected = decoded.rejectedList.toFinset) &&
    (!decoded.validateRejections ||
      ((if decoded.table.allBlockableSources then
          !decoded.definitions.isEmpty
        else
          decoded.definitions.isEmpty && decoded.exactDefinitions.isEmpty) &&
        decoded.rejectedCandidatesInvalid))

theorem WireEqProductionBlockingTable.check_sound
    (wire : WireEqProductionBlockingTable)
    (decoded : DecodedEqProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true) :
    decoded.table.base.equalityClosureValidB = true ∧
      decoded.table.ParentEarlier ∧
      decoded.table.options = decoded.table.expectedOptions ∧
      (∀ assignment ∈ enumerateFoldAssignments decoded.table.options,
        assignment ∈ decoded.rejected) ∧
      (∀ option ∈ decoded.table.options, option.2 ≠ []) ∧
      decoded.rejected = decoded.rejectedList.toFinset ∧
      (decoded.validateRejections = true →
        decoded.rejectedCandidatesInvalid = true) := by
  simp only [WireEqProductionBlockingTable.check, hdecode] at hcheck
  have hbool : (decoded.table.computableCheck &&
      decoded.assignmentsExhausted && decoded.optionsNonempty &&
      decide (decoded.rejected = decoded.rejectedList.toFinset) &&
      (!decoded.validateRejections ||
        ((if decoded.table.allBlockableSources then
            !decoded.definitions.isEmpty
          else
            decoded.definitions.isEmpty && decoded.exactDefinitions.isEmpty) &&
          decoded.rejectedCandidatesInvalid))) = true := by
    simpa using hcheck
  have checks : decoded.table.computableCheck = true ∧
      decoded.assignmentsExhausted = true ∧
      decoded.optionsNonempty = true ∧
      decide (decoded.rejected = decoded.rejectedList.toFinset) = true ∧
      (!decoded.validateRejections ||
        ((if decoded.table.allBlockableSources then
            !decoded.definitions.isEmpty
          else
            decoded.definitions.isEmpty && decoded.exactDefinitions.isEmpty) &&
          decoded.rejectedCandidatesInvalid)) = true := by
    simpa only [Bool.and_eq_true, and_assoc] using hbool
  have htable := decoded.table.computableCheck_sound checks.1
  refine ⟨htable.1, htable.2.1, htable.2.2,
    decoded.assignmentsExhausted_eq_true_iff.mp checks.2.1,
    decoded.optionsNonempty_eq_true_iff.mp checks.2.2.1,
    of_decide_eq_true checks.2.2.2.1, ?_⟩
  intro hvalidate
  have hrejections := checks.2.2.2.2
  simp only [hvalidate, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hrejections
  exact hrejections.2

theorem WireEqProductionBlockingTable.checked_sourceExpansionControlled
    (wire : WireEqProductionBlockingTable)
    (decoded : DecodedEqProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true)
    {source blockers}
    (hoption : (source, blockers) ∈ decoded.table.options) :
    SourceExpansionControlled decoded.rejected source blockers := by
  have checked := wire.check_sound decoded hdecode hcheck
  exact sourceExpansionControlled_of_assignment_exhaustion checked.2.2.2.2.1
    decoded.rejected checked.2.2.2.1 hoption

theorem WireEqProductionBlockingTable.checked_rejectedCandidate_invalid
    (wire : WireEqProductionBlockingTable)
    (decoded : DecodedEqProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true)
    (hvalidate : decoded.validateRejections = true)
    {assignment : FoldAssignment (Fin decoded.nodeCount)}
    (hrejected : assignment ∈ decoded.rejected) :
    (match decoded.nativeContext with
      | none => decoded.assignmentCandidateValidB assignment
      | some context =>
          decoded.nativeAssignmentCandidateValidB context assignment) = false := by
  have checked := wire.check_sound decoded hdecode hcheck
  have hinvalid := decoded.rejectedCandidatesInvalid_eq_true_iff.mp
    (checked.2.2.2.2.2.2 hvalidate)
  apply hinvalid assignment
  have hrepresentation := checked.2.2.2.2.2.1
  rw [hrepresentation] at hrejected
  simpa using hrejected

theorem WireEqProductionBlockingTable.checked_expansion_has_fresh_pair
    (wire : WireEqProductionBlockingTable)
    (decoded : DecodedEqProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true)
    (hnonempty : decoded.table.options ≠ []) :
    ∃ pair ∈ foldOptionPairs decoded.table.options,
      pair ∉ decoded.table.forbidden := by
  have checked := wire.check_sound decoded hdecode hcheck
  exact decoded.checked_foldOptionPairs_has_fresh checked.2.2.1 hnonempty
    checked.2.2.2.2.1

theorem WireEqProductionBlockingTable.checked_expansion_strict
    (wire : WireEqProductionBlockingTable)
    (decoded : DecodedEqProductionBlockingTable)
    (hdecode : wire.decode = .ok decoded)
    (hcheck : wire.check = .ok true)
    (hnonempty : decoded.table.options ≠ []) :
    decoded.table.forbidden ⊂ decoded.table.forbidden ∪
      foldOptionPairs decoded.table.options := by
  rcases wire.checked_expansion_has_fresh_pair decoded hdecode hcheck hnonempty with
    ⟨pair, hpairs, hfresh⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, by
    intro heq
    apply hfresh
    rw [heq]
    exact Finset.mem_union_right decoded.table.forbidden hpairs⟩

#print axioms FiniteEqCertificate.computableQuotientRoleBlockingSignature_eq
#print axioms FiniteEqCertificate.productionMatchesB_state
#print axioms DecodedEqProductionBlockingTable.assignmentCandidateValidB_eq_foldCheck
#print axioms FiniteEqProductionBlockingTable.computableExpectedOptions_eq
#print axioms WireEqProductionBlockingTable.check_sound
#print axioms WireEqProductionTerminal.check_sound
#print axioms DecodedEqProductionBlockingTable.nativeAssignmentCandidateValidB_sound
#print axioms WireEqProductionBlockingTable.checked_sourceExpansionControlled
#print axioms WireEqProductionBlockingTable.checked_rejectedCandidate_invalid
#print axioms WireEqProductionBlockingTable.checked_expansion_has_fresh_pair
#print axioms WireEqProductionBlockingTable.checked_expansion_strict

end ContextCalculus.Hypertableau
