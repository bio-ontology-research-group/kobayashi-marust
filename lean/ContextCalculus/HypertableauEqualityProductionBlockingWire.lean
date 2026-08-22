import ContextCalculus.HypertableauProductionBlockingWire
import ContextCalculus.HypertableauEqualityBlocking
import ContextCalculus.HypertableauEqualityBlockingCertificate
import ContextCalculus.HypertableauEqualityWire
import ContextCalculus.HypertableauCardinalityWire

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

def DecodedEqProductionBlockingTable.assignmentCandidateValidB
    (decoded : DecodedEqProductionBlockingTable)
    (assignment : FoldAssignment (Fin decoded.nodeCount)) : Bool :=
  let certificate : FiniteEqFoldCertificate decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount := {
    base := decoded.table.base
    folds := (finiteFoldPairs decoded.nodeCount).filter fun pair =>
      decide (pair ∈ assignment)
  }
  if decoded.table.allBlockableSources then
    certificate.checkWithCardinality decoded.definitions &&
      certificate.materialize.checkCardinalityDefsExact decoded.exactDefinitions
  else
    certificate.check

def DecodedEqProductionBlockingTable.rejectedCandidatesInvalid
    (decoded : DecodedEqProductionBlockingTable) : Bool :=
  decoded.rejectedList.all fun assignment =>
    !decoded.assignmentCandidateValidB assignment

theorem DecodedEqProductionBlockingTable.rejectedCandidatesInvalid_eq_true_iff
    (decoded : DecodedEqProductionBlockingTable) :
    decoded.rejectedCandidatesInvalid = true ↔
      ∀ assignment ∈ decoded.rejectedList,
        decoded.assignmentCandidateValidB assignment = false := by
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
      }
  | _ => throw "equality production blocker base is not a SAT-state payload"

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
    decoded.assignmentCandidateValidB assignment = false := by
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
#print axioms FiniteEqProductionBlockingTable.computableExpectedOptions_eq
#print axioms WireEqProductionBlockingTable.check_sound
#print axioms WireEqProductionBlockingTable.checked_sourceExpansionControlled
#print axioms WireEqProductionBlockingTable.checked_rejectedCandidate_invalid
#print axioms WireEqProductionBlockingTable.checked_expansion_has_fresh_pair
#print axioms WireEqProductionBlockingTable.checked_expansion_strict

end ContextCalculus.Hypertableau
