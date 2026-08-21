import ContextCalculus.HypertableauEqualityBlocking
import ContextCalculus.HypertableauEqualityCertificate
import ContextCalculus.HypertableauCardinalityCertificate

/-!
# Checked finite equality-quotient folds

The runtime may propose a pairwise blocker, but the blocker is not a trusted
semantic premise. This module materializes every outgoing edge visible at the
blocker's equality class at the blocked node and sends the resulting ordinary
equality certificate through `checkEqSat`.
-/

namespace ContextCalculus.Hypertableau

structure FiniteEqFoldCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteEqCertificate nodeCount conceptCount roleCount variableCount
  folds : List (Fin nodeCount × Fin nodeCount)

/-- Copy every raw outgoing blocker-class edge to the blocked source. -/
def FiniteEqFoldCertificate.outgoingFoldedEdges
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  certificate.folds.flatMap fun fold =>
    certificate.base.base.edges.filterMap fun edge =>
      if certificate.base.representative edge.2.1 =
          certificate.base.representative fold.2 then
        some (edge.1, fold.1, edge.2.2)
      else none

/-- Copy every raw incoming blocker-class edge to the blocked target. Inverse
role clauses require this dual half of a model fold. -/
def FiniteEqFoldCertificate.incomingFoldedEdges
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  certificate.folds.flatMap fun fold =>
    certificate.base.base.edges.filterMap fun edge =>
      if certificate.base.representative edge.2.2 =
          certificate.base.representative fold.2 then
        some (edge.1, edge.2.1, fold.1)
      else none

/-- Materialize both directions of every blocker-class edge. Invalid
representative maps are rejected by the ordinary equality checker. -/
def FiniteEqFoldCertificate.foldedEdges
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    List (Fin roleCount × Fin nodeCount × Fin nodeCount) :=
  certificate.base.base.edges ++ certificate.outgoingFoldedEdges ++
    certificate.incomingFoldedEdges

def FiniteEqFoldCertificate.materialize
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteEqCertificate nodeCount conceptCount roleCount variableCount := {
  certificate.base with
  base := { certificate.base.base with edges := certificate.foldedEdges }
}

@[simp] theorem FiniteEqFoldCertificate.materialize_ontology
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.base.ontology = certificate.base.base.ontology := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_equalities
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.equalities = certificate.base.equalities := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_representative
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.representative = certificate.base.representative := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_labels
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.base.labels = certificate.base.base.labels := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_obligations
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.base.obligations =
      certificate.base.base.obligations := rfl

@[simp] theorem FiniteEqFoldCertificate.materialize_equalityClosureValidB
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.materialize.equalityClosureValidB =
      certificate.base.equalityClosureValidB := rfl

theorem FiniteEqFoldCertificate.base_edge_mem_foldedEdges
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (edge : Fin roleCount × Fin nodeCount × Fin nodeCount)
    (hedge : edge ∈ certificate.base.base.edges) :
    edge ∈ certificate.foldedEdges := by
  exact List.mem_append_left _ (List.mem_append_left _ hedge)

/-- Every materialized edge is original, copied from an outgoing blocker-class
edge, or copied from an incoming blocker-class edge. -/
theorem FiniteEqFoldCertificate.mem_foldedEdges_iff
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (role : Fin roleCount) (source target : Fin nodeCount) :
    (role, source, target) ∈ certificate.foldedEdges ↔
      (role, source, target) ∈ certificate.base.base.edges ∨
        (∃ blocker edgeSource,
          (source, blocker) ∈ certificate.folds ∧
          (role, edgeSource, target) ∈ certificate.base.base.edges ∧
          certificate.base.representative edgeSource =
            certificate.base.representative blocker) ∨
        (∃ blocker edgeTarget,
          (target, blocker) ∈ certificate.folds ∧
          (role, source, edgeTarget) ∈ certificate.base.base.edges ∧
          certificate.base.representative edgeTarget =
            certificate.base.representative blocker) := by
  simp only [FiniteEqFoldCertificate.foldedEdges,
    FiniteEqFoldCertificate.outgoingFoldedEdges,
    FiniteEqFoldCertificate.incomingFoldedEdges, List.mem_append,
    List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ((hbase | ⟨fold, hfold, edge, hedge, hmap⟩) |
      ⟨fold, hfold, edge, hedge, hmap⟩)
    · exact Or.inl hbase
    · rcases fold with ⟨blocked, blocker⟩
      rcases edge with ⟨edgeRole, edgeSource, edgeTarget⟩
      split at hmap
      · simp only [Option.some.injEq, Prod.mk.injEq] at hmap
        rcases hmap with ⟨rfl, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨blocker, edgeSource, hfold, hedge, ‹_›⟩)
      · contradiction
    · rcases fold with ⟨blocked, blocker⟩
      rcases edge with ⟨edgeRole, edgeSource, edgeTarget⟩
      split at hmap
      · simp only [Option.some.injEq, Prod.mk.injEq] at hmap
        rcases hmap with ⟨rfl, rfl, rfl⟩
        exact Or.inr (Or.inr ⟨blocker, edgeTarget, hfold, hedge, ‹_›⟩)
      · contradiction
  · rintro (hbase | houtgoing | hincoming)
    · exact Or.inl (Or.inl hbase)
    · rcases houtgoing with
        ⟨blocker, edgeSource, hfold, hedge, hrepresentative⟩
      exact Or.inl (Or.inr ⟨(source, blocker), hfold,
        (role, edgeSource, target), hedge, by simp [hrepresentative]⟩)
    · rcases hincoming with
        ⟨blocker, edgeTarget, hfold, hedge, hrepresentative⟩
      exact Or.inr ⟨(target, blocker), hfold,
        (role, source, edgeTarget), hedge, by simp [hrepresentative]⟩

/-- The label component of pairwise blocking, stated directly on the finite
fold certificate. -/
def FiniteEqFoldCertificate.FoldLabelCompatible
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) : Prop :=
  ∀ blocked blocker, (blocked, blocker) ∈ certificate.folds → ∀ lit,
    certificate.base.state.closedLabel blocker lit ↔
      certificate.base.state.closedLabel blocked lit

theorem FiniteEqFoldCertificate.foldLabelCompatible_of_signatures
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (hsignatures : ∀ blocked blocker,
      (blocked, blocker) ∈ certificate.folds →
      certificate.base.state.quotientRoleBlockingSignature parent blocker =
        certificate.base.state.quotientRoleBlockingSignature parent blocked) :
    certificate.FoldLabelCompatible := by
  intro blocked blocker hfold lit
  have hequal := certificate.base.state.quotientRoleBlockingSignature_label parent
    (hsignatures blocked blocker hfold)
  rw [← certificate.base.state.mem_closedLabelSet,
    ← certificate.base.state.mem_closedLabelSet, hequal]

/-- Folding changes only the edge list, so equality-quotient clashes cannot be
introduced. -/
theorem FiniteEqFoldCertificate.closedClashFree_of_base
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hclash : certificate.base.state.ClosedClashFree) :
    certificate.materialize.state.ClosedClashFree := by
  intro positiveNode negativeNode concept hrelated hlabels
  exact hclash positiveNode negativeNode concept hrelated hlabels

/-- Existing witnesses remain witnesses because every base edge is retained by
the materialized fold. -/
theorem FiniteEqFoldCertificate.closedWitnessComplete_of_base
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hwitness : certificate.base.state.ClosedWitnessComplete) :
    certificate.materialize.state.ClosedWitnessComplete := by
  intro node role filler hobligation
  rcases hwitness node role filler hobligation with ⟨witness, hedge, hlabel⟩
  exact ⟨witness, certificate.base_edge_mem_foldedEdges _ hedge, hlabel⟩

/-- Body atoms unaffected by adding role edges. -/
def Atom.RoleFree : Atom Variable Concept Role → Prop
  | .role .. => False
  | _ => True

def Clause.RoleFreeBody (clause : Clause Variable Concept Role) : Prop :=
  ∀ atom ∈ clause.body, atom.RoleFree

/-- Every closed fact true before folding remains true afterwards. -/
theorem FiniteEqFoldCertificate.closedHoldsAtom_of_base
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hholds : certificate.base.state.closedHoldsAtom assignment atom) :
    certificate.materialize.state.closedHoldsAtom assignment atom := by
  cases atom with
  | concept => exact hholds
  | role role source target =>
      rcases hholds with ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
      exact ⟨edgeSource, edgeTarget, hsource, htarget,
        certificate.base_edge_mem_foldedEdges _ hedge⟩
  | exists_ => exact hholds
  | eq => exact hholds

/-- A role-free closed body fact cannot become newly true merely because a fold
adds role edges. -/
theorem FiniteEqFoldCertificate.closedHoldsAtom_base_of_roleFree
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (hroleFree : atom.RoleFree)
    (hholds : certificate.materialize.state.closedHoldsAtom assignment atom) :
    certificate.base.state.closedHoldsAtom assignment atom := by
  cases atom with
  | concept => exact hholds
  | role => contradiction
  | exists_ => exact hholds
  | eq => exact hholds

/-- A role implication valid in the base closed graph remains valid after
folding. If the premise edge was copied, provenance identifies its blocker edge;
the implication produces a base conclusion there, and the same fold copies that
conclusion back to the blocked source. -/
theorem FiniteEqFoldCertificate.closedRole_implication
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (premise conclusion : Fin roleCount) (source target : Fin nodeCount)
    (himplication : ∀ left right,
      certificate.base.state.closedEdge premise left right →
        certificate.base.state.closedEdge conclusion left right)
    (hpremise : certificate.materialize.state.closedEdge premise source target) :
    certificate.materialize.state.closedEdge conclusion source target := by
  rcases hpremise with
    ⟨rawSource, rawTarget, hsource, htarget, hedge⟩
  rcases (certificate.mem_foldedEdges_iff premise rawSource rawTarget).mp hedge with
    hbase | houtgoing | hincoming
  · rcases himplication source target
        ⟨rawSource, rawTarget, hsource, htarget, hbase⟩ with
      ⟨headSource, headTarget, hheadSource, hheadTarget, hheadEdge⟩
    exact ⟨headSource, headTarget, hheadSource, hheadTarget,
      certificate.base_edge_mem_foldedEdges _ hheadEdge⟩
  · rcases houtgoing with
      ⟨blocker, edgeSource, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        edgeSource rawTarget :=
      ⟨edgeSource, rawTarget,
        certificate.base.state.equiv_equivalence.1 edgeSource,
        certificate.base.state.equiv_equivalence.1 rawTarget, hbase⟩
    rcases himplication edgeSource rawTarget hbasePremise with
      ⟨headSource, headTarget, hheadSource, hheadTarget, hheadEdge⟩
    have hheadRepresentative :
        certificate.base.representative headSource =
          certificate.base.representative blocker := by
      exact ((certificate.base.equalityClosureValidB_sound hvalid _ _).mp
        hheadSource).trans hrepresentative
    have hfoldedHead :
        (conclusion, rawSource, headTarget) ∈ certificate.foldedEdges :=
      (certificate.mem_foldedEdges_iff conclusion rawSource headTarget).mpr
        (Or.inr (Or.inl
          ⟨blocker, headSource, hfold, hheadEdge, hheadRepresentative⟩))
    exact ⟨rawSource, headTarget, hsource,
      certificate.base.state.equiv_equivalence.trans hheadTarget htarget,
      hfoldedHead⟩
  · rcases hincoming with
      ⟨blocker, edgeTarget, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        rawSource edgeTarget :=
      ⟨rawSource, edgeTarget,
        certificate.base.state.equiv_equivalence.refl rawSource,
        certificate.base.state.equiv_equivalence.refl edgeTarget, hbase⟩
    rcases himplication rawSource edgeTarget hbasePremise with
      ⟨headSource, headTarget, hheadSource, hheadTarget, hheadEdge⟩
    have hheadRepresentative :
        certificate.base.representative headTarget =
          certificate.base.representative blocker := by
      exact ((certificate.base.equalityClosureValidB_sound hvalid _ _).mp
        hheadTarget).trans hrepresentative
    have hfoldedHead :
        (conclusion, headSource, rawTarget) ∈ certificate.foldedEdges :=
      (certificate.mem_foldedEdges_iff conclusion headSource rawTarget).mpr
        (Or.inr (Or.inr
          ⟨blocker, headTarget, hfold, hheadEdge, hheadRepresentative⟩))
    exact ⟨headSource, rawTarget,
      certificate.base.state.equiv_equivalence.trans hheadSource hsource,
      htarget, hfoldedHead⟩

/-- Reversed role implications are preserved by bidirectional materialization.
An outgoing copied premise uses the incoming half of the same fold for its
reversed conclusion, and conversely. -/
theorem FiniteEqFoldCertificate.closedInverseRole_implication
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (premise conclusion : Fin roleCount) (source target : Fin nodeCount)
    (himplication : ∀ left right,
      certificate.base.state.closedEdge premise left right →
        certificate.base.state.closedEdge conclusion right left)
    (hpremise : certificate.materialize.state.closedEdge premise source target) :
    certificate.materialize.state.closedEdge conclusion target source := by
  rcases hpremise with
    ⟨rawSource, rawTarget, hsource, htarget, hedge⟩
  rcases (certificate.mem_foldedEdges_iff premise rawSource rawTarget).mp hedge with
    hbase | houtgoing | hincoming
  · rcases himplication source target
        ⟨rawSource, rawTarget, hsource, htarget, hbase⟩ with
      ⟨headSource, headTarget, hheadSource, hheadTarget, hheadEdge⟩
    exact ⟨headSource, headTarget, hheadSource, hheadTarget,
      certificate.base_edge_mem_foldedEdges _ hheadEdge⟩
  · rcases houtgoing with
      ⟨blocker, edgeSource, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        edgeSource rawTarget :=
      ⟨edgeSource, rawTarget,
        certificate.base.state.equiv_equivalence.refl edgeSource,
        certificate.base.state.equiv_equivalence.refl rawTarget, hbase⟩
    rcases himplication edgeSource rawTarget hbasePremise with
      ⟨headSource, headTarget, hheadSource, hheadTarget, hheadEdge⟩
    have htargetRepresentative :
        certificate.base.representative headTarget =
          certificate.base.representative blocker := by
      exact ((certificate.base.equalityClosureValidB_sound hvalid _ _).mp
        hheadTarget).trans hrepresentative
    have hfoldedHead :
        (conclusion, headSource, rawSource) ∈ certificate.foldedEdges :=
      (certificate.mem_foldedEdges_iff conclusion headSource rawSource).mpr
        (Or.inr (Or.inr
          ⟨blocker, headTarget, hfold, hheadEdge, htargetRepresentative⟩))
    exact ⟨headSource, rawSource,
      certificate.base.state.equiv_equivalence.trans hheadSource htarget,
      hsource, hfoldedHead⟩
  · rcases hincoming with
      ⟨blocker, edgeTarget, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        rawSource edgeTarget :=
      ⟨rawSource, edgeTarget,
        certificate.base.state.equiv_equivalence.refl rawSource,
        certificate.base.state.equiv_equivalence.refl edgeTarget, hbase⟩
    rcases himplication rawSource edgeTarget hbasePremise with
      ⟨headSource, headTarget, hheadSource, hheadTarget, hheadEdge⟩
    have hsourceRepresentative :
        certificate.base.representative headSource =
          certificate.base.representative blocker := by
      exact ((certificate.base.equalityClosureValidB_sound hvalid _ _).mp
        hheadSource).trans hrepresentative
    have hfoldedHead :
        (conclusion, rawTarget, headTarget) ∈ certificate.foldedEdges :=
      (certificate.mem_foldedEdges_iff conclusion rawTarget headTarget).mpr
        (Or.inr (Or.inl
          ⟨blocker, headSource, hfold, hheadEdge, hsourceRepresentative⟩))
    exact ⟨rawTarget, headTarget, htarget,
      certificate.base.state.equiv_equivalence.trans hheadTarget hsource,
      hfoldedHead⟩

/-- A forward role-and-target-label implication remains valid after pairwise
folding. This is the normalized `R(x,y) ∧ A(y) → B(x)` transfer: copied premise
edges are evaluated at the blocker, then the pairwise label equality transports
the conclusion back to the blocked source. -/
theorem FiniteEqFoldCertificate.closedForwardConcept_implication
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (hlabels : certificate.FoldLabelCompatible)
    (premise : Fin roleCount) (guard conclusion : Lit (Fin conceptCount))
    (source target : Fin nodeCount)
    (himplication : ∀ left right,
      certificate.base.state.closedEdge premise left right →
      certificate.base.state.closedLabel right guard →
      certificate.base.state.closedLabel left conclusion)
    (hpremise : certificate.materialize.state.closedEdge premise source target)
    (hguard : certificate.materialize.state.closedLabel target guard) :
    certificate.materialize.state.closedLabel source conclusion := by
  change certificate.base.state.closedLabel target guard at hguard
  rcases hpremise with
    ⟨rawSource, rawTarget, hsource, htarget, hedge⟩
  have hrawGuard : certificate.base.state.closedLabel rawTarget guard :=
    (certificate.base.state.closedLabel_congr htarget guard).mpr hguard
  rcases (certificate.mem_foldedEdges_iff premise rawSource rawTarget).mp hedge with
    hbase | houtgoing | hincoming
  · have hconclusion := himplication source target
      ⟨rawSource, rawTarget, hsource, htarget, hbase⟩ hguard
    exact hconclusion
  · rcases houtgoing with
      ⟨blocker, edgeSource, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        edgeSource rawTarget :=
      ⟨edgeSource, rawTarget,
        certificate.base.state.equiv_equivalence.refl edgeSource,
        certificate.base.state.equiv_equivalence.refl rawTarget, hbase⟩
    have hedgeSourceBlocker : certificate.base.state.equiv edgeSource blocker :=
      (certificate.base.equalityClosureValidB_sound hvalid _ _).mpr hrepresentative
    have hatEdgeSource := himplication edgeSource rawTarget hbasePremise hrawGuard
    have hatBlocker :=
      (certificate.base.state.closedLabel_congr hedgeSourceBlocker conclusion).mp
        hatEdgeSource
    have hatRawSource := (hlabels rawSource blocker hfold conclusion).mp hatBlocker
    have hatSource :=
      (certificate.base.state.closedLabel_congr hsource conclusion).mp hatRawSource
    exact hatSource
  · rcases hincoming with
      ⟨blocker, edgeTarget, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        rawSource edgeTarget :=
      ⟨rawSource, edgeTarget,
        certificate.base.state.equiv_equivalence.refl rawSource,
        certificate.base.state.equiv_equivalence.refl edgeTarget, hbase⟩
    have hatRawTarget : certificate.base.state.closedLabel rawTarget guard :=
      hrawGuard
    have hatBlocker : certificate.base.state.closedLabel blocker guard :=
      (hlabels rawTarget blocker hfold guard).mpr hatRawTarget
    have hedgeTargetBlocker : certificate.base.state.equiv edgeTarget blocker :=
      (certificate.base.equalityClosureValidB_sound hvalid _ _).mpr hrepresentative
    have hatEdgeTarget : certificate.base.state.closedLabel edgeTarget guard :=
      (certificate.base.state.closedLabel_congr hedgeTargetBlocker guard).mpr
        hatBlocker
    have hatRawSource :=
      himplication rawSource edgeTarget hbasePremise hatEdgeTarget
    exact (certificate.base.state.closedLabel_congr hsource conclusion).mp
      hatRawSource

/-- The dual normalized propagation `R(x,y) ∧ A(x) → B(y)` is also preserved.
For a copied edge, pairwise label equality transports the source guard to the
blocker; the base implication derives the target label, whose node is unchanged
by materialization. -/
theorem FiniteEqFoldCertificate.closedTargetConcept_implication
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (hlabels : certificate.FoldLabelCompatible)
    (premise : Fin roleCount) (guard conclusion : Lit (Fin conceptCount))
    (source target : Fin nodeCount)
    (himplication : ∀ left right,
      certificate.base.state.closedEdge premise left right →
      certificate.base.state.closedLabel left guard →
      certificate.base.state.closedLabel right conclusion)
    (hpremise : certificate.materialize.state.closedEdge premise source target)
    (hguard : certificate.materialize.state.closedLabel source guard) :
    certificate.materialize.state.closedLabel target conclusion := by
  change certificate.base.state.closedLabel source guard at hguard
  rcases hpremise with
    ⟨rawSource, rawTarget, hsource, htarget, hedge⟩
  rcases (certificate.mem_foldedEdges_iff premise rawSource rawTarget).mp hedge with
    hbase | houtgoing | hincoming
  · exact himplication source target
      ⟨rawSource, rawTarget, hsource, htarget, hbase⟩ hguard
  · rcases houtgoing with
      ⟨blocker, edgeSource, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        edgeSource rawTarget :=
      ⟨edgeSource, rawTarget,
        certificate.base.state.equiv_equivalence.refl edgeSource,
        certificate.base.state.equiv_equivalence.refl rawTarget, hbase⟩
    have hatRawSource : certificate.base.state.closedLabel rawSource guard :=
      (certificate.base.state.closedLabel_congr hsource guard).mpr hguard
    have hatBlocker : certificate.base.state.closedLabel blocker guard :=
      (hlabels rawSource blocker hfold guard).mpr hatRawSource
    have hedgeSourceBlocker : certificate.base.state.equiv edgeSource blocker :=
      (certificate.base.equalityClosureValidB_sound hvalid _ _).mpr hrepresentative
    have hatEdgeSource : certificate.base.state.closedLabel edgeSource guard :=
      (certificate.base.state.closedLabel_congr hedgeSourceBlocker guard).mpr
        hatBlocker
    have hatRawTarget :=
      himplication edgeSource rawTarget hbasePremise hatEdgeSource
    have hatTarget :=
      (certificate.base.state.closedLabel_congr htarget conclusion).mp hatRawTarget
    exact hatTarget
  · rcases hincoming with
      ⟨blocker, edgeTarget, hfold, hbase, hrepresentative⟩
    have hbasePremise : certificate.base.state.closedEdge premise
        rawSource edgeTarget :=
      ⟨rawSource, edgeTarget,
        certificate.base.state.equiv_equivalence.refl rawSource,
        certificate.base.state.equiv_equivalence.refl edgeTarget, hbase⟩
    have hatRawSource : certificate.base.state.closedLabel rawSource guard :=
      (certificate.base.state.closedLabel_congr hsource guard).mpr hguard
    have hatEdgeTarget :=
      himplication rawSource edgeTarget hbasePremise hatRawSource
    have hedgeTargetBlocker : certificate.base.state.equiv edgeTarget blocker :=
      (certificate.base.equalityClosureValidB_sound hvalid _ _).mpr hrepresentative
    have hatBlocker :=
      (certificate.base.state.closedLabel_congr hedgeTargetBlocker conclusion).mp
        hatEdgeTarget
    have hatRawTarget := (hlabels rawTarget blocker hfold conclusion).mp hatBlocker
    exact (certificate.base.state.closedLabel_congr htarget conclusion).mp
      hatRawTarget

/-- Adding fold edges preserves saturation for the role-free-body portion of
the ontology. -/
theorem FiniteEqFoldCertificate.closedSaturatedFor_of_roleFree
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hroleFree : ∀ clause ∈ certificate.base.base.ontology, clause.RoleFreeBody)
    (hsaturated : certificate.base.state.ClosedSaturatedFor
      certificate.base.base.ontology) :
    certificate.materialize.state.ClosedSaturatedFor
      certificate.base.base.ontology := by
  intro clause hclause assignment hbody
  have hbaseBody : ∀ atom ∈ clause.body,
      certificate.base.state.closedHoldsAtom assignment atom := by
    intro atom hatom
    exact certificate.closedHoldsAtom_base_of_roleFree assignment atom
      (hroleFree clause hclause atom hatom) (hbody atom hatom)
  rcases hsaturated clause hclause assignment hbaseBody with ⟨atom, hatom, hholds⟩
  exact ⟨atom, hatom,
    certificate.closedHoldsAtom_of_base assignment atom hholds⟩

def FiniteEqFoldCertificate.check
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.materialize.checkEqSat

theorem FiniteEqFoldCertificate.check_eq_true_iff_materialize_valid
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount) :
    certificate.check = true ↔ certificate.materialize.Valid := by
  exact certificate.materialize.checkEqSat_eq_true_iff_valid

theorem FiniteEqFoldCertificate.check_complete
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.materialize.Valid) :
    certificate.check = true :=
  certificate.materialize.checkEqSat_complete hvalid

theorem FiniteEqFoldCertificate.check_complete_of
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hequality : certificate.base.equalityClosureValidB = true)
    (hguarded : ∀ clause ∈ certificate.base.base.ontology, clause.GuardedBody)
    (hclash : certificate.materialize.state.ClosedClashFree)
    (hwitness : certificate.materialize.state.ClosedWitnessComplete)
    (hsaturated : certificate.materialize.state.ClosedSaturatedFor
      certificate.base.base.ontology) :
    certificate.check = true := by
  apply certificate.check_complete
  exact ⟨hequality, hguarded, hclash, hwitness, hsaturated⟩

/-- Any fold over a valid equality endpoint is accepted when all clause bodies
are role-free. This closes the complete role-free portion of blocked search;
only clauses activated by newly copied role edges require pairwise reasoning. -/
theorem FiniteEqFoldCertificate.check_of_base_valid_roleFree
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.Valid)
    (hroleFree : ∀ clause ∈ certificate.base.base.ontology, clause.RoleFreeBody) :
    certificate.check = true := by
  apply certificate.check_complete_of hvalid.1 hvalid.2.1
  · exact certificate.closedClashFree_of_base hvalid.2.2.1
  · exact certificate.closedWitnessComplete_of_base hvalid.2.2.2.1
  · exact certificate.closedSaturatedFor_of_roleFree hroleFree hvalid.2.2.2.2

/-- Any accepted equality-aware fold is a model of the exact unchanged
ontology. The theorem assumes no correctness property of the proposed folds. -/
theorem FiniteEqFoldCertificate.check_satisfiable
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    ∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      I.models certificate.base.base.ontology := by
  simpa [FiniteEqFoldCertificate.check] using
    certificate.materialize.checkEqSat_satisfiable hcheck

def FiniteEqFoldCertificate.checkWithCardinality
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Bool :=
  certificate.materialize.checkEqSatWithCardinality definitions

theorem FiniteEqFoldCertificate.checkWithCardinality_eq_true_iff
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    certificate.checkWithCardinality definitions = true ↔
      certificate.materialize.Valid ∧
        certificate.materialize.state.quotientCanonical.modelsCardinalityDefs
          definitions := by
  exact certificate.materialize.checkEqSatWithCardinality_eq_true_iff definitions

/-- The same untrusted fold boundary for cardinality-aware search. Acceptance
constructs one quotient interpretation satisfying both the exact ontology and
the exact minimum/maximum definitions. -/
theorem FiniteEqFoldCertificate.checkWithCardinality_models
    (certificate : FiniteEqFoldCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hcheck : certificate.checkWithCardinality definitions = true) :
    ∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      I.models certificate.base.base.ontology ∧
        I.modelsCardinalityDefs definitions := by
  have hmodels := certificate.materialize.checkEqSatWithCardinality_models
    definitions hcheck
  exact ⟨certificate.materialize.state.QuotientDomain,
    certificate.materialize.state.quotientCanonical, hmodels⟩

namespace EqFoldTests

private def cyclicBase : FiniteEqCertificate 3 1 1 1 where
  base := {
    ontology := [
      { body := [], head := [.concept (.pos 0) 0] },
      { body := [.concept (.pos 0) 0], head := [.exists_ 0 (.pos 0) 0] }
    ]
    labels := [(0, .pos 0), (1, .pos 0), (2, .pos 0)]
    edges := [(0, 0, 1), (0, 1, 2)]
    obligations := [(0, .pos 0, 0), (0, .pos 0, 1), (0, .pos 0, 2)]
  }
  equalities := []
  representative := id
  representativePath := fun _ => []

private def cyclicFold : FiniteEqFoldCertificate 3 1 1 1 where
  base := cyclicBase
  folds := [(2, 1)]

example : cyclicFold.materialize.base.edges =
    [(0, 0, 1), (0, 1, 2), (0, 2, 2), (0, 0, 2)] := by native_decide

example : cyclicFold.check = true := by native_decide

/-! Pairwise labels and parent-role signatures do not make one-round folding
closed under role chains.  The blocked node `2` has the same pairwise signature
as blocker `1`: their respective parents `0` and `4` carry the same `R` edge.
Copying the blocker's `S` successor creates `R(0,2), S(2,3)` and therefore a
new `T(0,3)` obligation that was absent from the valid base endpoint. -/

private def chainBase : FiniteEqCertificate 5 1 3 3 where
  base := {
    ontology := [{
      body := [.role 0 0 1, .role 1 1 2]
      head := [.role 2 0 2]
    }]
    labels := []
    edges := [(0, 4, 1), (1, 1, 3), (2, 4, 3), (0, 0, 2)]
    obligations := []
  }
  equalities := []
  representative := id
  representativePath := fun _ => []

private def chainFold : FiniteEqFoldCertificate 5 1 3 3 where
  base := chainBase
  folds := [(2, 1)]

private def chainParent : Fin 5 → Option (Fin 5)
  | 1 => some 4
  | 2 => some 0
  | _ => none

example : chainBase.Valid := by
  apply chainBase.checkEqSat_eq_true_iff_valid.mp
  native_decide

example : chainBase.state.quotientRoleBlockingSignature chainParent 1 =
    chainBase.state.quotientRoleBlockingSignature chainParent 2 := by
  classical
  have heqvgenFalse (left right : Fin 5) :
      Relation.EqvGen (fun _ _ : Fin 5 => False) left right ↔ left = right := by
    constructor
    · intro h
      induction h with
      | rel _ _ hrel => contradiction
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · rintro rfl
      exact Relation.EqvGen.refl _
  simp [EqState.quotientRoleBlockingSignature, EqState.closedLocalBlockingFacts,
    EqState.closedLabelSet, EqState.closedObligationSet,
    EqState.closedForwardParentRoles, EqState.closedBackwardParentRoles,
    EqState.closedLabel, EqState.closedObligation, EqState.closedEdge,
    heqvgenFalse, chainBase,
    chainParent, FiniteEqCertificate.state, FiniteSatCertificate.state]

example : (2, 0, 3) ∉ chainFold.foldedEdges := by native_decide

example : chainFold.check = false := by native_decide

end EqFoldTests

#print axioms FiniteEqFoldCertificate.check_satisfiable
#print axioms FiniteEqFoldCertificate.closedClashFree_of_base
#print axioms FiniteEqFoldCertificate.closedWitnessComplete_of_base
#print axioms FiniteEqFoldCertificate.closedHoldsAtom_of_base
#print axioms FiniteEqFoldCertificate.closedHoldsAtom_base_of_roleFree
#print axioms FiniteEqFoldCertificate.mem_foldedEdges_iff
#print axioms FiniteEqFoldCertificate.closedRole_implication
#print axioms FiniteEqFoldCertificate.closedInverseRole_implication
#print axioms FiniteEqFoldCertificate.foldLabelCompatible_of_signatures
#print axioms FiniteEqFoldCertificate.closedForwardConcept_implication
#print axioms FiniteEqFoldCertificate.closedTargetConcept_implication
#print axioms FiniteEqFoldCertificate.closedSaturatedFor_of_roleFree
#print axioms FiniteEqFoldCertificate.check_eq_true_iff_materialize_valid
#print axioms FiniteEqFoldCertificate.check_complete
#print axioms FiniteEqFoldCertificate.check_complete_of
#print axioms FiniteEqFoldCertificate.check_of_base_valid_roleFree
#print axioms FiniteEqFoldCertificate.checkWithCardinality_eq_true_iff
#print axioms FiniteEqFoldCertificate.checkWithCardinality_models

end ContextCalculus.Hypertableau
