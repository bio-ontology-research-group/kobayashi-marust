import ContextCalculus.HypertableauCoverObstructionWire
import ContextCalculus.HypertableauEndpointRoleEvidenceWire
import ContextCalculus.HypertableauEndpointRoleFoldEvidence

/-!
# Checked cover-refinement evidence

This combines an exact residual obstruction with a derivation of one
cover-only role atom in its body. It is the proof-bearing rejection boundary
needed before a runtime may refine blocker choices.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRegularCoverRefinement where
  version : Nat
  certificate : WireRegularCertificate
  clause : Nat
  assignment : List Nat
  evidence : WireEndpointRoleEvidence
deriving FromJson, ToJson, Repr

structure DecodedRegularCoverRefinement where
  decoded : DecodedRegularCertificate
  clauseIndex : Fin decoded.certificate.residual.length
  assignment : Fin decoded.variableCount → Fin decoded.nodeCount
  evidence : FiniteEndpointRoleEvidence
    (Fin decoded.nodeCount) (Fin decoded.roleCount)

def DecodedRegularCoverRefinement.clause
    (refinement : DecodedRegularCoverRefinement) :=
  refinement.decoded.certificate.residual.get refinement.clauseIndex

def WireRegularCoverRefinement.decode (wire : WireRegularCoverRefinement) :
    Except String DecodedRegularCoverRefinement := do
  if wire.version != 1 then
    throw s!"unsupported regular cover refinement version {wire.version}"
  let decoded ← wire.certificate.decode
  let clauseIndex ← checkedFin "residual clause"
    decoded.certificate.residual.length wire.clause
  let assignment ← decodeAssignment decoded.nodeCount decoded.variableCount
    wire.assignment
  let evidence ← wire.evidence.decode decoded.nodeCount decoded.roleCount
  return { decoded, clauseIndex, assignment, evidence }

def DecodedRegularCoverRefinement.matchesBodyAtomB
    (refinement : DecodedRegularCoverRefinement) :
    Atom (Fin refinement.decoded.variableCount)
      (Fin refinement.decoded.conceptCount)
      (Fin refinement.decoded.roleCount) → Bool
  | .role role source target =>
      decide (role = refinement.evidence.role) &&
      decide (refinement.assignment source = refinement.evidence.source) &&
      decide (refinement.assignment target = refinement.evidence.target)
  | _ => false

def DecodedRegularCoverRefinement.check
    (refinement : DecodedRegularCoverRefinement) : Bool :=
  refinement.decoded.certificate.coverObstructionB refinement.clause
      refinement.assignment &&
    refinement.decoded.certificate.roleClausesRepresentB &&
    refinement.evidence.check refinement.decoded.certificate &&
    decide ((refinement.evidence.role, refinement.evidence.source,
      refinement.evidence.target) ∈ refinement.decoded.certificate.cover) &&
    decide ((refinement.evidence.role, refinement.evidence.source,
      refinement.evidence.target) ∉ refinement.decoded.certificate.edges) &&
    refinement.clause.body.any refinement.matchesBodyAtomB

def DecodedRegularCoverRefinement.Valid
    (refinement : DecodedRegularCoverRefinement) : Prop :=
  refinement.decoded.certificate.state.CoverObstruction
      refinement.decoded.certificate.coverRelation refinement.clause
      refinement.assignment ∧
  NormalizedRoleClauses.Represent refinement.decoded.certificate.rules
      refinement.decoded.certificate.roleClauses ∧
  EndpointRole refinement.decoded.certificate.state
      refinement.decoded.certificate.redirect
      refinement.decoded.certificate.rules refinement.evidence.role
      refinement.evidence.source refinement.evidence.target ∧
  refinement.decoded.certificate.coverRelation refinement.evidence.role
      refinement.evidence.source refinement.evidence.target ∧
  ¬refinement.decoded.certificate.state.edge refinement.evidence.role
      refinement.evidence.source refinement.evidence.target ∧
  ∃ source target,
    Atom.role refinement.evidence.role source target ∈ refinement.clause.body ∧
    refinement.assignment source = refinement.evidence.source ∧
    refinement.assignment target = refinement.evidence.target

theorem DecodedRegularCoverRefinement.matchesBodyAtomB_eq_true_iff
    (refinement : DecodedRegularCoverRefinement)
    (atom : Atom (Fin refinement.decoded.variableCount)
      (Fin refinement.decoded.conceptCount)
      (Fin refinement.decoded.roleCount)) :
    refinement.matchesBodyAtomB atom = true ↔
      ∃ source target,
        atom = .role refinement.evidence.role source target ∧
        refinement.assignment source = refinement.evidence.source ∧
        refinement.assignment target = refinement.evidence.target := by
  cases atom <;> simp [DecodedRegularCoverRefinement.matchesBodyAtomB, and_assoc]

theorem DecodedRegularCoverRefinement.check_sound
    (refinement : DecodedRegularCoverRefinement)
    (hcheck : refinement.check = true) : refinement.Valid := by
  simp only [DecodedRegularCoverRefinement.check, Bool.and_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨hobstruction, hrepresents⟩, hevidence⟩, hcover⟩, hraw⟩, hbody⟩
  refine ⟨
    (refinement.decoded.certificate.coverObstructionB_eq_true_iff
      refinement.clause refinement.assignment).mp hobstruction,
    refinement.decoded.certificate.roleClausesRepresentB_eq_true_iff.mp
      hrepresents,
    refinement.evidence.check_sound refinement.decoded.certificate hevidence,
    ?_, ?_, ?_⟩
  · simpa [FiniteRegularCertificate.coverRelation] using hcover
  · simpa [FiniteRegularCertificate.state] using hraw
  · rw [List.any_eq_true] at hbody
    rcases hbody with ⟨atom, hatom, hmatch⟩
    rcases (refinement.matchesBodyAtomB_eq_true_iff atom).mp hmatch with
      ⟨source, target, rfl, hsource, htarget⟩
    exact ⟨source, target, hatom, hsource, htarget⟩

theorem DecodedRegularCoverRefinement.checked_rejection_has_fold
    (refinement : DecodedRegularCoverRefinement)
    (blocked : Fin refinement.decoded.nodeCount → Bool)
    (fold : Fin refinement.decoded.nodeCount →
      Fin refinement.decoded.nodeCount → Prop)
    (hcheck : refinement.check = true)
    (hclosed : refinement.decoded.certificate.state.RoleClosed
      refinement.decoded.certificate.rules)
    (hredirect : State.BlockedRedirectRefines blocked fold
      refinement.decoded.certificate.redirect)
    (htotal : State.BlockedFoldTotal blocked fold) :
    ∃ source blocker, fold source blocker := by
  have hvalid := refinement.check_sound hcheck
  have hcomponents := hcheck
  simp only [DecodedRegularCoverRefinement.check, Bool.and_eq_true] at hcomponents
  rcases hcomponents with
    ⟨⟨⟨⟨⟨_, _⟩, hevidence⟩, _⟩, _⟩, _⟩
  exact refinement.evidence.exists_fold_of_cover_only_check
    refinement.decoded.certificate blocked fold hevidence
    hclosed hvalid.2.2.2.2.1 hredirect htotal

/-- The fully checked rejection boundary needs no externally supplied RBox
closure invariant. Saturation of the represented normalized clauses derives
that invariant before exposing the concrete fold. -/
theorem DecodedRegularCoverRefinement.checked_rejection_has_fold_of_saturated
    (refinement : DecodedRegularCoverRefinement)
    (blocked : Fin refinement.decoded.nodeCount → Bool)
    (fold : Fin refinement.decoded.nodeCount →
      Fin refinement.decoded.nodeCount → Prop)
    (hcheck : refinement.check = true)
    (hsaturated : refinement.decoded.certificate.state.SaturatedFor
      (refinement.decoded.certificate.roleClauses.map
        (NormalizedRoleClause.toClause
          (Concept := Fin refinement.decoded.conceptCount))))
    (hredirect : State.BlockedRedirectRefines blocked fold
      refinement.decoded.certificate.redirect)
    (htotal : State.BlockedFoldTotal blocked fold) :
    ∃ source blocker, fold source blocker := by
  have hvalid := refinement.check_sound hcheck
  have hclosed := State.roleClosed_of_saturated_normalized
      refinement.decoded.certificate.state refinement.decoded.certificate.rules
      refinement.decoded.certificate.roleClauses hvalid.2.1 hsaturated
  exact refinement.checked_rejection_has_fold blocked fold hcheck hclosed
    hredirect htotal

#print axioms DecodedRegularCoverRefinement.check_sound
#print axioms DecodedRegularCoverRefinement.checked_rejection_has_fold
#print axioms DecodedRegularCoverRefinement.checked_rejection_has_fold_of_saturated

end ContextCalculus.Hypertableau
