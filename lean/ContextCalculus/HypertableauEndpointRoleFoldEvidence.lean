import ContextCalculus.HypertableauEndpointRoleEvidence
import ContextCalculus.HypertableauRuntimeSearch

/-! # Connecting checked endpoint evidence to concrete blocker folds -/

namespace ContextCalculus.Hypertableau

/-- With the concrete blocker invariants, the non-identity redirect exposed by
checked endpoint evidence contains at least one actual fold. -/
theorem FiniteEndpointRoleEvidence.exists_fold_of_cover_only_check
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (evidence : FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount))
    (blocked : Fin nodeCount → Bool)
    (fold : Fin nodeCount → Fin nodeCount → Prop)
    (hcheck : evidence.check certificate = true)
    (hclosed : certificate.state.RoleClosed certificate.rules)
    (hraw : ¬certificate.state.edge evidence.role evidence.source
      evidence.target)
    (hredirect : State.BlockedRedirectRefines blocked fold certificate.redirect)
    (htotal : State.BlockedFoldTotal blocked fold) :
    ∃ source blocker, fold source blocker := by
  obtain ⟨source, hnonidentity⟩ :=
    evidence.exists_nonidentity_redirect_of_check certificate hcheck hclosed hraw
  cases hblocked : blocked source with
  | false => exact (hnonidentity (hredirect.1 source hblocked)).elim
  | true =>
      obtain ⟨blocker, hfold⟩ := htotal source hblocked
      exact ⟨source, blocker, hfold⟩

#print axioms FiniteEndpointRoleEvidence.exists_fold_of_cover_only_check

end ContextCalculus.Hypertableau
