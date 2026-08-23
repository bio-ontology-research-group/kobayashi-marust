import ContextCalculus.ELCompletionPublication

/-!
# Executable ELC publication boundary

This module closes the final parser boundary around the V5 ELC certificate.
The native checker consumes `WireCertificate`, not an already decoded value,
so its public theorem must retain the exact successful decode as well as the
source-level publication semantics of that decoded certificate.
-/

namespace ContextCalculus.ELCompletion

/-- Acceptance by the executable wire checker yields the exact decoded
certificate and its complete source-level inconsistency and taxonomy contract. -/
theorem WireCertificate.check_publication_semantics
    (wire : WireCertificate) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCertificate wire.symbol_count,
      wire.decode = .ok decoded ∧ PublicationSemantics decoded := by
  unfold WireCertificate.check at hcheck
  cases hdecode : wire.decode with
  | error error => simp [hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.checkV5_publication_semantics ?_⟩
      simpa [hdecode] using hcheck

#print axioms WireCertificate.check_publication_semantics

end ContextCalculus.ELCompletion
