import ContextCalculus.HypertableauRuntimeSearch
import ContextCalculus.HypertableauRegularCertificate

/-!
# Equality-free blocked-open regular certificate production

This module composes the concrete blocker-aware terminal selector with the
regular certificate producer boundary. The finite certificate retains the raw
saturated terminal graph. Existential witnesses are read at blocker redirects,
so certificate production neither copies edges nor creates new clause matches.
-/

namespace ContextCalculus.Hypertableau

/-- A blocker-aware runtime terminal and checked fold metadata supply every
regular-model invariant. In particular, saturation transfers by state equality
because the serializer no longer mutates the completion graph. -/
theorem FiniteRegularCertificate.check_of_blocked_runtime_terminal
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (runtime : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (blocked : Fin nodeCount → Bool)
    (fold : Fin nodeCount → Fin nodeCount → Prop)
    (hstate : certificate.state = runtime)
    (hterminal : runtime.BlockedRuntimeTerminal certificate.residual blocked)
    (hwitnessRefines : runtime.BlockedWitnessRefines blocked fold)
    (hredirectRefines : State.BlockedRedirectRefines blocked fold
      certificate.redirect)
    (hauthorized : ∀ rule ∈ certificate.roleClauses,
      rule.Authorized certificate.rules)
    (hguarded : ∀ clause ∈ certificate.residual, clause.GuardedBody)
    (hheads : ∀ clause ∈ certificate.residual, ∀ atom ∈ clause.head,
      PathLiftableHead atom)
    (hcoverClosed : certificate.CoverClosed)
    (hcoverEdge : ∀ role source target,
      certificate.coverRelation role source target →
        certificate.state.edge role source target) :
    certificate.check = true := by
  have hclash : certificate.state.ClashFree := by
    rw [hstate]
    exact hterminal.clashFree
  have hwitness : certificate.state.RedirectWitnessComplete
      certificate.redirect := by
    rw [hstate]
    exact runtime.blockedRedirectWitnessComplete certificate.residual blocked
      fold certificate.redirect hterminal hwitnessRefines hredirectRefines
  have hsaturated : certificate.state.SaturatedFor certificate.residual := by
    rw [hstate]
    exact hterminal.saturatedFor
  exact certificate.check_of_producer_invariants hauthorized hguarded hheads
    hclash hwitness hcoverClosed hcoverEdge hsaturated

#print axioms FiniteRegularCertificate.check_of_blocked_runtime_terminal

end ContextCalculus.Hypertableau
