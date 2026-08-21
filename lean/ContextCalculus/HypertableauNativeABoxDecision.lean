import ContextCalculus.HypertableauNativeABoxProjection
import ContextCalculus.HypertableauEqualityCertificate
import ContextCalculus.HypertableauCardinalityDistinctCertificate

/-!
# Native-ABox hypertableau decision semantics

This module states the actual model-existence proposition for a normalized
TBox together with KM's native named-individual ABox. It then composes a checked
finite equality model, native-root seed preservation, explicit inequality
separation, singleton proxies, and negative role assertions into one witness of
that proposition.
-/

namespace ContextCalculus.Hypertableau

def NativeABox.SatisfiableWith
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    I.models ontology ∧ abox.models I value

/-- Semantic contract for an initial equality-refutation state. Every model of
the source ABox can be extended to values for all finite search nodes that
realize the exact initial state. A wire checker will establish this contract
from the ordered native roots and the absence of non-ABox seed facts. -/
def NativeABox.InitializesEqState
    (abox : NativeABox Individual Concept Role)
    (state : EqState Node Concept Role) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    abox.models I value → ∃ nodeValue : Node → Domain,
      state.RealizedBy I nodeValue

theorem FiniteEqRefutationTree.check_native_abox_unsatisfiable
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (hinitial : abox.InitializesEqState certificate.state)
    (hcheck : tree.check certificate = true) :
    ¬abox.SatisfiableWith certificate.base.ontology := by
  rintro ⟨Domain, I, value, hmodels, habox⟩
  rcases hinitial Domain I value habox with ⟨nodeValue, hrealized⟩
  exact tree.check_unsatisfiable certificate hcheck
    ⟨Domain, I, nodeValue, hmodels, hrealized⟩

def FiniteDistinctEqCertificate.apartSeparatedB
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.apart.all fun pair =>
    decide (certificate.base.representative pair.1 ≠
      certificate.base.representative pair.2)

theorem FiniteDistinctEqCertificate.apartSeparatedB_sound
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (hcheck : certificate.apartSeparatedB = true) :
    ∀ pair ∈ certificate.apart,
      ¬certificate.base.state.equiv pair.1 pair.2 := by
  simp only [FiniteDistinctEqCertificate.apartSeparatedB, List.all_eq_true,
    decide_eq_true_eq] at hcheck
  intro pair hpair hequivalent
  exact hcheck pair hpair
    ((certificate.base.equalityClosureValidB_sound hvalid pair.1 pair.2).1
      hequivalent)

theorem FiniteDistinctEqCertificate.checkEqSat_native_satisfiable
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (root : Individual → Fin nodeCount)
    (hseeded : abox.SeededIn certificate.state root)
    (hcheck : certificate.base.checkEqSat = true)
    (hapart : certificate.apartSeparatedB = true)
    (hsingletons : abox.ProxySingletons
      certificate.base.state.quotientCanonical
      (fun individual => Quotient.mk certificate.base.state.nodeSetoid
        (root individual)))
    (hnegative : abox.NegativeRoles
      certificate.base.state.quotientCanonical
      (fun individual => Quotient.mk certificate.base.state.nodeSetoid
        (root individual))) :
    abox.SatisfiableWith certificate.base.base.ontology := by
  let nodeValue : Fin nodeCount → certificate.base.state.QuotientDomain :=
    fun node => Quotient.mk certificate.base.state.nodeSetoid node
  have hbaseRealized : certificate.base.state.RealizedBy
      certificate.base.state.quotientCanonical nodeValue :=
    certificate.base.checkEqSat_realizes hcheck
  have hparts := hcheck
  simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hparts
  have hvalid : certificate.base.equalityClosureValidB = true :=
    hparts.1.1.1.1
  have hapartSound := certificate.apartSeparatedB_sound hvalid hapart
  have hdistinctRealized : certificate.state.RealizedBy
      certificate.base.state.quotientCanonical nodeValue := by
    refine ⟨hbaseRealized, ?_⟩
    intro left right hlisted hequal
    exact hapartSound (left, right) hlisted (Quotient.exact hequal)
  refine ⟨certificate.base.state.QuotientDomain,
    certificate.base.state.quotientCanonical,
    nodeValue ∘ root, certificate.base.checkEqSat_models hcheck, ?_⟩
  exact abox.models_of_seeded certificate.state root
    certificate.base.state.quotientCanonical nodeValue hseeded
    hdistinctRealized hsingletons hnegative

#print axioms FiniteDistinctEqCertificate.checkEqSat_native_satisfiable
#print axioms FiniteDistinctEqCertificate.apartSeparatedB_sound
#print axioms FiniteEqRefutationTree.check_native_abox_unsatisfiable

end ContextCalculus.Hypertableau
