import Mathlib.Tactic

/-!
# Certified hypertableau input coverage

This module mirrors the fail-closed production gate applied before KM accepts
a hypertableau certificate.  The gate requires a complete frontend projection,
excludes ontology features that the certified projection does not represent,
and permits inverse roles together with number restrictions only when the
producer supplies the independently checked role-separation fact.
-/

namespace ContextCalculus.HypertableauCertifiedInput

/-- The summary fields consumed by the certified hypertableau input gate. -/
structure Coverage where
  dropped : Nat
  fenced : Nat
  inverse : Bool
  number : Bool
  inverseCardinalityRoleSeparable : Bool
  nominals : Bool
  nativeABox : Bool
  deriving DecidableEq, Repr

/-- The declarative condition required at the certified HT boundary. -/
def Valid (c : Coverage) : Prop :=
  c.dropped = 0 ∧
  c.fenced = 0 ∧
  c.nominals = false ∧
  c.nativeABox = false ∧
  (c.inverse = true ∧ c.number = true →
    c.inverseCardinalityRoleSeparable = true)

/-- Executable counterpart of the production Rust coverage check. -/
def check (c : Coverage) : Bool :=
  c.dropped == 0 &&
  c.fenced == 0 &&
  !c.nominals &&
  !c.nativeABox &&
  (!c.inverse || !c.number || c.inverseCardinalityRoleSeparable)

theorem check_eq_true_iff (c : Coverage) : check c = true ↔ Valid c := by
  simp only [check, Valid, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.or_eq_true]
  constructor
  · aesop
  · intro h
    cases hi : c.inverse <;> cases hn : c.number <;> simp_all

theorem accepted_projection_complete (c : Coverage) (h : check c = true) :
    c.dropped = 0 ∧ c.fenced = 0 := by
  exact ⟨(check_eq_true_iff c).mp h |>.1,
    (check_eq_true_iff c).mp h |>.2.1⟩

theorem accepted_excludes_unrepresented_features (c : Coverage)
    (h : check c = true) :
    c.nominals = false ∧ c.nativeABox = false := by
  exact ⟨(check_eq_true_iff c).mp h |>.2.2.1,
    (check_eq_true_iff c).mp h |>.2.2.2.1⟩

theorem accepted_inverse_cardinality_is_separated (c : Coverage)
    (h : check c = true) (hi : c.inverse = true) (hn : c.number = true) :
    c.inverseCardinalityRoleSeparable = true := by
  exact (check_eq_true_iff c).mp h |>.2.2.2.2 ⟨hi, hn⟩

end ContextCalculus.HypertableauCertifiedInput
