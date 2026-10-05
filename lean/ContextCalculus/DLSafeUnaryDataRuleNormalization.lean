/-!
A unary DL-safe concrete rule is equivalent to a named-object implication with
one existential tuple of data witnesses. The tuple remains shared across all
body tests. This theorem does not justify separate existential tests, closed
world data evaluation, or publishing an unsupported concrete-domain answer.
-/
namespace ContextCalculus.DLSafeUnaryDataRuleNormalization
variable {Object Data : Type}
theorem data_assertion_iff_singleton_witness (role : Object → Data → Prop)
    (object : Object) (value : Data) :
    role object value ↔ ∃ witness, role object witness ∧ witness = value := by
  constructor
  · intro assertion
    exact ⟨value, assertion, rfl⟩
  · rintro ⟨witness, assertion, rfl⟩
    exact assertion
/-- Constant data atoms can be defined as private classes without changing
    any rule instance, including rules with several joined object variables. -/
theorem constant_data_body_definition_iff {Valuation : Type}
    (role : Object → Data → Prop) (value : Data)
    (subject : Valuation → Object) (guard rest conclusion : Valuation → Prop)
    (defined : Object → Prop)
    (definition : ∀ object, defined object ↔
      ∃ witness, role object witness ∧ witness = value) :
    (∀ binding, guard binding → rest binding →
      role (subject binding) value → conclusion binding) ↔
    (∀ binding, guard binding → rest binding →
      defined (subject binding) → conclusion binding) := by
  constructor
  · intro rule binding hg hr hd
    exact rule binding hg hr
      ((data_assertion_iff_singleton_witness role _ value).mpr
        ((definition _).mp hd))
  · intro rule binding hg hr hd
    exact rule binding hg hr ((definition _).mpr
      ((data_assertion_iff_singleton_witness role _ value).mp hd))
theorem constant_data_head_definition_iff {Valuation : Type}
    (role : Object → Data → Prop) (value : Data)
    (subject : Valuation → Object) (premise : Valuation → Prop)
    (defined : Object → Prop)
    (definition : ∀ object, defined object ↔
      ∃ witness, role object witness ∧ witness = value) :
    (∀ binding, premise binding → role (subject binding) value) ↔
    (∀ binding, premise binding → defined (subject binding)) := by
  constructor
  · intro rule binding hp
    exact (definition _).mpr
      ((data_assertion_iff_singleton_witness role _ value).mp (rule binding hp))
  · intro rule binding hp
    exact (data_assertion_iff_singleton_witness role _ value).mpr
      ((definition _).mp (rule binding hp))
/-- Self-role bodies and constant data heads preserve every named rule instance. -/
theorem self_role_constant_data_head_iff
    (named : Object → Prop) (objectRole : Object → Object → Prop)
    (dataRole : Object → Data → Prop) (value : Data) :
    (∀ x, named x → objectRole x x → dataRole x value) ↔
      (∀ x, named x → objectRole x x →
        ∃ witness, dataRole x witness ∧ witness = value) := by
  constructor
  · intro rule x hn hr
    exact (data_assertion_iff_singleton_witness dataRole x value).mp (rule x hn hr)
  · intro rule x hn hr
    exact (data_assertion_iff_singleton_witness dataRole x value).mpr (rule x hn hr)
def sourceRule (named conditions conclusion : Object → Prop)
    (dataBody : Object → Data → Prop) : Prop :=
  ∀ x value, named x → conditions x → dataBody x value → conclusion x
def normalizedRule (named conditions conclusion : Object → Prop)
    (dataBody : Object → Data → Prop) : Prop :=
  ∀ x, named x → conditions x → (∃ value, dataBody x value) → conclusion x
theorem shared_witness_rule_iff
    (named conditions conclusion : Object → Prop)
    (dataBody : Object → Data → Prop) :
    sourceRule named conditions conclusion dataBody ↔
      normalizedRule named conditions conclusion dataBody := by
  constructor
  · intro rule x hn hc witness
    obtain ⟨value, hv⟩ := witness
    exact rule x value hn hc hv
  · intro rule x value hn hc hv
    exact rule x hn hc ⟨value, hv⟩
theorem theory_models_preserved (base : Prop)
    (named conditions conclusion : Object → Prop)
    (dataBody : Object → Data → Prop) :
    (base ∧ sourceRule named conditions conclusion dataBody) ↔
      (base ∧ normalizedRule named conditions conclusion dataBody) := by
  constructor
  · intro h
    exact ⟨h.1, (shared_witness_rule_iff named conditions conclusion dataBody).mp h.2⟩
  · intro h
    exact ⟨h.1, (shared_witness_rule_iff named conditions conclusion dataBody).mpr h.2⟩
#print axioms self_role_constant_data_head_iff
#print axioms constant_data_body_definition_iff
#print axioms constant_data_head_definition_iff
#print axioms shared_witness_rule_iff
#print axioms data_assertion_iff_singleton_witness
#print axioms theory_models_preserved
end ContextCalculus.DLSafeUnaryDataRuleNormalization
