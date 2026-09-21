import ContextCalculus.GroundDataProjection
namespace ContextCalculus.GroundDataRangeClash
/-- A ground range violation refutes every data edge interpretation. -/
theorem no_extension_of_range_violation {P I O D : Type}
    (facts : P → I → D → Prop) (denote : I → O) (range : P → D → Prop)
    (p : P) (i : I) (v : D) (asserted : facts p i v)
    (outside : ¬ range p v) :
    ¬ ∃ edge : P → O → D → Prop,
      (∀ q j w, facts q j w → edge q (denote j) w) ∧
      (∀ q o w, edge q o w → range q w) := by
  rintro ⟨edge, contains, valid⟩
  exact outside (valid p (denote i) v (contains p i v asserted))
#print axioms no_extension_of_range_violation
end ContextCalculus.GroundDataRangeClash
