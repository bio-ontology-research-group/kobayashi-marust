import ContextCalculus.FunctionalGroundDataProjection

namespace ContextCalculus.FloatingDataIdentity

/-- OWL floating-point value identity is sorted by primitive datatype and
retains the IEEE sign bit of zero. NaN input is canonicalized before this key. -/
inductive Value where
  | single (bits : UInt32)
  | double (bits : UInt64)
  deriving DecidableEq

theorem primitive_spaces_disjoint (a : UInt32) (b : UInt64) :
    Value.single a ≠ Value.double b := by intro h; cases h

theorem single_signed_zeros_distinct :
    Value.single 0 ≠ Value.single 2147483648 := by decide

theorem double_signed_zeros_distinct :
    Value.double 0 ≠ Value.double 9223372036854775808 := by decide

/-- The existing exact functional projection rejects opposite signed zeros
at owners forced equal; it assumes no global unique-name condition. -/
theorem single_signed_zeros_incompatible
    {P I O : Type} (facts : P → I → Value → Prop) (denote : I → O)
    (functional : P → Prop) (p : P) (i j : I)
    (hp : functional p) (hi : facts p i (.single 0))
    (hj : facts p j (.single 2147483648)) (same : denote i = denote j) :
    ¬ FunctionalGroundDataProjection.Compatible facts denote functional := by
  intro h
  exact single_signed_zeros_distinct (h p i j _ _ hp hi hj same)

theorem cross_primitive_values_incompatible
    {P I O : Type} (facts : P → I → Value → Prop) (denote : I → O)
    (functional : P → Prop) (p : P) (i j : I) (a : UInt32) (b : UInt64)
    (hp : functional p) (hi : facts p i (.single a))
    (hj : facts p j (.double b)) (same : denote i = denote j) :
    ¬ FunctionalGroundDataProjection.Compatible facts denote functional := by
  intro h
  exact primitive_spaces_disjoint a b (h p i j _ _ hp hi hj same)

#print axioms single_signed_zeros_incompatible
#print axioms cross_primitive_values_incompatible
#print axioms double_signed_zeros_distinct
end ContextCalculus.FloatingDataIdentity
