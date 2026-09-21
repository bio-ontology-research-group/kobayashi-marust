import ContextCalculus.FunctionalGroundDataProjection
namespace ContextCalculus.GroundDataOwnerClash
open FunctionalGroundDataProjection
/-- An asserted owner denotes itself in every interpretation. Distinct values
of one functional property therefore refute compatibility without a UNA. -/
theorem same_owner_incompatible {P I O D : Type}
    (facts : P → I → D → Prop) (denote : I → O) (functional : P → Prop)
    (p : P) (i : I) (v w : D) (hp : functional p)
    (hv : facts p i v) (hw : facts p i w) (different : v ≠ w) :
    ¬ Compatible facts denote functional := by
  intro compatible
  exact different (compatible p i i v w hp hv hw rfl)
#print axioms same_owner_incompatible
end ContextCalculus.GroundDataOwnerClash
