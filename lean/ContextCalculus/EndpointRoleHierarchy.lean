import ContextCalculus.EndpointTransitivity
/-! Simultaneous closure preserves direct and inverse role inclusions.
The source guard closes the selected set upward along both orientations. -/
namespace ContextCalculus.EndpointTransitivity
variable {D : Type}

theorem reach_inclusion {R S : D → D → Prop}
    (included : ∀ a b, R a b → S a b) {a b : D}
    (path : Reach R a b) : Reach S a b := by
  induction path with
  | edge h => exact .edge (included _ _ h)
  | step h _ ih => exact .step (included _ _ h) ih

theorem reach_inverse_inclusion {R S : D → D → Prop}
    (included : ∀ a b, R a b → S b a) {a b : D}
    (path : Reach R a b) : Reach S b a := by
  induction path with
  | edge h => exact .edge (included _ _ h)
  | step h _ ih => exact reach_transitive ih (.edge (included _ _ h))

def closeIf (selected : Bool) (R : D → D → Prop) : D → D → Prop :=
  if selected then Reach R else R

theorem selective_inclusion {R S : D → D → Prop} (left right : Bool)
    (closedUpward : left = true → right = true)
    (included : ∀ a b, R a b → S a b) :
    ∀ a b, closeIf left R a b → closeIf right S a b := by
  cases left <;> cases right
  · exact included
  · exact fun _ _ h => .edge (included _ _ h)
  · exact False.elim (Bool.noConfusion (closedUpward rfl))
  · exact fun _ _ h => reach_inclusion included h

theorem selective_inverse_inclusion {R S : D → D → Prop} (left right : Bool)
    (closedUpward : left = true → right = true)
    (included : ∀ a b, R a b → S b a) :
    ∀ a b, closeIf left R a b → closeIf right S b a := by
  cases left <;> cases right
  · exact included
  · exact fun _ _ h => .edge (included _ _ h)
  · exact False.elim (Bool.noConfusion (closedUpward rfl))
  · exact fun _ _ h => reach_inverse_inclusion included h

#print axioms reach_inclusion
#print axioms reach_inverse_inclusion
#print axioms selective_inclusion
#print axioms selective_inverse_inclusion
end ContextCalculus.EndpointTransitivity
