import ContextCalculus.EndpointRoleHierarchy
/-! Left-absorbing chains R o S <= S survive selective transitive closure. -/
namespace ContextCalculus.EndpointTransitivity
variable {D : Type}

theorem left_reach_absorption {R S : D → D → Prop}
    (absorb : ∀ a b c, R a b → S b c → S a c)
    {a b : D} (path : Reach R a b) : ∀ c, S b c → S a c := by
  induction path with
  | edge edge => exact fun c tail => absorb _ _ c edge tail
  | step edge _ ih => exact fun c tail => absorb _ _ c edge (ih c tail)

theorem left_absorption_reach_target {R S : D → D → Prop}
    (absorb : ∀ a b c, R a b → S b c → S a c)
    {a b c : D} (edge : R a b) (path : Reach S b c) : Reach S a c := by
  cases path with
  | edge tail => exact .edge (absorb _ _ _ edge tail)
  | step first tail => exact .step (absorb _ _ _ edge first) tail

theorem left_absorption_both_reach {R S : D → D → Prop}
    (absorb : ∀ a b c, R a b → S b c → S a c)
    {a b c : D} (left : Reach R a b) (right : Reach S b c) : Reach S a c := by
  cases right with
  | edge tail => exact .edge (left_reach_absorption absorb left _ tail)
  | step first tail => exact .step (left_reach_absorption absorb left _ first) tail

theorem selective_left_absorption {R S : D → D → Prop}
    (left right : Bool) (absorb : ∀ a b c, R a b → S b c → S a c) :
    ∀ a b c, closeIf left R a b → closeIf right S b c → closeIf right S a c := by
  cases left <;> cases right
  · exact absorb
  · exact fun _ _ _ h k => left_absorption_reach_target absorb h k
  · exact fun _ _ _ h k => left_reach_absorption absorb h _ k
  · exact fun _ _ _ h k => left_absorption_both_reach absorb h k

#print axioms left_reach_absorption
#print axioms left_absorption_reach_target
#print axioms left_absorption_both_reach
#print axioms selective_left_absorption
end ContextCalculus.EndpointTransitivity
