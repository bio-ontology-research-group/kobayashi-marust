namespace ContextCalculus.SourceSubsumerClosure

universe u v w

/-- Named and structural top-level conjuncts used by the source closure. -/
inductive Atom (N : Type u) (S : Type v) where
  | named : N → Atom N S
  | structural : S → Atom N S

def holds {N : Type u} {S : Type v} {D : Type w}
    (named : N → D → Prop) (structural : S → D → Prop) : Atom N S → D → Prop
  | .named n => named n
  | .structural s => structural s

/-- Positive closure of asserted superclass conjuncts and established semantic
pairs. Providers are source inclusions from a conjunction to a named class.
No assumption about the ABox, cardinalities, or nominal independence is used. -/
inductive Closure {N : Type u} {S : Type v}
    (seed : N → Atom N S → Prop) (provider : List (Atom N S) → N → Prop) :
    N → Atom N S → Prop where
  | seed {n a} : seed n a → Closure seed provider n a
  | identity (n) : Closure seed provider n (.named n)
  | inherit {n m a} : Closure seed provider n (.named m) →
      Closure seed provider m a → Closure seed provider n a
  | definition {n m body} : provider body m →
      (∀ a, a ∈ body → Closure seed provider n a) →
      Closure seed provider n (.named m)

/-- Every derived conjunct holds in each model of the source providers and
initial facts. `inherit` covers named transitivity and structural inheritance;
`definition` covers conjunction introduction followed by the asserted inclusion. -/
theorem sound {N : Type u} {S : Type v} {D : Type w}
    (named : N → D → Prop) (structural : S → D → Prop)
    (seed : N → Atom N S → Prop) (provider : List (Atom N S) → N → Prop)
    (seed_sound : ∀ n a, seed n a → ∀ x, named n x → holds named structural a x)
    (provider_sound : ∀ body m, provider body m →
      ∀ x, (∀ a, a ∈ body → holds named structural a x) → named m x)
    {n a} (derived : Closure seed provider n a) :
    ∀ x, named n x → holds named structural a x := by
  induction derived with
  | seed h => exact seed_sound _ _ h
  | identity n => intro x hx; exact hx
  | inherit _ _ left right =>
      intro x hx
      exact right x (left x hx)
  | definition hp _ ih =>
      intro x hx
      exact provider_sound _ _ hp x (fun a ha => ih a ha x hx)

/-- Adding the closure cannot remove or add a model once the initial facts and
source providers hold in that model. This is model preservation, not a claim
that this search-free subset decides all OWL entailments. -/
theorem model_preserved {N : Type u} {S : Type v} {D : Type w}
    (named : N → D → Prop) (structural : S → D → Prop)
    (seed : N → Atom N S → Prop) (provider : List (Atom N S) → N → Prop)
    (provider_sound : ∀ body m, provider body m →
      ∀ x, (∀ a, a ∈ body → holds named structural a x) → named m x) :
    (∀ n a, seed n a → ∀ x, named n x → holds named structural a x) ↔
    (∀ n a, Closure seed provider n a → ∀ x, named n x → holds named structural a x) := by
  constructor
  · intro h n a derived
    exact sound named structural seed provider h provider_sound derived
  · intro h n a hs
    exact h n a (.seed hs)

#print axioms sound
#print axioms model_preserved
end ContextCalculus.SourceSubsumerClosure
