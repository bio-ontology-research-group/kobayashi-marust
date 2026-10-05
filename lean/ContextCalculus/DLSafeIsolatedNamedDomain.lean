/-!
Obligations for isolating named objects when projecting DL-safe rules.
A false body on every guarded valuation makes each rule true. Taxonomy
projection additionally requires a base-model extension preserving each query;
inactivity on the asserted facts alone does not establish that obligation.
-/
namespace ContextCalculus.DLSafeIsolatedNamedDomain

theorem inactive_rule {Valuation : Type}
    (guard body head : Valuation → Prop)
    (inactive : ∀ valuation, guard valuation → ¬body valuation) :
    ∀ valuation, guard valuation → body valuation → head valuation := by
  intro valuation guarded matched
  exact False.elim (inactive valuation guarded matched)

theorem inactive_rules {Rule Valuation : Type}
    (guard : Valuation → Prop) (body head : Rule → Valuation → Prop)
    (inactive : ∀ rule valuation, guard valuation → ¬body rule valuation) :
    ∀ rule valuation, guard valuation → body rule valuation → head rule valuation := by
  intro rule
  exact inactive_rule guard (body rule) (head rule) (inactive rule)

/-- Neither source-assertion evaluation nor one model can replace extension. -/
theorem classification_preserved {BaseModel FullModel : Type}
    (base : BaseModel → Prop) (full : FullModel → Prop)
    (baseQuery : BaseModel → Prop) (fullQuery : FullModel → Prop)
    (forget : FullModel → BaseModel)
    (projection : ∀ model, full model → base (forget model))
    (queryProjection : ∀ model, full model →
      (fullQuery model ↔ baseQuery (forget model)))
    (extension : ∀ model, base model →
      ∃ extended, full extended ∧ (fullQuery extended ↔ baseQuery model)) :
    (∀ model, full model → fullQuery model) ↔
      (∀ model, base model → baseQuery model) := by
  constructor
  · intro entailed model modeled
    obtain ⟨extended, modeledExtended, preserved⟩ := extension model modeled
    exact preserved.mp (entailed extended modeledExtended)
  · intro entailed model modeled
    exact (queryProjection model modeled).mpr (entailed (forget model) (projection model modeled))

#print axioms inactive_rule
#print axioms inactive_rules
#print axioms classification_preserved
end ContextCalculus.DLSafeIsolatedNamedDomain
