import ContextCalculus.HypertableauNativeABoxProjection

/-! An identity-only cache cannot discharge a positive foreign singleton
without representing the equality it requires. This uses the same native-ABox
model contract as the source-bound HT certificate; it assumes no unique names.
Incomplete cache entries must leave the equality to ordinary completion. -/
namespace ContextCalculus.Hypertableau

variable {Individual Concept Role Domain : Type}

theorem NativeABox.models.proxy_requires_owner_equality
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain)
    (model : abox.models I value) (owner target : Individual) (proxy : Concept)
    (bound : proxy ∈ abox.proxies target)
    (label : I.concept proxy (value owner)) : value owner = value target :=
  (model.1 target proxy bound (value owner)).mp label

theorem NativeABox.models.unmerged_cache_rejects_foreign_proxy
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain)
    (model : abox.models I value) (owner target : Individual) (proxy : Concept)
    (bound : proxy ∈ abox.proxies target)
    (unmerged : value owner ≠ value target) : ¬ I.concept proxy (value owner) := by
  intro label
  exact unmerged (model.proxy_requires_owner_equality abox I value owner target proxy bound label)

#print axioms NativeABox.models.proxy_requires_owner_equality
#print axioms NativeABox.models.unmerged_cache_rejects_foreign_proxy
end ContextCalculus.Hypertableau
