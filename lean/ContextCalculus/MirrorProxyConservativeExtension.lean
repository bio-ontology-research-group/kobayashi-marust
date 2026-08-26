/-!
# Conservative fresh-proxy extension for the mirror route

The mirror classifier replaces private negative existential names by fresh
positive proxies.  Its richer projection adds, for each fresh proxy `p`, the
one-way axiom `target p ⊆ p`; selected proxies additionally receive the reverse
axiom.  This file proves that the richer projection is conservative for every
old concept, independently of the contents of the old ontology.

The proof gives each fresh proxy exactly its target interpretation when an old
model is extended.  Conversely, forgetting the fresh predicates from any
extended model leaves the old interpretation unchanged.  Therefore a second
classification of the proxy-free projection cannot add semantic assurance for
old-signature taxonomy queries.
-/

namespace ContextCalculus.MirrorProxyConservativeExtension

universe u v w x

structure Interpretation (Concept : Type u) (Role : Type v) where
  Carrier : Type w
  concept : Concept → Carrier → Prop
  role : Role → Carrier → Carrier → Prop

structure ProxyInterpretation (Concept : Type u) (Role : Type v)
    (Proxy : Type x) extends Interpretation Concept Role where
  proxy : Proxy → Carrier → Prop

variable {Concept : Type u} {Role : Type v} {Proxy : Type x}

abbrev Ontology (Concept : Type u) (Role : Type v) :=
  Interpretation Concept Role → Prop

def OldEntails (ontology : Ontology Concept Role) (sub sup : Concept) : Prop :=
  ∀ interpretation, ontology interpretation → ∀ element,
    interpretation.concept sub element → interpretation.concept sup element

def SliceModel
    (ontology : Ontology Concept Role)
    (target : ∀ interpretation : Interpretation Concept Role,
      Proxy → interpretation.Carrier → Prop)
    (selected : Proxy → Prop)
    (interpretation : ProxyInterpretation Concept Role Proxy) : Prop :=
  ontology interpretation.toInterpretation ∧
  (∀ proxy element,
    target interpretation.toInterpretation proxy element →
      interpretation.proxy proxy element) ∧
  (∀ proxy, selected proxy → ∀ element,
    interpretation.proxy proxy element →
      target interpretation.toInterpretation proxy element)

def SliceEntails
    (ontology : Ontology Concept Role)
    (target : ∀ interpretation : Interpretation Concept Role,
      Proxy → interpretation.Carrier → Prop)
    (selected : Proxy → Prop)
    (sub sup : Concept) : Prop :=
  ∀ interpretation, SliceModel ontology target selected interpretation →
    ∀ element,
      interpretation.concept sub element → interpretation.concept sup element

def extend
    (target : ∀ interpretation : Interpretation Concept Role,
      Proxy → interpretation.Carrier → Prop)
    (interpretation : Interpretation Concept Role) :
    ProxyInterpretation Concept Role Proxy where
  toInterpretation := interpretation
  proxy := target interpretation

theorem extend_models_slice
    (ontology : Ontology Concept Role)
    (target : ∀ interpretation : Interpretation Concept Role,
      Proxy → interpretation.Carrier → Prop)
    (selected : Proxy → Prop)
    (interpretation : Interpretation Concept Role)
    (model : ontology interpretation) :
    SliceModel ontology target selected (extend target interpretation) := by
  refine ⟨model, ?_, ?_⟩
  · intro proxy element membership
    exact membership
  · intro proxy _ element membership
    exact membership

theorem oldEntails_iff_sliceEntails
    (ontology : Ontology Concept Role)
    (target : ∀ interpretation : Interpretation Concept Role,
      Proxy → interpretation.Carrier → Prop)
    (selected : Proxy → Prop)
    (sub sup : Concept) :
    OldEntails ontology sub sup ↔
      SliceEntails ontology target selected sub sup := by
  constructor
  · intro entails interpretation model element membership
    exact entails interpretation.toInterpretation model.1 element membership
  · intro entails interpretation model element membership
    exact entails (extend target interpretation)
      (extend_models_slice ontology target selected interpretation model)
      element membership

#print axioms oldEntails_iff_sliceEntails

end ContextCalculus.MirrorProxyConservativeExtension
