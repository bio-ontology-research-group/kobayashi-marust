import ContextCalculus.HTDirectCommonSourceWire
import ContextCalculus.HTMixedCommonSourceWire
import ContextCalculus.HTBundleCommonSourceWire
import ContextCalculus.HTDirectCardinalityCommonSourceWire
import ContextCalculus.HTMixedCardinalityCommonSourceWire
import ContextCalculus.HTBundleCardinalityCommonSourceWire

/-!
# Unified executable HT common-source translation

Every production HT projection shape is checked here against the common
proper-term source used by routing. The constructor selects only the matching
decoder. Acceptance recovers the complete branch-specific taxonomy equivalence
and contributes no semantic premise of its own.
-/

namespace ContextCalculus.HTCommonRoutingWire

open ContextCalculus

inductive WireHTCommonSource where
  | direct (document : HTDirectCommonSourceWire.WireDirectCommonSource)
  | mixed (document : HTMixedCommonSourceWire.WireMixedCommonSource)
  | bundle (document : HTBundleCommonSourceWire.WireBundleCommonSource)
  | directCardinality
      (document : HTDirectCardinalityCommonSourceWire.WireDirectCardinalityCommonSource)
  | mixedCardinality
      (document : HTMixedCardinalityCommonSourceWire.WireMixedCardinalityCommonSource)
  | bundleCardinality
      (document : HTBundleCardinalityCommonSourceWire.WireBundleCardinalityCommonSource)
deriving Lean.FromJson, Lean.ToJson, Repr

def WireHTCommonSource.check : WireHTCommonSource → Except String Bool
  | .direct document => document.check
  | .mixed document => document.check
  | .bundle document => document.check
  | .directCardinality document => document.check
  | .mixedCardinality document => document.check
  | .bundleCardinality document => document.check

/-- The exact dependent semantic contract for each accepted source shape.
Queries range over the checked finite source signature, so the theorem covers
the complete taxonomy rather than one producer-selected coordinate. -/
def WireHTCommonSource.SemanticallyValid : WireHTCommonSource → Prop
  | .direct document =>
      ∀ decoded, document.decode = .ok decoded →
        ∀ sub sup : Fin decoded.projection.concepts.length,
          decoded.CommonEntails sub sup ↔
            Hypertableau.EntailsSub decoded.projection.target sub sup
  | .mixed document =>
      ∀ decoded, document.decode = .ok decoded →
        ∀ sub sup : Fin decoded.projection.concepts.length,
          decoded.CommonEntails sub sup ↔
            Hypertableau.EntailsSub decoded.projection.target sub sup
  | .bundle document =>
      ∀ decoded, document.decode = .ok decoded →
        ∀ sub sup : Fin decoded.projection.sourceConcepts.length,
          decoded.CommonEntails sub sup ↔
            Hypertableau.EntailsSub decoded.projection.target
              (decoded.projection.sourceTargets sub)
              (decoded.projection.sourceTargets sup)
  | .directCardinality document =>
      ∀ decoded, document.decode = .ok decoded →
        ∀ sub sup : Fin decoded.projection.concepts.length,
          decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup
  | .mixedCardinality document =>
      ∀ decoded, document.decode = .ok decoded →
        ∀ sub sup : Fin decoded.projection.mixed.concepts.length,
          decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup
  | .bundleCardinality document =>
      ∀ decoded, document.decode = .ok decoded →
        ∀ sub sup : Fin decoded.projection.bundle.sourceConcepts.length,
          decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup

theorem WireHTCommonSource.check_sound (wire : WireHTCommonSource)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  cases wire with
  | direct document =>
      intro decoded hdecode sub sup
      exact document.check_target_sound decoded hdecode hcheck sub sup
  | mixed document =>
      intro decoded hdecode sub sup
      exact document.check_sound decoded hdecode hcheck sub sup
  | bundle document =>
      intro decoded hdecode sub sup
      exact document.check_sound decoded hdecode hcheck sub sup
  | directCardinality document =>
      intro decoded hdecode sub sup
      exact document.check_sound decoded hdecode hcheck sub sup
  | mixedCardinality document =>
      intro decoded hdecode sub sup
      exact document.check_sound decoded hdecode hcheck sub sup
  | bundleCardinality document =>
      intro decoded hdecode sub sup
      exact document.check_sound decoded hdecode hcheck sub sup

#print axioms WireHTCommonSource.check_sound

end ContextCalculus.HTCommonRoutingWire
