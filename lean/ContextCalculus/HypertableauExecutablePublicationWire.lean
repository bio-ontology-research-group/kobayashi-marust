import ContextCalculus.HypertableauSourceBoundOrdinaryGlobalWire
import ContextCalculus.HypertableauSourceBoundOrdinaryTaxonomyWire
import ContextCalculus.HypertableauSourceBoundCardinalityWire
import ContextCalculus.HypertableauSourceBoundNativeABoxWire

/-!
# Executable source-bound hypertableau publication routes

These tagged documents are the executable HT publication boundary.  Route
selection is data, not a theorem premise: every branch reruns the matching
source-normalization, production-run, and exact-payload-binding checker.
-/

namespace ContextCalculus.Hypertableau

inductive WireExecutableHTGlobalPublication where
  | ordinary (document : WireSourceBoundOrdinaryGlobal)
  | cardinality (document : WireSourceBoundCardinalityGlobal)
  | nativeABox (document : WireSourceBoundNativeABoxGlobal)
  | nativeABoxCardinality
      (document : WireSourceBoundNativeABoxCardinalityGlobal)
deriving Lean.FromJson, Lean.ToJson, Repr

def WireExecutableHTGlobalPublication.check :
    WireExecutableHTGlobalPublication → Bool
  | .ordinary document => document.check
  | .cardinality document => document.check
  | .nativeABox document => document.check
  | .nativeABoxCardinality document => document.check

def WireExecutableHTGlobalPublication.SemanticallyValid :
    WireExecutableHTGlobalPublication → Prop
  | .ordinary document =>
      document.production.check = true ∧ document.payloadBoundB = true ∧
        ∃ decoded : DecodedNormalizedCertificate,
          document.source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .cardinality document =>
      document.run.check = true ∧ document.payloadBoundB = true ∧
        ∃ decoded : DecodedNormalizedCertificate,
          document.source.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .nativeABox document =>
      document.source.SemanticallyValid ∧ document.run.check = true ∧
        document.payloadBoundB = true
  | .nativeABoxCardinality document =>
      document.source.SemanticallyValid ∧ document.run.check = true ∧
        document.payloadBoundB = true

theorem WireExecutableHTGlobalPublication.check_sound
    (wire : WireExecutableHTGlobalPublication) (hcheck : wire.check = true) :
    wire.SemanticallyValid := by
  cases wire with
  | ordinary document =>
      exact ⟨(document.check_sound hcheck).2.1,
        (document.check_sound hcheck).2.2.1,
        (document.check_sound hcheck).2.2.2⟩
  | cardinality document =>
      exact ⟨(document.check_sound hcheck).2.1,
        (document.check_sound hcheck).2.2.1,
        (document.check_sound hcheck).2.2.2⟩
  | nativeABox document => exact document.check_sound hcheck
  | nativeABoxCardinality document => exact document.check_sound hcheck

inductive WireExecutableHTTaxonomyPublication where
  | ordinary (document : WireSourceBoundOrdinaryTaxonomy)
  | cardinality (document : WireSourceBoundCardinalityTaxonomy)
  | nativeABox (document : WireSourceBoundNativeABoxTaxonomy)
  | nativeABoxCardinality
      (document : WireSourceBoundNativeABoxCardinalityTaxonomy)
deriving Lean.FromJson, Lean.ToJson, Repr

def WireExecutableHTTaxonomyPublication.check :
    WireExecutableHTTaxonomyPublication → Bool
  | .ordinary document => document.check
  | .cardinality document => document.check
  | .nativeABox document => document.check
  | .nativeABoxCardinality document => document.check

def WireExecutableHTTaxonomyPublication.SemanticallyValid :
    WireExecutableHTTaxonomyPublication → Prop
  | .ordinary document =>
      document.runs.check = true ∧ document.payloadBoundB = true ∧
        ∃ decoded : DecodedNormalizedTaxonomyCertificate,
          document.source.decode = .ok decoded ∧ decoded.SemanticallyComplete
  | .cardinality document =>
      document.runs.check = true ∧ document.payloadBoundB = true ∧
        ∃ decoded : DecodedNormalizedCardinalityTaxonomyCertificate,
          document.source.decode = .ok decoded ∧
            ∃ certificate : CompleteCardinalityTaxonomyCertificate
              decoded.normalization.source decoded.target.definitions
              decoded.target.named,
              certificate = decoded.semantic
  | .nativeABox document =>
      document.source.SemanticallyValid ∧ document.runs.check = true ∧
        document.payloadBoundB = true
  | .nativeABoxCardinality document =>
      document.source.SemanticallyValid ∧ document.runs.check = true ∧
        document.payloadBoundB = true

theorem WireExecutableHTTaxonomyPublication.check_sound
    (wire : WireExecutableHTTaxonomyPublication)
    (hcheck : wire.check = true) : wire.SemanticallyValid := by
  cases wire with
  | ordinary document =>
      exact ⟨(document.check_sound hcheck).2.1,
        (document.check_sound hcheck).2.2.1,
        (document.check_sound hcheck).2.2.2⟩
  | cardinality document =>
      exact ⟨(document.check_sound hcheck).2.1,
        (document.check_sound hcheck).2.2.1,
        (document.check_sound hcheck).2.2.2⟩
  | nativeABox document => exact document.check_sound hcheck
  | nativeABoxCardinality document => exact document.check_sound hcheck

#print axioms WireExecutableHTGlobalPublication.check_sound
#print axioms WireExecutableHTTaxonomyPublication.check_sound

end ContextCalculus.Hypertableau
