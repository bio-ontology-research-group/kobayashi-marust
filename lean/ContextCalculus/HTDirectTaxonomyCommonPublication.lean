import ContextCalculus.HypertableauSourceBoundOrdinaryTaxonomyWire
import ContextCalculus.HTDirectCommonSourceWire

/-!
# Direct HT taxonomy publications over the common routing source

This checker derives the common source from the normalized source embedded in
the source-bound publication itself. It therefore cannot accept a publication
and a common-source certificate for different ontologies. Sources containing
existential atoms fail closed and must use the mixed or bundle publication
adapter.
-/

namespace ContextCalculus.HTDirectTaxonomyCommonPublication

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire

inductive DecodedDirectTaxonomyPublication where
  | plain (decoded : DecodedNormalizedPlainTaxonomy)
      (direct : ∀ clause ∈ decoded.normalization.source,
        clauseNoExistentials clause = true)
  | mixed (decoded : DecodedNormalizedMixedTaxonomy)
      (direct : ∀ clause ∈ decoded.normalization.source,
        clauseNoExistentials clause = true)

def decodeDirectTaxonomy
    (wire : WireNormalizedTaxonomyCertificate) :
    Except String DecodedDirectTaxonomyPublication := do
  let decoded ← wire.decode
  match decoded with
  | .plain document =>
      if hdirect : ∀ clause ∈ document.normalization.source,
          clauseNoExistentials clause = true then
        return .plain document hdirect
      else throw "direct HT taxonomy source contains an existential atom"
  | .mixed document =>
      if hdirect : ∀ clause ∈ document.normalization.source,
          clauseNoExistentials clause = true then
        return .mixed document hdirect
      else throw "direct HT taxonomy source contains an existential atom"

def DecodedDirectTaxonomyPublication.CommonSemantics :
    DecodedDirectTaxonomyPublication → Prop
  | .plain decoded direct =>
      ∀ sub sup : Fin decoded.target.conceptCount,
        sub ∈ decoded.target.named → sup ∈ decoded.target.named →
        ((sub, sup) ∈ decoded.semantic.subsumptions ↔
          HTCheckerTermEmbedding.CommonEntailsSub
            (mapOntology decoded.normalization.source)
            sub.val sup.val)
  | .mixed decoded direct =>
      ∀ sub sup : Fin decoded.target.conceptCount,
        sub ∈ decoded.target.named → sup ∈ decoded.target.named →
        ((sub, sup) ∈ decoded.semantic.subsumptions ↔
          HTCheckerTermEmbedding.CommonEntailsSub
            (mapOntology decoded.normalization.source)
            sub.val sup.val)

theorem DecodedDirectTaxonomyPublication.common_semantics
    (decoded : DecodedDirectTaxonomyPublication) : decoded.CommonSemantics := by
  cases decoded with
  | plain decoded direct =>
      intro sub sup hsub hsup
      rw [decoded.subsumptions_exact sub sup hsub hsup]
      exact (entails_mapOntology_iff decoded.normalization.source direct sub sup).symm
  | mixed decoded direct =>
      intro sub sup hsub hsup
      rw [decoded.subsumptions_exact sub sup hsub hsup]
      exact (entails_mapOntology_iff decoded.normalization.source direct sub sup).symm

structure WireDirectTaxonomyPublication where
  version : Nat
  document : WireSourceBoundOrdinaryTaxonomy
deriving Lean.FromJson, Lean.ToJson, Repr

def WireDirectTaxonomyPublication.decode
    (wire : WireDirectTaxonomyPublication) :
    Except String DecodedDirectTaxonomyPublication :=
  if wire.version != 1 then
    .error s!"unsupported direct HT common-publication version {wire.version}"
  else if wire.document.check != true then
    .error "source-bound HT taxonomy publication rejected"
  else decodeDirectTaxonomy wire.document.source

def WireDirectTaxonomyPublication.check
    (wire : WireDirectTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

def WireDirectTaxonomyPublication.SemanticallyValid
    (wire : WireDirectTaxonomyPublication) : Prop :=
  wire.document.runs.check = true ∧
    wire.document.payloadBoundB = true ∧
    ∃ decoded : DecodedDirectTaxonomyPublication,
      wire.decode = .ok decoded ∧ decoded.CommonSemantics

theorem WireDirectTaxonomyPublication.check_sound
    (wire : WireDirectTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  have hdecodeOk : ∃ decoded, wire.decode = .ok decoded := by
    cases hdecode : wire.decode with
    | error message =>
        simp [WireDirectTaxonomyPublication.check, hdecode] at hcheck
    | ok decoded => exact ⟨decoded, rfl⟩
  rcases hdecodeOk with ⟨decoded, hdecode⟩
  have hdocument : wire.document.check = true := by
    cases hdocument : wire.document.check with
    | true => rfl
    | false =>
        cases hversion : wire.version != 1 <;>
          simp [WireDirectTaxonomyPublication.decode, hversion, hdocument] at hdecode
  have hsourceBound := wire.document.check_sound hdocument
  exact ⟨hsourceBound.2.1, hsourceBound.2.2.1, decoded,
    hdecode, decoded.common_semantics⟩

#print axioms DecodedDirectTaxonomyPublication.common_semantics
#print axioms WireDirectTaxonomyPublication.check_sound

end ContextCalculus.HTDirectTaxonomyCommonPublication
