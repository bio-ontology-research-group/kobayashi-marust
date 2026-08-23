import ContextCalculus.HypertableauSourceTaxonomyPublication
import ContextCalculus.HypertableauNativeABoxSourceDecisionWire

/-!
# Joint source-level HT classification certificates

Global consistency and taxonomy must be statements about one source problem.
The joint wire therefore carries the source projection and native ABox once.
The checker injects that shared problem into the untrusted global and taxonomy
evidence before invoking the existing semantic decoders.  It never trusts a
producer-supplied fingerprint or two independently checked documents.
-/

namespace ContextCalculus.Hypertableau

open Lean

def WireNativeABoxSeed.withABox
    (seed : WireNativeABoxSeed) (abox : WireNativeABox) : WireNativeABoxSeed :=
  { seed with abox }

def WireNativeABoxSatCertificate.withABox
    (certificate : WireNativeABoxSatCertificate) (abox : WireNativeABox) :
    WireNativeABoxSatCertificate :=
  { certificate with seed := certificate.seed.withABox abox }

def WireNativeABoxRefutation.withABox
    (refutation : WireNativeABoxRefutation) (abox : WireNativeABox) :
    WireNativeABoxRefutation :=
  { refutation with initial := refutation.initial.withABox abox }

def WireNativeABoxDecisionCertificate.withABox
    (decision : WireNativeABoxDecisionCertificate) (abox : WireNativeABox) :
    WireNativeABoxDecisionCertificate :=
  { decision with evidence := match decision.evidence with
    | .sat certificate => .sat (certificate.withABox abox)
    | .unsat refutation => .unsat (refutation.withABox abox) }

def WireNativeABoxTaxonomyDecision.withABox
    (decision : WireNativeABoxTaxonomyDecision) (abox : WireNativeABox) :
    WireNativeABoxTaxonomyDecision :=
  { decision with evidence := match decision.evidence with
    | .sat certificate => .sat (certificate.withABox abox)
    | .unsat initial tree => .unsat (initial.withABox abox) tree }

def WireNativeABoxTaxonomyMatrix.withABox
    (matrix : WireNativeABoxTaxonomyMatrix) (abox : WireNativeABox) :
    WireNativeABoxTaxonomyMatrix :=
  { matrix with
    concepts := matrix.concepts.map (·.withABox abox)
    subsumptions := matrix.subsumptions.map fun row =>
      row.map (·.withABox abox) }

def bindDirectSourceDecision
    (source : List WireDirectSourceClause) (abox : WireNativeABox)
    (decision : WireNativeABoxDecisionCertificate) :
    WireDirectNativeABoxDecisionCertificate :=
  let decision := decision.withABox abox
  { version := 1
    evidence := match decision.evidence with
    | .sat certificate => .sat { source, certificate }
    | .unsat refutation => .unsat { source, refutation } }

structure WireJointDirectNativeABoxClassification where
  version : Nat
  source : List WireDirectSourceClause
  abox : WireNativeABox
  global : WireNativeABoxDecisionCertificate
  taxonomy : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedJointDirectNativeABoxClassification where
  global : DecodedDirectNativeABoxDecision
  taxonomy : DecodedDirectNativeABoxTaxonomyMatrix

def WireJointDirectNativeABoxClassification.decode
    (wire : WireJointDirectNativeABoxClassification) :
    Except String DecodedJointDirectNativeABoxClassification := do
  if wire.version != 1 then
    throw s!"unsupported joint direct native ABox classification version {wire.version}"
  let global ← (bindDirectSourceDecision wire.source wire.abox wire.global).decode
  let taxonomy ← ({
    version := 1
    source := wire.source
    matrix := wire.taxonomy.withABox wire.abox
  } : WireDirectNativeABoxTaxonomyMatrix).decode
  return { global, taxonomy }

def WireJointDirectNativeABoxClassification.check
    (wire : WireJointDirectNativeABoxClassification) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedJointDirectNativeABoxClassification.SemanticallyValid
    (decoded : DecodedJointDirectNativeABoxClassification) : Prop :=
  decoded.global.SemanticallyValid ∧ decoded.taxonomy.SemanticallyValid

theorem DecodedJointDirectNativeABoxClassification.semantic_valid
    (decoded : DecodedJointDirectNativeABoxClassification) :
    decoded.SemanticallyValid :=
  ⟨decoded.global.semantic_valid, decoded.taxonomy.semantic_valid⟩

#print axioms DecodedJointDirectNativeABoxClassification.semantic_valid

/-! ## Mixed direct/Skolem-pair projection -/

def bindMixedSourceDecision
    (functions : List String) (direct : List WireDirectSourceClause)
    (pairs : List WireSkolemPair) (abox : WireNativeABox)
    (decision : WireNativeABoxDecisionCertificate) :
    WireMixedNativeABoxDecisionCertificate :=
  let decision := decision.withABox abox
  { version := 1
    evidence := match decision.evidence with
    | .sat certificate => .sat { functions, direct, pairs, certificate }
    | .unsat refutation => .unsat { functions, direct, pairs, refutation } }

structure WireJointMixedNativeABoxClassification where
  version : Nat
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  abox : WireNativeABox
  global : WireNativeABoxDecisionCertificate
  taxonomy : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedJointMixedNativeABoxClassification where
  global : DecodedMixedNativeABoxDecision
  taxonomy : DecodedMixedNativeABoxTaxonomyMatrix

def WireJointMixedNativeABoxClassification.decode
    (wire : WireJointMixedNativeABoxClassification) :
    Except String DecodedJointMixedNativeABoxClassification := do
  if wire.version != 1 then
    throw s!"unsupported joint mixed native ABox classification version {wire.version}"
  let global ← (bindMixedSourceDecision wire.functions wire.direct wire.pairs
    wire.abox wire.global).decode
  let taxonomy ← ({
    version := 1
    functions := wire.functions
    direct := wire.direct
    pairs := wire.pairs
    matrix := wire.taxonomy.withABox wire.abox
  } : WireMixedNativeABoxTaxonomyMatrix).decode
  return { global, taxonomy }

def WireJointMixedNativeABoxClassification.check
    (wire : WireJointMixedNativeABoxClassification) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedJointMixedNativeABoxClassification.SemanticallyValid
    (decoded : DecodedJointMixedNativeABoxClassification) : Prop :=
  decoded.global.SemanticallyValid ∧ decoded.taxonomy.SemanticallyValid

theorem DecodedJointMixedNativeABoxClassification.semantic_valid
    (decoded : DecodedJointMixedNativeABoxClassification) :
    decoded.SemanticallyValid :=
  ⟨decoded.global.semantic_valid, decoded.taxonomy.semantic_valid⟩

#print axioms DecodedJointMixedNativeABoxClassification.semantic_valid

/-! ## Skolem-bundle projection -/

def bindBundleSourceDecision
    (sourceConcepts functions : List String)
    (direct : List WireDirectSourceClause) (bundles : List WireSkolemBundle)
    (domainExtras : List WireBundleDomainExtra) (aboxSourceMap : List Nat)
    (abox : WireNativeABox) (decision : WireNativeABoxDecisionCertificate) :
    WireBundleNativeABoxDecisionCertificate :=
  let decision := decision.withABox abox
  { version := 1
    evidence := match decision.evidence with
    | .sat certificate => .sat {
        source_concepts := sourceConcepts, functions, direct, bundles
        domain_extras := domainExtras, abox_source_map := aboxSourceMap, certificate }
    | .unsat refutation => .unsat {
        source_concepts := sourceConcepts, functions, direct, bundles
        domain_extras := domainExtras, abox_source_map := aboxSourceMap, refutation } }

structure WireJointBundleNativeABoxClassification where
  version : Nat
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  abox_source_map : List Nat
  abox : WireNativeABox
  global : WireNativeABoxDecisionCertificate
  taxonomy : WireNativeABoxTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedJointBundleNativeABoxClassification where
  global : DecodedBundleNativeABoxDecision
  taxonomy : DecodedBundleNativeABoxTaxonomyMatrix

def WireJointBundleNativeABoxClassification.decode
    (wire : WireJointBundleNativeABoxClassification) :
    Except String DecodedJointBundleNativeABoxClassification := do
  if wire.version != 1 then
    throw s!"unsupported joint bundle native ABox classification version {wire.version}"
  let global ← (bindBundleSourceDecision wire.source_concepts wire.functions
    wire.direct wire.bundles wire.domain_extras wire.abox_source_map
    wire.abox wire.global).decode
  let taxonomy ← ({
    version := 1
    source_concepts := wire.source_concepts
    functions := wire.functions
    direct := wire.direct
    bundles := wire.bundles
    domain_extras := wire.domain_extras
    abox_source_map := wire.abox_source_map
    matrix := wire.taxonomy.withABox wire.abox
  } : WireBundleNativeABoxTaxonomyMatrix).decode
  return { global, taxonomy }

def WireJointBundleNativeABoxClassification.check
    (wire : WireJointBundleNativeABoxClassification) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedJointBundleNativeABoxClassification.SemanticallyValid
    (decoded : DecodedJointBundleNativeABoxClassification) : Prop :=
  decoded.global.SemanticallyValid ∧ decoded.taxonomy.SemanticallyValid

theorem DecodedJointBundleNativeABoxClassification.semantic_valid
    (decoded : DecodedJointBundleNativeABoxClassification) :
    decoded.SemanticallyValid :=
  ⟨decoded.global.semantic_valid, decoded.taxonomy.semantic_valid⟩

#print axioms DecodedJointBundleNativeABoxClassification.semantic_valid

/-! ## Shared cardinality evidence -/

def WireNativeABoxCardinalitySatCertificate.withABox
    (certificate : WireNativeABoxCardinalitySatCertificate) (abox : WireNativeABox) :
    WireNativeABoxCardinalitySatCertificate :=
  { certificate with seed := certificate.seed.withABox abox }

def WireNativeABoxCardinalityRefutation.withABox
    (refutation : WireNativeABoxCardinalityRefutation) (abox : WireNativeABox) :
    WireNativeABoxCardinalityRefutation :=
  { refutation with initial := refutation.initial.withABox abox }

def WireNativeABoxCardinalityDecisionCertificate.withABox
    (decision : WireNativeABoxCardinalityDecisionCertificate) (abox : WireNativeABox) :
    WireNativeABoxCardinalityDecisionCertificate :=
  { decision with evidence := match decision.evidence with
    | .sat certificate => .sat (certificate.withABox abox)
    | .unsat refutation => .unsat (refutation.withABox abox) }

def WireNativeABoxCardinalityTaxonomyDecision.withABox
    (decision : WireNativeABoxCardinalityTaxonomyDecision) (abox : WireNativeABox) :
    WireNativeABoxCardinalityTaxonomyDecision :=
  { decision with evidence := match decision.evidence with
    | .sat certificate => .sat (certificate.withABox abox)
    | .unsat initial definitions depth tree =>
        .unsat (initial.withABox abox) definitions depth tree }

def WireNativeABoxCardinalityTaxonomyMatrix.withABox
    (matrix : WireNativeABoxCardinalityTaxonomyMatrix) (abox : WireNativeABox) :
    WireNativeABoxCardinalityTaxonomyMatrix :=
  { matrix with
    concepts := matrix.concepts.map (·.withABox abox)
    subsumptions := matrix.subsumptions.map fun row =>
      row.map (·.withABox abox) }

/-! ## Direct cardinality projection -/

def bindDirectCardinalitySourceDecision
    (projection : WireDirectNativeABoxCardinalityTaxonomyProjection)
    (abox : WireNativeABox) (decision : WireNativeABoxCardinalityDecisionCertificate) :
    WireDirectNativeABoxCardinalityDecisionCertificate :=
  let decision := decision.withABox abox
  { version := 1
    evidence := match decision.evidence with
    | .sat certificate => .sat {
        source := projection.source, target := projection.target
        definitions := projection.definitions, exact_pairs := projection.exact_pairs
        certificate }
    | .unsat refutation => .unsat {
        source := projection.source, target := projection.target
        definitions := projection.definitions, exact_pairs := projection.exact_pairs
        refutation } }

structure WireJointDirectNativeABoxCardinalityClassification where
  version : Nat
  projection : WireDirectNativeABoxCardinalityTaxonomyProjection
  abox : WireNativeABox
  global : WireNativeABoxCardinalityDecisionCertificate
  taxonomy : WireNativeABoxCardinalityTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedJointDirectNativeABoxCardinalityClassification where
  global : DecodedDirectNativeABoxCardinalityDecision
  taxonomy : DecodedDirectNativeABoxCardinalityTaxonomyMatrix

def WireJointDirectNativeABoxCardinalityClassification.decode
    (wire : WireJointDirectNativeABoxCardinalityClassification) :
    Except String DecodedJointDirectNativeABoxCardinalityClassification := do
  if wire.version != 1 then
    throw s!"unsupported joint direct native ABox cardinality classification version {wire.version}"
  let global ← (bindDirectCardinalitySourceDecision wire.projection wire.abox
    wire.global).decode
  let sourceTaxonomy : WireDirectNativeABoxCardinalityTaxonomyMatrix := {
    version := 1
    projection := wire.projection
    matrix := wire.taxonomy.withABox wire.abox }
  let taxonomy ← sourceTaxonomy.decode
  return { global, taxonomy }

def WireJointDirectNativeABoxCardinalityClassification.check
    (wire : WireJointDirectNativeABoxCardinalityClassification) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedJointDirectNativeABoxCardinalityClassification.SemanticallyValid
    (decoded : DecodedJointDirectNativeABoxCardinalityClassification) : Prop :=
  decoded.global.SemanticallyValid ∧ decoded.taxonomy.SemanticallyValid

theorem DecodedJointDirectNativeABoxCardinalityClassification.semantic_valid
    (decoded : DecodedJointDirectNativeABoxCardinalityClassification) :
    decoded.SemanticallyValid :=
  ⟨decoded.global.semantic_valid, decoded.taxonomy.semantic_valid⟩

#print axioms DecodedJointDirectNativeABoxCardinalityClassification.semantic_valid

/-! ## Mixed cardinality projection -/

def bindMixedCardinalitySourceDecision
    (projection : WireMixedNativeABoxCardinalityTaxonomyProjection)
    (abox : WireNativeABox) (decision : WireNativeABoxCardinalityDecisionCertificate) :
    WireMixedNativeABoxCardinalityDecisionCertificate :=
  let decision := decision.withABox abox
  { version := 1
    evidence := match decision.evidence with
    | .sat certificate => .sat {
        functions := projection.functions, direct := projection.direct
        pairs := projection.pairs, definitions := projection.definitions
        exact_pairs := projection.exact_pairs, certificate }
    | .unsat refutation => .unsat {
        functions := projection.functions, direct := projection.direct
        pairs := projection.pairs, definitions := projection.definitions
        exact_pairs := projection.exact_pairs, refutation } }

structure WireJointMixedNativeABoxCardinalityClassification where
  version : Nat
  projection : WireMixedNativeABoxCardinalityTaxonomyProjection
  abox : WireNativeABox
  global : WireNativeABoxCardinalityDecisionCertificate
  taxonomy : WireNativeABoxCardinalityTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedJointMixedNativeABoxCardinalityClassification where
  global : DecodedMixedNativeABoxCardinalityDecision
  taxonomy : DecodedMixedNativeABoxCardinalityTaxonomyMatrix

def WireJointMixedNativeABoxCardinalityClassification.decode
    (wire : WireJointMixedNativeABoxCardinalityClassification) :
    Except String DecodedJointMixedNativeABoxCardinalityClassification := do
  if wire.version != 1 then
    throw s!"unsupported joint mixed native ABox cardinality classification version {wire.version}"
  let global ← (bindMixedCardinalitySourceDecision wire.projection wire.abox
    wire.global).decode
  let sourceTaxonomy : WireMixedNativeABoxCardinalityTaxonomyMatrix := {
    version := 1
    projection := wire.projection
    matrix := wire.taxonomy.withABox wire.abox }
  let taxonomy ← sourceTaxonomy.decode
  return { global, taxonomy }

def WireJointMixedNativeABoxCardinalityClassification.check
    (wire : WireJointMixedNativeABoxCardinalityClassification) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedJointMixedNativeABoxCardinalityClassification.SemanticallyValid
    (decoded : DecodedJointMixedNativeABoxCardinalityClassification) : Prop :=
  decoded.global.SemanticallyValid ∧ decoded.taxonomy.SemanticallyValid

theorem DecodedJointMixedNativeABoxCardinalityClassification.semantic_valid
    (decoded : DecodedJointMixedNativeABoxCardinalityClassification) :
    decoded.SemanticallyValid :=
  ⟨decoded.global.semantic_valid, decoded.taxonomy.semantic_valid⟩

#print axioms DecodedJointMixedNativeABoxCardinalityClassification.semantic_valid

/-! ## Skolem-bundle cardinality projection -/

def bindBundleCardinalitySourceDecision
    (projection : WireBundleNativeABoxCardinalityTaxonomyProjection)
    (abox : WireNativeABox) (decision : WireNativeABoxCardinalityDecisionCertificate) :
    WireBundleNativeABoxCardinalityDecisionCertificate :=
  let decision := decision.withABox abox
  { version := 1
    evidence := match decision.evidence with
    | .sat certificate => .sat {
        source_concepts := projection.source_concepts, functions := projection.functions
        direct := projection.direct, bundles := projection.bundles
        domain_extras := projection.domain_extras, definitions := projection.definitions
        exact_pairs := projection.exact_pairs, abox_source_map := projection.abox_source_map
        certificate }
    | .unsat refutation => .unsat {
        source_concepts := projection.source_concepts, functions := projection.functions
        direct := projection.direct, bundles := projection.bundles
        domain_extras := projection.domain_extras, definitions := projection.definitions
        exact_pairs := projection.exact_pairs, abox_source_map := projection.abox_source_map
        refutation } }

structure WireJointBundleNativeABoxCardinalityClassification where
  version : Nat
  projection : WireBundleNativeABoxCardinalityTaxonomyProjection
  abox : WireNativeABox
  global : WireNativeABoxCardinalityDecisionCertificate
  taxonomy : WireNativeABoxCardinalityTaxonomyMatrix
deriving FromJson, ToJson, Repr

structure DecodedJointBundleNativeABoxCardinalityClassification where
  global : DecodedBundleNativeABoxCardinalityDecision
  taxonomy : DecodedBundleNativeABoxCardinalityTaxonomyMatrix

def WireJointBundleNativeABoxCardinalityClassification.decode
    (wire : WireJointBundleNativeABoxCardinalityClassification) :
    Except String DecodedJointBundleNativeABoxCardinalityClassification := do
  if wire.version != 1 then
    throw s!"unsupported joint bundle native ABox cardinality classification version {wire.version}"
  let global ← (bindBundleCardinalitySourceDecision wire.projection wire.abox
    wire.global).decode
  let sourceTaxonomy : WireBundleNativeABoxCardinalityTaxonomyMatrix := {
    version := 1
    projection := wire.projection
    matrix := wire.taxonomy.withABox wire.abox }
  let taxonomy ← sourceTaxonomy.decode
  return { global, taxonomy }

def WireJointBundleNativeABoxCardinalityClassification.check
    (wire : WireJointBundleNativeABoxCardinalityClassification) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedJointBundleNativeABoxCardinalityClassification.SemanticallyValid
    (decoded : DecodedJointBundleNativeABoxCardinalityClassification) : Prop :=
  decoded.global.SemanticallyValid ∧ decoded.taxonomy.SemanticallyValid

theorem DecodedJointBundleNativeABoxCardinalityClassification.semantic_valid
    (decoded : DecodedJointBundleNativeABoxCardinalityClassification) :
    decoded.SemanticallyValid :=
  ⟨decoded.global.semantic_valid, decoded.taxonomy.semantic_valid⟩

#print axioms DecodedJointBundleNativeABoxCardinalityClassification.semantic_valid

/-! ## Unified executable native-ABox classification boundary -/

/-- Every production native-ABox classification shape.  The constructor only
selects the matching decoder; source identity is established by that decoder
injecting one shared source and ABox into both global and taxonomy evidence. -/
inductive WireJointNativeABoxClassification where
  | direct (document : WireJointDirectNativeABoxClassification)
  | mixed (document : WireJointMixedNativeABoxClassification)
  | bundle (document : WireJointBundleNativeABoxClassification)
  | directCardinality
      (document : WireJointDirectNativeABoxCardinalityClassification)
  | mixedCardinality
      (document : WireJointMixedNativeABoxCardinalityClassification)
  | bundleCardinality
      (document : WireJointBundleNativeABoxCardinalityClassification)
deriving FromJson, ToJson, Repr

def WireJointNativeABoxClassification.check :
    WireJointNativeABoxClassification → Except String Bool
  | .direct document => document.check
  | .mixed document => document.check
  | .bundle document => document.check
  | .directCardinality document => document.check
  | .mixedCardinality document => document.check
  | .bundleCardinality document => document.check

def WireJointNativeABoxClassification.SemanticallyValid :
    WireJointNativeABoxClassification → Prop
  | .direct document => ∃ decoded,
      document.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .mixed document => ∃ decoded,
      document.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .bundle document => ∃ decoded,
      document.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .directCardinality document => ∃ decoded,
      document.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .mixedCardinality document => ∃ decoded,
      document.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .bundleCardinality document => ∃ decoded,
      document.decode = .ok decoded ∧ decoded.SemanticallyValid

/-- Acceptance yields source-level global and taxonomy semantics for one exact
shared TBox projection and native ABox. No fingerprint or independently
supplied duplicate source is trusted. -/
theorem WireJointNativeABoxClassification.check_sound
    (wire : WireJointNativeABoxClassification)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  cases wire with
  | direct document =>
      unfold WireJointNativeABoxClassification.check
        WireJointDirectNativeABoxClassification.check at hcheck
      cases hdecode : document.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | mixed document =>
      unfold WireJointNativeABoxClassification.check
        WireJointMixedNativeABoxClassification.check at hcheck
      cases hdecode : document.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | bundle document =>
      unfold WireJointNativeABoxClassification.check
        WireJointBundleNativeABoxClassification.check at hcheck
      cases hdecode : document.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | directCardinality document =>
      unfold WireJointNativeABoxClassification.check
        WireJointDirectNativeABoxCardinalityClassification.check at hcheck
      cases hdecode : document.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | mixedCardinality document =>
      unfold WireJointNativeABoxClassification.check
        WireJointMixedNativeABoxCardinalityClassification.check at hcheck
      cases hdecode : document.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩
  | bundleCardinality document =>
      unfold WireJointNativeABoxClassification.check
        WireJointBundleNativeABoxCardinalityClassification.check at hcheck
      cases hdecode : document.decode with
      | error message => simp [hdecode] at hcheck
      | ok decoded => exact ⟨decoded, hdecode, decoded.semantic_valid⟩

#print axioms WireJointNativeABoxClassification.check_sound

end ContextCalculus.Hypertableau
