import ContextCalculus.HTMixedCommonSourceWire
import ContextCalculus.HTDirectCardinalityCommonSourceWire
import ContextCalculus.HypertableauMixedCardinalityProjectionWire

/-!
# Mixed Skolem and cardinality common sources

Mixed HT sources already occupy a checked finite prefix of the common unary
function namespace. Cardinality witness functions are shifted beyond that
prefix. The semantic transport and merged-model construction below prove that
the two independently complete source families coexist without function-name
aliasing.
-/

namespace ContextCalculus.HTMixedCardinalityCommonSourceWire

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.Hypertableau
open ContextCalculus.HTMixedCommonSourceWire
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire
open ContextCalculus.HTCardinalityCheckerTermEmbedding

def shiftTermFunctions (offset : Nat) : FTerm → FTerm
  | .var index => .var index
  | .const index => .const index
  | .app function argument =>
      .app (offset + function) (shiftTermFunctions offset argument)

def shiftPredicateFunctions (offset : Nat) : FPred → FPred
  | .concept concept term => .concept concept (shiftTermFunctions offset term)
  | .role role source target =>
      .role role (shiftTermFunctions offset source)
        (shiftTermFunctions offset target)

def shiftLiteralFunctions (offset : Nat) : FLit → FLit
  | .P predicate => .P (shiftPredicateFunctions offset predicate)
  | .eq left right =>
      .eq (shiftTermFunctions offset left) (shiftTermFunctions offset right)
  | .ineq left right =>
      .ineq (shiftTermFunctions offset left) (shiftTermFunctions offset right)

def shiftClauseFunctions (offset : Nat) (clause : FCL) : FCL := {
  body := clause.body.map (shiftLiteralFunctions offset)
  head := clause.head.map (shiftLiteralFunctions offset)
}

def shiftOntologyFunctions (offset : Nat) (ontology : List FCL) : List FCL :=
  ontology.map (shiftClauseFunctions offset)

def functionView (model : TModel Domain) (offset : Nat) : TModel Domain where
  conc := model.conc
  rol := model.rol
  const := model.const
  fn function := model.fn (offset + function)

@[simp] theorem eval_shiftTermFunctions (model : TModel Domain)
    (assignment : Int → Domain) (offset : Nat) (term : FTerm) :
    model.evalT assignment (shiftTermFunctions offset term) =
      (functionView model offset).evalT assignment term := by
  induction term with
  | var index => rfl
  | const index => rfl
  | app function argument ih =>
      simp [shiftTermFunctions, TModel.evalT, functionView, ih]

@[simp] theorem eval_shiftLiteralFunctions (model : TModel Domain)
    (assignment : Int → Domain) (offset : Nat) (literal : FLit) :
    model.evalL assignment (shiftLiteralFunctions offset literal) ↔
      (functionView model offset).evalL assignment literal := by
  cases literal with
  | P predicate =>
      cases predicate <;>
        simp [shiftLiteralFunctions, shiftPredicateFunctions, TModel.evalL,
          functionView]
  | eq left right => simp [shiftLiteralFunctions, TModel.evalL]
  | ineq left right => simp [shiftLiteralFunctions, TModel.evalL]

theorem valid_shiftClauseFunctions_iff (model : TModel Domain)
    (offset : Nat) (clause : FCL) :
    valid model (shiftClauseFunctions offset clause) ↔
      valid (functionView model offset) clause := by
  constructor <;> intro hvalid assignment hbody
  · have hshiftedBody : ∀ literal ∈ (shiftClauseFunctions offset clause).body,
        model.evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
      exact (eval_shiftLiteralFunctions model assignment offset source).2
        (hbody source hsource)
    rcases hvalid assignment hshiftedBody with ⟨literal, hliteral, htrue⟩
    rcases List.mem_map.mp hliteral with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource,
      (eval_shiftLiteralFunctions model assignment offset source).1 htrue⟩
  · have hsourceBody : ∀ literal ∈ clause.body,
        (functionView model offset).evalL assignment literal := by
      intro literal hliteral
      exact (eval_shiftLiteralFunctions model assignment offset literal).1
        (hbody (shiftLiteralFunctions offset literal)
          (List.mem_map.mpr ⟨literal, hliteral, rfl⟩))
    rcases hvalid assignment hsourceBody with
      ⟨literal, hliteral, htrue⟩
    exact ⟨shiftLiteralFunctions offset literal,
      List.mem_map.mpr ⟨literal, hliteral, rfl⟩,
      (eval_shiftLiteralFunctions model assignment offset literal).2 htrue⟩

theorem models_shiftOntologyFunctions_iff (model : TModel Domain)
    (offset : Nat) (ontology : List FCL) :
    (∀ clause ∈ shiftOntologyFunctions offset ontology, valid model clause) ↔
      ∀ clause ∈ ontology, valid (functionView model offset) clause := by
  constructor <;> intro hmodels clause hclause
  · exact (valid_shiftClauseFunctions_iff model offset clause).1
      (hmodels (shiftClauseFunctions offset clause)
        (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact (valid_shiftClauseFunctions_iff model offset source).2
      (hmodels source hsource)

def mergeFunctions (offset : Nat)
    (prefixFunctions suffixFunctions : Nat → Domain → Domain) : Nat → Domain → Domain :=
  fun function source =>
    if function < offset then prefixFunctions function source
    else suffixFunctions (function - offset) source

@[simp] theorem mergeFunctions_prefix (offset : Nat)
    (prefixFunctions suffixFunctions : Nat → Domain → Domain) (function : Fin offset)
    (source : Domain) :
    mergeFunctions offset prefixFunctions suffixFunctions function.val source =
      prefixFunctions function.val source := by
  simp [mergeFunctions, function.isLt]

@[simp] theorem mergeFunctions_suffix (offset : Nat)
    (prefixFunctions suffixFunctions : Nat → Domain → Domain) (function : Nat)
    (source : Domain) :
    mergeFunctions offset prefixFunctions suffixFunctions (offset + function) source =
      suffixFunctions function source := by
  simp [mergeFunctions]

def mergedModel (offset : Nat) (prefixFunctions : Nat → Domain → Domain)
    (suffixModel : TModel Domain) : TModel Domain where
  conc := suffixModel.conc
  rol := suffixModel.rol
  const := suffixModel.const
  fn := mergeFunctions offset prefixFunctions suffixModel.fn

@[simp] theorem functionView_mergedModel (offset : Nat)
    (prefixFunctions : Nat → Domain → Domain) (suffixModel : TModel Domain) :
    functionView (mergedModel offset prefixFunctions suffixModel) offset = suffixModel := by
  rcases suffixModel with ⟨concepts, roles, constants, suffixFunctions⟩
  simp only [functionView, mergedModel]
  have hfunctions :
      (fun function => mergeFunctions offset prefixFunctions suffixFunctions
        (offset + function)) = suffixFunctions := by
    funext function source
    exact mergeFunctions_suffix offset prefixFunctions suffixFunctions function source
  rw [hfunctions]

structure WireMixedCardinalityCommonSource where
  version : Nat
  projection : WireMixedCardinalityProjection
deriving Lean.FromJson, Lean.ToJson, Repr

structure DecodedMixedCardinalityCommonSource where
  projection : DecodedMixedCardinalityProjection
  directClauses : ∀ clause ∈ projection.mixed.direct,
    clauseNoExistentials clause = true
  pairBodies : ∀ pair ∈ projection.mixed.pairs,
    pairNoExistentials pair = true

def WireMixedCardinalityCommonSource.decode
    (wire : WireMixedCardinalityCommonSource) :
    Except String DecodedMixedCardinalityCommonSource := do
  if wire.version != 1 then
    throw s!"unsupported mixed-cardinality common-source version {wire.version}"
  let projection ← wire.projection.decode
  if hdirect : ∀ clause ∈ projection.mixed.direct,
      clauseNoExistentials clause = true then
    if hpairs : ∀ pair ∈ projection.mixed.pairs,
        pairNoExistentials pair = true then
      return { projection, directClauses := hdirect, pairBodies := hpairs }
    else throw "mixed-cardinality Skolem body contains an existential atom"
  else throw "mixed-cardinality direct residual contains an existential atom"

def WireMixedCardinalityCommonSource.check
    (wire : WireMixedCardinalityCommonSource) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedCardinalityCommonSource.commonDirect
    (decoded : DecodedMixedCardinalityCommonSource) :=
  mapOntology decoded.projection.mixed.direct

def DecodedMixedCardinalityCommonSource.commonPairs
    (decoded : DecodedMixedCardinalityCommonSource) :=
  mapPairs decoded.projection.mixed.pairs

def DecodedMixedCardinalityCommonSource.natDefinitions
    (decoded : DecodedMixedCardinalityCommonSource) :=
  decoded.projection.definitions.map mapCardinalityDef

def DecodedMixedCardinalityCommonSource.natPairs
    (decoded : DecodedMixedCardinalityCommonSource) :=
  decoded.projection.semanticPairs.map mapPairedCardinality

def DecodedMixedCardinalityCommonSource.commonOntology
    (decoded : DecodedMixedCardinalityCommonSource) : List FCL :=
  HTSkolemPairCheckerTermEmbedding.encodeMixed decoded.commonDirect
      decoded.commonPairs ++
    shiftOntologyFunctions decoded.projection.mixed.functions.length
      (cardinalityClauses decoded.natDefinitions decoded.natPairs)

theorem DecodedMixedCardinalityCommonSource.directMixed
    (decoded : DecodedMixedCardinalityCommonSource) :
    HTSkolemPairCheckerTermEmbedding.DirectMixed decoded.commonDirect
      decoded.commonPairs := by
  constructor
  · intro clause hclause
    rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact direct_mapClause source (decoded.directClauses source hsource)
  · intro pair hpair
    rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
    exact direct_mapPair source (decoded.pairBodies source hsource)

def DecodedMixedCardinalityCommonSource.CommonEntails
    (decoded : DecodedMixedCardinalityCommonSource)
    (sub sup : Fin decoded.projection.mixed.concepts.length) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ decoded.commonOntology, valid model clause) →
      ∀ value, model.conc sub.val value → model.conc sup.val value

def DecodedMixedCardinalityCommonSource.FiniteSourceEntails
    (decoded : DecodedMixedCardinalityCommonSource)
    (sub sup : Fin decoded.projection.mixed.concepts.length) : Prop :=
  ∀ (Domain : Type)
    (I : Interp Domain (Fin decoded.projection.mixed.concepts.length)
      (Fin decoded.projection.mixed.roles.length))
    (functions : SkolemInterp Domain
      (Fin decoded.projection.mixed.functions.length)),
    I.models decoded.projection.mixed.direct →
    ModelsSkolemPairs I functions decoded.projection.mixed.pairs →
    I.modelsProjectedCardinalityDefs decoded.projection.definitions
      decoded.projection.semanticPairs →
      ∀ value, I.concept sub value → I.concept sup value

def DecodedMixedCardinalityCommonSource.TargetEntails
    (decoded : DecodedMixedCardinalityCommonSource)
    (sub sup : Fin decoded.projection.mixed.concepts.length) : Prop :=
  ∀ (Domain : Type)
    (I : Interp Domain (Fin decoded.projection.mixed.concepts.length)
      (Fin decoded.projection.mixed.roles.length)),
    (I.models decoded.projection.mixed.target ∧
      I.modelsPairedCardinalityTargets decoded.projection.definitions
        decoded.projection.semanticPairs) →
      ∀ value, I.concept sub value → I.concept sup value

theorem DecodedMixedCardinalityCommonSource.finiteSource_entails_iff_target
    (decoded : DecodedMixedCardinalityCommonSource)
    (sub sup : Fin decoded.projection.mixed.concepts.length) :
    decoded.FiniteSourceEntails sub sup ↔ decoded.TargetEntails sub sup := by
  constructor
  · intro hsource Domain I htarget value hsub
    let base : SkolemInterp Domain
        (Fin decoded.projection.mixed.functions.length) := ⟨fun _ _ => value⟩
    rcases (decoded.projection.models_source_iff_target I base).2 htarget with
      ⟨functions, hdirect, hpairs, hcardinality⟩
    exact hsource Domain I functions hdirect hpairs hcardinality value hsub
  · intro htarget Domain I functions hdirect hpairs hcardinality value hsub
    exact htarget Domain I
      ((decoded.projection.models_source_iff_target I functions).1
        ⟨functions, hdirect, hpairs, hcardinality⟩) value hsub

theorem DecodedMixedCardinalityCommonSource.common_entails_iff_finiteSource
    (decoded : DecodedMixedCardinalityCommonSource)
    (sub sup : Fin decoded.projection.mixed.concepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.FiniteSourceEntails sub sup := by
  constructor
  · intro hcommon Domain I functions hdirect hpairs hcardinality value hsub
    letI : Nonempty Domain := ⟨value⟩
    let natI := natInterp I
    let natFunctions := HTMixedCommonSourceWire.natFunctions functions
    have hcardNat : natI.modelsProjectedCardinalityDefs
        decoded.natDefinitions decoded.natPairs :=
      (modelsProjectedDefs_map_natInterp I decoded.projection.definitions
        decoded.projection.semanticPairs).2 hcardinality
    rcases projected_implies_exists_cardinalityClauses_model natI value
        decoded.natDefinitions decoded.natPairs hcardNat with
      ⟨cardinalityModel, hcardInterp, hcardClauses⟩
    let model := mergedModel decoded.projection.mixed.functions.length
      natFunctions.app cardinalityModel
    have hcardShifted : ∀ clause ∈ shiftOntologyFunctions
        decoded.projection.mixed.functions.length
          (cardinalityClauses decoded.natDefinitions decoded.natPairs),
        valid model clause := by
      apply (models_shiftOntologyFunctions_iff model
        decoded.projection.mixed.functions.length _).2
      simpa [model] using hcardClauses
    have hdirectNat : natI.models decoded.commonDirect := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (modelsClause_map_natInterp I source).2 (hdirect source hsource)
    have hpairsMerged : ModelsSkolemPairs
        (HTCheckerTermEmbedding.htInterp model)
        (HTSkolemPairCheckerTermEmbedding.skolemInterp model)
        decoded.commonPairs := by
      intro pair hpair
      rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
      have hpairNat := (models_mapPair_nat_iff I functions source).2
        (hpairs source hsource)
      change SkolemPairSpec.models natI natFunctions (mapPair source) at hpairNat
      rw [← hcardInterp] at hpairNat
      have hfn (sourceValue : Domain) :
          (HTSkolemPairCheckerTermEmbedding.skolemInterp model).app
              source.function.val sourceValue =
            natFunctions.app source.function.val sourceValue := by
        exact mergeFunctions_prefix decoded.projection.mixed.functions.length
          natFunctions.app cardinalityModel.fn source.function sourceValue
      rw [SkolemPairSpec.models, ModelsSkolemPair] at hpairNat ⊢
      simp only [mapPair] at hpairNat ⊢
      constructor
      · intro assignment hbody
        rw [hfn]
        exact hpairNat.1 assignment (by
          simpa [model, mergedModel, HTCheckerTermEmbedding.htInterp, mapPair]
            using hbody)
      · intro assignment hbody
        rw [hfn]
        exact hpairNat.2 assignment (by
          simpa [model, mergedModel, HTCheckerTermEmbedding.htInterp, mapPair]
            using hbody)
    have hdirectMerged : (HTCheckerTermEmbedding.htInterp model).models
        decoded.commonDirect := by
      rw [← hcardInterp] at hdirectNat
      simpa [model, mergedModel, HTCheckerTermEmbedding.htInterp] using hdirectNat
    have hmixed : ∀ clause ∈
        HTSkolemPairCheckerTermEmbedding.encodeMixed decoded.commonDirect
          decoded.commonPairs, valid model clause :=
      (HTSkolemPairCheckerTermEmbedding.models_mixed_encode_iff model
        decoded.commonDirect decoded.commonPairs decoded.directMixed).2
        ⟨hdirectMerged, hpairsMerged⟩
    have hmodels : ∀ clause ∈ decoded.commonOntology, valid model clause := by
      intro clause hclause
      simp only [DecodedMixedCardinalityCommonSource.commonOntology,
        List.mem_append] at hclause
      exact hclause.elim (hmixed clause) (hcardShifted clause)
    have hsubModel : model.conc sub.val value := by
      have hconcept := congrArg (fun interpretation => interpretation.concept)
        hcardInterp
      change cardinalityModel.conc = natI.concept at hconcept
      simpa [model, mergedModel, natI, natInterp, hconcept] using hsub
    have hresult := hcommon Domain model hmodels value hsubModel
    have hconcept := congrArg (fun interpretation => interpretation.concept)
      hcardInterp
    change cardinalityModel.conc = natI.concept at hconcept
    simpa [model, mergedModel, natI, natInterp, hconcept] using hresult
  · intro hfinite Domain model hmodels value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hmixedClauses : ∀ clause ∈
        HTSkolemPairCheckerTermEmbedding.encodeMixed decoded.commonDirect
          decoded.commonPairs, valid model clause := by
      intro clause hclause
      exact hmodels clause (by
        simp only [DecodedMixedCardinalityCommonSource.commonOntology,
          List.mem_append]
        exact Or.inl hclause)
    have hmixed := (HTSkolemPairCheckerTermEmbedding.models_mixed_encode_iff
      model decoded.commonDirect decoded.commonPairs decoded.directMixed).1
      hmixedClauses
    let natI := HTCheckerTermEmbedding.htInterp model
    let natFunctions := HTSkolemPairCheckerTermEmbedding.skolemInterp model
    let finI : Interp Domain (Fin decoded.projection.mixed.concepts.length)
        (Fin decoded.projection.mixed.roles.length) := finInterp natI
    let finFunctions : SkolemInterp Domain
        (Fin decoded.projection.mixed.functions.length) :=
      HTMixedCommonSourceWire.finFunctions natFunctions
    have hdirectFin : finI.models decoded.projection.mixed.direct := by
      intro clause hclause
      exact (modelsClause_map_finInterp natI clause).2
        (hmixed.1 (mapClause clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hpairsFin : ModelsSkolemPairs finI finFunctions
        decoded.projection.mixed.pairs := by
      intro pair hpair
      exact (models_mapPair_fin_iff natI natFunctions pair).2
        (hmixed.2 (mapPair pair) (List.mem_map.mpr ⟨pair, hpair, rfl⟩))
    have hcardShifted : ∀ clause ∈ shiftOntologyFunctions
        decoded.projection.mixed.functions.length
          (cardinalityClauses decoded.natDefinitions decoded.natPairs),
        valid model clause := by
      intro clause hclause
      exact hmodels clause (by
        simp only [DecodedMixedCardinalityCommonSource.commonOntology,
          List.mem_append]
        exact Or.inr hclause)
    have hcardCommon := (models_shiftOntologyFunctions_iff model
      decoded.projection.mixed.functions.length _).1 hcardShifted
    have hcardNat := models_cardinalityClauses_implies_projected
      (functionView model decoded.projection.mixed.functions.length)
      decoded.natDefinitions decoded.natPairs hcardCommon
    have hcardFin : finI.modelsProjectedCardinalityDefs
        decoded.projection.definitions decoded.projection.semanticPairs := by
      apply (modelsProjectedDefs_map_finInterp
        (HTCheckerTermEmbedding.htInterp
          (functionView model decoded.projection.mixed.functions.length))
        decoded.projection.definitions decoded.projection.semanticPairs).2
      simpa [functionView, natI] using hcardNat
    exact hfinite Domain finI finFunctions hdirectFin hpairsFin hcardFin value
      (by simpa [finI, finInterp, natI, HTCheckerTermEmbedding.htInterp] using hsub)

theorem DecodedMixedCardinalityCommonSource.entails_target_iff
    (decoded : DecodedMixedCardinalityCommonSource)
    (sub sup : Fin decoded.projection.mixed.concepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup :=
  (decoded.common_entails_iff_finiteSource sub sup).trans
    (decoded.finiteSource_entails_iff_target sub sup)

theorem WireMixedCardinalityCommonSource.check_sound
    (wire : WireMixedCardinalityCommonSource)
    (decoded : DecodedMixedCardinalityCommonSource)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.mixed.concepts.length) :
    decoded.CommonEntails sub sup ↔ decoded.TargetEntails sub sup :=
  decoded.entails_target_iff sub sup

#print axioms valid_shiftClauseFunctions_iff
#print axioms models_shiftOntologyFunctions_iff
#print axioms functionView_mergedModel
#print axioms DecodedMixedCardinalityCommonSource.entails_target_iff
#print axioms WireMixedCardinalityCommonSource.check_sound

end ContextCalculus.HTMixedCardinalityCommonSourceWire
