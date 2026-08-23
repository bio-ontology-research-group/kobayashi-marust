import ContextCalculus.HTDirectCommonSourceWire
import ContextCalculus.HTSkolemPairCheckerTermEmbedding
import ContextCalculus.HypertableauMixedProjectionWire

/-!
# Executable mixed HT source adapter

This composes the checked finite-ID mixed projection with the exact proper-term
encoding of its direct residual and shared unary Skolem pairs.  The resulting
wire theorem speaks about the same common source semantics as ELC, CB, and the
direct HT adapter.
-/

namespace ContextCalculus.HTMixedCommonSourceWire

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTSkolemPairCheckerTermEmbedding
open Lean

def mapPair
    (pair : SkolemPairSpec (Fin nvars) (Fin concepts) (Fin roles) (Fin functions)) :
    SkolemPairSpec Nat Nat Nat Nat where
  body := pair.body.map mapAtom
  source := pair.source.val
  function := pair.function.val
  role := pair.role.val
  filler := ⟨pair.filler.concept.val, pair.filler.neg⟩

def mapPairs
    (pairs : List
      (SkolemPairSpec (Fin nvars) (Fin concepts) (Fin roles) (Fin functions))) :
    List (SkolemPairSpec Nat Nat Nat Nat) := pairs.map mapPair

def pairNoExistentials
    (pair : SkolemPairSpec Variable Concept Role Function) : Bool :=
  pair.body.all noExistential

theorem direct_mapPair
    (pair : SkolemPairSpec (Fin nvars) (Fin concepts) (Fin roles) (Fin functions))
    (hcheck : pairNoExistentials pair = true) :
    HTSkolemPairCheckerTermEmbedding.Direct (mapPair pair) := by
  intro atom hatom
  rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
  have hall := List.all_eq_true.mp hcheck source hsource
  cases source <;> simp_all [pairNoExistentials, noExistential,
    HTCheckerTermEmbedding.directAtom, mapAtom]

def finFunctions (functions : SkolemInterp Domain Nat) :
    SkolemInterp Domain (Fin count) where
  app function := functions.app function.val

noncomputable def natFunctions [Nonempty Domain]
    (functions : SkolemInterp Domain (Fin count)) : SkolemInterp Domain Nat where
  app function value :=
    if h : function < count then functions.app ⟨function, h⟩ value
    else Classical.choice inferInstance

@[simp] theorem natFunctions_fin [Nonempty Domain]
    (functions : SkolemInterp Domain (Fin count))
    (function : Fin count) (value : Domain) :
    (natFunctions functions).app function.val value = functions.app function value := by
  simp [natFunctions]

private theorem holdsBody_map_nat [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (assignment : Fin nvars → Domain)
    (body : List (Atom (Fin nvars) (Fin concepts) (Fin roles))) :
    HoldsBody (natInterp interpretation)
        (fun index => if h : index < nvars then assignment ⟨index, h⟩
          else Classical.choice inferInstance)
        (body.map mapAtom) ↔ HoldsBody interpretation assignment body := by
  constructor
  · intro hbody atom hatom
    exact (satAtom_map_natInterp interpretation assignment atom).1
      (hbody (mapAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
  · intro hbody mapped hmapped
    rcases List.mem_map.mp hmapped with ⟨source, hsource, rfl⟩
    exact (satAtom_map_natInterp interpretation assignment source).2
      (hbody source hsource)

private theorem holdsBody_map_fin [Nonempty Domain]
    (interpretation : Interp Domain Nat Nat) (assignment : Nat → Domain)
    (body : List (Atom (Fin nvars) (Fin concepts) (Fin roles))) :
    HoldsBody (finInterp interpretation) (fun index => assignment index.val) body ↔
      HoldsBody interpretation assignment (body.map mapAtom) := by
  constructor <;> intro hbody atom hatom
  · rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
    exact (satAtom_map_finInterp interpretation assignment source).1
      (hbody source hsource)
  · exact (satAtom_map_finInterp interpretation assignment atom).2
      (hbody (mapAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))

theorem models_mapPair_nat_iff [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (functions : SkolemInterp Domain (Fin functionCount))
    (pair : SkolemPairSpec (Fin nvars) (Fin concepts) (Fin roles)
      (Fin functionCount)) :
    (mapPair pair).models (natInterp interpretation) (natFunctions functions) ↔
      pair.models interpretation functions := by
  constructor
  · intro hpair
    constructor
    · intro assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hmapped := hpair.1 extension
        ((holdsBody_map_nat interpretation assignment pair.body).2 hbody)
      simpa [mapPair, extension, natInterp] using hmapped
    · intro assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hmapped := hpair.2 extension
        ((holdsBody_map_nat interpretation assignment pair.body).2 hbody)
      simpa [mapPair, extension, natInterp, Interp.satLit] using hmapped
  · intro hpair
    constructor
    · intro assignment hbody
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody : HoldsBody interpretation restricted pair.body := by
        apply (holdsBody_map_nat interpretation restricted pair.body).1
        intro atom hatom
        have hmapped := hbody atom hatom
        rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
        apply (satAtom_map_assignment_congr interpretation assignment
          (fun index => if h : index < nvars then restricted ⟨index, h⟩
            else Classical.choice inferInstance)
          (by intro index; simp [restricted]) source).1
        exact hmapped
      have hresult := hpair.1 restricted hsourceBody
      simpa [mapPair, restricted, natInterp] using hresult
    · intro assignment hbody
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody : HoldsBody interpretation restricted pair.body := by
        apply (holdsBody_map_nat interpretation restricted pair.body).1
        intro atom hatom
        rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
        apply (satAtom_map_assignment_congr interpretation assignment
          (fun index => if h : index < nvars then restricted ⟨index, h⟩
            else Classical.choice inferInstance)
          (by intro index; simp [restricted]) source).1
        exact hbody (mapAtom source) (List.mem_map.mpr ⟨source, hsource, rfl⟩)
      have hresult := hpair.2 restricted hsourceBody
      simpa [mapPair, restricted, natInterp, Interp.satLit] using hresult

theorem models_mapPair_fin_iff [Nonempty Domain]
    (interpretation : Interp Domain Nat Nat) (functions : SkolemInterp Domain Nat)
    (pair : SkolemPairSpec (Fin nvars) (Fin concepts) (Fin roles)
      (Fin functionCount)) :
    pair.models (finInterp interpretation) (finFunctions functions) ↔
      (mapPair pair).models interpretation functions := by
  constructor
  · intro hpair
    constructor
    · intro assignment hbody
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody := (holdsBody_map_fin interpretation assignment pair.body).2 hbody
      have hresult := hpair.1 restricted hsourceBody
      simpa [mapPair, restricted, finInterp, finFunctions] using hresult
    · intro assignment hbody
      let restricted : Fin nvars → Domain := fun index => assignment index.val
      have hsourceBody := (holdsBody_map_fin interpretation assignment pair.body).2 hbody
      have hresult := hpair.2 restricted hsourceBody
      simpa [mapPair, restricted, finInterp, finFunctions, Interp.satLit] using hresult
  · intro hpair
    constructor
    · intro assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hmappedBody : HoldsBody interpretation extension (pair.body.map mapAtom) := by
        apply (holdsBody_map_fin interpretation extension pair.body).1
        simpa [extension] using hbody
      have hresult := hpair.1 extension hmappedBody
      simpa [mapPair, extension, finInterp, finFunctions] using hresult
    · intro assignment hbody
      let extension : Nat → Domain := fun index =>
        if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
      have hmappedBody : HoldsBody interpretation extension (pair.body.map mapAtom) := by
        apply (holdsBody_map_fin interpretation extension pair.body).1
        simpa [extension] using hbody
      have hresult := hpair.2 extension hmappedBody
      simpa [mapPair, extension, finInterp, finFunctions, Interp.satLit] using hresult

structure WireMixedCommonSource where
  version : Nat
  projection : WireMixedProjection
deriving FromJson, ToJson, Repr

structure DecodedMixedCommonSource where
  projection : DecodedMixedProjection
  directClauses : ∀ clause ∈ projection.direct, clauseNoExistentials clause = true
  pairBodies : ∀ pair ∈ projection.pairs, pairNoExistentials pair = true

def WireMixedCommonSource.decode (wire : WireMixedCommonSource) :
    Except String DecodedMixedCommonSource := do
  if wire.version != 1 then
    throw s!"unsupported mixed common-source version {wire.version}"
  let projection ← wire.projection.decode
  if hdirect : ∀ clause ∈ projection.direct, clauseNoExistentials clause = true then
    if hpairs : ∀ pair ∈ projection.pairs, pairNoExistentials pair = true then
      return { projection, directClauses := hdirect, pairBodies := hpairs }
    else throw "mixed common-source Skolem body contains an existential atom"
  else throw "mixed common-source direct residual contains an existential atom"

def WireMixedCommonSource.check (wire : WireMixedCommonSource) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedCommonSource.commonDirect (decoded : DecodedMixedCommonSource) :=
  mapOntology decoded.projection.direct

def DecodedMixedCommonSource.commonPairs (decoded : DecodedMixedCommonSource) :=
  mapPairs decoded.projection.pairs

theorem DecodedMixedCommonSource.directMixed
    (decoded : DecodedMixedCommonSource) :
    DirectMixed decoded.commonDirect decoded.commonPairs := by
  constructor
  · intro clause hclause
    rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact direct_mapClause source (decoded.directClauses source hsource)
  · intro pair hpair
    rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
    exact direct_mapPair source (decoded.pairBodies source hsource)

def DecodedMixedCommonSource.CommonEntails (decoded : DecodedMixedCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) : Prop :=
  CommonEntailsSub decoded.commonDirect decoded.commonPairs sub.val sup.val

def FiniteSourceEntails (decoded : DecodedMixedCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) : Prop :=
  ∀ (Domain : Type)
    (interpretation : Interp Domain (Fin decoded.projection.concepts.length)
      (Fin decoded.projection.roles.length))
    (functions : SkolemInterp Domain (Fin decoded.projection.functions.length)),
    interpretation.models decoded.projection.direct →
      ModelsSkolemPairs interpretation functions decoded.projection.pairs →
      ∀ value, interpretation.concept sub value → interpretation.concept sup value

theorem DecodedMixedCommonSource.entails_iff
    (decoded : DecodedMixedCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔ FiniteSourceEntails decoded sub sup := by
  change HTSkolemPairCheckerTermEmbedding.CommonEntailsSub
      decoded.commonDirect decoded.commonPairs sub.val sup.val ↔
    FiniteSourceEntails decoded sub sup
  rw [entailsSub_mixed_encode_iff decoded.commonDirect decoded.commonPairs
    decoded.directMixed sub.val sup.val]
  constructor
  · intro hnat Domain interpretation functions hdirect hpairs value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hresult := hnat Domain (natInterp interpretation) (natFunctions functions)
      (by
        intro clause hclause
        rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
        exact (modelsClause_map_natInterp interpretation source).2
          (hdirect source hsource))
      (by
        intro pair hpair
        rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
        exact (models_mapPair_nat_iff interpretation functions source).2
          (hpairs source hsource)) value (by simpa using hsub)
    simpa using hresult
  · intro hfin Domain interpretation functions hdirect hpairs value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hresult := hfin Domain (finInterp interpretation) (finFunctions functions)
      (by
        intro clause hclause
        exact (modelsClause_map_finInterp interpretation clause).2
          (hdirect (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩)))
      (by
        intro pair hpair
        exact (models_mapPair_fin_iff interpretation functions pair).2
          (hpairs (mapPair pair) (List.mem_map.mpr ⟨pair, hpair, rfl⟩)))
      value (by simpa [finInterp] using hsub)
    simpa [finInterp] using hresult

theorem DecodedMixedCommonSource.finiteSource_entails_iff_target
    (decoded : DecodedMixedCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    FiniteSourceEntails decoded sub sup ↔
      EntailsSub decoded.projection.target sub sup := by
  constructor
  · intro hsource Domain interpretation htarget value hsub
    let base : SkolemInterp Domain (Fin decoded.projection.functions.length) :=
      ⟨fun _ _ => value⟩
    rcases (decoded.projection.models_source_iff_target interpretation base).2 htarget with
      ⟨functions, hdirect, hpairs⟩
    exact hsource Domain interpretation functions hdirect hpairs value hsub
  · intro htarget Domain interpretation functions hdirect hpairs value hsub
    have hmodels : interpretation.models decoded.projection.target :=
      (decoded.projection.models_source_iff_target interpretation functions).1
        ⟨functions, hdirect, hpairs⟩
    exact htarget Domain interpretation hmodels value hsub

theorem DecodedMixedCommonSource.entails_target_iff
    (decoded : DecodedMixedCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.target sub sup :=
  (decoded.entails_iff sub sup).trans
    (decoded.finiteSource_entails_iff_target sub sup)

theorem WireMixedCommonSource.check_sound (wire : WireMixedCommonSource)
    (decoded : DecodedMixedCommonSource) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.target sub sup :=
  decoded.entails_target_iff sub sup

private def acceptedExample : WireMixedCommonSource where
  version := 1
  projection := {
    variable_count := 1
    concepts := ["A", "B"]
    roles := ["r"]
    functions := ["f"]
    direct := []
    pairs := [{
      variableNames := ["x"]
      body := [.con "A" "x" true]
      source := "x"
      function := "f"
      role := "r"
      filler := "B"
      neg := false }]
    target := [{
      body := [.concept ⟨0, true⟩ 0]
      head := [.exists_ 0 ⟨1, false⟩ 0] }] }

example : acceptedExample.check = .ok true := by native_decide

private def existentialBody : WireMixedCommonSource :=
  { acceptedExample with projection := {
      acceptedExample.projection with
      pairs := [{
        variableNames := ["x"]
        body := [.ex "r" "A" "x" false]
        source := "x"
        function := "f"
        role := "r"
        filler := "B"
        neg := false }]
      target := [{
        body := [.exists_ 0 ⟨0, false⟩ 0]
        head := [.exists_ 0 ⟨1, false⟩ 0] }] } }

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : rejected existentialBody.check = true := by native_decide

#print axioms DecodedMixedCommonSource.entails_iff
#print axioms DecodedMixedCommonSource.entails_target_iff
#print axioms WireMixedCommonSource.check_sound

end ContextCalculus.HTMixedCommonSourceWire
