import ContextCalculus.HypertableauDirectProjectionWire
import ContextCalculus.HTCheckerTermEmbedding

/-!
# Executable direct-HT adapter to the common routing source

This checker composes the exact name/finite-ID projection with the signed
clause normalization theorem.  Acceptance therefore binds the source carried
by an HT certificate to a proper-term first-order ontology.  Existential atoms
fail closed here and must use the separately checked Skolem-pair or bundle
adapter.
-/

namespace ContextCalculus.HTDirectCommonSourceWire

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTCheckerTermEmbedding
open Lean

def noExistential : Atom Variable Concept Role → Bool
  | .exists_ .. => false
  | _ => true

def clauseNoExistentials
    (clause : Hypertableau.Clause Variable Concept Role) : Bool :=
  (clause.body ++ clause.head).all noExistential

def mapAtom : Atom (Fin nvars) (Fin concepts) (Fin roles) → Atom Nat Nat Nat
  | .concept literal node => .concept ⟨literal.concept.val, literal.neg⟩ node.val
  | .role role source target => .role role.val source.val target.val
  | .exists_ role filler node =>
      .exists_ role.val ⟨filler.concept.val, filler.neg⟩ node.val
  | .eq left right => .eq left.val right.val

def mapClause (clause : Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles)) :
    Hypertableau.Clause Nat Nat Nat where
  body := clause.body.map mapAtom
  head := clause.head.map mapAtom

def mapOntology
    (ontology : List (Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles))) :
    List (Hypertableau.Clause Nat Nat Nat) := ontology.map mapClause

theorem direct_mapClause
    (clause : Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles))
    (hcheck : clauseNoExistentials clause = true) : Direct (mapClause clause) := by
  intro atom hatom
  simp only [mapClause, List.mem_append, List.mem_map] at hatom
  rcases hatom with ⟨source, hsource, rfl⟩ | ⟨source, hsource, rfl⟩
  all_goals
    have hall := List.all_eq_true.mp hcheck source
      (List.mem_append.mpr (by first | exact Or.inl hsource | exact Or.inr hsource))
    cases source <;> simp_all [noExistential, directAtom, mapAtom]

def finInterp (interpretation : Interp Domain Nat Nat) :
    Interp Domain (Fin concepts) (Fin roles) where
  concept concept := interpretation.concept concept.val
  role role := interpretation.role role.val

def natInterp [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles)) :
    Interp Domain Nat Nat where
  concept concept value :=
    if h : concept < concepts then interpretation.concept ⟨concept, h⟩ value else False
  role role source target :=
    if h : role < roles then interpretation.role ⟨role, h⟩ source target else False

@[simp] theorem natInterp_concept_fin [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (concept : Fin concepts) (value : Domain) :
    (natInterp interpretation).concept concept.val value ↔
      interpretation.concept concept value := by
  simp [natInterp]

theorem satAtom_map_assignment_congr [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (left right : Nat → Domain)
    (hsame : ∀ index : Fin nvars, left index.val = right index.val)
    (atom : Atom (Fin nvars) (Fin concepts) (Fin roles)) :
    (natInterp interpretation).satAtom left (mapAtom atom) ↔
      (natInterp interpretation).satAtom right (mapAtom atom) := by
  cases atom with
  | concept literal node => simp [mapAtom, Interp.satAtom, hsame node]
  | role role source target =>
      simp [mapAtom, Interp.satAtom, hsame source, hsame target]
  | exists_ role filler node => simp [mapAtom, Interp.satAtom, hsame node]
  | eq leftNode rightNode =>
      simp [mapAtom, Interp.satAtom, hsame leftNode, hsame rightNode]

@[simp] theorem satAtom_map_natInterp [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (assignment : Fin nvars → Domain)
    (atom : Atom (Fin nvars) (Fin concepts) (Fin roles)) :
    (natInterp interpretation).satAtom
        (fun index => if h : index < nvars then assignment ⟨index, h⟩
          else Classical.choice inferInstance)
        (mapAtom atom) ↔ interpretation.satAtom assignment atom := by
  cases atom with
  | concept literal node =>
      simp [mapAtom, Interp.satAtom, Interp.satLit, natInterp]
  | role role source target =>
      simp [mapAtom, Interp.satAtom, natInterp]
  | exists_ role filler node =>
      simp [mapAtom, Interp.satAtom, Interp.satLit, natInterp]
  | eq left right =>
      simp [mapAtom, Interp.satAtom]

@[simp] theorem satAtom_map_finInterp
    (interpretation : Interp Domain Nat Nat) (assignment : Nat → Domain)
    (atom : Atom (Fin nvars) (Fin concepts) (Fin roles)) :
    (finInterp interpretation).satAtom (fun index => assignment index.val) atom ↔
      interpretation.satAtom assignment (mapAtom atom) := by
  cases atom <;> simp [mapAtom, Interp.satAtom, Interp.satLit, finInterp]

theorem modelsClause_map_natInterp [Nonempty Domain]
    (interpretation : Interp Domain (Fin concepts) (Fin roles))
    (clause : Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles)) :
    (natInterp interpretation).modelsClause (mapClause clause) ↔
      interpretation.modelsClause clause := by
  constructor
  · intro hmodels assignment hbody
    let extension : Nat → Domain := fun index =>
      if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
    have hmappedBody : ∀ atom ∈ (mapClause clause).body,
        (natInterp interpretation).satAtom extension atom := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
      exact (satAtom_map_natInterp interpretation assignment source).2
        (hbody source hsource)
    rcases hmodels extension hmappedBody with ⟨atom, hatom, hsat⟩
    rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource, (satAtom_map_natInterp interpretation assignment source).1 hsat⟩
  · intro hmodels assignment hbody
    let restricted : Fin nvars → Domain := fun index => assignment index.val
    have hsourceBody : ∀ atom ∈ clause.body,
        interpretation.satAtom restricted atom := by
      intro atom hatom
      have hmapped := hbody (mapAtom atom)
        (List.mem_map.mpr ⟨atom, hatom, rfl⟩)
      exact (satAtom_map_natInterp interpretation restricted atom).1
        ((satAtom_map_assignment_congr interpretation assignment
          (fun index => if h : index < nvars then restricted ⟨index, h⟩
            else Classical.choice inferInstance)
          (by intro index; simp [restricted]) atom).1 hmapped)
    rcases hmodels restricted hsourceBody with ⟨atom, hatom, hsat⟩
    refine ⟨mapAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩, ?_⟩
    apply (satAtom_map_assignment_congr interpretation
      (fun index => if h : index < nvars then restricted ⟨index, h⟩
        else Classical.choice inferInstance) assignment
      (by intro index; simp [restricted]) atom).1
    exact (satAtom_map_natInterp interpretation restricted atom).2 hsat

theorem modelsClause_map_finInterp
    [Nonempty Domain] (interpretation : Interp Domain Nat Nat)
    (clause : Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles)) :
    (finInterp interpretation).modelsClause clause ↔
      interpretation.modelsClause (mapClause clause) := by
  constructor
  · intro hmodels assignment hbody
    let restricted : Fin nvars → Domain := fun index => assignment index.val
    have hsourceBody : ∀ atom ∈ clause.body,
        (finInterp interpretation).satAtom restricted atom := by
      intro atom hatom
      exact (satAtom_map_finInterp interpretation assignment atom).2
        (hbody (mapAtom atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
    rcases hmodels restricted hsourceBody with ⟨atom, hatom, hsat⟩
    exact ⟨mapAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (satAtom_map_finInterp interpretation assignment atom).1 hsat⟩
  · intro hmodels assignment hbody
    let extension : Nat → Domain := fun index =>
      if h : index < nvars then assignment ⟨index, h⟩ else Classical.choice inferInstance
    have hmappedBody : ∀ atom ∈ (mapClause clause).body,
        interpretation.satAtom extension atom := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
      have hsourceSat := hbody source hsource
      have hassignment : (fun index : Fin nvars => extension index.val) = assignment := by
        funext index
        simp [extension]
      exact (satAtom_map_finInterp interpretation extension source).1
        (by simpa [hassignment] using hsourceSat)
    rcases hmodels extension hmappedBody with ⟨atom, hatom, hsat⟩
    rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
    refine ⟨source, hsource, ?_⟩
    simpa [extension] using
      (satAtom_map_finInterp interpretation extension source).2 hsat

structure WireDirectCommonSource where
  version : Nat
  projection : WireDirectProjection
deriving FromJson, ToJson, Repr

structure DecodedDirectCommonSource where
  projection : DecodedDirectProjection
  direct : ∀ clause ∈ projection.source, clauseNoExistentials clause = true

def WireDirectCommonSource.decode (wire : WireDirectCommonSource) :
    Except String DecodedDirectCommonSource := do
  if wire.version != 1 then
    throw s!"unsupported direct common-source version {wire.version}"
  let projection ← wire.projection.decode
  if hdirect : ∀ clause ∈ projection.source, clauseNoExistentials clause = true then
    return { projection, direct := hdirect }
  else
    throw "direct common-source residual contains an existential atom"

def WireDirectCommonSource.check (wire : WireDirectCommonSource) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedDirectCommonSource.commonOntology (decoded : DecodedDirectCommonSource) :=
  mapOntology decoded.projection.source

theorem DecodedDirectCommonSource.common_direct
    (decoded : DecodedDirectCommonSource) :
    DirectOntology decoded.commonOntology := by
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
  exact direct_mapClause source (decoded.direct source hsource)

def DecodedDirectCommonSource.CommonEntails
    (decoded : DecodedDirectCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) : Prop :=
  CommonEntailsSub decoded.commonOntology sub.val sup.val

/-- Accepted executable direct-source evidence has exactly the same taxonomy
meaning in the common routing source and in the checked HT source. -/
theorem DecodedDirectCommonSource.entails_iff
    (decoded : DecodedDirectCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.source sub sup := by
  change CommonEntailsSub decoded.commonOntology sub.val sup.val ↔
    EntailsSub decoded.projection.source sub sup
  rw [entailsSub_encode_iff decoded.commonOntology decoded.common_direct sub.val sup.val]
  constructor
  · intro hnat Domain interpretation hmodels value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hresult := hnat Domain (natInterp interpretation)
      (by
        intro clause hclause
        rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
        exact (modelsClause_map_natInterp interpretation source).2
          (hmodels source hsource)) value (by simpa using hsub)
    simpa using hresult
  · intro hfin Domain interpretation hmodels value hsub
    letI : Nonempty Domain := ⟨value⟩
    exact hfin Domain (finInterp interpretation)
      (by
        intro clause hclause
        exact (modelsClause_map_finInterp interpretation clause).2
          (hmodels (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩)))
      value (by simpa [finInterp] using hsub)

theorem WireDirectCommonSource.check_sound (wire : WireDirectCommonSource)
    (decoded : DecodedDirectCommonSource) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.source sub sup := by
  exact decoded.entails_iff sub sup

/-- The common proper-term source and the executable direct HT target have the
same complete taxonomy. This composes signed-clause normalization with the
checked finite projection instead of stopping at the intermediate source. -/
theorem DecodedDirectCommonSource.entails_target_iff
    (decoded : DecodedDirectCommonSource)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.target sub sup := by
  rw [decoded.entails_iff sub sup]
  constructor
  · intro hsource Domain interpretation htarget value hsub
    exact hsource Domain interpretation
      ((decoded.projection.models_source_iff_target interpretation).2 htarget)
      value hsub
  · intro htarget Domain interpretation hsource value hsub
    exact htarget Domain interpretation
      ((decoded.projection.models_source_iff_target interpretation).1 hsource)
      value hsub

theorem WireDirectCommonSource.check_target_sound
    (wire : WireDirectCommonSource) (decoded : DecodedDirectCommonSource)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true)
    (sub sup : Fin decoded.projection.concepts.length) :
    decoded.CommonEntails sub sup ↔
      EntailsSub decoded.projection.target sub sup :=
  decoded.entails_target_iff sub sup

private def acceptedExample : WireDirectCommonSource where
  version := 1
  projection := {
    variable_count := 1
    concepts := ["A", "B"]
    roles := []
    source := [{
      variableNames := ["x"]
      body := [.con "A" "x" false]
      head := [.con "B" "x" true] }]
    target := [{
      body := [.concept ⟨0, false⟩ 0]
      head := [.concept ⟨1, true⟩ 0] }] }

example : acceptedExample.check = .ok true := by native_decide

private def existentialExample : WireDirectCommonSource :=
  { acceptedExample with projection := {
      acceptedExample.projection with
      roles := ["r"]
      source := [{
        variableNames := ["x"]
        body := [.con "A" "x" false]
        head := [.ex "r" "B" "x" false] }]
      target := [{
        body := [.concept ⟨0, false⟩ 0]
        head := [.exists_ 0 ⟨1, false⟩ 0] }] } }

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : rejected existentialExample.check = true := by native_decide

#print axioms DecodedDirectCommonSource.entails_iff
#print axioms DecodedDirectCommonSource.entails_target_iff
#print axioms WireDirectCommonSource.check_sound
#print axioms WireDirectCommonSource.check_target_sound

end ContextCalculus.HTDirectCommonSourceWire
