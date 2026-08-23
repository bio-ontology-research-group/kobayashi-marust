import ContextCalculus.ELCheckerTermEmbedding
import ContextCalculus.ELCompletionExecutablePublication

/-!
# Executable ELC adapter to the common routing source

The V5 wire decodes finite concept and role identifiers. This adapter maps its
exact equality-bearing residual source into the common natural-number
proper-term language and proves complete taxonomy equivalence through finite
restriction and natural extension.
-/

namespace ContextCalculus.ELCommonSourceWire

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.ELCompletion
open ContextCalculus.ELCheckerTermEmbedding

def mapResidualAtom : RawResidualAtom (Fin n) (Fin n) →
    RawResidualAtom Nat Nat
  | .concept concept term => .concept concept.val term
  | .role role source target => .role role.val source target
  | .eq left right => .eq left right

def mapResidualClause (clause : RawResidualClause (Fin n) (Fin n)) :
    RawResidualClause Nat Nat := {
  body := clause.body.map mapResidualAtom
  head := clause.head.map mapResidualAtom
}

def mapResidualOntology
    (ontology : List (RawResidualClause (Fin n) (Fin n))) :
    List (RawResidualClause Nat Nat) := ontology.map mapResidualClause

def natInterp (I : Interp Domain (Fin n) (Fin n) top bottom) :
    Interp Domain Nat Nat top.val bottom.val where
  concept concept value :=
    if h : concept < n then I.concept ⟨concept, h⟩ value else False
  role role source target :=
    if h : role < n then I.role ⟨role, h⟩ source target else False
  top_true value := by simp [I.top_true]
  bottom_false value := by simp [I.bottom_false]

def finInterp {top bottom : Fin n}
    (I : Interp Domain Nat Nat top.val bottom.val) :
    Interp Domain (Fin n) (Fin n) top bottom where
  concept concept := I.concept concept.val
  role role := I.role role.val
  top_true := I.top_true
  bottom_false := I.bottom_false

@[simp] theorem sat_mapResidualAtom_nat_iff
    (I : Interp Domain (Fin n) (Fin n) top bottom)
    (T : RawTermInterp Domain) (environment : Nat → Domain)
    (atom : RawResidualAtom (Fin n) (Fin n)) :
    satRawResidualAtom (natInterp I) T environment (mapResidualAtom atom) ↔
      satRawResidualAtom I T environment atom := by
  cases atom <;> simp [mapResidualAtom, satRawResidualAtom, natInterp]

@[simp] theorem sat_mapResidualAtom_fin_iff
    {top bottom : Fin n}
    (I : Interp Domain Nat Nat top.val bottom.val)
    (T : RawTermInterp Domain) (environment : Nat → Domain)
    (atom : RawResidualAtom (Fin n) (Fin n)) :
    satRawResidualAtom (finInterp I) T environment atom ↔
      satRawResidualAtom I T environment (mapResidualAtom atom) := by
  cases atom <;> simp [mapResidualAtom, satRawResidualAtom, finInterp]

theorem sat_mapResidualClause_nat_iff
    (I : Interp Domain (Fin n) (Fin n) top bottom)
    (T : RawTermInterp Domain)
    (clause : RawResidualClause (Fin n) (Fin n)) :
    satRawResidualClause (natInterp I) T (mapResidualClause clause) ↔
      satRawResidualClause I T clause := by
  constructor
  · intro hmapped environment hbody
    rcases hmapped environment (by
        intro atom hatom
        rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
        exact (sat_mapResidualAtom_nat_iff I T environment source).2
          (hbody source hsource)) with ⟨atom, hatom, htrue⟩
    rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource,
      (sat_mapResidualAtom_nat_iff I T environment source).1 htrue⟩
  · intro hsource environment hbody
    rcases hsource environment (by
        intro atom hatom
        exact (sat_mapResidualAtom_nat_iff I T environment atom).1
          (hbody (mapResidualAtom atom)
            (List.mem_map.mpr ⟨atom, hatom, rfl⟩))) with
      ⟨atom, hatom, htrue⟩
    exact ⟨mapResidualAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (sat_mapResidualAtom_nat_iff I T environment atom).2 htrue⟩

theorem sat_mapResidualClause_fin_iff
    {top bottom : Fin n}
    (I : Interp Domain Nat Nat top.val bottom.val)
    (T : RawTermInterp Domain)
    (clause : RawResidualClause (Fin n) (Fin n)) :
    satRawResidualClause (finInterp I) T clause ↔
      satRawResidualClause I T (mapResidualClause clause) := by
  constructor
  · intro hsource environment hbody
    rcases hsource environment (by
        intro atom hatom
        exact (sat_mapResidualAtom_fin_iff I T environment atom).2
          (hbody (mapResidualAtom atom)
            (List.mem_map.mpr ⟨atom, hatom, rfl⟩))) with
      ⟨atom, hatom, htrue⟩
    exact ⟨mapResidualAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (sat_mapResidualAtom_fin_iff I T environment atom).1 htrue⟩
  · intro hmapped environment hbody
    rcases hmapped environment (by
        intro atom hatom
        rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
        exact (sat_mapResidualAtom_fin_iff I T environment source).1
          (hbody source hsource)) with ⟨atom, hatom, htrue⟩
    rcases List.mem_map.mp hatom with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource,
      (sat_mapResidualAtom_fin_iff I T environment source).2 htrue⟩

def FiniteResidualEntails (top bottom : Fin n)
    (ontology : List (RawResidualClause (Fin n) (Fin n)))
    (sub sup : Fin n) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain (Fin n) (Fin n) top bottom)
    (T : RawTermInterp Domain),
    modelsRawResidual I T ontology →
      ∀ value, I.concept sub value → I.concept sup value

theorem rawMappedEntails_iff_finite (top bottom : Fin n)
    (ontology : List (RawResidualClause (Fin n) (Fin n)))
    (sub sup : Fin n) :
    RawResidualEntails top.val bottom.val (mapResidualOntology ontology)
        sub.val sup.val ↔
      FiniteResidualEntails top bottom ontology sub sup := by
  constructor
  · intro hnat Domain I T hmodels value hsub
    have hmapped : modelsRawResidual (natInterp I) T
        (mapResidualOntology ontology) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (sat_mapResidualClause_nat_iff I T source).2
        (hmodels source hsource)
    have hresult := hnat Domain (natInterp I) T hmapped value
      (by simpa [natInterp] using hsub)
    simpa [natInterp] using hresult
  · intro hfin Domain I T hmodels value hsub
    have hsource : modelsRawResidual (finInterp I) T ontology := by
      intro clause hclause
      exact (sat_mapResidualClause_fin_iff I T clause).2
        (hmodels (mapResidualClause clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hresult := hfin Domain (finInterp I) T hsource value
      (by simpa [finInterp] using hsub)
    simpa [finInterp] using hresult

theorem commonMappedEntails_iff_finite (top bottom : Fin n)
    (ontology : List (RawResidualClause (Fin n) (Fin n)))
    (sub sup : Fin n) :
    CommonResidualEntails top.val bottom.val (mapResidualOntology ontology)
        sub.val sup.val ↔
      FiniteResidualEntails top bottom ontology sub sup :=
  (commonResidualEntails_iff_raw top.val bottom.val
    (mapResidualOntology ontology) sub.val sup.val).trans
      (rawMappedEntails_iff_finite top bottom ontology sub sup)

/-- Acceptance by the actual V5 wire yields both its complete publication
contract and a source translation theorem for every finite taxonomy query. -/
theorem WireCertificate.check_common_source_sound
    (wire : WireCertificate) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCertificate wire.symbol_count,
      wire.decode = .ok decoded ∧ PublicationSemantics decoded ∧
        ∀ sub sup : Fin wire.symbol_count,
          CommonResidualEntails decoded.top.val decoded.bottom.val
              (mapResidualOntology decoded.source_ontology) sub.val sup.val ↔
            FiniteResidualEntails decoded.top decoded.bottom
              decoded.source_ontology sub sup := by
  rcases wire.check_publication_semantics hcheck with
    ⟨decoded, hdecode, hpublication⟩
  exact ⟨decoded, hdecode, hpublication,
    fun sub sup => commonMappedEntails_iff_finite decoded.top decoded.bottom
      decoded.source_ontology sub sup⟩

#print axioms sat_mapResidualClause_nat_iff
#print axioms sat_mapResidualClause_fin_iff
#print axioms commonMappedEntails_iff_finite
#print axioms WireCertificate.check_common_source_sound

end ContextCalculus.ELCommonSourceWire
