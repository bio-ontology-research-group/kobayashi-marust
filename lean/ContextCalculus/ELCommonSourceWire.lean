import ContextCalculus.ELNormalCheckerTermEmbedding
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
open ContextCalculus.ELNormalCheckerTermEmbedding

def mapNormalClause : ELCompletion.Clause (Fin n) (Fin n) →
    ELCompletion.Clause Nat Nat
  | .nf1 sub sup => .nf1 sub.val sup.val
  | .nf2 left right sup => .nf2 left.val right.val sup.val
  | .nf3 sub role filler => .nf3 sub.val role.val filler.val
  | .nf4 role filler sup => .nf4 role.val filler.val sup.val
  | .nf5 sub => .nf5 sub.val
  | .nf6 sub sup => .nf6 sub.val sup.val
  | .nf7 first second sup => .nf7 first.val second.val sup.val
  | .reflexive role => .reflexive role.val

def mapNormalOntology (ontology : ELCompletion.Ontology (Fin n) (Fin n)) :
    ELCompletion.Ontology Nat Nat :=
  ontology.map mapNormalClause

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

@[simp] theorem sat_mapNormalClause_nat_iff
    (I : Interp Domain (Fin n) (Fin n) top bottom)
    (clause : ELCompletion.Clause (Fin n) (Fin n)) :
    ELCompletion.satClause (natInterp I) (mapNormalClause clause) ↔
      ELCompletion.satClause I clause := by
  cases clause <;> simp [mapNormalClause, ELCompletion.satClause, natInterp]

@[simp] theorem sat_mapNormalClause_fin_iff
    {top bottom : Fin n}
    (I : Interp Domain Nat Nat top.val bottom.val)
    (clause : ELCompletion.Clause (Fin n) (Fin n)) :
    ELCompletion.satClause (finInterp I) clause ↔
      ELCompletion.satClause I (mapNormalClause clause) := by
  cases clause <;> simp [mapNormalClause, ELCompletion.satClause, finInterp]

theorem models_mapNormalOntology_nat_iff
    (I : Interp Domain (Fin n) (Fin n) top bottom)
    (ontology : ELCompletion.Ontology (Fin n) (Fin n)) :
    ELCompletion.models (natInterp I) (mapNormalOntology ontology) ↔
      ELCompletion.models I ontology := by
  constructor <;> intro hmodels clause hclause
  · exact (sat_mapNormalClause_nat_iff I clause).1
      (hmodels (mapNormalClause clause)
        (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact (sat_mapNormalClause_nat_iff I source).2
      (hmodels source hsource)

theorem models_mapNormalOntology_fin_iff
    {top bottom : Fin n}
    (I : Interp Domain Nat Nat top.val bottom.val)
    (ontology : ELCompletion.Ontology (Fin n) (Fin n)) :
    ELCompletion.models (finInterp I) ontology ↔
      ELCompletion.models I (mapNormalOntology ontology) := by
  constructor
  · intro hmodels clause hclause
    rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
    exact (sat_mapNormalClause_fin_iff I source).1
      (hmodels source hsource)
  · intro hmodels clause hclause
    exact (sat_mapNormalClause_fin_iff I clause).2
      (hmodels (mapNormalClause clause)
        (List.mem_map.mpr ⟨clause, hclause, rfl⟩))

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

def FiniteELCSourceEntails (top bottom : Fin n)
    (ontology : ELCompletion.Ontology (Fin n) (Fin n))
    (residual : List (RawResidualClause (Fin n) (Fin n)))
    (sub sup : Fin n) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain (Fin n) (Fin n) top bottom)
    (terms : RawTermInterp Domain),
    ELCompletion.models I ontology →
    modelsRawResidual I terms residual →
    ∀ value, I.concept sub value → I.concept sup value

theorem mappedELCSourceEntails_iff_finite (top bottom : Fin n)
    (ontology : ELCompletion.Ontology (Fin n) (Fin n))
    (residual : List (RawResidualClause (Fin n) (Fin n)))
    (sub sup : Fin n) :
    ELCSourceEntails top.val bottom.val (mapNormalOntology ontology)
        (mapResidualOntology residual) sub.val sup.val ↔
      FiniteELCSourceEntails top bottom ontology residual sub sup := by
  constructor
  · intro hnat Domain I terms hnormal hresidual value hsub
    have hnormalMapped : ELCompletion.models (natInterp I)
        (mapNormalOntology ontology) :=
      (models_mapNormalOntology_nat_iff I ontology).2 hnormal
    have hresidualMapped : modelsRawResidual (natInterp I) terms
        (mapResidualOntology residual) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (sat_mapResidualClause_nat_iff I terms source).2
        (hresidual source hsource)
    have hresult := hnat Domain (natInterp I) terms hnormalMapped
      hresidualMapped value (by simpa [natInterp] using hsub)
    simpa [natInterp] using hresult
  · intro hfin Domain I terms hnormal hresidual value hsub
    have hnormalFinite : ELCompletion.models (finInterp I) ontology :=
      (models_mapNormalOntology_fin_iff I ontology).2 hnormal
    have hresidualFinite : modelsRawResidual (finInterp I) terms residual := by
      intro clause hclause
      exact (sat_mapResidualClause_fin_iff I terms clause).2
        (hresidual (mapResidualClause clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hresult := hfin Domain (finInterp I) terms hnormalFinite
      hresidualFinite value (by simpa [finInterp] using hsub)
    simpa [finInterp] using hresult

theorem commonMappedCombinedEntails_iff_finite (top bottom : Fin n)
    (ontology : ELCompletion.Ontology (Fin n) (Fin n))
    (residual : List (RawResidualClause (Fin n) (Fin n)))
    (sub sup : Fin n) :
    CommonCombinedEntails top.val bottom.val (mapNormalOntology ontology)
        (mapResidualOntology residual) sub.val sup.val ↔
      FiniteELCSourceEntails top bottom ontology residual sub sup :=
  (commonCombinedEntails_iff_elcSource top.val bottom.val
    (mapNormalOntology ontology) (mapResidualOntology residual)
    sub.val sup.val).trans
      (mappedELCSourceEntails_iff_finite top bottom ontology residual sub sup)

theorem finiteELCSourceEntails_iff_publicationSource
    (doc : DecodedCertificate n) (sub sup : Fin n) :
    FiniteELCSourceEntails doc.top doc.bottom doc.ontology
        doc.source_ontology sub sup ↔
      EntailsSubWithResidual doc.ontology doc.sourceResidualTheory sub sup := by
  constructor
  · intro hfinite Domain I hmodels value hsub
    rcases hmodels.2 with ⟨terms, hresidual⟩
    exact hfinite Domain I terms hmodels.1 hresidual value hsub
  · intro hsource Domain I terms hnormal hresidual value hsub
    exact hsource I ⟨hnormal, ⟨terms, hresidual⟩⟩ value hsub

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
contract and exact equivalence between every published finite taxonomy query
and the combined normalized-plus-residual common proper-term source. -/
theorem WireCertificate.check_common_source_sound
    (wire : WireCertificate) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCertificate wire.symbol_count,
      wire.decode = .ok decoded ∧ PublicationSemantics decoded ∧
        ∀ sub sup : Fin wire.symbol_count,
          CommonCombinedEntails decoded.top.val decoded.bottom.val
              (mapNormalOntology decoded.ontology)
              (mapResidualOntology decoded.source_ontology) sub.val sup.val ↔
            EntailsSubWithResidual decoded.ontology
              decoded.sourceResidualTheory sub sup := by
  rcases wire.check_publication_semantics hcheck with
    ⟨decoded, hdecode, hpublication⟩
  exact ⟨decoded, hdecode, hpublication, fun sub sup =>
    (commonMappedCombinedEntails_iff_finite decoded.top decoded.bottom
      decoded.ontology decoded.source_ontology sub sup).trans
        (finiteELCSourceEntails_iff_publicationSource decoded sub sup)⟩

#print axioms sat_mapResidualClause_nat_iff
#print axioms sat_mapResidualClause_fin_iff
#print axioms commonMappedEntails_iff_finite
#print axioms commonMappedCombinedEntails_iff_finite
#print axioms finiteELCSourceEntails_iff_publicationSource
#print axioms WireCertificate.check_common_source_sound

end ContextCalculus.ELCommonSourceWire
