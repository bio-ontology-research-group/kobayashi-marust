import ContextCalculus.ELCommonSourceWire
import ContextCalculus.HTCheckerTermEmbedding
import ContextCalculus.HTDirectTaxonomyCommonPublication
import ContextCalculus.CBSourceProductionTaxonomyWire

/-!
# One semantic source for certified KM routing

The production workers use different internal normal forms, but routing may
compose them only after each normal form is tied to the same source.  This
module fixes that source to the proper-term first-order clause language used by
the CB checker.  ELC's distinguished top and bottom concepts are represented
by ordinary source clauses, so no semantic side condition disappears when an
ELC publication is compared with an HT or CB publication.
-/

namespace ContextCalculus.KMCommonRoutingSource

open ContextCalculus
open ContextCalculus.CheckerTerm

/-- The source-level taxonomy semantics shared by every routed worker. -/
def Entails (ontology : List FCL) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ ontology, valid model clause) →
    ∀ value, model.conc sub value → model.conc sup value

def Unsatisfiable (ontology : List FCL) (concept : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ ontology, valid model clause) →
    ∀ value, ¬ model.conc concept value

private def x : FTerm := .var 0

/-- Make ELC's semantic top concept explicit in the common clause source. -/
def topClause (top : Nat) : FCL :=
  ⟨[], [.P (.concept top x)]⟩

/-- Make ELC's semantic bottom concept explicit in the common clause source. -/
def bottomClause (bottom : Nat) : FCL :=
  ⟨[.P (.concept bottom x)], []⟩

theorem valid_topClause_iff (model : TModel Domain) (top : Nat) :
    valid model (topClause top) ↔ ∀ value, model.conc top value := by
  constructor
  · intro hvalid value
    obtain ⟨literal, hliteral, htrue⟩ :=
      hvalid (fun _ => value) (by intro literal hliteral; cases hliteral)
    simp only [topClause, List.mem_singleton] at hliteral
    subst literal
    simpa [x, TModel.evalL, TModel.evalT] using htrue
  · intro htop assignment _
    exact ⟨.P (.concept top x), (by
        change FLit.P (FPred.concept top x) ∈
          [FLit.P (FPred.concept top x)]
        simp),
      by simpa [x, TModel.evalL, TModel.evalT] using htop (assignment 0)⟩

theorem valid_bottomClause_iff (model : TModel Domain) (bottom : Nat) :
    valid model (bottomClause bottom) ↔
      ∀ value, ¬ model.conc bottom value := by
  constructor
  · intro hvalid value hbottom
    obtain ⟨literal, hliteral, _⟩ := hvalid (fun _ => value) (by
      intro literal hliteral
      simp only [bottomClause, List.mem_singleton] at hliteral
      subst literal
      simpa [x, TModel.evalL, TModel.evalT] using hbottom)
    cases hliteral
  · intro hbottom assignment hbody
    exact (hbottom (assignment 0)
      (hbody (.P (.concept bottom x)) (by
        change FLit.P (FPred.concept bottom x) ∈
          [FLit.P (FPred.concept bottom x)]
        simp))).elim

def elcOntology (top bottom : Nat)
    (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (ELCompletion.RawResidualClause Nat Nat)) : List FCL :=
  topClause top :: bottomClause bottom ::
    ELNormalCheckerTermEmbedding.encodeCombinedSource ontology residual

theorem models_elcOntology_iff (model : TModel Domain)
    (top bottom : Nat) (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (ELCompletion.RawResidualClause Nat Nat)) :
    (∀ clause ∈ elcOntology top bottom ontology residual,
      valid model clause) ↔
      (∀ value, model.conc top value) ∧
      (∀ value, ¬ model.conc bottom value) ∧
      (∀ clause ∈
        ELNormalCheckerTermEmbedding.encodeCombinedSource ontology residual,
        valid model clause) := by
  simp only [elcOntology, List.forall_mem_cons, valid_topClause_iff,
    valid_bottomClause_iff]

theorem entails_elcOntology_iff (top bottom : Nat)
    (ontology : ELCompletion.Ontology Nat Nat)
    (residual : List (ELCompletion.RawResidualClause Nat Nat))
    (sub sup : Nat) :
    Entails (elcOntology top bottom ontology residual) sub sup ↔
      ELNormalCheckerTermEmbedding.CommonCombinedEntails
        top bottom ontology residual sub sup := by
  constructor <;> intro h Domain model
  · intro htop hbottom hcombined
    exact h Domain model
      ((models_elcOntology_iff model top bottom ontology residual).2
        ⟨htop, hbottom, hcombined⟩)
  · intro hmodels
    rcases (models_elcOntology_iff model top bottom ontology residual).1 hmodels with
      ⟨htop, hbottom, hcombined⟩
    exact h Domain model htop hbottom hcombined

def directHTOntology
    (ontology : List (Hypertableau.Clause Nat Nat Nat)) : List FCL :=
  ontology.map HTCheckerTermEmbedding.encodeClause

theorem entails_directHTOntology_iff
    (ontology : List (Hypertableau.Clause Nat Nat Nat)) (sub sup : Nat) :
    Entails (directHTOntology ontology) sub sup ↔
      HTCheckerTermEmbedding.CommonEntailsSub ontology sub sup := by
  simp only [Entails, directHTOntology,
    HTCheckerTermEmbedding.CommonEntailsSub, List.forall_mem_map]

theorem unsatisfiable_directHTOntology_iff
    (ontology : List (Hypertableau.Clause Nat Nat Nat)) (concept : Nat) :
    Unsatisfiable (directHTOntology ontology) concept ↔
      HTCheckerTermEmbedding.CommonUnsatisfiableConcept ontology concept := by
  simp only [Unsatisfiable, directHTOntology,
    HTCheckerTermEmbedding.CommonUnsatisfiableConcept, List.forall_mem_map]

theorem entails_cbOntology_iff (ontology : List FCL) (sub sup : Nat) :
    Entails ontology sub sup ↔
      CBSourceProductionTaxonomyWire.Entails ontology sub sup := by
  rfl

/-- The exact common clause source extracted from an accepted finite ELC
certificate.  Finite identifiers are embedded into naturals exactly as in the
executable common-source checker. -/
def elcWireOntology
    (decoded : ELCompletion.DecodedCertificate n) : List FCL :=
  elcOntology decoded.top.val decoded.bottom.val
    (ELCommonSourceWire.mapNormalOntology decoded.ontology)
    (ELCommonSourceWire.mapResidualOntology decoded.source_ontology)

/-- Acceptance of the production ELC wire yields its full publication
semantics and, for every finite taxonomy coordinate, equivalence with the one
proper-term source used by routed CB and HT workers. -/
theorem ELCompletion.WireCertificate.check_common_routing_source_sound
    (wire : ELCompletion.WireCertificate)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : ELCompletion.DecodedCertificate wire.symbol_count,
      wire.decode = .ok decoded ∧
      ELCompletion.PublicationSemantics decoded ∧
      ∀ sub sup : Fin wire.symbol_count,
        Entails (elcWireOntology decoded) sub.val sup.val ↔
          ELCompletion.EntailsSubWithResidual decoded.ontology
            decoded.sourceResidualTheory sub sup := by
  rcases ELCommonSourceWire.WireCertificate.check_common_source_sound
      wire hcheck with ⟨decoded, hdecode, hpublication, hcommon⟩
  refine ⟨decoded, hdecode, hpublication, ?_⟩
  intro sub sup
  exact (entails_elcOntology_iff decoded.top.val decoded.bottom.val
    (ELCommonSourceWire.mapNormalOntology decoded.ontology)
    (ELCommonSourceWire.mapResidualOntology decoded.source_ontology)
    sub.val sup.val).trans (hcommon sub sup)

def directHTPublicationOntology :
    HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication → List FCL
  | .plain decoded _ =>
      directHTOntology (HTDirectCommonSourceWire.mapOntology
        decoded.normalization.source)
  | .mixed decoded _ =>
      directHTOntology (HTDirectCommonSourceWire.mapOntology
        decoded.normalization.source)

def DirectHTRoutingSemantics
    (decoded :
      HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication) : Prop :=
  match decoded with
  | .plain publication _ =>
      (∀ concept : Fin publication.target.conceptCount,
        concept ∈ publication.target.named →
        (concept ∈ publication.semantic.unsatisfiable ↔
          Unsatisfiable (directHTPublicationOntology decoded) concept.val)) ∧
      (∀ sub sup : Fin publication.target.conceptCount,
        sub ∈ publication.target.named → sup ∈ publication.target.named →
        ((sub, sup) ∈ publication.semantic.subsumptions ↔
          Entails (directHTPublicationOntology decoded) sub.val sup.val))
  | .mixed publication _ =>
      (∀ concept : Fin publication.target.conceptCount,
        concept ∈ publication.target.named →
        (concept ∈ publication.semantic.unsatisfiable ↔
          Unsatisfiable (directHTPublicationOntology decoded) concept.val)) ∧
      (∀ sub sup : Fin publication.target.conceptCount,
        sub ∈ publication.target.named → sup ∈ publication.target.named →
        ((sub, sup) ∈ publication.semantic.subsumptions ↔
          Entails (directHTPublicationOntology decoded) sub.val sup.val))

theorem directHTRoutingSemantics
    (decoded :
      HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication) :
    DirectHTRoutingSemantics decoded := by
  have hcommon :=
    HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication.common_semantics
      decoded
  cases decoded with
  | plain publication direct | mixed publication direct =>
      constructor
      · intro concept hnamed
        exact (hcommon.1 concept hnamed).trans
          (unsatisfiable_directHTOntology_iff
            (HTDirectCommonSourceWire.mapOntology publication.normalization.source)
            concept.val).symm
      · intro sub sup hsub hsup
        exact (hcommon.2 sub sup hsub hsup).trans
          (entails_directHTOntology_iff
            (HTDirectCommonSourceWire.mapOntology publication.normalization.source)
            sub.val sup.val).symm

theorem directHTCheck_common_routing_source_sound
    (wire :
      HTDirectTaxonomyCommonPublication.WireDirectTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    wire.document.runs.check = true ∧
      wire.document.payloadBoundB = true ∧
      ∃ decoded :
          HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication,
        wire.decode = .ok decoded ∧ DirectHTRoutingSemantics decoded := by
  rcases HTDirectTaxonomyCommonPublication.WireDirectTaxonomyPublication.check_sound
      wire hcheck with
    ⟨hruns, hpayload, decoded, hdecode, _⟩
  exact ⟨hruns, hpayload, decoded, hdecode,
    directHTRoutingSemantics decoded⟩

#print axioms models_elcOntology_iff
#print axioms entails_elcOntology_iff
#print axioms entails_directHTOntology_iff
#print axioms unsatisfiable_directHTOntology_iff
#print axioms entails_cbOntology_iff
#print axioms ELCompletion.WireCertificate.check_common_routing_source_sound
#print axioms directHTCheck_common_routing_source_sound

end ContextCalculus.KMCommonRoutingSource
