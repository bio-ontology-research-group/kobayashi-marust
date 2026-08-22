import ContextCalculus.ELCompletionWire

/-!
# Complete production ELC publication boundary

This module packages the source-level consequences of the executable ELC wire
checker into one public capstone.  The same statement covers pure EL inputs and
inputs split into direct, canonical-witness, and finitely checked residual
parts.  It binds the published inconsistency flag, ID-level taxonomy, and
named taxonomy to the source clause semantics checked by `checkV5`.
-/

namespace ContextCalculus.ELCompletion

/-- Soundness and completeness contract for one checked production ELC result. -/
structure PublicationSemantics {n : Nat} (doc : DecodedCertificate n) : Prop where
  inconsistent_exact :
    doc.public_inconsistent = true ↔
      UnsatisfiableWithResidual doc.ontology doc.sourceResidualTheory
  id_taxonomy_exact : ∀ {sub sup : Fin n},
    sub ∈ doc.active_concepts →
    sub ≠ doc.top → sub ≠ doc.bottom → sup ≠ sub → sup ≠ doc.top →
    (sup = doc.bottom ∨
      ¬ EntailsSubWithResidual doc.ontology doc.sourceResidualTheory
        sub doc.bottom) →
    ((sub, sup) ∈ doc.public_subsumptions ↔
      EntailsSubWithResidual doc.ontology doc.sourceResidualTheory sub sup)
  named_taxonomy_sound : ∀ {subName supName : String},
    (subName, supName) ∈ doc.public_named_subsumptions →
    ∃ sub sup,
      (sub, sup) ∈ doc.public_subsumptions ∧
      doc.symbols sub = subName ∧
      (if sup = doc.bottom then "owl:Nothing" else doc.symbols sup) = supName ∧
      EntailsSubWithResidual doc.ontology doc.sourceResidualTheory sub sup
  named_taxonomy_complete : ∀ {sub sup : Fin n},
    sub ∈ doc.active_concepts →
    sub ≠ doc.top → sub ≠ doc.bottom → sup ≠ sub → sup ≠ doc.top →
    (sup = doc.bottom ∨
      ¬ EntailsSubWithResidual doc.ontology doc.sourceResidualTheory
        sub doc.bottom) →
    EntailsSubWithResidual doc.ontology doc.sourceResidualTheory sub sup →
    (doc.symbols sub,
      if sup = doc.bottom then "owl:Nothing" else doc.symbols sup) ∈
        doc.public_named_subsumptions

/-- A successful executable V5 check establishes the whole ELC publication contract. -/
theorem DecodedCertificate.checkV5_publication_semantics {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.checkV5 = true) :
    PublicationSemantics doc where
  inconsistent_exact := doc.public_inconsistent_source_exact hcheck
  id_taxonomy_exact hactive hsubTop hsubBottom hsupSub hsupTop hcase :=
    doc.public_subsumption_source_exact hcheck hactive hsubTop hsubBottom
      hsupSub hsupTop hcase
  named_taxonomy_sound hnamed := by
    have hcheckCore := hcheck
    simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheckCore
    have hexpected := (doc.namedSub_iff_expected hcheckCore.2).1 hnamed
    simp only [DecodedCertificate.expectedNamedOutput, List.mem_map] at hexpected
    rcases hexpected with ⟨⟨sub, sup⟩, hpublic, hnames⟩
    simp only [Prod.mk.injEq] at hnames
    exact ⟨sub, sup, hpublic, hnames.1, hnames.2,
      doc.public_subsumption_sound_source hcheck hpublic⟩
  named_taxonomy_complete hactive hsubTop hsubBottom hsupSub hsupTop hcase
      hentails := by
    have hpublic := (doc.public_subsumption_source_exact hcheck hactive
      hsubTop hsubBottom hsupSub hsupTop hcase).2 hentails
    have hcheckCore := hcheck
    simp only [DecodedCertificate.checkV5, Bool.and_eq_true] at hcheckCore
    apply (doc.namedSub_iff_expected hcheckCore.2).2
    simp only [DecodedCertificate.expectedNamedOutput, List.mem_map]
    exact ⟨(_, _), hpublic, rfl⟩

#print axioms DecodedCertificate.checkV5_publication_semantics

end ContextCalculus.ELCompletion
