import ContextCalculus.KMConcreteAutomaticSupervisor
import ContextCalculus.HypertableauProductionGlobalPublication

/-!
# Certified incremental publications and source-axiom explanations

An incremental update may reuse arbitrary internal state, but it may publish a
revision only with accepted ELC, HT, or CB evidence bound to the exact
post-update source. Explanation extraction uses the same boundary for the
entailing support and for every one-axiom deletion used to establish
minimality.
-/

namespace ContextCalculus.KMIncrementalExplanationCertification

open ContextCalculus
open ContextCalculus.CertifiedRouting
open ContextCalculus.KMCommonRoutingSource
open ContextCalculus.KMConcreteWorkerAdapters
open ContextCalculus.Hypertableau

/-- A taxonomy publication for one exact incremental revision. Reuse counters
are operational evidence only; semantic acceptance remains source-bound. -/
structure IncrementalRevisionPublication where
  revision : Nat
  source : RequestedTaxonomySource
  answer : TaxonomyAnswer
  evidence : KMExactEvidence
  accepted : requestedExactAccept source answer evidence = true
  reusedFacts : Nat := 0

theorem IncrementalRevisionPublication.exact
    (publication : IncrementalRevisionPublication) :
    RequestedCorrect publication.source publication.answer :=
  requestedExactAccept_sound publication.source publication.answer
    publication.evidence publication.accepted

/-- A checked answer for one requested taxonomy coordinate. -/
structure CheckedCell (source : RequestedTaxonomySource) (sub sup : Nat) where
  answer : TaxonomyAnswer
  evidence : KMExactEvidence
  accepted : requestedExactAccept source answer evidence = true
  cell : TaxonomyCell
  cell_mem : cell ∈ answer.cells
  cell_sub : cell.sub = sub
  cell_sup : cell.sup = sup

theorem CheckedCell.answer_iff_entails
    (checked : CheckedCell source sub sup) :
    checked.cell.answer = true ↔ Entails source.ontology sub sup := by
  have correct := requestedExactAccept_sound source checked.answer
    checked.evidence checked.accepted
  have exact := correct.matrix_exact.2.2 checked.cell checked.cell_mem
  simpa [checked.cell_sub, checked.cell_sup] using exact

theorem CheckedCell.entailed (checked : CheckedCell source sub sup)
    (htrue : checked.cell.answer = true) :
    Entails source.ontology sub sup :=
  checked.answer_iff_entails.mp htrue

theorem CheckedCell.notEntailed (checked : CheckedCell source sub sup)
    (hfalse : checked.cell.answer = false) :
    ¬ Entails source.ontology sub sup := by
  intro hentails
  have htrue := checked.answer_iff_entails.mpr hentails
  simp [hfalse] at htrue

/-- Semantic inclusion between source-axiom collections. -/
def SourceIncluded (small large : List CheckerTerm.FCL) : Prop :=
  ∀ clause, clause ∈ small → clause ∈ large

theorem entails_mono {small large : List CheckerTerm.FCL}
    (hincluded : SourceIncluded small large)
    (hentails : Entails small sub sup) : Entails large sub sup := by
  intro Domain model hlarge value hsub
  exact hentails Domain model
    (fun clause hsmall => hlarge clause (hincluded clause hsmall)) value hsub

/-- A published source-axiom explanation. Every positive and negative oracle
answer is a source-bound checked taxonomy cell. -/
structure CertifiedExplanation (named : List Nat) (sub sup : Nat) where
  support : List CheckerTerm.FCL
  supportChecked : CheckedCell { ontology := support, named } sub sup
  supportTrue : supportChecked.cell.answer = true
  deletionChecked : ∀ sourceClause, sourceClause ∈ support →
    CheckedCell {
      ontology := support.filter (· != sourceClause)
      named
    } sub sup
  deletionFalse : ∀ sourceClause (hsourceClause : sourceClause ∈ support),
    (deletionChecked sourceClause hsourceClause).cell.answer = false

theorem CertifiedExplanation.entails
    (explanation : CertifiedExplanation named sub sup) :
    Entails explanation.support sub sup :=
  explanation.supportChecked.entailed explanation.supportTrue

theorem CertifiedExplanation.oneDeletionMinimal
    (explanation : CertifiedExplanation named sub sup)
    (sourceClause : CheckerTerm.FCL)
    (hsourceClause : sourceClause ∈ explanation.support) :
    ¬ Entails (explanation.support.filter (· != sourceClause)) sub sup :=
  (explanation.deletionChecked sourceClause hsourceClause).notEntailed
    (explanation.deletionFalse sourceClause hsourceClause)

/-- If a candidate omits at least one support axiom, it cannot entail the
query. This lifts checked one-deletion failures to subset minimality by
monotonicity. -/
theorem CertifiedExplanation.subsetMinimal
    (explanation : CertifiedExplanation named sub sup)
    (candidate : List CheckerTerm.FCL)
    (hincluded : SourceIncluded candidate explanation.support)
    (hproper : ∃ sourceClause,
      sourceClause ∈ explanation.support ∧ sourceClause ∉ candidate) :
    ¬ Entails candidate sub sup := by
  rintro hentails
  rcases hproper with ⟨sourceClause, hsupport, hcandidate⟩
  have hfiltered : SourceIncluded candidate
      (explanation.support.filter (· != sourceClause)) := by
    intro clause hclause
    have hsupportClause := hincluded clause hclause
    have hne : clause ≠ sourceClause := by
      intro heq
      subst clause
      exact hcandidate hclause
    simp [hsupportClause, hne]
  exact explanation.oneDeletionMinimal sourceClause hsupport
    (entails_mono hfiltered hentails)

/-- Named-class unsatisfiability is the taxonomy query from the class to the
distinguished bottom concept. -/
abbrev CertifiedUnsatisfiableExplanation (named : List Nat)
    (concept bottom : Nat) := CertifiedExplanation named concept bottom

/-- Common source satisfiability, used by the public inconsistency query. -/
def Satisfiable (ontology : List CheckerTerm.FCL) : Prop :=
  ∃ (Domain : Type) (model : CheckerTerm.TModel Domain),
    ∀ clause ∈ ontology, CheckerTerm.valid model clause

def Inconsistent (ontology : List CheckerTerm.FCL) : Prop :=
  ¬ Satisfiable ontology

/-- A global verdict produced by a certified exact worker. -/
structure CheckedGlobal (source : List CheckerTerm.FCL) where
  publication : ExactBooleanGlobalPublication (Satisfiable source)

theorem CheckedGlobal.inconsistent (checked : CheckedGlobal source)
    (hfalse : checked.publication.answer = false) : Inconsistent source :=
  checked.publication.false_iff.mp hfalse

theorem CheckedGlobal.satisfiable (checked : CheckedGlobal source)
    (htrue : checked.publication.answer = true) : Satisfiable source :=
  checked.publication.answerExact.mp htrue

theorem satisfiable_of_included {small large : List CheckerTerm.FCL}
    (hincluded : SourceIncluded small large)
    (hsatisfiable : Satisfiable large) : Satisfiable small := by
  rcases hsatisfiable with ⟨Domain, model, hmodel⟩
  exact ⟨Domain, model,
    fun clause hsmall => hmodel clause (hincluded clause hsmall)⟩

/-- A minimal inconsistency explanation uses a checked UNSAT global verdict
for the support and a checked SAT verdict after every one-axiom deletion. -/
structure CertifiedInconsistencyExplanation where
  support : List CheckerTerm.FCL
  supportChecked : CheckedGlobal support
  supportFalse : supportChecked.publication.answer = false
  deletionChecked : ∀ sourceClause, sourceClause ∈ support →
    CheckedGlobal (support.filter (· != sourceClause))
  deletionTrue : ∀ sourceClause (hsourceClause : sourceClause ∈ support),
    (deletionChecked sourceClause hsourceClause).publication.answer = true

theorem CertifiedInconsistencyExplanation.inconsistent
    (explanation : CertifiedInconsistencyExplanation) :
    Inconsistent explanation.support :=
  explanation.supportChecked.inconsistent explanation.supportFalse

theorem CertifiedInconsistencyExplanation.subsetMinimal
    (explanation : CertifiedInconsistencyExplanation)
    (candidate : List CheckerTerm.FCL)
    (hincluded : SourceIncluded candidate explanation.support)
    (hproper : ∃ sourceClause,
      sourceClause ∈ explanation.support ∧ sourceClause ∉ candidate) :
    ¬ Inconsistent candidate := by
  rcases hproper with ⟨sourceClause, hsupport, hcandidate⟩
  have hfiltered : SourceIncluded candidate
      (explanation.support.filter (· != sourceClause)) := by
    intro clause hclause
    have hsupportClause := hincluded clause hclause
    have hne : clause ≠ sourceClause := by
      intro heq
      subst clause
      exact hcandidate hclause
    simp [hsupportClause, hne]
  have hsatisfiable :=
    (explanation.deletionChecked sourceClause hsupport).satisfiable
      (explanation.deletionTrue sourceClause hsupport)
  exact fun hinconsistent => hinconsistent
    (satisfiable_of_included hfiltered hsatisfiable)

#print axioms IncrementalRevisionPublication.exact
#print axioms CheckedCell.answer_iff_entails
#print axioms CheckedCell.entailed
#print axioms CheckedCell.notEntailed
#print axioms entails_mono
#print axioms CertifiedExplanation.entails
#print axioms CertifiedExplanation.oneDeletionMinimal
#print axioms CertifiedExplanation.subsetMinimal
#print axioms CheckedGlobal.inconsistent
#print axioms CheckedGlobal.satisfiable
#print axioms satisfiable_of_included
#print axioms CertifiedInconsistencyExplanation.inconsistent
#print axioms CertifiedInconsistencyExplanation.subsetMinimal

end ContextCalculus.KMIncrementalExplanationCertification
