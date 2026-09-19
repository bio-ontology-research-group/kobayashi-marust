import ContextCalculus.KMIncrementalExplanationCertification
import ContextCalculus.HypertableauDisjointUnionABoxProjection

/-!
# Atomic ABox projection and incremental source-clash publication

The executable atomic projection screen must establish one asserted class per
semantic individual, complete atomic-assertion coverage, and TBox closure under
disjoint union. Individual class satisfiability alone does not suffice when one
individual has several distinct class assertions. This module constructs the
missing full-ABox model, then uses the existing taxonomy projection theorem.

The publication lemmas model the changed Boolean/list boundary in
`source_incremental::map_incremental_result`. Detector soundness and binding of
the Rust frontend/worker to the current source remain explicit premises. This
is not an extraction or verification of the Rust parser or the prechecks.
-/

namespace ContextCalculus.KMAtomicABoxPublication

open ContextCalculus.Hypertableau

abbrev AtomicRows := List (Nat × Nat)
abbrev TBox := List (Hypertableau.Clause Nat Nat Nat)

/-- Rows use semantic individual and concept identifiers, not raw tokens. -/
def SingleClassPerIndividual (rows : AtomicRows) : Prop :=
  ∀ left ∈ rows, ∀ right ∈ rows, left.1 = right.1 → left.2 = right.2

def ClassSatisfiable (ontology : TBox) (concept : Nat) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Nat Nat) (witness : Domain),
    I.models ontology ∧ I.concept concept witness

def TBoxSatisfiable (ontology : TBox) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Nat Nat), Nonempty Domain ∧ I.models ontology

def AtomicSatisfiable (ontology : TBox) (rows : AtomicRows) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Nat Nat) (value : Nat → Domain),
    Nonempty Domain ∧ I.models ontology ∧
      ∀ row ∈ rows, I.concept row.2 (value row.1)

/-- The one-class shortcut needs no distinct-individual assumption. -/
theorem singleClass_of_oneClass (rows : AtomicRows) (concept : Nat)
    (hall : ∀ row ∈ rows, row.2 = concept) : SingleClassPerIndividual rows := by
  intro left hleft right hright _
  exact (hall left hleft).trans (hall right hright).symm

/-- Restricting the screen declines multiple classes on one individual. -/
theorem conflicting_rows_decline (rows : AtomicRows) (left right : Nat × Nat)
    (hleft : left ∈ rows) (hright : right ∈ rows)
    (hsame : left.1 = right.1) (hdifferent : left.2 ≠ right.2) :
    ¬SingleClassPerIndividual rows := by
  intro hsingle
  exact hdifferent (hsingle left hleft right hright hsame)

/-- A lexical per-individual check transfers to semantic identifiers only if
distinct accepted spellings cannot alias. This is the obligation addressed by
the conservative absolute, unescaped IRI and scoped anonymous-label screen. -/
theorem singleClass_map_of_injective (rows : AtomicRows)
    (individual concept : Nat → Nat) (hinjective : Function.Injective individual)
    (hsingle : SingleClassPerIndividual rows) :
    SingleClassPerIndividual
      (rows.map (fun row => (individual row.1, concept row.2))) := by
  intro left hleft right hright heq
  rcases List.mem_map.mp hleft with ⟨leftRow, hleftRow, rfl⟩
  rcases List.mem_map.mp hright with ⟨rightRow, hrightRow, rfl⟩
  exact congrArg concept
    (hsingle leftRow hleftRow rightRow hrightRow (hinjective heq))

/-- Full IRIs and document-local anonymous labels use disjoint identifier
namespaces. Injectivity within each namespace therefore suffices for the
lexical screen's combined identifier map. This says nothing about distinct
individuals having distinct denotations in every model. -/
theorem scopedIndividual_injective (named anonymous : Nat → Nat)
    (hnamed : Function.Injective named) (hanonymous : Function.Injective anonymous)
    (hdisjoint : ∀ n a, named n ≠ anonymous a) :
    Function.Injective (Sum.elim named anonymous) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hnamed h)
      | inr y => exact False.elim (hdisjoint x y h)
  | inr x =>
      cases y with
      | inl y => exact False.elim (hdisjoint y x h.symm)
      | inr y => exact congrArg Sum.inr (hanonymous h)

/-- Construct a joint model, rather than assume that individually satisfiable
classes can be assigned to the same named individual. -/
theorem atomicSatisfiable_of_singleClass
    (ontology : TBox) (rows : AtomicRows)
    (hclosed : Interp.MaskedDisjointUnionClosed ontology (fun _ => False))
    (htbox : TBoxSatisfiable ontology)
    (hsingle : SingleClassPerIndividual rows)
    (hclasses : ∀ row ∈ rows, ClassSatisfiable ontology row.2) :
    AtomicSatisfiable ontology rows := by
  classical
  induction rows with
  | nil =>
      rcases htbox with ⟨Domain, I, ⟨witness⟩, hmodel⟩
      exact ⟨Domain, I, fun _ => witness, ⟨witness⟩, hmodel, by simp⟩
  | cons head tail ih =>
      have htailSingle : SingleClassPerIndividual tail := by
        intro left hleft right hright heq
        exact hsingle left (List.mem_cons_of_mem _ hleft)
          right (List.mem_cons_of_mem _ hright) heq
      have htailClasses : ∀ row ∈ tail, ClassSatisfiable ontology row.2 := by
        intro row hrow
        exact hclasses row (List.mem_cons_of_mem _ hrow)
      rcases ih htailSingle htailClasses with
        ⟨TailDomain, tailModel, tailValue, htailNonempty, htailModel, htailRows⟩
      rcases hclasses head (by simp) with
        ⟨HeadDomain, headModel, headValue, hheadModel, hheadClass⟩
      let combined := Interp.maskedDisjointUnion (fun _ => False) headModel tailModel
      let value : Nat → Sum HeadDomain TailDomain := fun individual =>
        if individual = head.1 then .inl headValue else .inr (tailValue individual)
      refine ⟨Sum HeadDomain TailDomain, combined, value, ⟨.inl headValue⟩,
        hclosed HeadDomain TailDomain headModel tailModel hheadModel htailModel, ?_⟩
      intro row hrow
      by_cases heq : row.1 = head.1
      · have hclass := hsingle row hrow head (by simp) heq
        simpa [combined, value, heq, Interp.maskedDisjointUnion, hclass]
          using hheadClass
      · have htail : row ∈ tail := by
          rcases List.mem_cons.mp hrow with hhead | htail
          · subst row
            exact False.elim (heq rfl)
          · exact htail
        simpa [combined, value, heq, Interp.maskedDisjointUnion]
          using htailRows row htail

theorem atomicSatisfiable_iff_classes
    (ontology : TBox) (rows : AtomicRows)
    (hclosed : Interp.MaskedDisjointUnionClosed ontology (fun _ => False))
    (htbox : TBoxSatisfiable ontology)
    (hsingle : SingleClassPerIndividual rows) :
    AtomicSatisfiable ontology rows ↔
      ∀ row ∈ rows, ClassSatisfiable ontology row.2 := by
  constructor
  · rintro ⟨Domain, I, value, _, hmodel, hrows⟩ row hrow
    exact ⟨Domain, I, value row.1, hmodel, hrows row hrow⟩
  · exact atomicSatisfiable_of_singleClass ontology rows hclosed htbox hsingle

def nativeAtomic (rows : AtomicRows) : NativeABox Nat Nat Nat where
  proxies _ := []
  assertions individual := (rows.filter (fun row => row.1 == individual)).map Prod.snd
  different := []
  roleAssertions := []
  negativeRoleAssertions := []

theorem nativeAtomic_models (rows : AtomicRows) (I : Interp Domain Nat Nat)
    (value : Nat → Domain)
    (hrows : ∀ row ∈ rows, I.concept row.2 (value row.1)) :
    (nativeAtomic rows).models I value := by
  refine ⟨by simp [nativeAtomic], ?_, by simp [nativeAtomic],
    by simp [nativeAtomic], by simp [nativeAtomic]⟩
  intro individual concept hconcept
  rcases List.mem_map.mp hconcept with ⟨row, hrow, hclass⟩
  have hfiltered := List.mem_filter.mp hrow
  have hindividual : row.1 = individual := by simpa using hfiltered.2
  simpa [hindividual, hclass] using hrows row hfiltered.1

theorem nativeAtomic_fullSatisfiable
    (ontology : TBox) (rows : AtomicRows)
    (hclosed : Interp.MaskedDisjointUnionClosed ontology (fun _ => False))
    (htbox : TBoxSatisfiable ontology)
    (hsingle : SingleClassPerIndividual rows)
    (hclasses : ∀ row ∈ rows, ClassSatisfiable ontology row.2) :
    (nativeAtomic rows).FullSatisfiable ontology := by
  rcases atomicSatisfiable_of_singleClass ontology rows hclosed htbox hsingle hclasses with
    ⟨Domain, I, value, hnonempty, hmodel, hrows⟩
  exact ⟨Domain, I, value, hnonempty, hmodel, nativeAtomic_models rows I value hrows⟩

/-- Source atomic-ABox consistency supplies the explicit full-model premise
required by the existing taxonomy projection theorem. -/
theorem nativeAtomic_taxonomy_exact
    (ontology : TBox) (rows : AtomicRows)
    (hclosed : Interp.MaskedDisjointUnionClosed ontology (fun _ => False))
    (htbox : TBoxSatisfiable ontology)
    (hsingle : SingleClassPerIndividual rows)
    (hclasses : ∀ row ∈ rows, ClassSatisfiable ontology row.2)
    (sub sup : Nat) :
    (nativeAtomic rows).EntailsSubWith ontology sub sup ↔ EntailsSub ontology sub sup := by
  have hproxy : (nativeAtomic rows).ProxyConcept = (fun _ => False) := by
    funext concept
    simp [NativeABox.ProxyConcept, nativeAtomic]
  have hamalgamation :=
    (nativeAtomic rows).modelAmalgamationFor_of_maskedDisjointUnionClosed
      ontology (fun _ => True) (by simpa [hproxy] using hclosed)
      (by simp [NativeABox.ProxyConcept, nativeAtomic])
  exact (nativeAtomic rows).entailsSubWith_iff_entailsSub_of_modelAmalgamationFor
    ontology (fun _ => True)
    (nativeAtomic_fullSatisfiable ontology rows hclosed htbox hsingle hclasses)
    hamalgamation sub sup trivial trivial

/-- This data boundary mirrors the three changed fields; `dropped` and the
already mapped taxonomy payload are passed through without reinterpretation. -/
structure Publication (Subsumption Unsatisfiable : Type) where
  consistent : Bool
  subsumptions : List Subsumption
  unsatisfiable : List Unsatisfiable
  dropped : Nat
  deriving DecidableEq

def publish (frontendClash assertedUnsat workerInconsistent : Bool)
    (subsumptions : List Subsumption) (unsatisfiable : List Unsatisfiable)
    (dropped : Nat) : Publication Subsumption Unsatisfiable :=
  let sourceClash := frontendClash || assertedUnsat
  { consistent := !workerInconsistent && !sourceClash
    subsumptions := if sourceClash then [] else subsumptions
    unsatisfiable := if sourceClash then [] else unsatisfiable
    dropped }

def oldPublish (assertedUnsat workerInconsistent : Bool)
    (subsumptions : List Subsumption) (unsatisfiable : List Unsatisfiable)
    (dropped : Nat) : Publication Subsumption Unsatisfiable :=
  { consistent := !workerInconsistent && !assertedUnsat
    subsumptions := if assertedUnsat then [] else subsumptions
    unsatisfiable := if assertedUnsat then [] else unsatisfiable
    dropped }

theorem publish_frontend_false
    (assertedUnsat workerInconsistent : Bool)
    (subsumptions : List Subsumption) (unsatisfiable : List Unsatisfiable) (dropped : Nat) :
    publish false assertedUnsat workerInconsistent subsumptions unsatisfiable dropped =
      oldPublish assertedUnsat workerInconsistent subsumptions unsatisfiable dropped := by
  simp [publish, oldPublish]

theorem publish_frontend_clash
    (assertedUnsat workerInconsistent : Bool)
    (subsumptions : List Subsumption) (unsatisfiable : List Unsatisfiable) (dropped : Nat) :
    publish true assertedUnsat workerInconsistent subsumptions unsatisfiable dropped =
      ⟨false, [], [], dropped⟩ := by
  simp [publish]

/-- The changed publisher is exact for the *current source*, provided its
detectors are sound on that source and its worker is exact on the residual
case. A prior revision's consistency proof cannot discharge these premises. -/
theorem publish_consistent_iff (sourceSatisfiable : Prop)
    (frontendClash assertedUnsat workerInconsistent : Bool)
    (subsumptions : List Subsumption) (unsatisfiable : List Unsatisfiable) (dropped : Nat)
    (hfrontend : frontendClash = true → ¬sourceSatisfiable)
    (hasserted : assertedUnsat = true → ¬sourceSatisfiable)
    (hworker : frontendClash = false → assertedUnsat = false →
      (workerInconsistent = false ↔ sourceSatisfiable)) :
    (publish frontendClash assertedUnsat workerInconsistent
      subsumptions unsatisfiable dropped).consistent = true ↔ sourceSatisfiable := by
  cases frontendClash <;> cases assertedUnsat <;> cases workerInconsistent <;>
    simp_all [publish]

def atomicFact (concept individual : Nat) : CheckerTerm.FCL :=
  ⟨[], [.P (.concept concept (.const individual))]⟩

def disjointClasses (left right : Nat) : CheckerTerm.FCL :=
  ⟨[.P (.concept left (.var 0)), .P (.concept right (.var 0))], []⟩

/-- Semantic witness for the actual regression: two disjoint named classes
asserted on the same individual make the exact source inconsistent, even when
each class separately has a model. The source may contain arbitrary extra
clauses. Normalization must bind these three clauses to the parsed source. -/
theorem direct_disjoint_assertions_inconsistent
    (source : List CheckerTerm.FCL) (left right individual : Nat)
    (hleft : atomicFact left individual ∈ source)
    (hright : atomicFact right individual ∈ source)
    (hdisjoint : disjointClasses left right ∈ source) :
    KMIncrementalExplanationCertification.Inconsistent source := by
  rintro ⟨Domain, model, hmodel⟩
  let assignment : Int → Domain := fun _ => model.const individual
  have hleftFact := hmodel (atomicFact left individual) hleft assignment (by
    simp [atomicFact])
  have hrightFact := hmodel (atomicFact right individual) hright assignment (by
    simp [atomicFact])
  have hleftClass : model.conc left (model.const individual) := by
    simpa [atomicFact, CheckerTerm.TModel.evalL, CheckerTerm.TModel.evalT]
      using hleftFact
  have hrightClass : model.conc right (model.const individual) := by
    simpa [atomicFact, CheckerTerm.TModel.evalL, CheckerTerm.TModel.evalT]
      using hrightFact
  have hfalse := hmodel (disjointClasses left right) hdisjoint assignment (by
    simp [disjointClasses, CheckerTerm.TModel.evalL, CheckerTerm.TModel.evalT,
      assignment, hleftClass, hrightClass])
  simp [disjointClasses] at hfalse

#print axioms singleClass_of_oneClass
#print axioms conflicting_rows_decline
#print axioms singleClass_map_of_injective
#print axioms atomicSatisfiable_of_singleClass
#print axioms atomicSatisfiable_iff_classes
#print axioms scopedIndividual_injective
#print axioms nativeAtomic_models
#print axioms nativeAtomic_fullSatisfiable
#print axioms nativeAtomic_taxonomy_exact
#print axioms publish_frontend_false
#print axioms publish_frontend_clash
#print axioms publish_consistent_iff
#print axioms direct_disjoint_assertions_inconsistent

end ContextCalculus.KMAtomicABoxPublication
