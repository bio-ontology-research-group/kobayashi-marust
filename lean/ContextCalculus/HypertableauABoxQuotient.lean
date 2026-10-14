import ContextCalculus.HypertableauDisjointUnionABoxProjection

/-!
# Homomorphic ABox quotients

OWL has no unique-name assumption. If every assertion of a source ABox has an
image in a target ABox under a map `h` on individuals, then every model of the
target ABox is a model of the source ABox, interpreting each individual `a` as
the target value of `h a`. The quotient route of KM's orchestrator
(`engine/src/orchestrate/abox_quotient.rs`) builds such a target ABox, much
smaller than the source, and classifies the TBox together with it. This module
proves the three publication facts that route relies on.

* `NativeABox.fullSatisfiable_of_homomorphism`: a consistent quotient proves
  the source consistent.
* `NativeABox.not_fullSatisfiable_of_subABox`: an inconsistent quotient whose
  assertions are all source assertions proves the source inconsistent.
* `NativeABox.entailsSubWith_iff_of_quotient` and
  `NativeABox.unsatisfiableConceptWith_iff_of_quotient`: when both ABoxes admit
  model amalgamation with arbitrary TBox models (nominal-free TBoxes, through
  `NativeABox.modelAmalgamationFor_of_maskedDisjointUnionClosed`), the quotient
  taxonomy equals the source taxonomy.
* `NativeABox.entailsSubWith_iff_of_sandwich` and
  `NativeABox.unsatisfiableConceptWith_iff_of_sandwich`: without any closure
  assumption (TBox nominals), the TBox-only answer is a lower bound and the
  quotient answer an upper bound, so their agreement fixes the source answer.

Data values are outside this clause model; their two transformations (thinning
of indistinguishable values of count-free data properties and string renaming
in isomorphic components) are argued in the module documentation of
`abox_quotient.rs`.
-/

namespace ContextCalculus.Hypertableau

/-- Every assertion of `source` has an image in `target` under `h`. -/
structure NativeABox.Homomorphism
    (source : NativeABox Individual Concept Role)
    (target : NativeABox Image Concept Role)
    (h : Individual → Image) : Prop where
  proxies : ∀ individual proxy, proxy ∈ source.proxies individual →
    proxy ∈ target.proxies (h individual)
  assertions : ∀ individual concept, concept ∈ source.assertions individual →
    concept ∈ target.assertions (h individual)
  different : ∀ pair ∈ source.different, (h pair.1, h pair.2) ∈ target.different
  roles : ∀ assertion ∈ source.roleAssertions,
    (assertion.1, h assertion.2.1, h assertion.2.2) ∈ target.roleAssertions
  negativeRoles : ∀ assertion ∈ source.negativeRoleAssertions,
    (assertion.1, h assertion.2.1, h assertion.2.2) ∈ target.negativeRoleAssertions

/-- A model of the quotient ABox is a model of the source ABox. -/
theorem NativeABox.models_of_homomorphism
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (I : Interp Domain Concept Role) (value : Image → Domain)
    (hmodels : target.models I value) :
    source.models I (value ∘ h) := by
  rcases hmodels with ⟨hproxy, hassertion, hdifferent, hrole, hnegative⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro individual proxy hmem candidate
    exact hproxy (h individual) proxy (hom.proxies individual proxy hmem) candidate
  · intro individual concept hmem
    exact hassertion (h individual) concept (hom.assertions individual concept hmem)
  · intro pair hmem
    exact hdifferent _ (hom.different pair hmem)
  · intro assertion hmem
    exact hrole _ (hom.roles assertion hmem)
  · intro assertion hmem
    exact hnegative _ (hom.negativeRoles assertion hmem)

/-- A consistent quotient proves the source ontology consistent. -/
theorem NativeABox.fullSatisfiable_of_homomorphism
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role))
    (hfull : target.FullSatisfiable ontology) :
    source.FullSatisfiable ontology := by
  rcases hfull with ⟨Domain, I, value, hnonempty, hmodels, habox⟩
  exact ⟨Domain, I, value ∘ h, hnonempty, hmodels,
    NativeABox.models_of_homomorphism hom I value habox⟩

/-- A sub-ABox of the source: every assertion of `sub` is an assertion of
`source` itself (identity map on individuals). -/
theorem NativeABox.not_fullSatisfiable_of_subABox
    {sub source : NativeABox Individual Concept Role}
    (hom : sub.Homomorphism source id)
    (ontology : List (Clause Variable Concept Role))
    (hunsat : ¬ sub.FullSatisfiable ontology) :
    ¬ source.FullSatisfiable ontology :=
  fun hfull => hunsat (NativeABox.fullSatisfiable_of_homomorphism hom ontology hfull)

/-- Every query realized together with the quotient is realized together with
the source, in the same interpretation. -/
theorem NativeABox.satisfiableWithQuery_of_homomorphism
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role)) (query : List (Lit Concept))
    (hquery : target.SatisfiableWithQuery ontology query) :
    source.SatisfiableWithQuery ontology query := by
  rcases hquery with ⟨Domain, I, value, element, hnonempty, hmodels, habox, hrealizes⟩
  exact ⟨Domain, I, value ∘ h, element, hnonempty, hmodels,
    NativeABox.models_of_homomorphism hom I value habox, hrealizes⟩

/-- Upper bound: the quotient entails every source subsumption. -/
theorem NativeABox.entailsSubWith_of_homomorphism
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role)) (sub sup : Concept)
    (hentails : source.EntailsSubWith ontology sub sup) :
    target.EntailsSubWith ontology sub sup :=
  fun hquery => hentails
    (NativeABox.satisfiableWithQuery_of_homomorphism hom ontology _ hquery)

/-- Upper bound: the quotient proves every source unsatisfiability. -/
theorem NativeABox.unsatisfiableConceptWith_of_homomorphism
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role)) (concept : Concept)
    (hunsat : source.UnsatisfiableConceptWith ontology concept) :
    target.UnsatisfiableConceptWith ontology concept :=
  fun hquery => hunsat
    (NativeABox.satisfiableWithQuery_of_homomorphism hom ontology _ hquery)

/-- Lower bound: TBox subsumptions hold with every ABox. -/
theorem NativeABox.entailsSubWith_of_entailsSub
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role)) (sub sup : Concept)
    (hentails : EntailsSub ontology sub sup) :
    abox.EntailsSubWith ontology sub sup := by
  rintro ⟨Domain, I, value, element, _, hmodels, _, hrealizes⟩
  have hsub : I.concept sub element := by
    simpa [Interp.satLit, Lit.pos] using hrealizes (.pos sub) (by simp)
  have hnotSup : ¬I.concept sup element := by
    simpa [Interp.satLit, Lit.negated] using hrealizes (.negated sup) (by simp)
  exact hnotSup (hentails Domain I hmodels element hsub)

/-- Lower bound: TBox unsatisfiability holds with every ABox. -/
theorem NativeABox.unsatisfiableConceptWith_of_unsatisfiableConcept
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role)) (concept : Concept)
    (hunsat : UnsatisfiableConcept ontology concept) :
    abox.UnsatisfiableConceptWith ontology concept := by
  rintro ⟨Domain, I, value, element, _, hmodels, _, hrealizes⟩
  have hconcept : I.concept concept element := by
    simpa [Interp.satLit, Lit.pos] using hrealizes (.pos concept) (by simp)
  exact hunsat Domain I hmodels element hconcept

/-- Sandwich: if the quotient answer never exceeds the TBox answer, the source
answer equals the quotient answer. No closure property of the TBox is needed,
so this covers TBox nominals. -/
theorem NativeABox.entailsSubWith_iff_of_sandwich
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role)) (sub sup : Concept)
    (hagree : target.EntailsSubWith ontology sub sup → EntailsSub ontology sub sup) :
    source.EntailsSubWith ontology sub sup ↔ target.EntailsSubWith ontology sub sup :=
  ⟨NativeABox.entailsSubWith_of_homomorphism hom ontology sub sup,
    fun htarget => source.entailsSubWith_of_entailsSub ontology sub sup (hagree htarget)⟩

theorem NativeABox.unsatisfiableConceptWith_iff_of_sandwich
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role)) (concept : Concept)
    (hagree : target.UnsatisfiableConceptWith ontology concept →
      UnsatisfiableConcept ontology concept) :
    source.UnsatisfiableConceptWith ontology concept ↔
      target.UnsatisfiableConceptWith ontology concept :=
  ⟨NativeABox.unsatisfiableConceptWith_of_homomorphism hom ontology concept,
    fun htarget => source.unsatisfiableConceptWith_of_unsatisfiableConcept
      ontology concept (hagree htarget)⟩

/-- With a consistent ABox and public-concept amalgamation, concept
unsatisfiability is exactly TBox unsatisfiability. -/
theorem NativeABox.unsatisfiableConceptWith_iff_of_modelAmalgamationFor
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (requested : Concept → Prop)
    (hfull : abox.FullSatisfiable ontology)
    (hamalgamate : abox.ModelAmalgamationFor ontology requested)
    (concept : Concept) (hpublic : requested concept) :
    abox.UnsatisfiableConceptWith ontology concept ↔
      UnsatisfiableConcept ontology concept := by
  constructor
  · intro hunsat OtherDomain other hother value hconcept
    rcases hfull with
      ⟨WitnessDomain, witness, individual, ⟨witnessValue⟩, hwitness, habox⟩
    rcases hamalgamate WitnessDomain witness individual hwitness habox
        OtherDomain other hother with
      ⟨CombinedDomain, combined, includeWitness, includeOther,
        hcombined, haboxCombined, hpreserve⟩
    apply hunsat
    refine ⟨CombinedDomain, combined, includeWitness ∘ individual,
      includeOther value, ⟨includeWitness witnessValue⟩, hcombined, haboxCombined, ?_⟩
    intro literal hliteral
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
    subst hliteral
    simpa [Interp.satLit, Lit.pos] using (hpreserve concept hpublic value).2 hconcept
  · exact abox.unsatisfiableConceptWith_of_unsatisfiableConcept ontology concept

/-- Quotient publication for amalgamating TBoxes: a consistent quotient has
the same public subsumptions as the source. -/
theorem NativeABox.entailsSubWith_iff_of_quotient
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role))
    (requested : Concept → Prop)
    (hfull : target.FullSatisfiable ontology)
    (hsource : source.ModelAmalgamationFor ontology requested)
    (htarget : target.ModelAmalgamationFor ontology requested)
    (sub sup : Concept) (hsub : requested sub) (hsup : requested sup) :
    source.EntailsSubWith ontology sub sup ↔ target.EntailsSubWith ontology sub sup := by
  rw [source.entailsSubWith_iff_entailsSub_of_modelAmalgamationFor ontology requested
      (NativeABox.fullSatisfiable_of_homomorphism hom ontology hfull) hsource
      sub sup hsub hsup,
    target.entailsSubWith_iff_entailsSub_of_modelAmalgamationFor ontology requested
      hfull htarget sub sup hsub hsup]

/-- Quotient publication for amalgamating TBoxes: unsatisfiability agrees. -/
theorem NativeABox.unsatisfiableConceptWith_iff_of_quotient
    {source : NativeABox Individual Concept Role}
    {target : NativeABox Image Concept Role} {h : Individual → Image}
    (hom : source.Homomorphism target h)
    (ontology : List (Clause Variable Concept Role))
    (requested : Concept → Prop)
    (hfull : target.FullSatisfiable ontology)
    (hsource : source.ModelAmalgamationFor ontology requested)
    (htarget : target.ModelAmalgamationFor ontology requested)
    (concept : Concept) (hpublic : requested concept) :
    source.UnsatisfiableConceptWith ontology concept ↔
      target.UnsatisfiableConceptWith ontology concept := by
  rw [source.unsatisfiableConceptWith_iff_of_modelAmalgamationFor ontology requested
      (NativeABox.fullSatisfiable_of_homomorphism hom ontology hfull) hsource
      concept hpublic,
    target.unsatisfiableConceptWith_iff_of_modelAmalgamationFor ontology requested
      hfull htarget concept hpublic]

#print axioms NativeABox.models_of_homomorphism
#print axioms NativeABox.fullSatisfiable_of_homomorphism
#print axioms NativeABox.not_fullSatisfiable_of_subABox
#print axioms NativeABox.satisfiableWithQuery_of_homomorphism
#print axioms NativeABox.entailsSubWith_of_homomorphism
#print axioms NativeABox.unsatisfiableConceptWith_of_homomorphism
#print axioms NativeABox.entailsSubWith_of_entailsSub
#print axioms NativeABox.unsatisfiableConceptWith_of_unsatisfiableConcept
#print axioms NativeABox.entailsSubWith_iff_of_sandwich
#print axioms NativeABox.unsatisfiableConceptWith_iff_of_sandwich
#print axioms NativeABox.unsatisfiableConceptWith_iff_of_modelAmalgamationFor
#print axioms NativeABox.entailsSubWith_iff_of_quotient
#print axioms NativeABox.unsatisfiableConceptWith_iff_of_quotient

end ContextCalculus.Hypertableau
