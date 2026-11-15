import ContextCalculus.OWLFrontend.HintWitness

/-!
# Built-in class IRIs in requested positions (stage H2, item 0)

`EntailsSubAt DM O A B` and the row axioms of the hint route read a class
IRI `A` as `I.cls A`, a free predicate. The parser reads the IRI
`owl:Thing` as `ClassExpr.thing` and `owl:Nothing` as `ClassExpr.nothing`,
so for those two IRIs the IRI-level rows are true statements about a free
name, not the OWL statements their names suggest. This file states the
rows for the class expression the parser gives an IRI (`clsOf`) and
derives them from the IRI-level theorems, which stay as they are:

* `hintNonSubC_sound`, `hintNonSubsC_sound`: `O ⊭ clsOf A ⊑ clsOf B`, for
  `A ≠ owl:Nothing` and `B ≠ owl:Thing` (`A ⊑ owl:Thing` always holds and
  `owl:Nothing ⊑ B` always holds, so those rows are never certified);
* `hintNonTypeC_sound`, `hintNonTypesC_sound`: `O ⊭ (clsOf C)(a)`, for
  `C ≠ owl:Thing`;
* `hintWitnessC_sound`: the witness row for class expressions, with
  `owl:Nothing` as object (any witness of `A` certifies `A ⋢ owl:Nothing`)
  and `owl:Thing` as subject (`owl:Thing ⋢ B` when some core element lacks
  `B`'s name). The requested classes of `wTab` never include the two
  built-in IRIs (`wReq` removes them), so `.cls A` there is the class `A`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.OWL.Parse (owlThing owlNothing owlNs)

/-- The class expression the parser gives a class IRI. -/
def clsOf (s : IRI) : ClassExpr :=
  if s = owlThing then .thing else if s = owlNothing then .nothing else .cls s

/-- `owl:Thing` or `owl:Nothing`. -/
def isBuiltinCls (s : IRI) : Bool := s == owlThing || s == owlNothing

/-- Subsumption between class expressions at a datatype map. -/
def EntailsSubCE (DM : DatatypeMap) (O : Ontology) (C D : ClassExpr) : Prop :=
  ∀ (Dom : Type) [Nonempty Dom] (I : Interp DM Dom), OWL.Model O I → ∀ x, I.ext C x → I.ext D x

variable {DM : DatatypeMap}

theorem ext_clsOf_of {Dom : Type} (I : Interp DM Dom) {s : IRI} {x : Dom} (hn : s ≠ owlNothing)
    (h : I.cls s x) : I.ext (clsOf s) x := by
  unfold clsOf
  split_ifs <;> simp_all [Interp.ext]

theorem not_ext_clsOf_of {Dom : Type} (I : Interp DM Dom) {s : IRI} {x : Dom} (ht : s ≠ owlThing)
    (h : ¬ I.cls s x) : ¬ I.ext (clsOf s) x := by
  unfold clsOf
  split_ifs <;> simp_all [Interp.ext]

theorem clsOf_of_not_builtin {s : IRI} (h : isBuiltinCls s = false) : clsOf s = .cls s := by
  simp only [isBuiltinCls, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [clsOf, h.1, h.2]

/-! ## The rows of the hint route -/

/-- **Non-subsumption row for class expressions.** -/
theorem hintNonSubC_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : RawHint} (h : hintNonSub O A B hint = some true) (hA : A ≠ owlNothing)
    (hB : B ≠ owlThing) : ¬ EntailsSubCE (owl2MapP pat) O (clsOf A) (clsOf B) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Interp.sat, Interp.ext] at hs
  exact not_ext_clsOf_of I hB hs.2 (he Dom I hI _ (ext_clsOf_of I hA hs.1))

/-- **Batch non-subsumption row for class expressions.** -/
theorem hintNonSubsC_sound (pat : String → String → Prop) {O : Ontology} {A : IRI}
    {Bs : List IRI} {hint : RawHint} (h : hintNonSubs O A Bs hint = some true) (hA : A ≠ owlNothing) :
    ∀ B ∈ Bs, B ≠ owlThing → ¬ EntailsSubCE (owl2MapP pat) O (clsOf A) (clsOf B) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro B hB hBt he
  have h1 := hs _ (List.mem_cons_self ..)
  have h2 := hs _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun B =>
    Axiom.classAssertion (.not (.cls B)) (.named (freshInd O))) hB))
  simp only [Interp.sat, Interp.ext] at h1 h2
  exact not_ext_clsOf_of I hBt h2 (he Dom I hI _ (ext_clsOf_of I hA h1))

/-- **Non-type row for class expressions.** -/
theorem hintNonTypeC_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : RawHint} (h : hintNonType O C a hint = some true) (hC : C ≠ owlThing) :
    ¬ EntailsAt (owl2MapP pat) O (.classAssertion (clsOf C) (.named a)) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  have := he Dom I hI
  simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
  exact not_ext_clsOf_of I hC hs this

/-- **Batch non-type row for class expressions.** -/
theorem hintNonTypesC_sound (pat : String → String → Prop) {O : Ontology} {a : IRI}
    {Cs : List IRI} {hint : RawHint} (h : hintNonTypes O a Cs hint = some true) :
    ∀ C ∈ Cs, C ≠ owlThing →
      ¬ EntailsAt (owl2MapP pat) O (.classAssertion (clsOf C) (.named a)) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro C hC hCt he
  have h2 := hs _ (List.mem_map_of_mem (f := fun C =>
    Axiom.classAssertion (.not (.cls C)) (.named a)) hC)
  have := he Dom I hI
  simp only [Interp.sat, Interp.ext] at h2 this
  exact not_ext_clsOf_of I hCt h2 this

/-! ## The witness row -/

/-- The requested classes the witness route translates: the built-in IRIs
removed (they stand for `owl:Thing` and `owl:Nothing`, handled below). -/
def wReq (req : List IRI) : List IRI := req.filter fun s => !isBuiltinCls s

/-- **The witness row for class expressions.** For requested classes that
are not built-in IRIs (`wReq` removes those before the translation), and
with `owl:Nothing` as object and `owl:Thing` as subject. -/
theorem hintWitnessC_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTab O req hint = some W) :
    ConsistentAt (owl2MapP pat) O ∧
    (∀ (A B : IRI) (iA iB : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → (B, iB) ∈ W.cls →
      isBuiltinCls A = false → isBuiltinCls B = false → iA ∈ W.ty w → iB ∉ W.ty w →
      ¬ EntailsSubCE (owl2MapP pat) O (clsOf A) (clsOf B)) ∧
    (∀ (A : IRI) (iA : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → isBuiltinCls A = false →
      iA ∈ W.ty w → ¬ EntailsSubCE (owl2MapP pat) O (clsOf A) (clsOf owlNothing)) ∧
    (∀ (B : IRI) (iB : Fin W.N) (w : Fin W.k), (B, iB) ∈ W.cls → isBuiltinCls B = false →
      iB ∉ W.ty w → ¬ EntailsSubCE (owl2MapP pat) O (clsOf owlThing) (clsOf B)) ∧
    (∀ (a C : IRI) (ia iC : Fin W.N) (w : Fin W.k), (a, ia) ∈ W.inds → (C, iC) ∈ W.cls →
      isBuiltinCls C = false → ia ∈ W.ty w → iC ∉ W.ty w →
      ¬ EntailsAt (owl2MapP pat) O (.classAssertion (clsOf C) (.named a))) := by
  obtain ⟨Dom, hD, I, f, hM, -, hcls, hind⟩ := wTab_model pat hw
  haveI := hD
  have hN : clsOf owlNothing = .nothing := by simp [clsOf, owlThing, owlNothing, owlNs]
  have hT : clsOf owlThing = .thing := by simp [clsOf]
  refine ⟨⟨Dom, hD, I, hM⟩, ?_, ?_, ?_, ?_⟩
  · intro A B iA iB w hA hB hbA hbB hiA hiB he
    rw [clsOf_of_not_builtin hbA, clsOf_of_not_builtin hbB] at he
    have := he Dom I hM (f w) (by simp only [Interp.ext]; exact (hcls A iA hA w).2 hiA)
    simp only [Interp.ext] at this
    exact hiB ((hcls B iB hB w).1 this)
  · intro A iA w hA hbA hiA he
    rw [clsOf_of_not_builtin hbA, hN] at he
    have := he Dom I hM (f w) (by simp only [Interp.ext]; exact (hcls A iA hA w).2 hiA)
    simpa [Interp.ext] using this
  · intro B iB w hB hbB hiB he
    rw [clsOf_of_not_builtin hbB, hT] at he
    have := he Dom I hM (f w) (by simp [Interp.ext])
    simp only [Interp.ext] at this
    exact hiB ((hcls B iB hB w).1 this)
  · intro a C ia iC w ha hC hbC hia hiC he
    have h1 := he Dom I hM
    rw [clsOf_of_not_builtin hbC] at h1
    simp only [Interp.sat, Interp.ext] at h1
    rw [← (hind a ia ha w).2 hia] at h1
    exact hiC ((hcls C iC hC w).1 h1)

/-- A consistent ontology does not entail `owl:Thing ⊑ owl:Nothing`. -/
theorem not_thing_sub_nothing_of_consistent {O : Ontology} (h : ConsistentAt DM O) :
    ¬ EntailsSubCE DM O (clsOf owlThing) (clsOf owlNothing) := by
  obtain ⟨Dom, hD, I, hI⟩ := h
  haveI := hD
  obtain ⟨x⟩ := hD
  intro he
  have := he Dom I hI x
  simp [clsOf, owlThing, owlNothing, owlNs, Interp.ext] at this

/-- A consistent ontology does not entail `owl:Nothing(a)`. -/
theorem not_entails_nothing_of_consistent {O : Ontology} (h : ConsistentAt DM O) (a : IRI) :
    ¬ EntailsAt DM O (.classAssertion (clsOf owlNothing) (.named a)) := by
  obtain ⟨Dom, hD, I, hI⟩ := h
  haveI := hD
  intro he
  have := he Dom I hI
  simp [clsOf, owlThing, owlNothing, owlNs, Interp.sat, Interp.ext] at this

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.hintNonSubC_sound
#print axioms ContextCalculus.OWLFrontend.hintNonSubsC_sound
#print axioms ContextCalculus.OWLFrontend.hintNonTypeC_sound
#print axioms ContextCalculus.OWLFrontend.hintNonTypesC_sound
#print axioms ContextCalculus.OWLFrontend.hintWitnessC_sound
#print axioms ContextCalculus.OWLFrontend.not_entails_nothing_of_consistent
#print axioms ContextCalculus.OWLFrontend.not_thing_sub_nothing_of_consistent
