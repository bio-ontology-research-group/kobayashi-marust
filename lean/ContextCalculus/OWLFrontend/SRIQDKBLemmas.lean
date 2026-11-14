import ContextCalculus.OWLFrontend.SRIQDKBTranslate
import ContextCalculus.OWLFrontend.SRIQKBTranslateCorrect

/-!
# Lemmas for the SHIQ(D) knowledge-base translation (v1.7.0 stage C4)

Rewriting, abstraction and congruence for the axioms of the SHIQ(D)
knowledge-base part (`Ontology.isSHIQDKB`), extending those of
`SRIQDTranslateCorrect.lean` to assertions.
-/

namespace ContextCalculus.OWLFrontend.SHIQD

open ContextCalculus.OWL

variable {DM DM' : DatatypeMap} {D : Type}

/-- A rewritten axiom of the knowledge-base part: an axiom of the SHIQ(D)
part that is not a data property axiom, or an assertion of the SHIQ
knowledge-base part over an ALCIQD class expression. -/
def RwOK (ax : Axiom) : Prop :=
  (ax.isSHIQD = true ∧ isDataPropAx ax = false) ∨
    (∃ c a, ax = .classAssertion c a ∧ c.isALCIQD = true ∧ a.isNamed = true) ∨
    (ax.isAssertion = true ∧ ax.isSHIQKB = true ∧ ∀ c a, ax ≠ .classAssertion c a)

theorem rwK_ok {ax0 ax : Axiom} (h0 : ax0.isSHIQDKB = true) (h : ax ∈ rwAxiomK ax0) : RwOK ax := by
  cases ax0
  case classAssertion c a =>
    simp only [rwAxiomK, rwAxiom, List.mem_singleton] at h; subst h
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at h0
    exact Or.inr (Or.inl ⟨c, a, rfl, h0.1, h0.2⟩)
  case objectPropertyAssertion r a b =>
    simp only [rwAxiomK, rwAxiom, List.mem_singleton] at h; subst h
    exact Or.inr (Or.inr ⟨rfl, by simpa [Axiom.isSHIQDKB, Axiom.isSHIQKB] using h0, by simp⟩)
  case negativeObjectPropertyAssertion r a b =>
    simp only [rwAxiomK, rwAxiom, List.mem_singleton] at h; subst h
    exact Or.inr (Or.inr ⟨rfl, by simpa [Axiom.isSHIQDKB, Axiom.isSHIQKB] using h0, by simp⟩)
  case sameIndividual as =>
    simp only [rwAxiomK, rwAxiom, List.mem_singleton] at h; subst h
    exact Or.inr (Or.inr ⟨rfl, by simpa [Axiom.isSHIQDKB, Axiom.isSHIQKB] using h0, by simp⟩)
  case differentIndividuals as =>
    simp only [rwAxiomK, rwAxiom, List.mem_singleton] at h; subst h
    exact Or.inr (Or.inr ⟨rfl, by simpa [Axiom.isSHIQDKB, Axiom.isSHIQKB] using h0, by simp⟩)
  case declareNamedIndividual a =>
    simp only [rwAxiomK, rwAxiom, List.mem_singleton] at h; subst h
    exact Or.inr (Or.inr ⟨rfl, by simp [Axiom.isSHIQKB], by simp⟩)
  case dataPropertyAssertion p a l =>
    simp only [rwAxiomK, List.mem_singleton] at h; subst h
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at h0
    exact Or.inr (Or.inl ⟨_, a, rfl, by simp [ClassExpr.isALCIQD, h0.1], h0.2⟩)
  case negativeDataPropertyAssertion p a l =>
    simp only [rwAxiomK, List.mem_singleton] at h; subst h
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at h0
    exact Or.inr (Or.inl ⟨_, a, rfl, by simp [ClassExpr.isALCIQD, h0.1], h0.2⟩)
  all_goals
    simp only [rwAxiomK] at h
    exact Or.inl (rw_isSHIQD (by simpa [Axiom.isSHIQDKB] using h0) h)

/-- The abstraction of a rewritten axiom is in the SHIQ knowledge-base part. -/
theorem isSHIQKB_absAxK (nm : DExpr → IRI) {ax : Axiom} (h : RwOK ax) :
    (absAxK nm ax).isSHIQKB = true := by
  rcases h with ⟨h1, h2⟩ | ⟨c, a, rfl, hc, ha⟩ | ⟨h1, h2, h3⟩
  · have := isSHIQ_absAx nm h1 h2
    cases ax
    case classAssertion c a => simp [Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI] at h1
    all_goals exact Axiom.isSHIQKB_of_isSHIQ this
  · simp only [absAxK, Axiom.isSHIQKB, Bool.and_eq_true]
    exact ⟨isALCIQ_absC nm c hc, ha⟩
  · cases ax
    case classAssertion c a => exact absurd rfl (h3 c a)
    all_goals first
      | (simp [Axiom.isAssertion] at h1; done)
      | simpa [absAxK, absAx] using h2

/-- The data expressions of a rewritten axiom are all its data expressions. -/
theorem sat_absAxK {I : Interp DM D} {nm : DExpr → IRI} {ax : Axiom} (h : RwOK ax)
    (H : ∀ e ∈ axDexprsK ax, ∀ x, I.cls (nm e) x ↔ I.ext e.toCE x) (N : List IRI) :
    I.sat N (absAxK nm ax) ↔ I.sat N ax := by
  rcases h with ⟨h1, -⟩ | ⟨c, a, rfl, hc, -⟩ | ⟨h1, -, h3⟩
  · cases ax
    case classAssertion c a => simp [Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI] at h1
    all_goals exact sat_absAx h1 H N
  · simp only [absAxK, Interp.sat]
    exact ext_absC c hc H _
  · cases ax
    case classAssertion c a => exact absurd rfl (h3 c a)
    all_goals first
      | (simp [Axiom.isAssertion] at h1; done)
      | exact Iff.rfl

/-- **Rewriting.** -/
theorem sat_rwAxiomK (I : Interp DM D) {ax : Axiom} (hax : ax.isSHIQDKB = true) (N : List IRI) :
    I.sat N ax ↔ (∀ ax' ∈ rwAxiomK ax, I.sat N ax') ∧
      ∀ pq ∈ subPairs ax, ∀ x v, I.dprop pq.1 x v → I.dprop pq.2 x v := by
  cases ax
  case dataPropertyAssertion p a l =>
    simp [rwAxiomK, subPairs, Interp.sat, Interp.ext]
  case negativeDataPropertyAssertion p a l =>
    simp [rwAxiomK, subPairs, Interp.sat, Interp.ext]
  case classAssertion c a => simp [rwAxiomK, rwAxiom, subPairs]
  case objectPropertyAssertion r a b => simp [rwAxiomK, rwAxiom, subPairs]
  case negativeObjectPropertyAssertion r a b => simp [rwAxiomK, rwAxiom, subPairs]
  case sameIndividual as => simp [rwAxiomK, rwAxiom, subPairs]
  case differentIndividuals as => simp [rwAxiomK, rwAxiom, subPairs]
  case declareNamedIndividual a => simp [rwAxiomK, rwAxiom, subPairs]
  all_goals exact sat_rwAxiom I (by simpa [Axiom.isSHIQDKB] using hax) N

/-- **Congruence in the classes** for the knowledge-base part. -/
theorem sat_congr_clsK {I J : Interp DM D} (hr : I.role = J.role) (hd : I.dprop = J.dprop)
    (ht : I.dtype = J.dtype) (hi : I.ind = J.ind) {ax : Axiom} (hax : ax.isSHIQDKB = true)
    (hc : ∀ a ∈ ax.classNames, I.cls a = J.cls a) (N N' : List IRI) :
    I.sat N ax ↔ J.sat N' ax := by
  have hp := Interp.prop_congr' hr
  cases ax
  case classAssertion c a =>
    simp only [Axiom.isSHIQDKB, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    rw [Interp.sat, Interp.sat, ext_congr_cls hr hd ht c hax.1 hc, hi]
  case objectPropertyAssertion r a b => simp only [Interp.sat, hp, hi]
  case negativeObjectPropertyAssertion r a b => simp only [Interp.sat, hp, hi]
  case sameIndividual as => simp only [Interp.sat, hi]
  case differentIndividuals as => simp only [Interp.sat, hi]
  case declareNamedIndividual a => simp only [Interp.sat]
  case dataPropertyAssertion p a l =>
    cases p <;> simp [Interp.sat, Interp.dp, hd, hi]
  case negativeDataPropertyAssertion p a l =>
    cases p <;> simp [Interp.sat, Interp.dp, hd, hi]
  all_goals exact sat_congr_cls hr hd ht (by simpa [Axiom.isSHIQDKB] using hax) hc N N'

/-- **Congruence across maps** for the SHIQ knowledge-base part. -/
theorem sat_congr_mapK {I : Interp DM D} {J : Interp DM' D} (hc : I.cls = J.cls)
    (hr : I.role = J.role) (hi : I.ind = J.ind) {ax : Axiom} (hax : ax.isSHIQKB = true)
    (N N' : List IRI) : I.sat N ax ↔ J.sat N' ax := by
  have hp := Interp.prop_congr' hr
  cases ax
  case classAssertion c a =>
    simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hax
    rw [Interp.sat, Interp.sat, ClassExpr.ext_congr' hc hr c hax.1, hi]
  case objectPropertyAssertion r a b => simp only [Interp.sat, hp, hi]
  case negativeObjectPropertyAssertion r a b => simp only [Interp.sat, hp, hi]
  case sameIndividual as => simp only [Interp.sat, hi]
  case differentIndividuals as => simp only [Interp.sat, hi]
  case declareNamedIndividual a => simp only [Interp.sat]
  all_goals exact Axiom.sat_congr' hc hr (by simpa [Axiom.isSHIQKB] using hax) N N'

theorem classNames_rwK {ax0 ax : Axiom} (h : ax ∈ rwAxiomK ax0) {a : IRI} (ha : a ∈ ax.classNames) :
    a ∈ ax0.classNames := by
  cases ax0 <;> simp_all [rwAxiomK, rwAxiom, Axiom.classNames, ClassExpr.names]

end ContextCalculus.OWLFrontend.SHIQD
