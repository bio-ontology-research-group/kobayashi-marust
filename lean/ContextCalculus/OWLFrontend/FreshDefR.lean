import ContextCalculus.OWLFrontend.FreshDef

/-!
# Fresh definitions with keys and DL-safe rules (stage H5, item 3)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 13. `addDefR R Q CE` adds
`EquivalentClasses(Q CE)` to the ontology part of an ontology with rules.
With the conditions of `FreshDef.lean` and one more (no rule mentions `Q`
in a class atom), the extension is conservative and `Q ⊑ D`, `D ⊑ Q`,
`Q(a)` on the extension are `CE ⊑ D`, `D ⊑ CE`, `CE(a)` on `R`:

* `entailsAtR_addDef`, `entailsSubCER_addDef_left`,
  `entailsSubCER_addDef_right`, `entailsAtR_addDef_type`.

So the witness row and `hintRefuteMR_sound` read on `addDefR R Q CE`
certify the rows of a class expression on `R`. Every statement holds at
every datatype map and every reading of the built-ins.
-/

namespace ContextCalculus.OWL

/-- The class names of a rule atom. -/
def RAtom.clsNames : RAtom → List IRI
  | .cls c _ => c.names
  | _ => []

/-- The class names of a rule. -/
def DLRule.clsNames (ρ : DLRule) : List IRI := (ρ.body ++ ρ.head).flatMap RAtom.clsNames

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

variable {DM : DatatypeMap}

/-- `R` with the definition `Q ≡ CE` in its ontology part. -/
def addDefR (R : OntologyR) (Q : IRI) (CE : ClassExpr) : OntologyR :=
  ⟨addDef R.onto Q CE, R.rules⟩

theorem mem_named_addDefR {R : OntologyR} {Q : IRI} {CE : ClassExpr}
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) (a : IRI) :
    a ∈ (addDefR R Q CE).named ↔ a ∈ R.named := by
  simp only [OntologyR.named, addDefR, List.mem_append]
  rw [mem_named_addDef hN]

theorem isNamed_congrN {Dom : Type} (I : Interp DM Dom) {N N' : List IRI} (h : ∀ a, a ∈ N ↔ a ∈ N')
    (x : Dom) : I.IsNamed N x ↔ I.IsNamed N' x := by
  simp only [Interp.IsNamed, h]

theorem ruleSat_congr_N (bi : BuiltIns DM) {Dom : Type} (I : Interp DM Dom) {N N' : List IRI}
    (h : ∀ a, a ∈ N ↔ a ∈ N') (ρ : DLRule) : ρ.sat bi I N ↔ ρ.sat bi I N' := by
  unfold DLRule.sat
  simp only [isNamed_congrN I h]

/-- An atom without `Q` has the same truth in `defI`. -/
theorem atomSat_defI (bi : BuiltIns DM) {Dom : Type} (I : Interp DM Dom) {Q : IRI} {CE : ClassExpr}
    (a : RAtom) (ha : Q ∉ a.clsNames) (σ : IRI → Dom) (δ : IRI → DM.Val) :
    a.sat bi (defI I Q CE) σ δ ↔ a.sat bi I σ δ := by
  cases a with
  | cls c x =>
    simp only [RAtom.clsNames] at ha
    exact defI_ext I ha _
  | obj r x y => exact Iff.rfl
  | data p x d => exact Iff.rfl
  | drange r d => exact Iff.rfl
  | same x y => exact Iff.rfl
  | diff x y => exact Iff.rfl
  | builtin f args => exact Iff.rfl

theorem ruleSat_defI (bi : BuiltIns DM) {Dom : Type} (I : Interp DM Dom) {Q : IRI} {CE : ClassExpr}
    (ρ : DLRule) (hρ : Q ∉ ρ.clsNames) (N : List IRI) :
    ρ.sat bi (defI I Q CE) N ↔ ρ.sat bi I N := by
  have hb : ∀ a ∈ ρ.body, Q ∉ a.clsNames := fun a ha h =>
    hρ (List.mem_flatMap.2 ⟨a, List.mem_append_left _ ha, h⟩)
  have hh : ∀ a ∈ ρ.head, Q ∉ a.clsNames := fun a ha h =>
    hρ (List.mem_flatMap.2 ⟨a, List.mem_append_right _ ha, h⟩)
  unfold DLRule.sat
  constructor
  · intro h σ δ hv hbody a ha
    exact (atomSat_defI bi I a (hh a ha) σ δ).1
      (h σ δ hv (fun b hb' => (atomSat_defI bi I b (hb b hb') σ δ).2 (hbody b hb')) a ha)
  · intro h σ δ hv hbody a ha
    exact (atomSat_defI bi I a (hh a ha) σ δ).2
      (h σ δ hv (fun b hb' => (atomSat_defI bi I b (hb b hb') σ δ).1 (hbody b hb')) a ha)

variable {R : OntologyR} {Q : IRI} {CE : ClassExpr}

theorem modelR_of_addDefR (bi : BuiltIns DM)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) {Dom : Type} {I : Interp DM Dom}
    (h : ModelR bi (addDefR R Q CE) I) : ModelR bi R I := by
  have hn := mem_named_addDefR (R := R) (Q := Q) hN
  refine ⟨fun ax hax => (sat_congr_N I hn ax).1 (h.1 ax (List.mem_append_left _ hax)),
    fun ρ hρ => (ruleSat_congr_N bi I hn ρ).1 (h.2 ρ hρ)⟩

theorem modelR_addDefR_defI (bi : BuiltIns DM) (hO : ∀ ax ∈ R.onto.axioms, Q ∉ ax.classIRIs)
    (hR : ∀ ρ ∈ R.rules, Q ∉ ρ.clsNames) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) {Dom : Type} {I : Interp DM Dom}
    (h : ModelR bi R I) : ModelR bi (addDefR R Q CE) (defI I Q CE) := by
  have hn := mem_named_addDefR (R := R) (Q := Q) hN
  refine ⟨fun ax hax => ?_, fun ρ hρ => ?_⟩
  · rw [sat_congr_N _ hn ax]
    rcases List.mem_append.1 hax with hax | hax
    · exact (defI_sat I (hO ax hax) _).2 (h.1 ax hax)
    · rw [List.mem_singleton.1 hax]
      have hQ := defI_Q I Q hC
      intro c hc d hd x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact hx
      · exact (hQ x).1 hx
      · exact (hQ x).2 hx
      · exact hx
  · rw [ruleSat_congr_N bi _ hn ρ]
    exact (ruleSat_defI bi I ρ (hR ρ hρ) _).2 (h.2 ρ hρ)

/-- **Conservativity with rules.** -/
theorem entailsAtR_addDef (bi : BuiltIns DM) (hO : ∀ ax ∈ R.onto.axioms, Q ∉ ax.classIRIs)
    (hR : ∀ ρ ∈ R.rules, Q ∉ ρ.clsNames) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) {ax : Axiom}
    (hax : Q ∉ ax.classIRIs) :
    EntailsAtR DM bi (addDefR R Q CE) ax ↔ EntailsAtR DM bi R ax := by
  constructor
  · intro h Dom _ I hI
    exact (defI_sat I hax _).1 (h Dom (defI I Q CE) (modelR_addDefR_defI bi hO hR hC hN hI))
  · intro h Dom _ I hI
    exact h Dom I (modelR_of_addDefR bi hN hI)

/-- **`Q ⊑ D` on the extension is `CE ⊑ D` on `R`.** -/
theorem entailsSubCER_addDef_left (bi : BuiltIns DM) (hO : ∀ ax ∈ R.onto.axioms, Q ∉ ax.classIRIs)
    (hR : ∀ ρ ∈ R.rules, Q ∉ ρ.clsNames) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) {D : ClassExpr} (hD : Q ∉ D.names) :
    EntailsSubCER DM bi (addDefR R Q CE) (.cls Q) D ↔ EntailsSubCER DM bi R CE D := by
  constructor
  · intro h Dom _ I hI x hx
    have hM := modelR_addDefR_defI bi hO hR hC hN hI
    have := h Dom _ hM x ((defI_Q I Q hC x).2 ((defI_ext I hC x).2 hx))
    exact (defI_ext I hD x).1 this
  · intro h Dom _ I hI x hx
    have hdef := hI.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact h Dom I (modelR_of_addDefR bi hN hI) x (hdef (.cls Q) (by simp) CE (by simp) x hx)

/-- **`D ⊑ Q` on the extension is `D ⊑ CE` on `R`.** -/
theorem entailsSubCER_addDef_right (bi : BuiltIns DM) (hO : ∀ ax ∈ R.onto.axioms, Q ∉ ax.classIRIs)
    (hR : ∀ ρ ∈ R.rules, Q ∉ ρ.clsNames) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) {D : ClassExpr} (hD : Q ∉ D.names) :
    EntailsSubCER DM bi (addDefR R Q CE) D (.cls Q) ↔ EntailsSubCER DM bi R D CE := by
  constructor
  · intro h Dom _ I hI x hx
    have hM := modelR_addDefR_defI bi hO hR hC hN hI
    have := h Dom _ hM x ((defI_ext I hD x).2 hx)
    exact (defI_ext I hC x).1 ((defI_Q I Q hC x).1 this)
  · intro h Dom _ I hI x hx
    have hdef := hI.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact hdef CE (by simp) (.cls Q) (by simp) x (h Dom I (modelR_of_addDefR bi hN hI) x hx)

/-- **`Q(a)` on the extension is `CE(a)` on `R`.** -/
theorem entailsAtR_addDef_type (bi : BuiltIns DM) (hO : ∀ ax ∈ R.onto.axioms, Q ∉ ax.classIRIs)
    (hR : ∀ ρ ∈ R.rules, Q ∉ ρ.clsNames) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ R.onto.namedIndividuals) (a : Individual) :
    EntailsAtR DM bi (addDefR R Q CE) (.classAssertion (.cls Q) a) ↔
      EntailsAtR DM bi R (.classAssertion CE a) := by
  constructor
  · intro h Dom _ I hI
    have hM := modelR_addDefR_defI bi hO hR hC hN hI
    have := h Dom _ hM
    simp only [Interp.sat] at this ⊢
    exact (defI_ext I hC _).1 ((defI_Q I Q hC _).1 this)
  · intro h Dom _ I hI
    have hdef := hI.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
    have := h Dom I (modelR_of_addDefR bi hN hI)
    simp only [Interp.sat] at this ⊢
    exact hdef CE (by simp) (.cls Q) (by simp) _ this

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.entailsAtR_addDef
#print axioms ContextCalculus.OWLFrontend.entailsSubCER_addDef_left
#print axioms ContextCalculus.OWLFrontend.entailsSubCER_addDef_right
#print axioms ContextCalculus.OWLFrontend.entailsAtR_addDef_type
