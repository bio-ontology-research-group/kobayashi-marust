import ContextCalculus.OWLFrontend.HintRows

/-!
# Fresh definitions are conservative (stage H4, item 4)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 12. The plugin asks for the
sub- and superclasses and the instances of a class expression `CE`; the
producer adds `EquivalentClasses(Q CE)` with a class IRI `Q` that the
ontology does not mention and reads the rows of `Q` on the extended
ontology. `addDef O Q CE` is that extension.

* `model_of_addDef`: a model of the extension is a model of `O`.
* `model_addDef_withCls`: a model of `O`, with `Q` read as `CE`, is a model
  of the extension.
* `entailsAt_addDef`: an axiom that does not mention `Q` is entailed by the
  extension iff it is entailed by `O`.
* `entailsSubCE_addDef_left`, `entailsSubCE_addDef_right`,
  `entailsAt_addDef_type`: `Q ⊑ D`, `D ⊑ Q` and `Q(a)` on the extension are
  `CE ⊑ D`, `D ⊑ CE` and `CE(a)` on `O`.

Conditions: no axiom of `O` mentions `Q`, `CE` does not mention `Q`, and
the named individuals of `CE` are named individuals of `O` (so the keys of
`O`, read over the named individuals, keep their meaning). Every statement
holds at every datatype map, so the rows of `hintRefute_sound` and of the
witness route read on the extension transfer to `O`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

variable {DM : DatatypeMap}

/-- `O` with the definition `Q ≡ CE`. -/
def addDef (O : Ontology) (Q : IRI) (CE : ClassExpr) : Ontology :=
  ⟨O.axioms ++ [.equivalentClasses [.cls Q, CE]]⟩

/-- Satisfaction reads the named individuals only through membership. -/
theorem sat_congr_N {Dom : Type} (I : Interp DM Dom) {N N' : List IRI} (h : ∀ a, a ∈ N ↔ a ∈ N')
    (ax : Axiom) : I.sat N ax ↔ I.sat N' ax := by
  have hn : ∀ x, I.IsNamed N x ↔ I.IsNamed N' x := fun x => by
    simp only [Interp.IsNamed, h]
  cases ax with
  | hasKey c rs ps =>
    simp only [Interp.sat, hn]
  | _ => exact Iff.rfl

theorem mem_named_addDef {O : Ontology} {Q : IRI} {CE : ClassExpr}
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) (a : IRI) :
    a ∈ (addDef O Q CE).namedIndividuals ↔ a ∈ O.namedIndividuals := by
  simp only [addDef, Ontology.namedIndividuals, List.flatMap_append, List.mem_append]
  constructor
  · rintro (h | h)
    · exact h
    · simp only [List.flatMap_cons, List.flatMap_nil, Axiom.namedIndividuals, List.mem_append,
        ClassExpr.namedIndividuals, List.not_mem_nil, false_or, or_false] at h
      exact hN a h
  · exact Or.inl

/-- **A model of the extension is a model of `O`.** -/
theorem model_of_addDef {O : Ontology} {Q : IRI} {CE : ClassExpr}
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) {Dom : Type} {I : Interp DM Dom}
    (h : OWL.Model (addDef O Q CE) I) : OWL.Model O I := fun ax hax =>
  (sat_congr_N I (mem_named_addDef hN) ax).1 (h ax (List.mem_append_left _ hax))

/-- `I` with `Q` read as `CE`. -/
def defI {Dom : Type} (I : Interp DM Dom) (Q : IRI) (CE : ClassExpr) : Interp DM Dom :=
  I.withCls (Function.update I.cls Q (I.ext CE))

theorem defI_ext {Dom : Type} (I : Interp DM Dom) {Q : IRI} {CE : ClassExpr} {E : ClassExpr}
    (hE : Q ∉ E.names) (x : Dom) : (defI I Q CE).ext E x ↔ I.ext E x :=
  Interp.ext_withCls I _ E (fun a ha => Function.update_of_ne (fun (h : a = Q) => hE (h ▸ ha)) _ _) x

theorem defI_sat {Dom : Type} (I : Interp DM Dom) {Q : IRI} {CE : ClassExpr} {ax : Axiom}
    (hax : Q ∉ ax.classIRIs) (N : List IRI) : (defI I Q CE).sat N ax ↔ I.sat N ax :=
  Interp.sat_withCls I _ N ax (fun a ha => Function.update_of_ne (fun (h : a = Q) => hax (h ▸ ha)) _ _)

theorem defI_Q {Dom : Type} (I : Interp DM Dom) (Q : IRI) {CE : ClassExpr} (hC : Q ∉ CE.names)
    (x : Dom) : (defI I Q CE).ext (.cls Q) x ↔ (defI I Q CE).ext CE x := by
  rw [defI_ext I hC, Interp.ext]
  simp [defI]

/-- **A model of `O`, with `Q` read as `CE`, is a model of the extension.** -/
theorem model_addDef_withCls {O : Ontology} {Q : IRI} {CE : ClassExpr}
    (hO : ∀ ax ∈ O.axioms, Q ∉ ax.classIRIs) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) {Dom : Type} {I : Interp DM Dom}
    (h : OWL.Model O I) : OWL.Model (addDef O Q CE) (defI I Q CE) := by
  intro ax hax
  rw [sat_congr_N _ (mem_named_addDef hN) ax]
  rcases List.mem_append.1 hax with hax | hax
  · exact (defI_sat I (hO ax hax) _).2 (h ax hax)
  · rw [List.mem_singleton.1 hax]
    have hQ := defI_Q I Q hC
    intro c hc d hd x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact hx
    · exact (hQ x).1 hx
    · exact (hQ x).2 hx
    · exact hx

variable {O : Ontology} {Q : IRI} {CE : ClassExpr}

/-- **Conservativity**: an axiom without `Q` is entailed by the extension iff by `O`. -/
theorem entailsAt_addDef (hO : ∀ ax ∈ O.axioms, Q ∉ ax.classIRIs) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) {ax : Axiom} (hax : Q ∉ ax.classIRIs) :
    EntailsAt DM (addDef O Q CE) ax ↔ EntailsAt DM O ax := by
  constructor
  · intro h Dom _ I hI
    exact (defI_sat I hax _).1 (h Dom (defI I Q CE) (model_addDef_withCls hO hC hN hI))
  · intro h Dom _ I hI
    exact h Dom I (model_of_addDef hN hI)

/-- **`Q ⊑ D` on the extension is `CE ⊑ D` on `O`.** -/
theorem entailsSubCE_addDef_left (hO : ∀ ax ∈ O.axioms, Q ∉ ax.classIRIs) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) {D : ClassExpr} (hD : Q ∉ D.names) :
    EntailsSubCE DM (addDef O Q CE) (.cls Q) D ↔ EntailsSubCE DM O CE D := by
  constructor
  · intro h Dom _ I hI x hx
    have hM := model_addDef_withCls hO hC hN hI
    have := h Dom _ hM x ((defI_Q I Q hC x).2 ((defI_ext I hC x).2 hx))
    exact (defI_ext I hD x).1 this
  · intro h Dom _ I hI x hx
    have hdef := hI _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact h Dom I (model_of_addDef hN hI) x (hdef (.cls Q) (by simp) CE (by simp) x hx)

/-- **`D ⊑ Q` on the extension is `D ⊑ CE` on `O`.** -/
theorem entailsSubCE_addDef_right (hO : ∀ ax ∈ O.axioms, Q ∉ ax.classIRIs) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) {D : ClassExpr} (hD : Q ∉ D.names) :
    EntailsSubCE DM (addDef O Q CE) D (.cls Q) ↔ EntailsSubCE DM O D CE := by
  constructor
  · intro h Dom _ I hI x hx
    have hM := model_addDef_withCls hO hC hN hI
    have := h Dom _ hM x ((defI_ext I hD x).2 hx)
    exact (defI_ext I hC x).1 ((defI_Q I Q hC x).1 this)
  · intro h Dom _ I hI x hx
    have hdef := hI _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact hdef CE (by simp) (.cls Q) (by simp) x (h Dom I (model_of_addDef hN hI) x hx)

/-- **`Q(a)` on the extension is `CE(a)` on `O`.** -/
theorem entailsAt_addDef_type (hO : ∀ ax ∈ O.axioms, Q ∉ ax.classIRIs) (hC : Q ∉ CE.names)
    (hN : ∀ a ∈ CE.namedIndividuals, a ∈ O.namedIndividuals) (a : Individual) :
    EntailsAt DM (addDef O Q CE) (.classAssertion (.cls Q) a) ↔
      EntailsAt DM O (.classAssertion CE a) := by
  constructor
  · intro h Dom _ I hI
    have hM := model_addDef_withCls hO hC hN hI
    have := h Dom _ hM
    simp only [Interp.sat] at this ⊢
    exact (defI_ext I hC _).1 ((defI_Q I Q hC _).1 this)
  · intro h Dom _ I hI
    have hdef := hI _ (List.mem_append_right _ (List.mem_singleton_self _))
    have := h Dom I (model_of_addDef hN hI)
    simp only [Interp.sat] at this ⊢
    exact hdef CE (by simp) (.cls Q) (by simp) _ this

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.entailsAt_addDef
#print axioms ContextCalculus.OWLFrontend.entailsSubCE_addDef_left
#print axioms ContextCalculus.OWLFrontend.entailsSubCE_addDef_right
#print axioms ContextCalculus.OWLFrontend.entailsAt_addDef_type
