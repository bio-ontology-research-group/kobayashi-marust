import ContextCalculus.SRIQN.NormalForm
import ContextCalculus.SRIQ.ABox

/-!
# ABoxes as nominal clauses (stage C2, design section 1)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. Each individual `i` gets a nominal
name `N_i` (`nN i`) and, for negative role assertions, a complement name
`nC i`. The names of the encoding are `CName ⊕ (Ind ⊕ Ind)`: old names,
nominal names, complement names. Each assertion contributes the nominal
clauses of its individuals and the clauses of the design table.

`encNom_correct`: the knowledge base is consistent iff its encoding is.
`entailsSubKB_encNom`: subsumption between old names is unchanged. This
embeds the C1b knowledge bases into `SRIQN`.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Assertion ABox satABox satAssert ConsistentKB EntailsSubKB)

variable {D CName Role Ind : Type}

/-- The names of the encoding. -/
abbrev EName (CName Ind : Type) := CName ⊕ (Ind ⊕ Ind)

/-- The nominal name of an individual. -/
def nN (i : Ind) : EName CName Ind := .inr (.inl i)

/-- The complement of the nominal name of an individual. -/
def nC (i : Ind) : EName CName Ind := .inr (.inr i)

/-- The clauses of one assertion. -/
def encAssert : Assertion CName Role Ind → Ontology (EName CName Ind) Role
  | .cls i X => [.nom (nN i), .base (.gci [nN i] [.inl X])]
  | .role i R j => [.nom (nN i), .nom (nN j), .base (.exRight (nN i) R (nN j))]
  | .nrole i R j => [.nom (nN i), .nom (nN j), .base (.allRight (nN i) R (nC j)),
      .base (.gci [nN j, nC j] []), .base (.gci [] [nN j, nC j])]
  | .same i j => [.nom (nN i), .nom (nN j), .base (.gci [nN i] [nN j]),
      .base (.gci [nN j] [nN i])]
  | .diff i j => [.nom (nN i), .nom (nN j), .base (.gci [nN i, nN j] [])]

/-- **The encoding of a knowledge base.** -/
def encNom (O : SRIQ.Ontology CName Role) (A : ABox CName Role Ind) :
    Ontology (EName CName Ind) Role :=
  (ofSRIQ O).map (mapN Sum.inl) ++ A.flatMap encAssert

/-- The interpretation of the encoding from a model of the knowledge base. -/
def upJ (I : Interp D CName Role) (ind : Ind → D) : Interp D (EName CName Ind) Role where
  c a x := match a with
    | .inl a => I.c a x
    | .inr (.inl i) => x = ind i
    | .inr (.inr i) => x ≠ ind i
  r := I.r

theorem upJ_rt (I : Interp D CName Role) (ind : Ind → D) (R : RoleT Role) (x y : D) :
    (upJ I ind).rt R x y ↔ I.rt R x y := by
  cases R <;> exact Iff.rfl

theorem models_upJ {I : Interp D CName Role} {ind : Ind → D} {O : SRIQ.Ontology CName Role}
    {A : ABox CName Role Ind} (hI : SRIQ.models I O) (hA : satABox I ind A) :
    models (upJ I ind) (encNom O A) := by
  intro cl hcl
  rcases List.mem_append.1 hcl with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    rw [satClause_mapN]
    exact models_ofSRIQ.2 hI c hc
  · obtain ⟨as, has, hcl⟩ := List.mem_flatMap.1 h
    have hs := hA as has
    cases as with
    | cls i X =>
      simp only [encAssert, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact ⟨ind i, fun y => Iff.rfl⟩
      · rintro x hx
        have : x = ind i := hx _ List.mem_cons_self
        subst this
        exact ⟨_, List.mem_cons_self, hs⟩
    | role i R j =>
      simp only [encAssert, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact ⟨ind i, fun y => Iff.rfl⟩
      · exact ⟨ind j, fun y => Iff.rfl⟩
      · rintro x (rfl : x = ind i)
        exact ⟨ind j, (upJ_rt I ind R _ _).2 hs, rfl⟩
    | nrole i R j =>
      simp only [encAssert, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl | rfl
      · exact ⟨ind i, fun y => Iff.rfl⟩
      · exact ⟨ind j, fun y => Iff.rfl⟩
      · rintro x (rfl : x = ind i) y hy (rfl : y = ind j)
        exact hs ((upJ_rt I ind R _ _).1 hy)
      · intro x hx
        exact absurd (hx _ List.mem_cons_self : x = ind j)
          (hx _ (List.mem_cons_of_mem _ List.mem_cons_self) : x ≠ ind j)
      · intro x _
        by_cases hx : x = ind j
        · exact ⟨_, List.mem_cons_self, hx⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hx⟩
    | same i j =>
      simp only [encAssert, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl
      · exact ⟨ind i, fun y => Iff.rfl⟩
      · exact ⟨ind j, fun y => Iff.rfl⟩
      · intro x hx
        have : x = ind i := hx _ List.mem_cons_self
        exact ⟨_, List.mem_cons_self, (this.trans hs : x = ind j)⟩
      · intro x hx
        have : x = ind j := hx _ List.mem_cons_self
        exact ⟨_, List.mem_cons_self, (this.trans hs.symm : x = ind i)⟩
    | diff i j =>
      simp only [encAssert, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact ⟨ind i, fun y => Iff.rfl⟩
      · exact ⟨ind j, fun y => Iff.rfl⟩
      · intro x hx
        have h1 : x = ind i := hx _ List.mem_cons_self
        have h2 : x = ind j := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
        exact absurd (h1.symm.trans h2) hs

/-- The values of the individuals in a model of the encoding. -/
noncomputable def indOf (J : Interp D (EName CName Ind) Role) (x0 : D) (i : Ind) : D := by
  classical
  exact if h : ∃ x, J.c (nN i) x then h.choose else x0

theorem indOf_spec {J : Interp D (EName CName Ind) Role} (x0 : D) {i : Ind}
    (h : NomAt J (nN i)) : ∀ y, J.c (nN i) y ↔ y = indOf J x0 i := by
  obtain ⟨x, hx⟩ := h
  have hex : ∃ x, J.c (nN i) x := ⟨x, (hx x).2 rfl⟩
  have hv : indOf J x0 i = x := by
    unfold indOf
    rw [dif_pos hex]
    exact (hx _).1 hex.choose_spec
  rw [hv]
  exact hx

theorem satABox_down {J : Interp D (EName CName Ind) Role} {O : SRIQ.Ontology CName Role}
    {A : ABox CName Role Ind} (hJ : models J (encNom O A)) (x0 : D) :
    SRIQ.models (pull J Sum.inl) O ∧ satABox (pull J Sum.inl) (indOf J x0) A := by
  refine ⟨models_ofSRIQ.1 ((models_mapN J _ _).1 fun cl hcl =>
    hJ cl (List.mem_append_left _ hcl)), fun as has => ?_⟩
  have hin : ∀ cl ∈ encAssert as, satClause J cl := fun cl hcl =>
    hJ cl (List.mem_append_right _ (List.mem_flatMap.2 ⟨as, has, hcl⟩))
  have hval : ∀ i, Clause.nom (nN i) ∈ encAssert as → J.c (nN i) (indOf J x0 i) :=
    fun i hi => (indOf_spec x0 (hin _ hi) _).2 rfl
  have huniq : ∀ i, Clause.nom (nN i) ∈ encAssert as → ∀ y, J.c (nN i) y → y = indOf J x0 i :=
    fun i hi y hy => (indOf_spec x0 (hin _ hi) _).1 hy
  cases as with
  | cls i X =>
    have h1 := hval i (by simp [encAssert])
    have h2 : satClause J (.base (.gci [nN i] [.inl X])) := hin _ (by simp [encAssert])
    obtain ⟨b, hb, hbx⟩ := h2 _ (by simpa using h1)
    simp only [List.mem_singleton] at hb
    subst hb
    exact hbx
  | role i R j =>
    have h1 := hval i (by simp [encAssert])
    have h2 : satClause J (.base (.exRight (nN i) R (nN j))) := hin _ (by simp [encAssert])
    obtain ⟨y, hy, hyj⟩ := h2 _ h1
    have := huniq j (by simp [encAssert]) y hyj
    subst this
    exact (pull_rt J _ R _ _).2 hy
  | nrole i R j =>
    intro hR
    have h1 := hval i (by simp [encAssert])
    have h2 : satClause J (.base (.allRight (nN i) R (nC j))) := hin _ (by simp [encAssert])
    have h3 : satClause J (.base (.gci [nN j, nC j] [])) := hin _ (by simp [encAssert])
    have hc := h2 _ h1 _ ((pull_rt J _ R _ _).1 hR)
    obtain ⟨b, hb, -⟩ := h3 (indOf J x0 j) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hval j (by simp [encAssert]), hc⟩)
    simp at hb
  | same i j =>
    have h1 := hval i (by simp [encAssert])
    have h2 : satClause J (.base (.gci [nN i] [nN j])) := hin _ (by simp [encAssert])
    obtain ⟨b, hb, hbx⟩ := h2 _ (by simpa using h1)
    simp only [List.mem_singleton] at hb
    subst hb
    exact huniq j (by simp [encAssert]) _ hbx
  | diff i j =>
    intro he
    have h1 := hval i (by simp [encAssert])
    have h1' := hval j (by simp [encAssert])
    have h2 : satClause J (.base (.gci [nN i, nN j] [])) := hin _ (by simp [encAssert])
    obtain ⟨b, hb, -⟩ := h2 (indOf J x0 i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨h1, he ▸ h1'⟩)
    simp at hb

/-- **ABox encoding.** A knowledge base is consistent iff its encoding as
nominal clauses is. -/
theorem encNom_correct (O : SRIQ.Ontology CName Role) (A : ABox CName Role Ind) :
    ConsistentKB O A ↔ ConsistentN (encNom O A) := by
  constructor
  · rintro ⟨D, hD, I, ind, hI, hA⟩
    exact ⟨D, hD, upJ I ind, models_upJ hI hA⟩
  · rintro ⟨D, ⟨x0⟩, J, hJ⟩
    obtain ⟨h1, h2⟩ := satABox_down hJ x0
    exact ⟨D, ⟨x0⟩, _, _, h1, h2⟩

/-- **Subsumption through the encoding.** -/
theorem entailsSubKB_encNom (O : SRIQ.Ontology CName Role) (A : ABox CName Role Ind)
    (a b : CName) :
    EntailsSubKB O A a b ↔ EntailsSubN (encNom O A) (.inl a) (.inl b) := by
  constructor
  · intro h D hD J hJ x hx
    obtain ⟨h1, h2⟩ := satABox_down hJ x
    exact h D (pull J Sum.inl) _ h1 h2 x hx
  · intro h D _ I ind hI hA x hx
    exact h D (upJ I ind) (models_upJ hI hA) x hx

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.encNom_correct
#print axioms ContextCalculus.SRIQN.entailsSubKB_encNom
