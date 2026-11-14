import ContextCalculus.SRIQ.ABoxProcedure

/-!
# Realization for SHIQ knowledge bases (stage C1b, design section 6)

`docs/V1.7.0-C1B-ABOX-DESIGN.md`, section 6. Two kinds of entailment
about individuals:

* `EntailsTypeKB O A a c`: every model of `(O, A)` puts `a` in `c`;
* `EntailsSameKB O A a b`: every model of `(O, A)` gives `a` and `b` the
  same value.

Both reduce to consistency.

* `entailsTypeKB_iff`: `a` is in `c` in every model iff the knowledge base
  with a complement name `nc` of `c` and the assertion `nc(a)` is
  inconsistent. Over `Fin n` names the complement name is the new name
  `Fin.last n` of `Fin (n + 1)`, with the clauses `c ⊓ nc ⊑ ⊥` and
  `⊤ ⊑ c ⊔ nc` (`complO`); the old names and assertions are lifted by
  `Fin.castAdd 1` (`liftClause`, `liftAssert 1`). So the statement applies
  to any ontology over `Fin n`, the translation of an OWL knowledge base
  included.
* `entailsSameKB_iff`: `a = b` in every model iff adding `diff a b` is
  inconsistent.
* `typeRow` and `sameRow` decide the two with the consistency procedure
  `consistentKBQ` (an optional countermodel hint first, the exhaustive
  search as fallback); `typeRow_iff` and `sameRow_iff` say they are exact
  for every hint on SHIQ knowledge bases.
-/

namespace ContextCalculus.SRIQ

open ContextCalculus.SRI (RoleT Interp)

variable {CName Role Ind : Type}

/-- Every model of the knowledge base puts the individual `a` in `c`. -/
def EntailsTypeKB (O : Ontology CName Role) (A : ABox CName Role Ind) (a : Ind) (c : CName) :
    Prop :=
  ∀ (D : Type) [Nonempty D] (I : Interp D CName Role) (ind : Ind → D),
    models I O → satABox I ind A → I.c c (ind a)

/-- Every model of the knowledge base gives `a` and `b` the same value. -/
def EntailsSameKB (O : Ontology CName Role) (A : ABox CName Role Ind) (a b : Ind) : Prop :=
  ∀ (D : Type) [Nonempty D] (I : Interp D CName Role) (ind : Ind → D),
    models I O → satABox I ind A → ind a = ind b

theorem satABox_append {D : Type} {I : Interp D CName Role} {ind : Ind → D}
    {A A' : ABox CName Role Ind} : satABox I ind (A ++ A') ↔ satABox I ind A ∧ satABox I ind A' := by
  simp only [satABox, List.mem_append]
  exact ⟨fun h => ⟨fun as has => h as (Or.inl has), fun as has => h as (Or.inr has)⟩,
    fun h as has => has.elim (h.1 as) (h.2 as)⟩

theorem satABox_singleton {D : Type} {I : Interp D CName Role} {ind : Ind → D}
    {as : Assertion CName Role Ind} : satABox I ind [as] ↔ satAssert I ind as := by
  simp [satABox]

/-- **Equality of individuals.** `a = b` follows from a knowledge base iff
the knowledge base with `a ≠ b` is inconsistent. -/
theorem entailsSameKB_iff (O : Ontology CName Role) (A : ABox CName Role Ind) (a b : Ind) :
    EntailsSameKB O A a b ↔ ¬ ConsistentKB O (A ++ [.diff a b]) := by
  constructor
  · rintro h ⟨D, hD, I, ind, hI, hA⟩
    rw [satABox_append, satABox_singleton] at hA
    exact hA.2 (h D I ind hI hA.1)
  · intro h D _ I ind hI hA
    by_contra hne
    exact h ⟨D, inferInstance, I, ind, hI, satABox_append.2 ⟨hA, satABox_singleton.2 hne⟩⟩

namespace Proc

variable {n m : Nat}

/-- A clause on the old names `Fin.castAdd 1` of `Fin (n + 1)`. -/
def liftClause : Clause (Fin n) (Fin m) → Clause (Fin (n + 1)) (Fin m)
  | .gci body head => .gci (body.map (Fin.castAdd 1)) (head.map (Fin.castAdd 1))
  | .exRight a R b => .exRight (Fin.castAdd 1 a) R (Fin.castAdd 1 b)
  | .allRight a R b => .allRight (Fin.castAdd 1 a) R (Fin.castAdd 1 b)
  | .atLeast a k R b => .atLeast (Fin.castAdd 1 a) k R (Fin.castAdd 1 b)
  | .atMost a k R b => .atMost (Fin.castAdd 1 a) k R (Fin.castAdd 1 b)
  | .chain body S => .chain body S

/-- `O` on the old names, with the new name `Fin.last n` as the complement
of `c`: `c ⊓ nc ⊑ ⊥` and `⊤ ⊑ c ⊔ nc`. -/
def complO (O : Ontology (Fin n) (Fin m)) (c : Fin n) : Ontology (Fin (n + 1)) (Fin m) :=
  O.map liftClause ++
    [.gci [Fin.castAdd 1 c, Fin.last n] [], .gci [] [Fin.castAdd 1 c, Fin.last n]]

/-- `A` on the old names, with `nc(a)`. -/
def complA (A : ABox (Fin n) (Fin m) Ind) (a : Ind) : ABox (Fin (n + 1)) (Fin m) Ind :=
  A.map (liftAssert 1) ++ [.cls a (Fin.last n)]

/-! ### Interpretations of the old names -/

variable {D : Type}

/-- The interpretation of the old names. -/
def resI (J : Interp D (Fin (n + 1)) (Fin m)) : Interp D (Fin n) (Fin m) :=
  ⟨fun x => J.c (Fin.castAdd 1 x), J.r⟩

/-- `I` with `P` as the new name. -/
def extI (I : Interp D (Fin n) (Fin m)) (P : D → Prop) : Interp D (Fin (n + 1)) (Fin m) :=
  ⟨fun x d => if h : x.val < n then I.c ⟨x.val, h⟩ d else P d, I.r⟩

theorem resI_extI (I : Interp D (Fin n) (Fin m)) (P : D → Prop) : resI (extI I P) = I := by
  cases I with
  | mk c r =>
    simp only [resI, extI, Interp.mk.injEq, and_true]
    funext x d
    simp [Fin.castAdd]

theorem extI_last (I : Interp D (Fin n) (Fin m)) (P : D → Prop) (d : D) :
    (extI I P).c (Fin.last n) d ↔ P d := by
  simp [extI]

theorem path_resI (J : Interp D (Fin (n + 1)) (Fin m)) :
    ∀ (body : List (RoleT (Fin m))) (x y : D), (resI J).path body x y ↔ J.path body x y
  | [], _, _ => Iff.rfl
  | R :: body, x, y => by
    simp only [SRI.Interp.path]
    exact exists_congr fun z => and_congr Iff.rfl (path_resI J body z y)

theorem satClause_lift (J : Interp D (Fin (n + 1)) (Fin m)) (cl : Clause (Fin n) (Fin m)) :
    satClause (resI J) cl ↔ satClause J (liftClause cl) := by
  cases cl with
  | gci body head =>
    simp only [satClause, liftClause, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, exists_exists_and_eq_and]
    rfl
  | exRight a R b => rfl
  | allRight a R b => rfl
  | atLeast a k R b => rfl
  | atMost a k R b => rfl
  | chain body S =>
    simp only [satClause, liftClause, path_resI]
    rfl

theorem models_lift (J : Interp D (Fin (n + 1)) (Fin m)) (O : Ontology (Fin n) (Fin m)) :
    models (resI J) O ↔ models J (O.map liftClause) := by
  simp only [models, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satClause_lift]

theorem satAssert_lift {Ind : Type} (J : Interp D (Fin (n + 1)) (Fin m)) (ind : Ind → D)
    (as : Assertion (Fin n) (Fin m) Ind) :
    satAssert (resI J) ind as ↔ satAssert J ind (liftAssert 1 as) := by
  cases as <;> rfl

theorem satABox_lift {Ind : Type} (J : Interp D (Fin (n + 1)) (Fin m)) (ind : Ind → D)
    (A : ABox (Fin n) (Fin m) Ind) :
    satABox (resI J) ind A ↔ satABox J ind (A.map (liftAssert 1)) := by
  simp only [satABox, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satAssert_lift]

/-- **Types of individuals.** `a` is in `c` in every model of `(O, A)` iff
`(O, A)` with the complement `nc` of `c` and `nc(a)` is inconsistent. -/
theorem entailsTypeKB_iff {Ind : Type} (O : Ontology (Fin n) (Fin m)) (A : ABox (Fin n) (Fin m) Ind)
    (a : Ind) (c : Fin n) :
    EntailsTypeKB O A a c ↔ ¬ ConsistentKB (complO O c) (complA A a) := by
  constructor
  · rintro h ⟨D, hD, J, ind, hJ, hA⟩
    simp only [complO, models, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hJ
    rw [complA, satABox_append, satABox_singleton] at hA
    have hO : models (resI J) O := (models_lift J O).2 fun cl hcl => hJ cl (Or.inl hcl)
    have hc := h D (resI J) ind hO ((satABox_lift J ind A).2 hA.1)
    obtain ⟨b, hb, _⟩ := hJ _ (Or.inr (Or.inl rfl)) (ind a) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hc
      · exact hA.2)
    simp at hb
  · intro h D _ I ind hI hA
    by_contra hc
    refine h ⟨D, inferInstance, extI I fun d => ¬ I.c c d, ind, ?_, ?_⟩
    · intro cl hcl
      simp only [complO, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with hcl | rfl | rfl
      · exact (models_lift _ O).1 (by rw [resI_extI]; exact hI) cl hcl
      · intro x hx
        have h1 := hx _ List.mem_cons_self
        have h2 := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
        rw [extI_last] at h2
        have h1' : (resI (extI I fun d => ¬ I.c c d)).c c x := h1
        rw [resI_extI] at h1'
        exact absurd h1' h2
      · intro x _
        by_cases hx : I.c c x
        · refine ⟨_, List.mem_cons_self, ?_⟩
          show (resI (extI I fun d => ¬ I.c c d)).c c x
          rw [resI_extI]; exact hx
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (extI_last _ _ x).2 hx⟩
    · rw [complA, satABox_append, satABox_singleton, ← satABox_lift, resI_extI]
      exact ⟨hA, (extI_last _ _ _).2 hc⟩

/-! ### The SHIQ conditions carry over -/

theorem mem_complO_chain {O : Ontology (Fin n) (Fin m)} {c : Fin n} {body : List (RoleT (Fin m))}
    {S : RoleT (Fin m)} : Clause.chain body S ∈ complO O c ↔ Clause.chain body S ∈ O := by
  rw [complO, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨cl, hcl, he⟩ | h)
    · cases cl <;> simp only [liftClause, reduceCtorEq, Clause.chain.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hcl
    · simp at h
  · intro h
    exact Or.inl ⟨_, h, rfl⟩

theorem roleLe_complO (O : Ontology (Fin n) (Fin m)) (c : Fin n) :
    RoleLe (complO O c) = RoleLe O := by
  unfold RoleLe SRI.RoleLe
  congr 1
  funext R S
  simp only [SRI.RoleStep, mem_sriPart, ofSRI, mem_complO_chain]

theorem mem_complO_count {O : Ontology (Fin n) (Fin m)} {c : Fin n} {a b : Fin (n + 1)} {k : Nat}
    {R : RoleT (Fin m)} (h : Clause.atLeast a k R b ∈ complO O c ∨ Clause.atMost a k R b ∈ complO O c) :
    ∃ a' b', Clause.atLeast a' k R b' ∈ O ∨ Clause.atMost a' k R b' ∈ O := by
  rw [complO, List.mem_append, List.mem_map, List.mem_append, List.mem_map] at h
  rcases h with (⟨cl, hcl, he⟩ | h) | (⟨cl, hcl, he⟩ | h)
  · cases cl <;> simp only [liftClause, reduceCtorEq, Clause.atLeast.injEq] at he
    obtain ⟨-, rfl, rfl, -⟩ := he
    exact ⟨_, _, Or.inl hcl⟩
  · simp at h
  · cases cl <;> simp only [liftClause, reduceCtorEq, Clause.atMost.injEq] at he
    obtain ⟨-, rfl, rfl, -⟩ := he
    exact ⟨_, _, Or.inr hcl⟩
  · simp at h

theorem isSHIQKB_compl {Ind : Type} {O : Ontology (Fin n) (Fin m)} {A : ABox (Fin n) (Fin m) Ind}
    (h : IsSHIQKB O A) (a : Ind) (c : Fin n) : IsSHIQKB (complO O c) (complA A a) := by
  obtain ⟨⟨hch, hcnt⟩, hneg⟩ := h
  refine ⟨⟨fun body S hcl => hch body S (mem_complO_chain.1 hcl), ?_⟩, ?_⟩
  · intro a' k R b' hcl T hT
    obtain ⟨a'', b'', hcl'⟩ := mem_complO_count hcl
    rw [roleLe_complO]
    exact hcnt a'' k R b'' hcl' T (mem_complO_chain.1 hT)
  · intro x R y hx T hT
    rw [roleLe_complO]
    rw [complA, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨as, has, he⟩ | hx
    · cases as <;> simp only [liftAssert, reduceCtorEq, Assertion.nrole.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact hneg _ _ _ has T (mem_complO_chain.1 hT)
    · simp at hx

theorem isSHIQKB_diff {Ind : Type} {O : Ontology (Fin n) (Fin m)} {A : ABox (Fin n) (Fin m) Ind}
    (h : IsSHIQKB O A) (a b : Ind) : IsSHIQKB O (A ++ [.diff a b]) := by
  refine ⟨h.1, fun x R y hx => ?_⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hx
  exact h.2 x R y hx

/-! ### The procedures -/

/-- **Type row.** Decides `EntailsTypeKB O A a c` with an optional hint: a
realisation of the knowledge base with the complement of `c` at `a`, over
the names of its transitivity encoding (a countermodel). -/
def typeRow {k : Nat} (O : Ontology (Fin n) (Fin m)) (A : ABox (Fin n) (Fin m) (Fin k))
    (a : Fin k) (c : Fin n) (hint : Option (Hint ((n + 1) + (encTransQ (complO O c)).1) m k)) :
    Bool :=
  !consistentKBQ (complO O c) (complA A a) hint

/-- **Same row.** Decides `EntailsSameKB O A a b` with an optional hint: a
realisation of the knowledge base with `a ≠ b`. -/
def sameRow {k : Nat} (O : Ontology (Fin n) (Fin m)) (A : ABox (Fin n) (Fin m) (Fin k))
    (a b : Fin k) (hint : Option (Hint (n + (encTransQ O).1) m k)) : Bool :=
  !consistentKBQ O (A ++ [.diff a b]) hint

/-- The type row is exact for every hint. -/
theorem typeRow_iff {k : Nat} {O : Ontology (Fin n) (Fin m)} {A : ABox (Fin n) (Fin m) (Fin k)}
    (h : IsSHIQKB O A) (a : Fin k) (c : Fin n)
    (hint : Option (Hint ((n + 1) + (encTransQ (complO O c)).1) m k)) :
    typeRow O A a c hint = true ↔ EntailsTypeKB O A a c := by
  rw [typeRow, entailsTypeKB_iff, Bool.not_eq_true', ← consistentKBQ_iff (isSHIQKB_compl h a c) hint]
  cases consistentKBQ (complO O c) (complA A a) hint <;> simp

/-- The same row is exact for every hint. -/
theorem sameRow_iff {k : Nat} {O : Ontology (Fin n) (Fin m)} {A : ABox (Fin n) (Fin m) (Fin k)}
    (h : IsSHIQKB O A) (a b : Fin k) (hint : Option (Hint (n + (encTransQ O).1) m k)) :
    sameRow O A a b hint = true ↔ EntailsSameKB O A a b := by
  rw [sameRow, entailsSameKB_iff, Bool.not_eq_true', ← consistentKBQ_iff (isSHIQKB_diff h a b) hint]
  cases consistentKBQ O (A ++ [.diff a b]) hint <;> simp

end Proc

end ContextCalculus.SRIQ

#print axioms ContextCalculus.SRIQ.entailsSameKB_iff
#print axioms ContextCalculus.SRIQ.Proc.entailsTypeKB_iff
#print axioms ContextCalculus.SRIQ.Proc.isSHIQKB_compl
#print axioms ContextCalculus.SRIQ.Proc.typeRow_iff
#print axioms ContextCalculus.SRIQ.Proc.sameRow_iff
