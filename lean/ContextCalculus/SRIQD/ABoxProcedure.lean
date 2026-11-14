import ContextCalculus.SRIQD.ABox
import ContextCalculus.SRIQD.Procedure
import ContextCalculus.SRIQ.ABoxProcedure

/-!
# A consistency procedure for knowledge bases with data assertions (stage C4, step 4)

Concepts `Fin n`, roles `Fin m`, data properties `Fin p`, data atoms
`Fin q`, individuals `Fin k`; the oracle `card` is any computable
function.

* `encO`, `encA`: each individual `i` gets a fresh name `Nᵢ`
  (`Fin.natAdd n i`) with the assertion `Nᵢ(i)`; a positive data
  assertion `dPos i u L` becomes the clause `Nᵢ ⊑ ∃u.L` and a negative one
  `dNeg i u L` the clause `Nᵢ ⊑ ∀u.¬L`. The old names move by
  `Fin.castAdd k`. Consistency is unchanged (`consistentKB_enc`): `Nᵢ`
  holds at the individual `i` and nowhere else in the model built from a
  model of the input.
* `reduceQ`: the object part with one forbidding gci per type without a
  data star (decided by `dataSatB`), as `reduceWith` of
  `SRIQD/ABox.lean`.
* `consistentKBD`: the `SRIQ` procedure `SRIQ.Proc.consistentKB` (a hint
  first, then the exhaustive search) on the reduced encoding. Exact for
  every hint (`consistentKBD_iff`); the hint is a realisation hint for
  the reduced encoding.
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (RoleT Interp)

/-! ## Renaming concept names -/

section Rename

variable {D V C1 C2 Role DProp DAtom : Type}

/-- An `SRIQ` clause with renamed concept names. -/
def renameO (f : C1 → C2) : SRIQ.Clause C1 Role → SRIQ.Clause C2 Role
  | .gci body head => .gci (body.map f) (head.map f)
  | .exRight a R b => .exRight (f a) R (f b)
  | .allRight a R b => .allRight (f a) R (f b)
  | .atLeast a j R b => .atLeast (f a) j R (f b)
  | .atMost a j R b => .atMost (f a) j R (f b)
  | .chain body S => .chain body S

/-- A clause with renamed concept names. -/
def rename (f : C1 → C2) : Clause C1 Role DProp DAtom → Clause C2 Role DProp DAtom
  | .obj cl => .obj (renameO f cl)
  | .dEx a u pos neg => .dEx (f a) u pos neg
  | .dAll a u head => .dAll (f a) u head
  | .dAtLeast a j u pos neg => .dAtLeast (f a) j u pos neg
  | .dAtMost a j u pos neg => .dAtMost (f a) j u pos neg
  | .dSub u w => .dSub u w

/-- An interpretation read along a renaming. -/
def comapI (J : DInterp D V C2 Role DProp) (f : C1 → C2) : DInterp D V C1 Role DProp :=
  { c := fun a => J.c (f a), r := J.r, d := J.d }

theorem rt_congr {I : Interp D C1 Role} {J : Interp D C2 Role} (h : ∀ r x y, I.r r x y ↔ J.r r x y)
    (R : RoleT Role) (x y : D) : I.rt R x y ↔ J.rt R x y := by
  cases R <;> exact h _ _ _

theorem path_congr {I : Interp D C1 Role} {J : Interp D C2 Role}
    (h : ∀ r x y, I.r r x y ↔ J.r r x y) :
    ∀ (body : List (RoleT Role)) (x y : D), I.path body x y ↔ J.path body x y
  | [], _, _ => Iff.rfl
  | R :: Rs, x, y => by
    simp only [Interp.path, rt_congr h, path_congr h Rs]

theorem satClause_rename (atom : DAtom → V → Prop) (J : DInterp D V C2 Role DProp) (f : C1 → C2)
    (cl : Clause C1 Role DProp DAtom) :
    satClause atom J (rename f cl) ↔ satClause atom (comapI J f) cl := by
  cases cl with
  | obj cl =>
    cases cl with
    | gci body head =>
      show (∀ x, (∀ a ∈ body.map f, J.c a x) → ∃ b ∈ head.map f, J.c b x) ↔
        (∀ x, (∀ a ∈ body, J.c (f a) x) → ∃ b ∈ head, J.c (f b) x)
      constructor
      · intro h x hx
        obtain ⟨b, hb, hbx⟩ := h x fun a ha => by
          obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
          exact hx a0 ha0
        obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
        exact ⟨b0, hb0, hbx⟩
      · intro h x hx
        obtain ⟨b, hb, hbx⟩ := h x fun a ha => hx _ (List.mem_map_of_mem ha)
        exact ⟨f b, List.mem_map_of_mem hb, hbx⟩
    | chain body S =>
      simp only [rename, renameO, satClause, SRIQ.satClause]
      have h : ∀ r x y, J.r r x y ↔ (comapI J f).r r x y := fun _ _ _ => Iff.rfl
      simp only [path_congr h, rt_congr h]
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

theorem models_rename (atom : DAtom → V → Prop) (J : DInterp D V C2 Role DProp) (f : C1 → C2)
    (O : Ontology C1 Role DProp DAtom) :
    models atom J (O.map (rename f)) ↔ models atom (comapI J f) O := by
  simp only [models, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satClause_rename]

theorem objPart_map_rename (f : C1 → C2) (O : Ontology C1 Role DProp DAtom) :
    objPart (O.map (rename f)) = (objPart O).map (renameO f) := by
  induction O with
  | nil => rfl
  | cons cl O ih =>
    cases cl <;> simp [objPart, rename, toObj] at ih ⊢ <;> exact ih

end Rename

namespace Proc

variable {n m p q k : Nat} {D V : Type}

/-! ## Data assertions as clauses on fresh names -/

section Enc

/-- The clause of a data assertion on the fresh name of its individual. -/
def dataAsClause : Assertion (Fin n) (Fin m) (Fin p) (Fin q) (Fin k) →
    Option (Clause (Fin (n + k)) (Fin m) (Fin p) (Fin q))
  | .obj _ => none
  | .dPos a u L => some (.dEx (Fin.natAdd n a) u [L] [])
  | .dNeg a u L => some (.dAll (Fin.natAdd n a) u [(L, false)])

/-- The encoded TBox. -/
def encO (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) :
    Ontology (Fin (n + k)) (Fin m) (Fin p) (Fin q) :=
  O.map (rename (Fin.castAdd k)) ++ A.filterMap dataAsClause

/-- The encoded ABox: the object assertions on the old names and `Nᵢ(i)`. -/
def encA (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) :
    SRIQ.ABox (Fin (n + k)) (Fin m) (Fin k) :=
  (objABox A).map (SRIQ.Proc.liftAssert k) ++ (List.finRange k).map fun i => .cls i (Fin.natAdd n i)

theorem objPart_encO (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) :
    objPart (encO O A) = (objPart O).map (renameO (Fin.castAdd k)) := by
  have h2 : objPart (A.filterMap dataAsClause) = [] := by
    unfold objPart
    rw [List.filterMap_eq_nil_iff]
    intro cl hcl
    obtain ⟨as, -, he⟩ := List.mem_filterMap.1 hcl
    cases as <;> simp only [dataAsClause, Option.some.injEq, reduceCtorEq] at he <;> subst he <;> rfl
  unfold encO
  rw [show objPart (O.map (rename (Fin.castAdd k)) ++ A.filterMap dataAsClause) =
    objPart (O.map (rename (Fin.castAdd k))) ++ objPart (A.filterMap dataAsClause) from
    List.filterMap_append, h2, List.append_nil, objPart_map_rename]

theorem isALCHIQ_encO {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} (hA : IsALCHIQ O)
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) : IsALCHIQ (encO O A) := by
  unfold IsALCHIQ at hA ⊢
  intro body S hcl
  rw [objPart_encO] at hcl
  obtain ⟨cl, h0, he⟩ := List.mem_map.1 hcl
  cases cl with
  | chain body' S' =>
    simp only [renameO, SRIQ.Clause.chain.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hA _ _ h0
  | _ => simp [renameO] at he

theorem satAssert_liftAssert (J : Interp D (Fin (n + k)) (Fin m)) (ind : Fin k → D)
    (as : SRIQ.Assertion (Fin n) (Fin m) (Fin k)) :
    SRIQ.satAssert J ind (SRIQ.Proc.liftAssert k as) ↔
      SRIQ.satAssert { c := fun a => J.c (Fin.castAdd k a), r := J.r } ind as := by
  cases as <;> exact Iff.rfl

/-- **The encoding keeps consistency.** -/
theorem consistentKB_enc {Θ : DataTheory (Fin q)} (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) :
    ConsistentKB Θ O A ↔ ConsistentKB Θ (encO O A) ((encA A).map Assertion.obj) := by
  constructor
  · rintro ⟨D, V, hD, atom, hΘ, ⟨⟨c, r⟩, d⟩, ind, hI, hA⟩
    let J : DInterp D V (Fin (n + k)) (Fin m) (Fin p) :=
      { c := Fin.addCases (motive := fun _ => D → Prop) (fun a x => c a x) (fun i x => x = ind i),
        r := r, d := d }
    have hJI : comapI J (Fin.castAdd k) = ⟨⟨c, r⟩, d⟩ := by
      simp only [comapI, J, Fin.addCases_left]
    have hfresh : ∀ (i : Fin k) x, J.c (Fin.natAdd n i) x ↔ x = ind i := by
      intro i x
      simp only [J, Fin.addCases_right]
    refine ⟨D, V, hD, atom, hΘ, J, ind, fun cl hcl => ?_, ?_⟩
    · rcases List.mem_append.1 hcl with h1 | h1
      · obtain ⟨cl0, h0, rfl⟩ := List.mem_map.1 h1
        rw [satClause_rename, hJI]
        exact hI cl0 h0
      · obtain ⟨as, has, he⟩ := List.mem_filterMap.1 h1
        cases as with
        | obj _ => simp [dataAsClause] at he
        | dPos a u L =>
          simp only [dataAsClause, Option.some.injEq] at he
          subst he
          rintro x hx
          rw [hfresh] at hx
          subst hx
          obtain ⟨v, hv, hL⟩ := hA _ has
          exact ⟨v, hv, fun p hp => by simp at hp; exact hp ▸ hL, fun _ h => by simp at h⟩
        | dNeg a u L =>
          simp only [dataAsClause, Option.some.injEq] at he
          subst he
          rintro x hx v hv
          rw [hfresh] at hx
          subst hx
          exact ⟨(L, false), List.mem_singleton_self _,
            by simpa [litSem] using hA _ has v hv⟩
    · rw [satABox_map_obj]
      intro as has
      rcases List.mem_append.1 has with h1 | h1
      · obtain ⟨as0, h0, rfl⟩ := List.mem_map.1 h1
        rw [satAssert_liftAssert]
        have := hA _ (mem_objABox.1 h0)
        have hc : (fun a => J.c (Fin.castAdd k a)) = c := by
          funext a x
          simp only [J, Fin.addCases_left]
        simp only [hc]
        exact this
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h1
        exact (hfresh i (ind i)).2 rfl
  · rintro ⟨D, V, hD, atom, hΘ, J, ind, hJ, hA⟩
    rw [satABox_map_obj] at hA
    have hJO : models atom J (O.map (rename (Fin.castAdd k))) :=
      fun cl hcl => hJ cl (List.mem_append_left _ hcl)
    have hfresh : ∀ i : Fin k, J.c (Fin.natAdd n i) (ind i) :=
      fun i => hA _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange _, rfl⟩))
    refine ⟨D, V, hD, atom, hΘ, comapI J (Fin.castAdd k), ind, (models_rename atom J _ O).1 hJO,
      fun as has => ?_⟩
    cases as with
    | obj as =>
      have := hA _ (List.mem_append_left _ (List.mem_map_of_mem (mem_objABox.2 has)))
      exact (satAssert_liftAssert J.toInterp ind as).1 this
    | dPos a u L =>
      have hcl : Clause.dEx (Fin.natAdd n a) u [L] [] ∈ encO O A :=
        List.mem_append_right _ (List.mem_filterMap.2 ⟨_, has, rfl⟩)
      obtain ⟨v, hv, hr⟩ := hJ _ hcl (ind a) (hfresh a)
      exact ⟨v, hv, hr.1 L (List.mem_singleton_self _)⟩
    | dNeg a u L =>
      have hcl : Clause.dAll (Fin.natAdd n a) u [(L, false)] ∈ encO O A :=
        List.mem_append_right _ (List.mem_filterMap.2 ⟨_, has, rfl⟩)
      intro v hv hL
      obtain ⟨l, hl, hlit⟩ := hJ _ hcl (ind a) (hfresh a) v hv
      rw [List.mem_singleton] at hl
      subst hl
      simp only [litSem] at hlit
      exact absurd (hlit.1 hL) (by simp)

end Enc

/-! ## The reduced encoding and the procedure -/

section Procedure

/-- The members of a set of names, in order. -/
def toLFin (t : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (· ∈ t)

theorem mem_toLFin (t : Finset (Fin n)) (a : Fin n) : a ∈ toLFin t ↔ a ∈ t := by
  simp [toLFin]

/-- All sets of names. -/
def allTypes (n : Nat) : List (Finset (Fin n)) :=
  (List.finRange n).sublists.map List.toFinset

theorem mem_allTypes (t : Finset (Fin n)) : t ∈ allTypes n := by
  refine List.mem_map.2 ⟨toLFin t, List.mem_sublists.2 List.filter_sublist, ?_⟩
  ext a
  simp [mem_toLFin]

/-- The types without a data star. -/
def badQ (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat) :
    List (Finset (Fin n)) :=
  (allTypes n).filter fun t => !dataSatB O card t

theorem mem_badQ {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {card : Finset (Fin q) → Option Nat}
    (t : Finset (Fin n)) : t ∈ badQ O card ↔ ¬ DataSat O card t := by
  simp [badQ, mem_allTypes, ← dataSatB_iff]

/-- The object part with the forbidding gcis, computed. -/
def reduceQ (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat) :
    SRIQ.Ontology (Fin n) (Fin m) :=
  reduceWith O toLFin (badQ O card)

/-- **Consistency with data assertions and a hint.** `true` if the hint
checks against the reduced encoding, else the exhaustive search. -/
def consistentKBD (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k))
    (hint : Option (SRIQ.Proc.Hint (n + k) m k)) : Bool :=
  SRIQ.Proc.consistentKB (reduceQ (encO O A) card) (encA A) hint

/-- **Exactness for every hint.** For an ALCHIQ object part and every data
theory for which `card` satisfies `OracleSpec`. -/
theorem consistentKBD_iff {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    (hspec : OracleSpec Θ card) {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} (hA : IsALCHIQ O)
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k))
    (hint : Option (SRIQ.Proc.Hint (n + k) m k)) :
    consistentKBD O card A hint = true ↔ ConsistentKB Θ O A := by
  rw [consistentKBD, reduceQ,
    SRIQ.Proc.consistentKB_iff (isALCHIQ_reduceWith (isALCHIQ_encO hA A) _ _),
    consistentKB_reduceWith hspec (mem_toLFin) mem_badQ, ← consistentKB_enc]

end Procedure

end Proc

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.Proc.consistentKB_enc
#print axioms ContextCalculus.SRIQD.Proc.consistentKBD_iff
