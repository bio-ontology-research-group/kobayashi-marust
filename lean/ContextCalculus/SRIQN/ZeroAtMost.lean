import ContextCalculus.SRIQN.Self

/-!
# At-most-zero restrictions as universals (stage C3d, item 1)

`a ⊑ ≤0 R.b` says that no `R`-neighbour of an `a` has `b`, a universal
restriction: `a ⊑ ∀R.Z`, `Z ⊓ b ⊑ ⊥` with a fresh `Z`. The rewriting
`encZeroD` (one fresh name per object clause, used for the at-most-zero
clauses) keeps the roles and the old names, so it keeps consistency
(`consistentDN_encZeroD`). It removes the at-most-zero clauses from the C2a
condition, which only counts at-most clauses.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory)

variable {n m p q : Nat}

namespace ZeroE

/-- The rewriting of the object clause number `i`. -/
def zeroCl (k : Nat) (i : Fin k) : SRIQ.Clause (Fin n) (Fin m) → List (SRIQ.Clause (Fin (n + k)) (Fin m))
  | .atMost a 0 R b =>
    [.allRight (Fin.castAdd k a) R (Fin.natAdd n i), .gci [Fin.natAdd n i, Fin.castAdd k b] []]
  | cl => [mapC (Fin.castAdd k) cl]

/-- The object clauses of the rewriting. -/
def zeroCls (B : SRIQ.Ontology (Fin n) (Fin m)) : List (SRIQ.Clause (Fin (n + B.length)) (Fin m)) :=
  (List.finRange B.length).flatMap fun i => zeroCl B.length i (B.get i)

/-- The fresh name of clause `i`: the filler of the at-most-zero clause is false. -/
def zSem {D : Type} (I : Interp D (Fin n) (Fin m)) : SRIQ.Clause (Fin n) (Fin m) → D → Prop
  | .atMost _ 0 _ b, x => ¬ I.c b x
  | _, _ => False

end ZeroE

open ZeroE

/-- **The rewriting of the at-most-zero clauses.** -/
def encZeroD (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    DOntology (Fin (n + (SRIQD.objPart (dbase O)).length)) (Fin m) (Fin p) (Fin q) :=
  ((zeroCls (SRIQD.objPart (dbase O))).map SRIQD.Clause.obj ++
      (dbase O).filterMap (SRIQD.Proc.liftData _)).map DClause.base ++
    (dnoms O).map fun a => .nom (Fin.castAdd _ a)

section Facts

variable (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q))

theorem dbase_encZeroD : dbase (encZeroD O) =
    (zeroCls (SRIQD.objPart (dbase O))).map SRIQD.Clause.obj ++
      (dbase O).filterMap (SRIQD.Proc.liftData _) :=
  Proc.dbase_map_noms _ _ _

theorem dnoms_encZeroD : dnoms (encZeroD O) = (dnoms O).map (Fin.castAdd _) := by
  simp only [encZeroD, dnoms, List.filterMap_append, List.filterMap_map]
  simp [List.map_filterMap]

theorem objPart_encZeroD :
    SRIQD.objPart (dbase (encZeroD O)) = zeroCls (SRIQD.objPart (dbase O)) := by
  rw [dbase_encZeroD]
  exact SRIQD.Proc.objPart_lift _ _

theorem mem_zeroCls {B : SRIQ.Ontology (Fin n) (Fin m)} {cl : SRIQ.Clause (Fin (n + B.length)) (Fin m)} :
    cl ∈ zeroCls B ↔ ∃ i, cl ∈ zeroCl B.length i (B.get i) := by
  simp [zeroCls]

/-- The rewriting is ALCHIQ when the ontology is. -/
theorem isALCHIQ_encZeroD (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O))) :
    SRIQD.IsALCHIQ (dbase (encZeroD O)) := by
  unfold SRIQD.IsALCHIQ
  rw [objPart_encZeroD]
  intro body S hcl
  obtain ⟨i, hi⟩ := mem_zeroCls.1 hcl
  have hmem : (SRIQD.objPart (dbase O)).get i ∈ SRIQD.objPart (dbase O) := List.get_mem _ _
  generalize (SRIQD.objPart (dbase O)).get i = cl0 at hi hmem
  cases cl0 with
  | chain body' S' =>
    simp only [zeroCl, mapC, List.mem_singleton, SRIQ.Clause.chain.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact hA _ _ hmem
  | atMost a k R b =>
    cases k with
    | zero => simp [zeroCl] at hi
    | succ k => simp [zeroCl, mapC] at hi
  | _ => simp [zeroCl, mapC] at hi

end Facts

section Maps

variable {D V : Type} {atom : Fin q → V → Prop} {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}

/-- The interpretation of the rewriting. -/
def upZ (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (I : DInterp D V (Fin n) (Fin m) (Fin p)) :
    DInterp D V (Fin (n + (SRIQD.objPart (dbase O)).length)) (Fin m) (Fin p) where
  c := Fin.addCases (motive := fun _ => D → Prop) (fun a => I.c a)
    (fun i => zSem I.toInterp ((SRIQD.objPart (dbase O)).get i))
  r := I.r
  d := I.d

theorem pull_upZ (I : DInterp D V (Fin n) (Fin m) (Fin p)) :
    pull (upZ O I).toInterp (Fin.castAdd _) = I.toInterp := by
  cases I
  simp [pull, upZ]

/-- The old names of an interpretation of the rewriting. -/
def downZ (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q))
    (J : DInterp D V (Fin (n + (SRIQD.objPart (dbase O)).length)) (Fin m) (Fin p)) :
    DInterp D V (Fin n) (Fin m) (Fin p) :=
  { toInterp := pull J.toInterp (Fin.castAdd _), d := J.d }

theorem up_obj {I : DInterp D V (Fin n) (Fin m) (Fin p)}
    (hI : SRIQ.models I.toInterp (SRIQD.objPart (dbase O))) :
    SRIQ.models (upZ O I).toInterp (zeroCls (SRIQD.objPart (dbase O))) := by
  intro cl hcl
  obtain ⟨i, hi⟩ := mem_zeroCls.1 hcl
  have hmem : (SRIQD.objPart (dbase O)).get i ∈ SRIQD.objPart (dbase O) := List.get_mem _ _
  have hI0 := hI _ hmem
  have hz : ∀ x, (upZ O I).c (Fin.natAdd n i) x ↔ zSem I.toInterp ((SRIQD.objPart (dbase O)).get i) x := by
    intro x; simp [upZ]
  have hold : ∀ a x, (upZ O I).c (Fin.castAdd _ a) x ↔ I.c a x := by intro a x; simp [upZ]
  generalize hc : (SRIQD.objPart (dbase O)).get i = cl0 at hi hI0 hz
  have hlift : ∀ cl1 : SRIQ.Clause (Fin n) (Fin m), SRIQ.satClause I.toInterp cl1 →
      SRIQ.satClause (upZ O I).toInterp (mapC (Fin.castAdd _) cl1) := fun cl1 h => by
    rw [satClause_mapC, pull_upZ]; exact h
  cases cl0 with
  | atMost a k R b =>
    cases k with
    | zero =>
      simp only [zeroCl, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · intro x hx y hxy
        rw [hz]
        intro hb
        have hr : I.rt R x y := by cases R <;> exact hxy
        have := hI0 x ((hold a x).1 hx) [y] (List.nodup_singleton y) (by simp [hr, hb])
        simp at this
      · intro x hx
        have h1 := (hz x).1 (hx _ (by simp))
        have h2 := (hold b x).1 (hx _ (by simp))
        exact absurd h2 h1
    | succ k =>
      simp only [zeroCl, List.mem_singleton] at hi
      subst hi; exact hlift _ hI0
  | gci _ _ => simp only [zeroCl, List.mem_singleton] at hi; subst hi; exact hlift _ hI0
  | exRight _ _ _ => simp only [zeroCl, List.mem_singleton] at hi; subst hi; exact hlift _ hI0
  | allRight _ _ _ => simp only [zeroCl, List.mem_singleton] at hi; subst hi; exact hlift _ hI0
  | atLeast _ _ _ _ => simp only [zeroCl, List.mem_singleton] at hi; subst hi; exact hlift _ hI0
  | chain _ _ => simp only [zeroCl, List.mem_singleton] at hi; subst hi; exact hlift _ hI0

theorem down_obj {J : DInterp D V (Fin (n + (SRIQD.objPart (dbase O)).length)) (Fin m) (Fin p)}
    (hJ : SRIQ.models J.toInterp (zeroCls (SRIQD.objPart (dbase O)))) :
    SRIQ.models (downZ O J).toInterp (SRIQD.objPart (dbase O)) := by
  intro cl0 hcl0
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 hcl0
  have hsat : ∀ cl ∈ zeroCl _ i cl0, SRIQ.satClause J.toInterp cl := fun cl hcl =>
    hJ cl (mem_zeroCls.2 ⟨i, by rw [hi]; exact hcl⟩)
  have hlift : ∀ cl1 : SRIQ.Clause (Fin n) (Fin m), mapC (Fin.castAdd _) cl1 ∈ zeroCl _ i cl0 →
      SRIQ.satClause (downZ O J).toInterp cl1 := fun cl1 h =>
    (satClause_mapC _ _ _).1 (hsat _ h)
  cases cl0 with
  | atMost a k R b =>
    cases k with
    | zero =>
      intro x hx l hnd hl
      cases l with
      | nil => simp
      | cons y l =>
        exfalso
        have h1 := hsat (.allRight (Fin.castAdd _ a) R (Fin.natAdd n i)) (by simp [zeroCl]) x hx y
          ((pull_rt J.toInterp (Fin.castAdd _) R x y).1 (hl y List.mem_cons_self).1)
        obtain ⟨c, hc, -⟩ := hsat (.gci [Fin.natAdd n i, Fin.castAdd _ b] []) (by simp [zeroCl]) y
          (by
            intro c hc
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact h1
            · exact (hl y List.mem_cons_self).2)
        simp at hc
    | succ k => exact hlift _ (by simp [zeroCl])
  | gci _ _ => exact hlift _ (by simp [zeroCl])
  | exRight _ _ _ => exact hlift _ (by simp [zeroCl])
  | allRight _ _ _ => exact hlift _ (by simp [zeroCl])
  | atLeast _ _ _ _ => exact hlift _ (by simp [zeroCl])
  | chain _ _ => exact hlift _ (by simp [zeroCl])

end Maps

/-- **The rewriting keeps consistency**, for every data theory. -/
theorem consistentDN_encZeroD {Θ : DataTheory (Fin q)} (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    ConsistentDN Θ O ↔ ConsistentDN Θ (encZeroD O) := by
  constructor
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
    obtain ⟨hIo, hId⟩ := SRIQD.models_iff.1 hI
    refine ⟨D, V, hD, atom, hΘ, upZ O I, SRIQD.models_iff.2 ⟨?_, fun cl hcl y => ?_⟩, fun a' ha' => ?_⟩
    · rw [objPart_encZeroD]; exact up_obj hIo
    · rw [dbase_encZeroD] at hcl
      rcases List.mem_append.1 hcl with h1 | h1
      · obtain ⟨cl0, -, rfl⟩ := List.mem_map.1 h1
        trivial
      · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h1
        refine (SRIQD.Proc.dLocal_liftData atom hl _ (fun u => I.d u y)).2 ?_
        have hc : (fun a => (upZ O I).c (Fin.castAdd _ a) y) = fun a => I.c a y :=
          funext fun a => by simp [upZ]
        show SRIQD.dLocal atom (fun a => (upZ O I).c (Fin.castAdd _ a) y) (fun u => I.d u y) cl0
        rw [hc]
        exact hId cl0 h0 y
    · rw [dnoms_encZeroD] at ha'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
      obtain ⟨x, hx⟩ := hn a ha
      exact ⟨x, fun y => by simpa [upZ] using hx y⟩
  · rintro ⟨D, V, hD, atom, hΘ, J, hJ, hn⟩
    obtain ⟨hJo, hJd⟩ := SRIQD.models_iff.1 hJ
    rw [objPart_encZeroD] at hJo
    refine ⟨D, V, hD, atom, hΘ, downZ O J, SRIQD.models_iff.2 ⟨down_obj hJo, fun cl hcl y => ?_⟩,
      fun a ha => ?_⟩
    · cases hl : SRIQD.Proc.liftData (SRIQD.objPart (dbase O)).length cl with
      | none =>
        cases cl <;> simp only [SRIQD.Proc.liftData, reduceCtorEq] at hl
        trivial
      | some cl' =>
        have hm : cl' ∈ dbase (encZeroD O) := by
          rw [dbase_encZeroD]
          exact List.mem_append_right _ (List.mem_filterMap.2 ⟨cl, hcl, hl⟩)
        exact (SRIQD.Proc.dLocal_liftData atom hl _ _).1 (hJd cl' hm y)
    · exact hn (Fin.castAdd _ a) (by rw [dnoms_encZeroD]; exact List.mem_map_of_mem ha)

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.consistentDN_encZeroD
#print axioms ContextCalculus.SRIQN.isALCHIQ_encZeroD
