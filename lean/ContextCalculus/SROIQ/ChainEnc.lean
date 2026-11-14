import ContextCalculus.SROIQ.AutomatonFin
import ContextCalculus.SRIQ.Transitivity

/-!
# Chain elimination (stage C3, design section 4)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 4. The generalisation of
`SRI.Proc.encTrans` and `SRIQ.Proc.encTransQ` to every role inclusion
chain, reflexivity included. For each universal clause `allRight a S c`
and each stack `st` of the listed automaton of `S` (`reachL`), a fresh
name `X(a, S, c, st)` stands for "every path along a word the automaton
accepts from `st` ends in `c`":

* `gci [a] [X(.., [(S, false)])]`;
* `allRight X(st) R X(st')` for a letter move, `gci [X(st)] [X(st')]` for a
  silent move;
* `gci [X([])] [c]`.

Every clause of `O` stays except the chains of length other than one.

* `models_upC`: a model of `O` gives a model of the encoding (`upC`, roles
  and old names unchanged).
* `models_downC`: under `CondC` (listed automata closed, counting roles
  simple in the sense of `SimpleC`), a model of the encoding gives a model
  of `O` (`downC`: old names unchanged, each role the union of the paths
  along its words).
* `encChain_correct`: subsumption between old names is kept;
  `encChain_isALCHIQ`: the encoding has chains of length one only.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Clause Ontology RoleLe satClause models)
open ContextCalculus.SROIQ

variable {n m : Nat} {D : Type}

/-! ## The encoding -/

section Enc

variable (O : Ontology (Fin n) (Fin m))

/-- The universal clauses whose role has a rule below it (on the others
the encoding keeps the clause as it is). -/
def allsQ : List (Fin n × RT m × Fin n) :=
  O.filterMap fun
    | .allRight a S c => if (rules O).any (fun p => leB O p.1 S) then some (a, S, c) else none
    | _ => none

abbrev Pair (n m : Nat) := (Fin n × RT m × Fin n) × Stack (Fin m)

/-- One fresh name per universal clause and listed stack. -/
def pairsP : List (Pair n m) := (allsQ O).flatMap fun q => (reachL O q.2.1).map (q, ·)

abbrev kC : Nat := (pairsP O).length

/-- The fresh name of a pair (its first position). -/
def nameOf (p : Pair n m) : Option (Fin (n + kC O)) :=
  if h : (pairsP O).idxOf p < kC O then some (Fin.natAdd n ⟨_, h⟩) else none

/-- A clause of `O` on the old names; chains of length other than one are dropped. -/
def liftC (k : Nat) : Clause (Fin n) (Fin m) → Option (Clause (Fin (n + k)) (Fin m))
  | .gci body head => some (.gci (body.map (Fin.castAdd k)) (head.map (Fin.castAdd k)))
  | .exRight a R b => some (.exRight (Fin.castAdd k a) R (Fin.castAdd k b))
  | .allRight a R b => some (.allRight (Fin.castAdd k a) R (Fin.castAdd k b))
  | .atLeast a j R b => some (.atLeast (Fin.castAdd k a) j R (Fin.castAdd k b))
  | .atMost a j R b => some (.atMost (Fin.castAdd k a) j R (Fin.castAdd k b))
  | .chain body S => if body.length = 1 then some (.chain body S) else none

/-- The transition clause of a move into the pair `(q, st')`. -/
def transCl (X : Fin (n + kC O)) (q : Fin n × RT m × Fin n) (lp : Option (RT m) × Stack (Fin m)) :
    Option (Clause (Fin (n + kC O)) (Fin m)) :=
  (nameOf O (q, lp.2)).map fun Y =>
    match lp.1 with
    | some R => .allRight X R Y
    | none => .gci [X] [Y]

/-- The clauses of the fresh name at position `j`. -/
def freshOf (X : Fin (n + kC O)) (p : Pair n m) : List (Clause (Fin (n + kC O)) (Fin m)) :=
  (if p.2 = [(p.1.2.1, false)] then [.gci [Fin.castAdd _ p.1.1] [X]] else []) ++
  (if p.2 = [] then [.gci [X] [Fin.castAdd _ p.1.2.2]] else []) ++
  (succs O p.2).filterMap (transCl O X p.1)

def freshCls : List (Clause (Fin (n + kC O)) (Fin m)) :=
  (pairsP O).zipIdx.flatMap fun pj =>
    if h : pj.2 < kC O then freshOf O (Fin.natAdd n ⟨pj.2, h⟩) pj.1 else []

/-- **The chain encoding.** -/
def encChain : Ontology (Fin (n + kC O)) (Fin m) := O.filterMap (liftC (kC O)) ++ freshCls O

/-- The conditions of the down direction: closed automata and simple
counting roles. -/
def CondC : Prop :=
  (∀ q ∈ allsQ O, closedB O (reachL O q.2.1) = true) ∧
  ∀ a k R b, (Clause.atLeast a k R b ∈ O ∨ Clause.atMost a k R b ∈ O) → SimpleC O R

end Enc

variable {O : Ontology (Fin n) (Fin m)}

theorem mem_allsQ {a c : Fin n} {S : RT m} : (a, S, c) ∈ allsQ O ↔
    Clause.allRight a S c ∈ O ∧ (rules O).any (fun p => leB O p.1 S) = true := by
  simp only [allsQ, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp only [reduceCtorEq] at he
    rename_i a' S' c'
    split_ifs at he with hs
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨hcl, hs⟩
  · rintro ⟨h, hs⟩; exact ⟨_, h, by simp [hs]⟩

theorem simpleC_of_not_any {S : RT m} (h : ¬ (rules O).any (fun p => leB O p.1 S) = true) :
    SimpleC O S := by
  intro T body hr hle
  exact h (List.any_eq_true.2 ⟨(T, body), hr, leB_iff.2 hle⟩)

theorem mem_pairsP {q : Fin n × RT m × Fin n} {st : Stack (Fin m)} :
    (q, st) ∈ pairsP O ↔ q ∈ allsQ O ∧ st ∈ reachL O q.2.1 := by
  simp only [pairsP, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq, st', hst, rfl, rfl⟩; exact ⟨hq, hst⟩
  · rintro ⟨hq, hst⟩; exact ⟨q, hq, st, hst, rfl, rfl⟩

theorem nameOf_spec {p : Pair n m} {Y : Fin (n + kC O)} (h : nameOf O p = some Y) :
    ∃ j, ∃ hj : j < kC O, Y = Fin.natAdd n ⟨j, hj⟩ ∧ (pairsP O)[j] = p := by
  unfold nameOf at h
  split_ifs at h with hlt
  cases h
  exact ⟨_, hlt, rfl, List.getElem_idxOf hlt⟩

theorem nameOf_isSome {p : Pair n m} (h : p ∈ pairsP O) :
    ∃ j, ∃ hj : j < kC O, nameOf O p = some (Fin.natAdd n ⟨j, hj⟩) ∧ (pairsP O)[j] = p := by
  have hlt : (pairsP O).idxOf p < kC O := List.idxOf_lt_length_iff.2 h
  exact ⟨_, hlt, by simp [nameOf, hlt], List.getElem_idxOf hlt⟩

theorem mem_freshCls {j : Nat} (hj : j < kC O) {cl : Clause (Fin (n + kC O)) (Fin m)}
    (h : cl ∈ freshOf O (Fin.natAdd n ⟨j, hj⟩) (pairsP O)[j]) : cl ∈ encChain O := by
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨((pairsP O)[j], j), ?_, ?_⟩)
  · rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hj]
  · simpa [hj] using h

theorem mem_freshCls_cases {cl : Clause (Fin (n + kC O)) (Fin m)} (h : cl ∈ freshCls O) :
    ∃ j, ∃ hj : j < kC O, cl ∈ freshOf O (Fin.natAdd n ⟨j, hj⟩) (pairsP O)[j] := by
  obtain ⟨⟨p, j⟩, hz, hm⟩ := List.mem_flatMap.1 h
  rw [List.mk_mem_zipIdx_iff_getElem?] at hz
  by_cases hj : j < kC O
  · rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hz
    subst hz
    exact ⟨j, hj, by simpa [hj] using hm⟩
  · simp [hj] at hm

theorem mem_encChain_lift {cl0 : Clause (Fin n) (Fin m)} {cl : Clause (Fin (n + kC O)) (Fin m)}
    (h : cl0 ∈ O) (hl : liftC (kC O) cl0 = some cl) : cl ∈ encChain O :=
  List.mem_append_left _ (List.mem_filterMap.2 ⟨cl0, h, hl⟩)

/-- **The encoding has chains of length one only.** -/
theorem encChain_isALCHIQ (O : Ontology (Fin n) (Fin m)) : SRIQ.IsALCHIQ (encChain O) := by
  intro body S hcl
  rcases List.mem_append.1 hcl with h | h
  · obtain ⟨cl0, -, hl⟩ := List.mem_filterMap.1 h
    cases cl0 <;> simp only [liftC, Option.some.injEq, reduceCtorEq] at hl
    split_ifs at hl with hb
    simp only [Option.some.injEq, Clause.chain.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact hb
  · obtain ⟨j, hj, hm⟩ := mem_freshCls_cases h
    simp only [freshOf, List.mem_append, List.mem_filterMap] at hm
    rcases hm with (hm | hm) | ⟨lp, -, ht⟩
    · split_ifs at hm <;> simp at hm
    · split_ifs at hm <;> simp at hm
    · obtain ⟨Y, -, he⟩ := Option.map_eq_some_iff.1 ht
      rcases lp with ⟨_ | R, st'⟩ <;> simp at he

/-! ## Up: from a model of `O` -/

section Up

/-- The meaning of a pair: every path along a word accepted from its stack
ends in the filler. -/
def sem (O : Ontology (Fin n) (Fin m)) (I : Interp D (Fin n) (Fin m)) (p : Pair n m) (y : D) : Prop :=
  ∀ w z, Acc O p.2 w → I.path w y z → I.c p.1.2.2 z

def upC (O : Ontology (Fin n) (Fin m)) (I : Interp D (Fin n) (Fin m)) :
    Interp D (Fin (n + kC O)) (Fin m) where
  c := Fin.addCases (motive := fun _ => D → Prop) (fun a => I.c a)
    (fun j y => sem O I ((pairsP O)[j.1]'j.2) y)
  r := I.r

theorem upC_rt (I : Interp D (Fin n) (Fin m)) (R : RT m) : (upC O I).rt R = I.rt R := by
  cases R <;> rfl

theorem upC_old (I : Interp D (Fin n) (Fin m)) (a : Fin n) (y : D) :
    (upC O I).c (Fin.castAdd _ a) y ↔ I.c a y := by
  simp [upC]

theorem upC_fresh (I : Interp D (Fin n) (Fin m)) {j : Nat} (hj : j < kC O) (y : D) :
    (upC O I).c (Fin.natAdd n ⟨j, hj⟩) y ↔ sem O I (pairsP O)[j] y := by
  simp only [upC]
  rw [Fin.addCases_right]

theorem upC_path (I : Interp D (Fin n) (Fin m)) :
    ∀ (L : List (RT m)) (x y : D), (upC O I).path L x y ↔ I.path L x y
  | [], _, _ => Iff.rfl
  | R :: L, x, y => by simp only [Interp.path, upC_rt, upC_path I L]

theorem models_upC {I : Interp D (Fin n) (Fin m)} (hI : models I O) : models (upC O I) (encChain O) := by
  intro cl hcl
  rcases List.mem_append.1 hcl with h | h
  · obtain ⟨cl0, h0, hl⟩ := List.mem_filterMap.1 h
    have hs := hI _ h0
    cases cl0 with
    | gci body head =>
      simp only [liftC, Option.some.injEq] at hl; subst hl
      intro x hx
      obtain ⟨b, hb, hbx⟩ := hs x (fun a ha => (upC_old I a x).1 (hx _ (List.mem_map_of_mem ha)))
      exact ⟨_, List.mem_map_of_mem hb, (upC_old I b x).2 hbx⟩
    | exRight a R b =>
      simp only [liftC, Option.some.injEq] at hl; subst hl
      intro x hx
      obtain ⟨y, hxy, hy⟩ := hs x ((upC_old I a x).1 hx)
      exact ⟨y, by rw [upC_rt]; exact hxy, (upC_old I b y).2 hy⟩
    | allRight a R b =>
      simp only [liftC, Option.some.injEq] at hl; subst hl
      intro x hx y hxy
      rw [upC_rt] at hxy
      exact (upC_old I b y).2 (hs x ((upC_old I a x).1 hx) y hxy)
    | atLeast a k R b =>
      simp only [liftC, Option.some.injEq] at hl; subst hl
      exact ((SRIQ.Proc.satClause_count_congr (I := I) (J := upC O I)
        (fun x y => by rw [upC_rt]) (fun y => (upC_old I a y).symm)
        (fun y => (upC_old I b y).symm) k).1).1 hs
    | atMost a k R b =>
      simp only [liftC, Option.some.injEq] at hl; subst hl
      exact ((SRIQ.Proc.satClause_count_congr (I := I) (J := upC O I)
        (fun x y => by rw [upC_rt]) (fun y => (upC_old I a y).symm)
        (fun y => (upC_old I b y).symm) k).2).1 hs
    | chain body S =>
      simp only [liftC] at hl
      split_ifs at hl
      simp only [Option.some.injEq] at hl; subst hl
      intro x y hxy
      rw [upC_path] at hxy
      rw [upC_rt]
      exact hs x y hxy
  · obtain ⟨j, hj, hm⟩ := mem_freshCls_cases h
    generalize hp : (pairsP O)[j] = p at hm
    obtain ⟨⟨a, S, c⟩, st⟩ := p
    have hpm : ((a, S, c), st) ∈ pairsP O := hp ▸ List.getElem_mem hj
    have hall : Clause.allRight a S c ∈ O := (mem_allsQ.1 (mem_pairsP.1 hpm).1).1
    simp only [freshOf, List.mem_append, List.mem_filterMap] at hm
    rcases hm with (hm | hm) | ⟨lp, hlp, ht⟩
    · split_ifs at hm with hst
      swap
      · simp at hm
      simp only [List.mem_singleton] at hm; subst hm
      try dsimp only at hst
      subst hst
      intro x hx
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [upC_fresh, hp]
      intro w z hw hp'
      have hx' := (upC_old I a x).1 (hx _ (List.mem_singleton_self _))
      exact hI _ hall x hx' z (gen_sound hI (acc_iff_gen.1 hw) x z hp')
    · split_ifs at hm with hst
      swap
      · simp at hm
      simp only [List.mem_singleton] at hm; subst hm
      try dsimp only at hst
      subst hst
      intro x hx
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      have := (upC_fresh I hj x).1 (hx _ (List.mem_singleton_self _))
      rw [hp] at this
      exact (upC_old I c x).2 (this [] x .nil rfl)
    · have hmove := mem_succs.1 hlp
      obtain ⟨Y, hY, he⟩ := Option.map_eq_some_iff.1 ht
      obtain ⟨j', hj', rfl, hp'⟩ := nameOf_spec hY
      rcases lp with ⟨_ | R, st'⟩
      · simp only at he; subst he
        intro x hx
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        have := (upC_fresh I hj x).1 (hx _ (List.mem_singleton_self _))
        rw [hp] at this
        rw [upC_fresh, hp']
        exact fun w z hw hpz => this w z (.eps hmove hw) hpz
      · simp only at he; subst he
        intro x hx y hxy
        have := (upC_fresh I hj x).1 hx
        rw [hp] at this
        rw [upC_rt] at hxy
        rw [upC_fresh, hp']
        exact fun w z hw hpz => this (R :: w) z (.read hmove hw) ⟨y, hxy, hpz⟩

end Up

/-! ## Down: from a model of the encoding -/

section Down

def downC (O : Ontology (Fin n) (Fin m)) (J : Interp D (Fin (n + kC O)) (Fin m)) :
    Interp D (Fin n) (Fin m) where
  c := fun a => J.c (Fin.castAdd _ a)
  r := fun r x y => ∃ w, Gen O w (.pos r) ∧ J.path w x y

variable {J : Interp D (Fin (n + kC O)) (Fin m)}

theorem downC_rt (R : RT m) (x y : D) :
    (downC O J).rt R x y ↔ ∃ w, Gen O w R ∧ J.path w x y := by
  cases R with
  | pos r => exact Iff.rfl
  | inv r =>
    show (∃ w, Gen O w (.pos r) ∧ J.path w y x) ↔ _
    constructor
    · rintro ⟨w, hg, hp⟩
      exact ⟨flipW w, gen_flip.1 hg, (path_flipW J w x y).2 hp⟩
    · rintro ⟨w, hg, hp⟩
      refine ⟨flipW w, ?_, (path_flipW J w y x).2 (by simpa using hp)⟩
      have := gen_flip.1 hg
      simpa using this

theorem downC_path : ∀ (body : List (RT m)) (x y : D),
    (downC O J).path body x y → ∃ w, GenSeq O w body ∧ J.path w x y
  | [], x, y, h => ⟨[], genSeq_nil, h⟩
  | B :: body, x, y, ⟨z, hxz, hzy⟩ => by
    obtain ⟨u, hu, hpu⟩ := (downC_rt B x z).1 hxz
    obtain ⟨v, hv, hpv⟩ := downC_path body z y hzy
    exact ⟨u ++ v, genSeq_cons hu hv, (path_append J u v x y).2 ⟨z, hpu, hpv⟩⟩

theorem roleLe_encChain {R S : RT m} (h : RoleLe O R S) : RoleLe (encChain O) R S := by
  refine Relation.ReflTransGen.mono (fun U V hst => ?_) h
  rcases hst with h1 | h1
  · exact Or.inl (SRIQ.mem_sriPart.2 (mem_encChain_lift (SRIQ.mem_sriPart.1 h1) (by simp [liftC, SRIQ.ofSRI])))
  · exact Or.inr (SRIQ.mem_sriPart.2 (mem_encChain_lift (SRIQ.mem_sriPart.1 h1) (by simp [liftC, SRIQ.ofSRI])))

/-- On a simple role, `downC` adds no edges. -/
theorem downC_rt_simple (hJ : models J (encChain O)) {R : RT m} (hs : SimpleC O R) (x y : D) :
    (downC O J).rt R x y ↔ J.rt R x y := by
  rw [downC_rt]
  constructor
  · rintro ⟨w, hg, hp⟩
    obtain ⟨R', rfl, hle⟩ := (gen_simple hs).1 hg
    exact SRIQ.roleLe_sound hJ (roleLe_encChain hle) x y ((path_single J R' x y).1 hp)
  · intro h
    exact ⟨[R], gen_self R, (path_single J R x y).2 h⟩

/-- The universal clauses hold along the runs of a closed automaton. -/
theorem run_all (hJ : models J (encChain O)) {q : Fin n × RT m × Fin n} (hq : q ∈ allsQ O)
    (hcl : closedB O (reachL O q.2.1) = true) {st st' : Stack (Fin m)} {w : List (RT m)}
    (hr : Run O st w st') (hst' : st' = []) :
    ∀ x y, st ∈ reachL O q.2.1 → (∀ Y, nameOf O (q, st) = some Y → J.c Y x) →
      J.path w x y → J.c (Fin.castAdd _ q.2.2) y := by
  induction hr with
  | @nil st =>
    subst hst'
    intro x y hst hx hp
    cases hp
    obtain ⟨j, hj, hn, hpj⟩ := nameOf_isSome (mem_pairsP.2 ⟨hq, hst⟩)
    have hcl' : Clause.gci [Fin.natAdd n ⟨j, hj⟩] [Fin.castAdd _ q.2.2] ∈ encChain O :=
      mem_freshCls hj (by rw [hpj]; simp [freshOf])
    obtain ⟨b, hb, hbx⟩ := hJ _ hcl' x (by simpa using hx _ hn)
    rw [List.mem_singleton] at hb; subst hb; exact hbx
  | @eps st st1 _ w hm _ ih =>
    intro x y hst hx hp
    have hst1 := closedB_move hcl hst hm
    obtain ⟨j, hj, hn, hpj⟩ := nameOf_isSome (mem_pairsP.2 ⟨hq, hst⟩)
    obtain ⟨j1, hj1, hn1, -⟩ := nameOf_isSome (mem_pairsP.2 ⟨hq, hst1⟩)
    have hcl' : Clause.gci [Fin.natAdd n ⟨j, hj⟩] [Fin.natAdd n ⟨j1, hj1⟩] ∈ encChain O := by
      refine mem_freshCls hj ?_
      rw [hpj]
      simp only [freshOf, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨(none, st1), mem_succs.2 hm, by simp [transCl, hn1]⟩
    refine ih hst' x y hst1 (fun Y hY => ?_) hp
    rw [hn1, Option.some.injEq] at hY; subst hY
    obtain ⟨b, hb, hbx⟩ := hJ _ hcl' x (by simpa using hx _ hn)
    rw [List.mem_singleton] at hb; subst hb; exact hbx
  | @read st st1 _ R w hm _ ih =>
    intro x y hst hx hp
    obtain ⟨z, hxz, hzy⟩ := hp
    have hst1 := closedB_move hcl hst hm
    obtain ⟨j, hj, hn, hpj⟩ := nameOf_isSome (mem_pairsP.2 ⟨hq, hst⟩)
    obtain ⟨j1, hj1, hn1, -⟩ := nameOf_isSome (mem_pairsP.2 ⟨hq, hst1⟩)
    have hcl' : Clause.allRight (Fin.natAdd n ⟨j, hj⟩) R (Fin.natAdd n ⟨j1, hj1⟩) ∈ encChain O := by
      refine mem_freshCls hj ?_
      rw [hpj]
      simp only [freshOf, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨(some R, st1), mem_succs.2 hm, by simp [transCl, hn1]⟩
    refine ih hst' z y hst1 (fun Y hY => ?_) hzy
    rw [hn1, Option.some.injEq] at hY; subst hY
    exact hJ _ hcl' x (hx _ hn) z hxz

theorem models_downC (hC : CondC O) (hJ : models J (encChain O)) : models (downC O J) O := by
  intro cl hcl
  cases cl with
  | gci body head =>
    have hs := hJ _ (mem_encChain_lift (cl0 := .gci body head) hcl rfl)
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hs x (fun a ha => by
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
      exact hx a0 ha0)
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    exact ⟨b0, hb0, hbx⟩
  | exRight a R b =>
    have hs := hJ _ (mem_encChain_lift (cl0 := .exRight a R b) hcl rfl)
    intro x hx
    obtain ⟨y, hxy, hy⟩ := hs x hx
    exact ⟨y, (downC_rt R x y).2 ⟨[R], gen_self R, (path_single J R x y).2 hxy⟩, hy⟩
  | allRight a S c =>
    intro x hx y hxy
    by_cases hany : (rules O).any (fun p => leB O p.1 S) = true
    swap
    · have hs := hJ _ (mem_encChain_lift (cl0 := .allRight a S c) hcl rfl)
      exact hs x hx y ((downC_rt_simple hJ (simpleC_of_not_any hany) x y).1 hxy)
    obtain ⟨w, hg, hp⟩ := (downC_rt S x y).1 hxy
    have hq : (a, S, c) ∈ allsQ O := mem_allsQ.2 ⟨hcl, hany⟩
    have hacc : Acc O [(S, false)] w := acc_iff_gen.2 hg
    have hst : [(S, false)] ∈ reachL O S := init_mem_reachL S
    obtain ⟨j, hj, hn, hpj⟩ := nameOf_isSome ((mem_pairsP (q := (a, S, c)) (st := [(S, false)])).2 ⟨hq, hst⟩)
    have hcl' : Clause.gci [Fin.castAdd _ a] [Fin.natAdd n ⟨j, hj⟩] ∈ encChain O :=
      mem_freshCls hj (by rw [hpj]; simp [freshOf])
    obtain ⟨b, hb, hbx⟩ := hJ _ hcl' x (by simpa [downC] using hx)
    rw [List.mem_singleton] at hb; subst hb
    exact run_all hJ hq (hC.1 _ hq) hacc rfl x y hst
      (fun Y hY => by rw [hn, Option.some.injEq] at hY; subst hY; exact hbx) hp
  | atLeast a k R b =>
    have hs := hJ _ (mem_encChain_lift (cl0 := .atLeast a k R b) hcl rfl)
    exact ((SRIQ.Proc.satClause_count_congr (I := downC O J) (J := J)
      (downC_rt_simple hJ (hC.2 a k R b (Or.inl hcl))) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      k).1).2 hs
  | atMost a k R b =>
    have hs := hJ _ (mem_encChain_lift (cl0 := .atMost a k R b) hcl rfl)
    exact ((SRIQ.Proc.satClause_count_congr (I := downC O J) (J := J)
      (downC_rt_simple hJ (hC.2 a k R b (Or.inr hcl))) (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      k).2).2 hs
  | chain body T =>
    intro x y hp
    obtain ⟨w, hw, hpw⟩ := downC_path body x y hp
    exact (downC_rt T x y).2 ⟨w, gen_chain hcl hw, hpw⟩

theorem downC_old (J : Interp D (Fin (n + kC O)) (Fin m)) (a : Fin n) (y : D) :
    (downC O J).c a y ↔ J.c (Fin.castAdd _ a) y := Iff.rfl

end Down

/-- **Chain elimination keeps subsumption** between old names. -/
theorem encChain_correct (hC : CondC O) (a b : Fin n) :
    SRIQ.EntailsSub O a b ↔ SRIQ.EntailsSub (encChain O) (Fin.castAdd _ a) (Fin.castAdd _ b) := by
  constructor
  · intro hO D _ J hJ x hx
    exact hO D (downC O J) (models_downC hC hJ) x hx
  · intro hE D _ I hI x hx
    have := hE D (upC O I) (models_upC hI) x ((upC_old I a x).2 hx)
    exact (upC_old I b x).1 this

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.encChain_isALCHIQ
#print axioms ContextCalculus.SROIQ.Proc.models_upC
#print axioms ContextCalculus.SROIQ.Proc.models_downC
#print axioms ContextCalculus.SROIQ.Proc.encChain_correct
