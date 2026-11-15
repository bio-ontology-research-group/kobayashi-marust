import ContextCalculus.SROIQ.RegularCheck

/-!
# The automaton of a role (stage C3, design section 3)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 3. A pushdown machine over
stacks of items `(S, b)`: `(S, false)` is the initial state `i_S` of the
automaton `B_S` of Horrocks, Kutz and Sattler, `(S, true)` its final state
`f_S`. Transitions on a smaller role become pushes (calls). The moves
(`Move`) follow the shape of each rule (`shapeOf`): reflexivity, an
ordinary body, a right-recursive body `w T`, a left-recursive body `T w`,
and transitivity `T T`.

* `acc_iff_gen`: the machine for `S` accepts exactly the words of `S`, for
  every ontology (no regularity needed).
* `succs`, `mem_succs`: the moves, computed.
* `reachL`, `closedB`, `run_mem`: a listed set of stacks closed under the
  moves contains every stack a run from a listed stack reaches.
-/

namespace ContextCalculus.SROIQ

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Clause Ontology RoleLe)

variable {CName Role : Type}

/-! ## Sequences of children -/

/-- A word split into one word per role of a list, each satisfying `P`. -/
def SeqOf (P : List (RoleT Role) → RoleT Role → Prop) (w : List (RoleT Role))
    (body : List (RoleT Role)) : Prop :=
  ∃ ws : List (List (RoleT Role)), ws.length = body.length ∧
    (∀ p ∈ ws.zip body, P p.1 p.2) ∧ ws.flatten = w

section Seq

variable {P : List (RoleT Role) → RoleT Role → Prop}

theorem seqOf_nil_iff {w : List (RoleT Role)} : SeqOf P w [] ↔ w = [] := by
  constructor
  · rintro ⟨ws, hl, -, rfl⟩
    cases ws with
    | nil => rfl
    | cons _ _ => simp at hl
  · rintro rfl; exact ⟨[], rfl, by simp, rfl⟩

theorem seqOf_cons_iff {w : List (RoleT Role)} {B : RoleT Role} {body : List (RoleT Role)} :
    SeqOf P w (B :: body) ↔ ∃ u v, w = u ++ v ∧ P u B ∧ SeqOf P v body := by
  constructor
  · rintro ⟨ws, hl, hc, rfl⟩
    cases ws with
    | nil => simp at hl
    | cons u ws =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      exact ⟨u, ws.flatten, rfl, hc (u, B) (by simp), ws, hl,
        fun p hp => hc p (List.mem_cons_of_mem _ hp), rfl⟩
  · rintro ⟨u, v, rfl, h1, ⟨ws, hl, hc, rfl⟩⟩
    exact ⟨u :: ws, by simp [hl], by
      intro p hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h1
      · exact hc p hp, rfl⟩

theorem seqOf_append_iff {w : List (RoleT Role)} :
    ∀ {b1 b2 : List (RoleT Role)},
      SeqOf P w (b1 ++ b2) ↔ ∃ u v, w = u ++ v ∧ SeqOf P u b1 ∧ SeqOf P v b2
  | [], b2 => by
    simp only [List.nil_append, seqOf_nil_iff]
    constructor
    · intro h; exact ⟨[], w, rfl, rfl, h⟩
    · rintro ⟨u, v, rfl, rfl, h⟩; simpa using h
  | B :: b1, b2 => by
    rw [List.cons_append, seqOf_cons_iff]
    constructor
    · rintro ⟨u, v, rfl, h1, h2⟩
      obtain ⟨v1, v2, rfl, hv1, hv2⟩ := seqOf_append_iff.1 h2
      exact ⟨u ++ v1, v2, by simp, seqOf_cons_iff.2 ⟨u, v1, rfl, h1, hv1⟩, hv2⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      obtain ⟨u1, u2, rfl, hu1, hu2⟩ := seqOf_cons_iff.1 hu
      exact ⟨u1, u2 ++ v, by simp, hu1, seqOf_append_iff.2 ⟨u2, v, rfl, hu2, hv⟩⟩

theorem seqOf_single {w : List (RoleT Role)} {B : RoleT Role} : SeqOf P w [B] ↔ P w B := by
  rw [seqOf_cons_iff]
  constructor
  · rintro ⟨u, v, rfl, h, hv⟩
    rw [seqOf_nil_iff] at hv; subst hv; simpa using h
  · intro h; exact ⟨w, [], by simp, h, seqOf_nil_iff.2 rfl⟩

end Seq

theorem genSeq_iff_seqOf {O : Ontology CName Role} {w body : List (RoleT Role)} :
    GenSeq O w body ↔ SeqOf (Gen O) w body := Iff.rfl

/-! ## Shapes of rules -/

/-- The shape of a rule body relative to its head. -/
inductive Shape
  | refl | trans | left | right | ord
deriving DecidableEq

set_option linter.unusedSectionVars false

variable [DecidableEq Role]

def shapeOf (T : RoleT Role) (B : List (RoleT Role)) : Shape :=
  if B = [] then .refl
  else if B = [T, T] then .trans
  else if B.head? = some T then .left
  else if B.getLast? = some T then .right
  else .ord

theorem shapeOf_refl {T : RoleT Role} {B : List (RoleT Role)} (h : shapeOf T B = .refl) : B = [] := by
  unfold shapeOf at h; split_ifs at h with h1; exact h1

theorem shapeOf_trans {T : RoleT Role} {B : List (RoleT Role)} (h : shapeOf T B = .trans) :
    B = [T, T] := by
  unfold shapeOf at h; split_ifs at h with h1 h2; exact h2

theorem shapeOf_left {T : RoleT Role} {B : List (RoleT Role)} (h : shapeOf T B = .left) :
    B = T :: B.tail := by
  unfold shapeOf at h
  split_ifs at h with h1 h2 h3
  cases B with
  | nil => exact absurd rfl h1
  | cons B0 B =>
    simp only [List.head?_cons, Option.some.injEq] at h3
    subst h3; rfl

theorem shapeOf_right {T : RoleT Role} {B : List (RoleT Role)} (h : shapeOf T B = .right) :
    B = B.dropLast ++ [T] := by
  unfold shapeOf at h
  split_ifs at h with h1 h2 h3 h4
  have hne : B ≠ [] := h1
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at h4
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [h4]

/-! ## Moves -/

abbrev Item (Role : Type) := RoleT Role × Bool
abbrev Stack (Role : Type) := List (Item Role)

/-- The items of a list of roles, all initial. -/
def ini (B : List (RoleT Role)) : Stack Role := B.map fun R => (R, false)

variable (O : Ontology CName Role)

/-- Two role terms are equivalent in the hierarchy. -/
def Eqv (T S : RoleT Role) : Prop := RoleLe O T S ∧ RoleLe O S T

/-- The moves of the machine; `some R` reads the letter `R`. -/
inductive Move : Stack Role → Option (RoleT Role) → Stack Role → Prop
  | letter {R S : RoleT Role} {rest : Stack Role} : RoleLe O R S →
      Move ((S, false) :: rest) (some R) ((S, true) :: rest)
  | call {R S : RoleT Role} {B : List (RoleT Role)} {rest : Stack Role} : (R, B) ∈ rules O →
      RoleLe O R S → ¬ RoleLe O S R → Move ((S, false) :: rest) none ((R, false) :: (S, true) :: rest)
  | refl {T S : RoleT Role} {B : List (RoleT Role)} {rest : Stack Role} : (T, B) ∈ rules O →
      shapeOf T B = .refl → RoleLe O T S → Move ((S, false) :: rest) none ((S, true) :: rest)
  | ord {T S : RoleT Role} {B : List (RoleT Role)} {rest : Stack Role} : (T, B) ∈ rules O →
      shapeOf T B = .ord → Eqv O T S → Move ((S, false) :: rest) none (ini B ++ (S, true) :: rest)
  | right {T S : RoleT Role} {B : List (RoleT Role)} {rest : Stack Role} : (T, B) ∈ rules O →
      shapeOf T B = .right → Eqv O T S →
      Move ((S, false) :: rest) none (ini B.dropLast ++ (S, false) :: rest)
  | left {T S : RoleT Role} {B : List (RoleT Role)} {rest : Stack Role} : (T, B) ∈ rules O →
      shapeOf T B = .left → Eqv O T S →
      Move ((S, true) :: rest) none (ini B.tail ++ (S, true) :: rest)
  | trans {T S : RoleT Role} {B : List (RoleT Role)} {rest : Stack Role} : (T, B) ∈ rules O →
      shapeOf T B = .trans → Eqv O T S → Move ((S, true) :: rest) none ((S, false) :: rest)
  | pop {S : RoleT Role} {rest : Stack Role} : Move ((S, true) :: rest) none rest

/-- Runs of the machine. -/
inductive Run : Stack Role → List (RoleT Role) → Stack Role → Prop
  | nil {st : Stack Role} : Run st [] st
  | eps {st st' st'' : Stack Role} {w : List (RoleT Role)} : Move O st none st' →
      Run st' w st'' → Run st w st''
  | read {st st' st'' : Stack Role} {R : RoleT Role} {w : List (RoleT Role)} :
      Move O st (some R) st' → Run st' w st'' → Run st (R :: w) st''

/-- The machine reads `w` from `st` to the empty stack. -/
def Acc (st : Stack Role) (w : List (RoleT Role)) : Prop := Run O st w []

variable {O}

theorem Run.append {a b c : Stack Role} {u v : List (RoleT Role)} (h1 : Run O a u b)
    (h2 : Run O b v c) : Run O a (u ++ v) c := by
  induction h1 with
  | nil => exact h2
  | eps hm _ ih => exact .eps hm (ih h2)
  | read hm _ ih => exact .read hm (ih h2)

theorem Run.single_eps {a b : Stack Role} (h : Move O a none b) : Run O a [] b := .eps h .nil

/-! ## Soundness -/

/-- The meaning of one item. -/
def MI (O : Ontology CName Role) : Item Role → List (RoleT Role) → Prop
  | (S, false), u => Gen O u S
  | (S, true), v => ∀ u, Gen O u S → Gen O (u ++ v) S

/-- The meaning of a stack: the concatenation of the item meanings. -/
def MS (O : Ontology CName Role) : Stack Role → List (RoleT Role) → Prop
  | [], w => w = []
  | it :: st, w => ∃ u v, w = u ++ v ∧ MI O it u ∧ MS O st v

theorem MS_append : ∀ (a b : Stack Role) (w : List (RoleT Role)),
    MS O (a ++ b) w ↔ ∃ u v, w = u ++ v ∧ MS O a u ∧ MS O b v
  | [], b, w => by
    simp only [List.nil_append, MS]
    exact ⟨fun h => ⟨[], w, rfl, rfl, h⟩, by rintro ⟨u, v, rfl, rfl, h⟩; simpa using h⟩
  | it :: a, b, w => by
    simp only [List.cons_append, MS]
    constructor
    · rintro ⟨u, v, rfl, h1, h2⟩
      obtain ⟨v1, v2, rfl, h3, h4⟩ := (MS_append a b v).1 h2
      exact ⟨u ++ v1, v2, by simp, ⟨u, v1, rfl, h1, h3⟩, h4⟩
    · rintro ⟨u', v, rfl, ⟨u, v1, rfl, h1, h3⟩, h4⟩
      exact ⟨u, v1 ++ v, by simp, h1, (MS_append a b _).2 ⟨v1, v, rfl, h3, h4⟩⟩

theorem MS_ini : ∀ (B : List (RoleT Role)) (w : List (RoleT Role)), MS O (ini B) w ↔ GenSeq O w B
  | [], w => by simp only [ini, List.map_nil, MS]; exact (seqOf_nil_iff (P := Gen O)).symm
  | B :: Bs, w => by
    simp only [ini, List.map_cons, MS]
    rw [genSeq_iff_seqOf, seqOf_cons_iff]
    refine exists_congr fun u => exists_congr fun v => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    exact MS_ini Bs v

theorem eqv_le {T S : RoleT Role} (h : Eqv O T S) : RoleLe O T S := h.1

/-- Every silent move shrinks the meaning. -/
theorem move_eps_sound {st st' : Stack Role} (h : Move O st none st') :
    ∀ w, MS O st' w → MS O st w := by
  generalize hl : (none : Option (RoleT Role)) = l at h
  cases h with
  | letter => cases hl
  | @call R S B rest hr hle _ =>
    intro w hw
    obtain ⟨u, v, rfl, hu, v1, v2, rfl, hv1, hv2⟩ := hw
    exact ⟨u ++ v1, v2, by simp, hv1 u (gen_mono hu hle), hv2⟩
  | @refl T S B rest hr hs hle =>
    intro w hw
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := hw
    have hB := shapeOf_refl hs; subst hB
    have h0 : Gen O [] S := gen_rule hr hle genSeq_nil
    exact ⟨v1, v2, rfl, by simpa using hv1 [] h0, hv2⟩
  | @ord T S B rest hr _ he =>
    intro w hw
    obtain ⟨u, v, rfl, hu, hv⟩ := (MS_append _ _ w).1 hw
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := hv
    rw [MS_ini] at hu
    exact ⟨u ++ v1, v2, by simp, hv1 u (gen_rule hr he.1 hu), hv2⟩
  | @right T S B rest hr hs he =>
    intro w hw
    obtain ⟨u, v, rfl, hu, hv⟩ := (MS_append _ _ w).1 hw
    obtain ⟨u2, v2, rfl, hu2, hv2⟩ := hv
    rw [MS_ini] at hu
    refine ⟨u ++ u2, v2, by simp, ?_, hv2⟩
    have hseq : GenSeq O (u ++ u2) B := by
      rw [shapeOf_right hs]
      exact genSeq_append hu (genSeq_single.2 (gen_mono hu2 he.2))
    exact gen_rule hr he.1 hseq
  | @left T S B rest hr hs he =>
    intro w hw
    obtain ⟨u, v, rfl, hu, hv⟩ := (MS_append _ _ w).1 hw
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := hv
    rw [MS_ini] at hu
    refine ⟨u ++ v1, v2, by simp, fun u0 h0 => ?_, hv2⟩
    have hseq : GenSeq O (u0 ++ u) B := by
      rw [shapeOf_left hs]
      exact genSeq_cons (gen_mono h0 he.2) hu
    have := hv1 _ (gen_rule hr he.1 hseq)
    simpa using this
  | @trans T S B rest hr hs he =>
    intro w hw
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := hw
    refine ⟨v1, v2, rfl, fun u0 h0 => ?_, hv2⟩
    have hseq : GenSeq O (u0 ++ v1) B := by
      rw [shapeOf_trans hs]
      exact genSeq_cons (gen_mono h0 he.2) (genSeq_single.2 (gen_mono hv1 he.2))
    exact gen_rule hr he.1 hseq
  | @pop S rest =>
    intro w hw
    exact ⟨[], w, rfl, fun u h => by simpa using h, hw⟩

theorem move_read_sound {st st' : Stack Role} {R : RoleT Role} (h : Move O st (some R) st') :
    ∀ w, MS O st' w → MS O st (R :: w) := by
  generalize hl : some R = l at h
  cases h with
  | @letter R' S rest hle =>
    cases hl
    intro w hw
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := hw
    exact ⟨[R] ++ v1, v2, by simp, hv1 [R] (.letter hle), hv2⟩
  | _ => cases hl

theorem run_sound {st st' : Stack Role} {w : List (RoleT Role)} (h : Run O st w st') :
    ∀ v, MS O st' v → MS O st (w ++ v) := by
  induction h with
  | nil => exact fun v hv => hv
  | eps hm _ ih => exact fun v hv => move_eps_sound hm _ (ih v hv)
  | read hm _ ih => exact fun v hv => move_read_sound hm _ (ih v hv)

/-! ## Completeness -/

theorem run_ini {P : List (RoleT Role) → RoleT Role → Prop}
    (hP : ∀ u B, P u B → ∀ rest, Run O ((B, false) :: rest) u ((B, true) :: rest)) :
    ∀ (B : List (RoleT Role)) (w : List (RoleT Role)) (rest : Stack Role), SeqOf P w B →
      Run O (ini B ++ rest) w rest
  | [], w, rest, h => by
    rw [seqOf_nil_iff] at h; subst h; exact .nil
  | B :: Bs, w, rest, h => by
    obtain ⟨u, v, rfl, hu, hv⟩ := seqOf_cons_iff.1 h
    have h1 := hP u B hu (ini Bs ++ rest)
    have h2 : Run O ((B, true) :: (ini Bs ++ rest)) [] (ini Bs ++ rest) := .single_eps .pop
    have h3 := run_ini hP Bs v rest hv
    have := (h1.append h2).append h3
    simpa [ini] using this

/-- The completeness claim for one derivation. -/
def CI (O : Ontology CName Role) (u : List (RoleT Role)) (G : RoleT Role) : Prop :=
  ∀ S rest, RoleLe O G S → Run O ((S, false) :: rest) u ((S, true) :: rest)

theorem seqOf_mono {P Q : List (RoleT Role) → RoleT Role → Prop}
    (h : ∀ u B, P u B → Q u B) {w body : List (RoleT Role)} (hs : SeqOf P w body) :
    SeqOf Q w body := by
  obtain ⟨ws, hl, hc, rfl⟩ := hs
  exact ⟨ws, hl, fun p hp => h _ _ (hc p hp), rfl⟩

theorem gen_complete_rule {T G : RoleT Role} {body w : List (RoleT Role)}
    (hr : (T, body) ∈ rules O) (hle : RoleLe O T G) (hc : SeqOf (CI O) w body) : CI O w G := by
  have hP : ∀ u B, CI O u B → ∀ rest, Run O ((B, false) :: rest) u ((B, true) :: rest) :=
    fun u B h rest => h B rest Relation.ReflTransGen.refl
  -- the case of an item equivalent to the rule head
  have heq : ∀ S rest, Eqv O T S → Run O ((S, false) :: rest) w ((S, true) :: rest) := by
    intro S rest he
    cases hs : shapeOf T body with
    | refl =>
      have hB := shapeOf_refl hs; subst hB
      rw [seqOf_nil_iff] at hc; subst hc
      exact .single_eps (.refl hr hs he.1)
    | ord =>
      exact .eps (.ord hr hs he) (run_ini hP body w _ hc)
    | right =>
      have hB := shapeOf_right hs
      rw [hB] at hc
      obtain ⟨u, v, rfl, hu, hv⟩ := seqOf_append_iff.1 hc
      rw [seqOf_single] at hv
      exact .eps (.right hr hs he) ((run_ini hP _ u _ hu).append (hv S rest he.1))
    | left =>
      have hB := shapeOf_left hs
      rw [hB] at hc
      obtain ⟨u, v, rfl, hu, hv⟩ := seqOf_cons_iff.1 hc
      exact (hu S rest he.1).append (.eps (.left hr hs he) (run_ini hP _ v _ hv))
    | trans =>
      have hB := shapeOf_trans hs
      rw [hB] at hc
      obtain ⟨u, v, rfl, hu, hv⟩ := seqOf_cons_iff.1 hc
      rw [seqOf_single] at hv
      exact (hu S rest he.1).append (.eps (.trans hr hs he) (hv S rest he.1))
  intro S rest hGS
  have hTS := hle.trans hGS
  by_cases hST : RoleLe O S T
  · exact heq S rest ⟨hTS, hST⟩
  · have h1 := heq T ((S, true) :: rest) ⟨.refl, .refl⟩
    have := (Run.eps (.call hr hTS hST) h1).append (.single_eps .pop)
    simpa using this

/-- **Completeness.** A word of `G` takes every item `(S, false)` with
`G ⊑₁* S` to `(S, true)`. -/
theorem gen_complete {w : List (RoleT Role)} {G : RoleT Role} (h : Gen O w G) : CI O w G := by
  induction h with
  | letter hle =>
    intro S rest hGS
    exact .read (.letter (hle.trans hGS)) .nil
  | @rule T G body ws hr hle hlen _ ih =>
    exact gen_complete_rule hr hle ⟨ws, hlen, ih, rfl⟩

/-- **The language theorem.** The machine for `S` accepts exactly the
words of `S`. -/
theorem acc_iff_gen {S : RoleT Role} {w : List (RoleT Role)} :
    Acc O [(S, false)] w ↔ Gen O w S := by
  constructor
  · intro h
    have := run_sound h [] rfl
    obtain ⟨u, v, he, hu, hv⟩ := this
    simp only [MS] at hv
    subst hv
    simp only [List.append_nil] at he
    subst he
    exact hu
  · intro h
    have := (gen_complete h S [] .refl).append (Run.single_eps (O := O) .pop)
    simpa using this

end ContextCalculus.SROIQ

#print axioms ContextCalculus.SROIQ.acc_iff_gen
