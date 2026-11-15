import ContextCalculus.SRIQ.NormalForm

/-!
# SROIQ role inclusions: the language of a role (stage C3, design sections 1, 2)

`docs/V1.7.0-C3-ROLES-DESIGN.md`. The role axioms of an `SRIQ` ontology
are its `chain body S` clauses. Chains of length one form the role
hierarchy `SRIQ.RoleLe` (`⊑₁*`). Every other chain, of length zero
(reflexivity, `chain [] S`) or at least two, is a *rule* `(S, body)`; a
rule also stands flipped, `(S.flip, flipW body)`.

`Gen O w G` (`w ⊑* G`) is the least relation with `Gen O [R] G` for
`R ⊑₁* G` and `Gen O (w₁ ++ … ++ wₖ) G` for a rule `(T, [B₁, …, Bₖ])`
with `T ⊑₁* G` and `Gen O wᵢ Bᵢ`.

* `gen_sound` (G1): in every model, a `w`-path is a `G`-edge.
* `gen_flip` (G2): `Gen O w G ↔ Gen O (flipW w) G.flip`.
* `gen_chain`, `gen_mono` (G3): closure under the chains and the hierarchy.
* `gen_simple` (G4): without a rule below `G`, the words of `G` are the
  letters below `G`.
-/

namespace ContextCalculus.SROIQ

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Clause Ontology RoleLe)

variable {D CName Role : Type}

/-! ## Paths -/

/-- The inverse of a word: flip every letter and reverse. -/
def flipW (w : List (RoleT Role)) : List (RoleT Role) := (w.map RoleT.flip).reverse

@[simp] theorem flipW_nil : flipW ([] : List (RoleT Role)) = [] := rfl

theorem flipW_cons (R : RoleT Role) (w : List (RoleT Role)) :
    flipW (R :: w) = flipW w ++ [R.flip] := by
  simp [flipW]

theorem flipW_append (u v : List (RoleT Role)) : flipW (u ++ v) = flipW v ++ flipW u := by
  simp [flipW]

@[simp] theorem flipW_flipW (w : List (RoleT Role)) : flipW (flipW w) = w := by
  simp [flipW, List.map_reverse, Function.comp_def]

theorem length_flipW (w : List (RoleT Role)) : (flipW w).length = w.length := by
  simp [flipW]

theorem path_append (I : Interp D CName Role) :
    ∀ (u v : List (RoleT Role)) (x y : D), I.path (u ++ v) x y ↔ ∃ z, I.path u x z ∧ I.path v z y
  | [], v, x, y => by simp [Interp.path]
  | R :: u, v, x, y => by
    simp only [List.cons_append, Interp.path]
    constructor
    · rintro ⟨z, hxz, hz⟩
      obtain ⟨z', h1, h2⟩ := (path_append I u v z y).1 hz
      exact ⟨z', ⟨z, hxz, h1⟩, h2⟩
    · rintro ⟨z', ⟨z, hxz, h1⟩, h2⟩
      exact ⟨z, hxz, (path_append I u v z y).2 ⟨z', h1, h2⟩⟩

theorem path_single (I : Interp D CName Role) (R : RoleT Role) (x y : D) :
    I.path [R] x y ↔ I.rt R x y := by
  simp [Interp.path]

theorem path_flipW (I : Interp D CName Role) :
    ∀ (w : List (RoleT Role)) (x y : D), I.path (flipW w) x y ↔ I.path w y x
  | [], x, y => by simp [Interp.path, eq_comm]
  | R :: w, x, y => by
    rw [flipW_cons, path_append]
    simp only [Interp.rt_flip, Interp.path, exists_eq_right]
    constructor
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, h2, (path_flipW I w x z).1 h1⟩
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, (path_flipW I w x z).2 h2, h1⟩

/-! ## Rules -/

/-- The rules of one clause: a chain whose body does not have length one,
and its flip. -/
def rulesOf : Clause CName Role → List (RoleT Role × List (RoleT Role))
  | .chain body S => if body.length = 1 then [] else [(S, body), (S.flip, flipW body)]
  | _ => []

/-- The rules of an ontology. -/
def rules (O : Ontology CName Role) : List (RoleT Role × List (RoleT Role)) :=
  O.flatMap rulesOf

theorem mem_rules {O : Ontology CName Role} {T : RoleT Role} {body : List (RoleT Role)} :
    (T, body) ∈ rules O ↔ body.length ≠ 1 ∧
      (Clause.chain body T ∈ O ∨ Clause.chain (flipW body) T.flip ∈ O) := by
  simp only [rules, List.mem_flatMap]
  constructor
  · rintro ⟨cl, hcl, hm⟩
    cases cl <;> simp only [rulesOf, List.not_mem_nil] at hm
    rename_i b S
    split_ifs at hm with hb
    · simp at hm
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hb, Or.inl hcl⟩
      · refine ⟨by rwa [length_flipW], Or.inr ?_⟩
        simpa using hcl
  · rintro ⟨hb, h | h⟩
    · exact ⟨_, h, by simp [rulesOf, hb]⟩
    · refine ⟨_, h, ?_⟩
      have : (flipW body).length ≠ 1 := by rwa [length_flipW]
      simp [rulesOf, this]

theorem flip_mem_rules {O : Ontology CName Role} {T : RoleT Role} {body : List (RoleT Role)}
    (h : (T, body) ∈ rules O) : (T.flip, flipW body) ∈ rules O := by
  rw [mem_rules] at h ⊢
  refine ⟨by rw [length_flipW]; exact h.1, ?_⟩
  rw [RoleT.flip_flip, flipW_flipW]
  exact h.2.symm

/-- A rule holds in every model: a path along its body is an edge of its head. -/
theorem rule_sound {I : Interp D CName Role} {O : Ontology CName Role} (hI : SRIQ.models I O)
    {T : RoleT Role} {body : List (RoleT Role)} (h : (T, body) ∈ rules O) (x y : D)
    (hp : I.path body x y) : I.rt T x y := by
  rcases (mem_rules.1 h).2 with h1 | h1
  · exact hI _ h1 x y hp
  · have := hI _ h1 y x ((path_flipW I body y x).2 hp)
    exact (Interp.rt_flip I T y x).1 this

/-! ## The language of a role -/

/-- `Gen O w G`: the word `w` lies in the language of `G` (`w ⊑* G`). -/
inductive Gen (O : Ontology CName Role) : List (RoleT Role) → RoleT Role → Prop
  | letter {R G : RoleT Role} : RoleLe O R G → Gen O [R] G
  | rule {T G : RoleT Role} {body : List (RoleT Role)} (ws : List (List (RoleT Role)))
      (hr : (T, body) ∈ rules O) (hle : RoleLe O T G) (hlen : ws.length = body.length)
      (h : ∀ p ∈ ws.zip body, Gen O p.1 p.2) : Gen O ws.flatten G

variable {O : Ontology CName Role}

/-- The children of a rule, as a predicate on two lists. -/
theorem zip_cons_iff {α β : Type} (P : α → β → Prop) (a : α) (b : β) (as : List α) (bs : List β) :
    (∀ p ∈ (a :: as).zip (b :: bs), P p.1 p.2) ↔ P a b ∧ ∀ p ∈ as.zip bs, P p.1 p.2 := by
  simp

/-- **G1.** In every model of `O`, a path along a word of `G` is a `G`-edge. -/
theorem gen_sound {I : Interp D CName Role} (hI : SRIQ.models I O) {w : List (RoleT Role)}
    {G : RoleT Role} (h : Gen O w G) : ∀ x y, I.path w x y → I.rt G x y := by
  induction h with
  | letter hle =>
    intro x y hp
    exact SRIQ.roleLe_sound hI hle x y ((path_single I _ x y).1 hp)
  | @rule T G body ws hr hle hlen hc ih =>
    intro x y hp
    refine SRIQ.roleLe_sound hI hle x y (rule_sound hI hr x y ?_)
    clear hle hr
    induction ws generalizing body x with
    | nil =>
      cases body with
      | nil => simpa [Interp.path] using hp
      | cons _ _ => simp at hlen
    | cons u ws ihw =>
      cases body with
      | nil => simp at hlen
      | cons B body =>
        rw [List.flatten_cons, path_append] at hp
        obtain ⟨z, h1, h2⟩ := hp
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        exact ⟨z, ih (u, B) (by simp) x z h1,
          ihw hlen (fun p hp => hc p (List.mem_cons_of_mem _ hp))
            (fun p hp => ih p (List.mem_cons_of_mem _ hp)) z h2⟩

/-- **G3, hierarchy.** A word of `R` is a word of every super-role of `R`. -/
theorem gen_mono {w : List (RoleT Role)} {R G : RoleT Role} (h : Gen O w R) (hle : RoleLe O R G) :
    Gen O w G := by
  cases h with
  | letter h0 => exact .letter (h0.trans hle)
  | rule ws hr h0 hlen hc => exact .rule ws hr (h0.trans hle) hlen hc

theorem gen_self (R : RoleT Role) : Gen O [R] R := .letter Relation.ReflTransGen.refl

/-- Build the flattened word of a rule from its children. -/
theorem gen_of_children {T G : RoleT Role} {body : List (RoleT Role)} (hr : (T, body) ∈ rules O)
    (hle : RoleLe O T G) :
    ∀ (ws : List (List (RoleT Role))), ws.length = body.length →
      (∀ p ∈ ws.zip body, Gen O p.1 p.2) → Gen O ws.flatten G :=
  fun ws hlen h => .rule ws hr hle hlen h

/-- The children of a sequence of roles: a word for each and their concatenation. -/
def GenSeq (O : Ontology CName Role) (w : List (RoleT Role)) (body : List (RoleT Role)) : Prop :=
  ∃ ws : List (List (RoleT Role)), ws.length = body.length ∧
    (∀ p ∈ ws.zip body, Gen O p.1 p.2) ∧ ws.flatten = w

theorem genSeq_nil : GenSeq O [] [] := ⟨[], rfl, by simp, rfl⟩

theorem genSeq_cons {u v : List (RoleT Role)} {B : RoleT Role} {body : List (RoleT Role)}
    (h1 : Gen O u B) (h2 : GenSeq O v body) : GenSeq O (u ++ v) (B :: body) := by
  obtain ⟨ws, hl, hc, rfl⟩ := h2
  exact ⟨u :: ws, by simp [hl], by
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h1
    · exact hc p hp, rfl⟩

theorem genSeq_cons_iff {w : List (RoleT Role)} {B : RoleT Role} {body : List (RoleT Role)} :
    GenSeq O w (B :: body) ↔ ∃ u v, w = u ++ v ∧ Gen O u B ∧ GenSeq O v body := by
  constructor
  · rintro ⟨ws, hl, hc, rfl⟩
    cases ws with
    | nil => simp at hl
    | cons u ws =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      refine ⟨u, ws.flatten, rfl, hc (u, B) (by simp), ws, hl,
        fun p hp => hc p (List.mem_cons_of_mem _ hp), rfl⟩
  · rintro ⟨u, v, rfl, h1, h2⟩
    exact genSeq_cons h1 h2

theorem genSeq_append {u v : List (RoleT Role)} :
    ∀ {b1 b2 : List (RoleT Role)}, GenSeq O u b1 → GenSeq O v b2 → GenSeq O (u ++ v) (b1 ++ b2)
  | [], _, h1, h2 => by
    obtain ⟨ws, hl, -, rfl⟩ := h1
    cases ws with
    | nil => simpa using h2
    | cons _ _ => simp at hl
  | B :: b1, b2, h1, h2 => by
    obtain ⟨u1, u2, rfl, hu1, hu2⟩ := genSeq_cons_iff.1 h1
    rw [List.append_assoc, List.cons_append]
    exact genSeq_cons hu1 (genSeq_append hu2 h2)

theorem genSeq_append_iff {w : List (RoleT Role)} :
    ∀ {b1 b2 : List (RoleT Role)},
      GenSeq O w (b1 ++ b2) ↔ ∃ u v, w = u ++ v ∧ GenSeq O u b1 ∧ GenSeq O v b2
  | [], b2 => ⟨fun h => ⟨[], w, rfl, genSeq_nil, h⟩, by
      rintro ⟨u, v, rfl, ⟨ws, hl, -, rfl⟩, h2⟩
      cases ws with
      | nil => simpa using h2
      | cons _ _ => simp at hl⟩
  | B :: b1, b2 => by
    rw [List.cons_append, genSeq_cons_iff]
    constructor
    · rintro ⟨u, v, rfl, h1, h2⟩
      obtain ⟨v1, v2, rfl, hv1, hv2⟩ := genSeq_append_iff.1 h2
      exact ⟨u ++ v1, v2, by simp, genSeq_cons h1 hv1, hv2⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      obtain ⟨u1, u2, rfl, hu1, hu2⟩ := genSeq_cons_iff.1 hu
      exact ⟨u1, u2 ++ v, by simp, hu1, genSeq_append hu2 hv⟩

theorem genSeq_single {w : List (RoleT Role)} {B : RoleT Role} :
    GenSeq O w [B] ↔ Gen O w B := by
  rw [genSeq_cons_iff]
  constructor
  · rintro ⟨u, v, rfl, h, ⟨ws, hl, -, rfl⟩⟩
    cases ws with
    | nil => simpa using h
    | cons _ _ => simp at hl
  · intro h
    exact ⟨w, [], by simp, h, genSeq_nil⟩

/-- **G3, rules.** The concatenated words of a rule body give a word of
every super-role of the rule head. -/
theorem gen_rule {T G : RoleT Role} {body w : List (RoleT Role)} (hr : (T, body) ∈ rules O)
    (hle : RoleLe O T G) (h : GenSeq O w body) : Gen O w G := by
  obtain ⟨ws, hl, hc, rfl⟩ := h
  exact .rule ws hr hle hl hc

/-- The rule case of `Gen`, with the children as a sequence. -/
theorem gen_cases {w : List (RoleT Role)} {G : RoleT Role} (h : Gen O w G) :
    (∃ R, w = [R] ∧ RoleLe O R G) ∨
      ∃ T body, (T, body) ∈ rules O ∧ RoleLe O T G ∧ GenSeq O w body := by
  cases h with
  | letter hle => exact Or.inl ⟨_, rfl, hle⟩
  | rule ws hr hle hl hc => exact Or.inr ⟨_, _, hr, hle, ws, hl, hc, rfl⟩

/-- **G3, chains.** A chain clause of `O` with a body of any length is closed
under `Gen`. -/
theorem gen_chain {body w : List (RoleT Role)} {T : RoleT Role} (hcl : Clause.chain body T ∈ O)
    (h : GenSeq O w body) : Gen O w T := by
  by_cases hb : body.length = 1
  · match body, hb with
    | [B], _ =>
      exact gen_mono (genSeq_single.1 h) (SRIQ.roleLe_single hcl)
  · exact gen_rule (mem_rules.2 ⟨hb, Or.inl hcl⟩) Relation.ReflTransGen.refl h

/-! ## Flip -/

/-- **G2.** The inverse of a word of `G` is a word of `G.flip`. -/
theorem gen_flip_of {w : List (RoleT Role)} {G : RoleT Role} (h : Gen O w G) :
    Gen O (flipW w) G.flip := by
  induction h with
  | letter hle => exact .letter (SRIQ.roleLe_flip hle)
  | @rule T G body ws hr hle hlen hc ih =>
    refine gen_rule (flip_mem_rules hr) (SRIQ.roleLe_flip hle) ?_
    -- children: flip each and reverse
    have key : ∀ (ws : List (List (RoleT Role))) (body : List (RoleT Role)),
        ws.length = body.length → (∀ p ∈ ws.zip body, Gen O (flipW p.1) p.2.flip) →
        GenSeq O (flipW ws.flatten) (flipW body) := by
      intro ws
      induction ws with
      | nil =>
        intro body hl _
        cases body with
        | nil => exact genSeq_nil
        | cons _ _ => simp at hl
      | cons u ws ihw =>
        intro body hl hc'
        cases body with
        | nil => simp at hl
        | cons B body =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          rw [List.flatten_cons, flipW_append, flipW_cons]
          exact genSeq_append (ihw body hl fun p hp => hc' p (List.mem_cons_of_mem _ hp))
            (genSeq_single.2 (hc' (u, B) (by simp)))
    exact key ws body hlen ih

theorem gen_flip {w : List (RoleT Role)} {G : RoleT Role} :
    Gen O w G ↔ Gen O (flipW w) G.flip := by
  refine ⟨gen_flip_of, fun h => ?_⟩
  have := gen_flip_of h
  rwa [flipW_flipW, RoleT.flip_flip] at this

/-! ## Simple roles -/

/-- `G` is simple in the strengthened sense: no rule (of length zero or at
least two) has its head below `G` or below `G.flip`. -/
def SimpleC (O : Ontology CName Role) (G : RoleT Role) : Prop :=
  ∀ T body, (T, body) ∈ rules O → ¬ RoleLe O T G

/-- **G4.** The words of a simple role are the letters below it. -/
theorem gen_simple {w : List (RoleT Role)} {G : RoleT Role} (hs : SimpleC O G) :
    Gen O w G ↔ ∃ R, w = [R] ∧ RoleLe O R G := by
  constructor
  · intro h
    rcases gen_cases h with h | ⟨T, body, hr, hle, -⟩
    · exact h
    · exact absurd hle (hs T body hr)
  · rintro ⟨R, rfl, hle⟩
    exact .letter hle

theorem simpleC_flip {G : RoleT Role} (hs : SimpleC O G) : SimpleC O G.flip := by
  intro T body hr hle
  have := hs T.flip (flipW body) (flip_mem_rules hr) (by simpa using SRIQ.roleLe_flip hle)
  exact this

end ContextCalculus.SROIQ

#print axioms ContextCalculus.SROIQ.gen_sound
#print axioms ContextCalculus.SROIQ.gen_flip
#print axioms ContextCalculus.SROIQ.gen_chain
#print axioms ContextCalculus.SROIQ.gen_simple
