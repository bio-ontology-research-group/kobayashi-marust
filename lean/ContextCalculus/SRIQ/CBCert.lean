import ContextCalculus.SRIQ.CBTypes
import ContextCalculus.SRIQ.FastElimAProof

/-!
# The two-sided route: a derivation for the "yes" answers (stage C1f)

`docs/V1.7.0-C1F-CLOSURE.md`, sections 3 and 3.2.

- `CCl.Sat`: a clause `⟨L, P, B, H, Q⟩` holds in an interpretation.
- `ruleOK`: the check of one step against the ontology and the earlier
  steps; `checkCert`: every step passes.
- `checkCert_sound`: in every model of the ontology, every clause of an
  accepted certificate holds (induction on the position, one lemma per
  rule).
- `witB`: the node, entry and back-set checks of a candidate set
  (`WitP`), without the closure rules R1 to R6.
- `cbClassify`: rows from the derivation, checked against the live root
  types of the witness; `cbClassify_spec`: every row is exact on the
  requested names.
-/

namespace ContextCalculus.SRIQ.CB

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ ContextCalculus.SRIQ.Fast

variable {n m : Nat} {D : Type}

/-! ## Semantics of clauses -/

/-- The clause holds in `I`: for every predecessor `y` and element `x`. -/
def CCl.Sat (I : Interp D (Fin n) (Fin m)) (c : CCl) : Prop :=
  ∀ y x : D, (∀ R : RoleT (Fin m), rc R ∈ c.L → I.rt R y x) →
    (∀ a : Fin n, a.val ∈ c.P → I.c a y) → (∀ a : Fin n, a.val ∈ c.B → I.c a x) →
    (∃ h : Fin n, h.val ∈ c.H ∧ I.c h x) ∨ (∃ h : Fin n, h.val ∈ c.Q ∧ I.c h y)

/-! ## The check -/

def subA (a b : Array Nat) : Bool := a.all (b.contains ·)

/-- `a ⊆ b ∪ {p}` -/
def subAx (a b : Array Nat) (p : Nat) : Bool := a.all fun x => x == p || b.contains x

theorem subA_mem {a b : Array Nat} (h : subA a b = true) {x : Nat} (hx : x ∈ a) : x ∈ b :=
  Array.contains_iff_mem.1 (Array.all_eq_true'.1 h x hx)

theorem subAx_mem {a b : Array Nat} {p : Nat} (h : subAx a b p = true) {x : Nat} (hx : x ∈ a) :
    x = p ∨ x ∈ b := by
  have := Array.all_eq_true'.1 h x hx
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  exact this.imp id Array.contains_iff_mem.1

theorem mem_of_contains {a : Array Nat} {x : Nat} (h : a.contains x = true) : x ∈ a :=
  Array.contains_iff_mem.1 h

/-- A lower clause `a ⊑ ≥k R.b` (`exRight` with `k = 1`). -/
def lowOf : Clause (Fin n) (Fin m) → Option (Fin n × Nat × RoleT (Fin m) × Fin n)
  | .exRight a R b => some (a, 1, R, b)
  | .atLeast a k R b => some (a, k, R, b)
  | _ => none

/-- The clause of step `j`. -/
def prem (S : Array CStep) (j : Nat) : CCl := (S[j]?.getD default).c

/-- Every role code of `L` is a super-role of `R`. -/
def underB (ixf : IxF) (R : RoleT (Fin m)) (L : Array Nat) : Bool := L.all (bsA (upSA ixf R))

/-- The check of a step at position `i` with conclusion `s`. -/
def ruleOK (ixf : IxF) (OA : Array (Clause (Fin n) (Fin m))) (S : Array CStep) (i : Nat)
    (s : CCl) : CRule → Bool
  | .gci g => match OA[g]? with
    | some (.gci body head) => body.all (fun a => s.B.contains a.val) && head.all (fun a => s.H.contains a.val)
    | _ => false
  | .taut p => decide (p < n) && s.B.contains p && s.H.contains p
  | .fwd g => match OA[g]? with
    | some (.allRight a R c) => s.L.contains (rc R) && s.P.contains a.val && s.H.contains c.val
    | _ => false
  | .bwd g => match OA[g]? with
    | some (.allRight a R c) => s.L.contains (rc R.flip) && s.B.contains a.val && s.Q.contains c.val
    | _ => false
  | .up j =>
    let c := prem S j
    decide (j < i) && c.L.isEmpty && c.P.isEmpty && c.Q.isEmpty && subA c.B s.P && subA c.H s.Q
  | .resX j k p =>
    let c₁ := prem S j
    let c₂ := prem S k
    decide (j < i) && decide (k < i) && c₁.H.contains p && c₂.B.contains p &&
      subA c₁.L s.L && subA c₂.L s.L && subA c₁.P s.P && subA c₂.P s.P &&
      subA c₁.B s.B && subAx c₂.B s.B p && subAx c₁.H s.H p && subA c₂.H s.H &&
      subA c₁.Q s.Q && subA c₂.Q s.Q
  | .resY j k p =>
    let c₁ := prem S j
    let c₂ := prem S k
    decide (j < i) && decide (k < i) && c₁.Q.contains p && c₂.P.contains p &&
      subA c₁.L s.L && subA c₂.L s.L && subA c₁.P s.P && subAx c₂.P s.P p &&
      subA c₁.B s.B && subA c₂.B s.B && subA c₁.H s.H && subA c₂.H s.H &&
      subAx c₁.Q s.Q p && subA c₂.Q s.Q
  | .pred g j =>
    let c := prem S j
    decide (j < i) && match OA[g]?.bind lowOf with
    | some (a, k, R, b) => decide (1 ≤ k) && c.H.isEmpty && c.B.all (· == b.val) &&
        underB ixf R c.L && subA c.P s.B && s.B.contains a.val && subA c.Q s.H
    | none => false
  | .amo0a g => match OA[g]? with
    | some (.atMost a k R e) => k == 0 && s.L.contains (rc R) && s.P.contains a.val && s.B.contains e.val
    | _ => false
  | .amo0b g => match OA[g]? with
    | some (.atMost a k R e) => k == 0 && s.L.contains (rc R.flip) && s.P.contains e.val &&
        s.B.contains a.val
    | _ => false
  | .clash gu gl je =>
    let ce := prem S je
    decide (je < i) && match OA[gu]?, OA[gl]?.bind lowOf with
    | some (.atMost a nn R e), some (a₂, k, R₂, b₂) =>
      decide (nn < k) && bsA (upSA ixf R₂) (rc R) && ce.B.all (· == b₂.val) &&
        ce.H.all (· == e.val) && underB ixf R₂ ce.L && s.B.contains a.val && s.B.contains a₂.val &&
        subA ce.P s.B && subA ce.Q s.H
    | _, _ => false
  | .sib gu gl je jr =>
    let ce := prem S je
    let cr := prem S jr
    decide (je < i) && decide (jr < i) && match OA[gu]?, OA[gl]?.bind lowOf with
    | some (.atMost a nn R e), some (a₂, k, R₂, b₂) =>
      decide (nn ≤ 1) && decide (1 ≤ k) && bsA (upSA ixf R₂) (rc R) && ce.B.all (· == b₂.val) &&
        ce.H.all (· == e.val) && underB ixf R₂ ce.L && underB ixf R₂ cr.L &&
        s.L.contains (rc R) && s.P.contains a.val && s.P.contains a₂.val && subA ce.P s.P &&
        subA cr.P s.P && s.B.contains e.val && subAx cr.B s.B b₂.val && subA cr.H s.H &&
        subA ce.Q s.Q && subA cr.Q s.Q
    | _, _ => false
  | .par gu gl je jr =>
    let ce := prem S je
    let cr := prem S jr
    decide (je < i) && decide (jr < i) && match OA[gu]?, OA[gl]?.bind lowOf with
    | some (.atMost a nn R e), some (a₂, k, R₂, b₂) =>
      decide (nn ≤ 1) && decide (1 ≤ k) && bsA (upSA ixf R₂) (rc R) && ce.B.all (· == b₂.val) &&
        ce.H.all (· == e.val) && underB ixf R₂ ce.L && underB ixf R₂ cr.L &&
        s.L.contains (rc R.flip) && s.P.contains e.val && subAx cr.B s.P b₂.val &&
        s.B.contains a.val && s.B.contains a₂.val && subA ce.P s.B && subA cr.P s.B &&
        subA ce.Q s.H && subA cr.Q s.H && subA cr.H s.Q
    | _, _ => false

/-- **The certificate check**: every step passes against the steps before it. -/
def checkCert (ixf : IxF) (OA : Array (Clause (Fin n) (Fin m))) (S : Array CStep) : Bool :=
  (List.range S.size).all fun i => ruleOK ixf OA S i (prem S i) (S[i]?.getD default).rule

/-! ## Soundness of the rules -/

section Sound

variable {O : Ontology (Fin n) (Fin m)} {I : Interp D (Fin n) (Fin m)}

theorem clause_of_get {g : Nat} {cl : Clause (Fin n) (Fin m)} (h : O.toArray[g]? = some cl) : cl ∈ O := by
  rw [List.getElem?_toArray] at h
  exact List.mem_of_getElem? h

theorem fin_eq_of_val {a b : Fin n} (h : a.val = b.val) : a = b := Fin.ext h

/-- Roles below `upSA R` hold where `R` holds. -/
theorem under_rt (hI : models I O) {R : RoleT (Fin m)} {L : Array Nat}
    (h : underB (mkIxF O (mkIx O)) R L = true) {x z : D} (hR : I.rt R x z) :
    ∀ R' : RoleT (Fin m), rc R' ∈ L → I.rt R' x z := by
  intro R' hR'
  have hb := Array.all_eq_true'.1 h _ hR'
  have hm : rc R' ∈ upSA (mkIxF O (mkIx O)) R := bsA_sound hb
  have : R' ∈ upS (mkIx O) R := by
    rw [← absLab_upSA (O := O)]
    exact mem_absLab.2 hm
  exact roleLe_sound hI (upS_sound this) x z hR

theorem up_rt (hI : models I O) {R R' : RoleT (Fin m)}
    (h : bsA (upSA (mkIxF O (mkIx O)) R) (rc R') = true) {x z : D} (hR : I.rt R x z) : I.rt R' x z := by
  have hm : rc R' ∈ upSA (mkIxF O (mkIx O)) R := bsA_sound h
  have : R' ∈ upS (mkIx O) R := by
    rw [← absLab_upSA (O := O)]
    exact mem_absLab.2 hm
  exact roleLe_sound hI (upS_sound this) x z hR

/-- The witnesses of a lower clause. -/
theorem lowOf_list (hI : models I O) {cl : Clause (Fin n) (Fin m)} (hcl : cl ∈ O)
    {a b : Fin n} {k : Nat} {R : RoleT (Fin m)} (hl : lowOf cl = some (a, k, R, b)) {x : D}
    (hx : I.c a x) : ∃ l : List D, l.Nodup ∧ l.length = k ∧ ∀ z ∈ l, I.rt R x z ∧ I.c b z := by
  have hs := hI cl hcl
  cases cl with
  | exRight a' R' b' =>
    simp only [lowOf, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    obtain ⟨z, hz⟩ := hs x hx
    exact ⟨[z], List.nodup_singleton z, rfl, by simpa using hz⟩
  | atLeast a' k' R' b' =>
    simp only [lowOf, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact hs x hx
  | _ => simp [lowOf] at hl

theorem lowOf_wit (hI : models I O) {cl : Clause (Fin n) (Fin m)} (hcl : cl ∈ O)
    {a b : Fin n} {k : Nat} {R : RoleT (Fin m)} (hl : lowOf cl = some (a, k, R, b)) (hk : 1 ≤ k)
    {x : D} (hx : I.c a x) : ∃ z, I.rt R x z ∧ I.c b z := by
  obtain ⟨l, -, hlen, hl⟩ := lowOf_list hI hcl hl hx
  match l, hlen with
  | z :: _, _ => exact ⟨z, hl z List.mem_cons_self⟩
  | [], h => simp at h; omega

/-- Two distinct counted neighbours violate an at-most clause with number at most one. -/
theorem amo_eq (hI : models I O) {a e : Fin n} {nn : Nat} {R : RoleT (Fin m)}
    (hcl : Clause.atMost a nn R e ∈ O) (hnn : nn ≤ 1) {x u v : D} (hx : I.c a x)
    (hu : I.rt R x u) (heu : I.c e u) (hv : I.rt R x v) (hev : I.c e v) : u = v := by
  by_contra hne
  have := hI _ hcl x hx [u, v] (by simp [hne]) (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨hu, heu⟩
    · exact ⟨hv, hev⟩)
  simp at this
  omega

theorem mem_B_single {c : CCl} {b : Fin n} (h : c.B.all (· == b.val) = true) {a : Fin n}
    (ha : a.val ∈ c.B) : a = b := by
  have := Array.all_eq_true'.1 h _ ha
  simp only [beq_iff_eq] at this
  exact Fin.ext this

theorem rt_flip_iff {R : RoleT (Fin m)} {y x : D} : I.rt R.flip y x ↔ I.rt R x y :=
  Interp.rt_flip I R y x

/-- **Each rule is sound.** -/
theorem ruleOK_sound (hI : models I O) {S : Array CStep} {i : Nat} {s : CCl} {r : CRule}
    (h : ruleOK (mkIxF O (mkIx O)) O.toArray S i s r = true)
    (hprev : ∀ j < i, (prem S j).Sat I) : s.Sat I := by
  intro y x hL hP hB
  cases r with
  | gci g =>
    simp only [ruleOK] at h
    split at h
    · next body head hg =>
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨b, hb, hbx⟩ := hI _ (clause_of_get hg) x (fun a ha => hB a (mem_of_contains (h.1 a ha)))
      exact Or.inl ⟨b, mem_of_contains (h.2 b hb), hbx⟩
    · simp at h
  | taut p =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp, hb⟩, hh⟩ := h
    exact Or.inl ⟨⟨p, hp⟩, mem_of_contains hh, hB ⟨p, hp⟩ (mem_of_contains hb)⟩
  | fwd g =>
    simp only [ruleOK] at h
    split at h
    · next a R c hg =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hl, hp⟩, hh⟩ := h
      have := hI _ (clause_of_get hg) y (hP a (mem_of_contains hp)) x (hL R (mem_of_contains hl))
      exact Or.inl ⟨c, mem_of_contains hh, this⟩
    · simp at h
  | bwd g =>
    simp only [ruleOK] at h
    split at h
    · next a R c hg =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hl, hb⟩, hq⟩ := h
      have hr := rt_flip_iff.1 (hL R.flip (mem_of_contains hl))
      have := hI _ (clause_of_get hg) x (hB a (mem_of_contains hb)) y hr
      exact Or.inr ⟨c, mem_of_contains hq, this⟩
    · simp at h
  | up j =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq, Array.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨hj, hl⟩, hp⟩, hq⟩, hb⟩, hh⟩ := h
    rcases hprev j hj x y (by simp [hl]) (by simp [hp]) (fun a ha => hP a (subA_mem hb ha)) with
      ⟨g, hg, hgy⟩ | ⟨g, hg, -⟩
    · exact Or.inr ⟨g, subA_mem hh hg, hgy⟩
    · simp [hq] at hg
  | resX j k p =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hj, hk⟩, hp1⟩, hp2⟩, hL1⟩, hL2⟩, hP1⟩, hP2⟩, hB1⟩, hB2⟩, hH1⟩, hH2⟩, hQ1⟩, hQ2⟩ := h
    rcases hprev j hj y x (fun R hR => hL R (subA_mem hL1 hR)) (fun a ha => hP a (subA_mem hP1 ha))
      (fun a ha => hB a (subA_mem hB1 ha)) with ⟨g, hg, hgx⟩ | ⟨g, hg, hgy⟩
    · by_cases hgp : g.val = p
      · rcases hprev k hk y x (fun R hR => hL R (subA_mem hL2 hR)) (fun a ha => hP a (subA_mem hP2 ha))
          (fun a ha => by
            rcases subAx_mem hB2 ha with h' | h'
            · rw [fin_eq_of_val (h'.trans hgp.symm)]; exact hgx
            · exact hB a h') with ⟨g', hg', hg'x⟩ | ⟨g', hg', hg'y⟩
        · exact Or.inl ⟨g', subA_mem hH2 hg', hg'x⟩
        · exact Or.inr ⟨g', subA_mem hQ2 hg', hg'y⟩
      · rcases subAx_mem hH1 hg with h' | h'
        · exact absurd h' hgp
        · exact Or.inl ⟨g, h', hgx⟩
    · exact Or.inr ⟨g, subA_mem hQ1 hg, hgy⟩
  | resY j k p =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hj, hk⟩, hp1⟩, hp2⟩, hL1⟩, hL2⟩, hP1⟩, hP2⟩, hB1⟩, hB2⟩, hH1⟩, hH2⟩, hQ1⟩, hQ2⟩ := h
    rcases hprev j hj y x (fun R hR => hL R (subA_mem hL1 hR)) (fun a ha => hP a (subA_mem hP1 ha))
      (fun a ha => hB a (subA_mem hB1 ha)) with ⟨g, hg, hgx⟩ | ⟨g, hg, hgy⟩
    · exact Or.inl ⟨g, subA_mem hH1 hg, hgx⟩
    · by_cases hgp : g.val = p
      · rcases hprev k hk y x (fun R hR => hL R (subA_mem hL2 hR))
          (fun a ha => by
            rcases subAx_mem hP2 ha with h' | h'
            · rw [fin_eq_of_val (h'.trans hgp.symm)]; exact hgy
            · exact hP a h')
          (fun a ha => hB a (subA_mem hB2 ha)) with ⟨g', hg', hg'x⟩ | ⟨g', hg', hg'y⟩
        · exact Or.inl ⟨g', subA_mem hH2 hg', hg'x⟩
        · exact Or.inr ⟨g', subA_mem hQ2 hg', hg'y⟩
      · rcases subAx_mem hQ1 hg with h' | h'
        · exact absurd h' hgp
        · exact Or.inr ⟨g, h', hgy⟩
  | pred g j =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hj, h⟩ := h
    split at h
    · next a k R b hlo =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Array.isEmpty_iff] at h
      obtain ⟨⟨⟨⟨⟨⟨hk, hH⟩, hBb⟩, hun⟩, hPB⟩, ha⟩, hQH⟩ := h
      obtain ⟨cl, hcl, hlo'⟩ := Option.bind_eq_some_iff.1 hlo
      obtain ⟨z, hRz, hbz⟩ := lowOf_wit hI (clause_of_get hcl) hlo' hk (hB a (mem_of_contains ha))
      rcases hprev j hj x z (under_rt hI hun hRz) (fun a' ha' => hB a' (subA_mem hPB ha'))
        (fun a' ha' => by rw [mem_B_single hBb ha']; exact hbz) with ⟨g', hg', -⟩ | ⟨g', hg', hg'x⟩
      · simp [hH] at hg'
      · exact Or.inl ⟨g', subA_mem hQH hg', hg'x⟩
    · simp at h
  | amo0a g =>
    simp only [ruleOK] at h
    split at h
    · next a k R e hg =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hk, hl⟩, hp⟩, hb⟩ := h
      subst hk
      have := hI _ (clause_of_get hg) y (hP a (mem_of_contains hp)) [x] (List.nodup_singleton x)
        (by simpa using ⟨hL R (mem_of_contains hl), hB e (mem_of_contains hb)⟩)
      simp at this
    · simp at h
  | amo0b g =>
    simp only [ruleOK] at h
    split at h
    · next a k R e hg =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hk, hl⟩, hp⟩, hb⟩ := h
      subst hk
      have := hI _ (clause_of_get hg) x (hB a (mem_of_contains hb)) [y] (List.nodup_singleton y)
        (by simpa using ⟨rt_flip_iff.1 (hL R.flip (mem_of_contains hl)), hP e (mem_of_contains hp)⟩)
      simp at this
    · simp at h
  | clash gu gl je =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hje, h⟩ := h
    split at h
    · next a nn R e a₂ k R₂ b₂ hgu hgl =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hnk, hRR⟩, hBb⟩, hHe⟩, hun⟩, ha⟩, ha₂⟩, hPB⟩, hQH⟩ := h
      obtain ⟨cl, hcl, hlo⟩ := Option.bind_eq_some_iff.1 hgl
      obtain ⟨l, hnd, hlen, hl⟩ := lowOf_list hI (clause_of_get hcl) hlo (hB a₂ (mem_of_contains ha₂))
      by_cases hq : ∃ g : Fin n, g.val ∈ (prem S je).Q ∧ I.c g x
      · obtain ⟨g, hg, hgx⟩ := hq
        exact Or.inl ⟨g, subA_mem hQH hg, hgx⟩
      · exfalso
        have he : ∀ z ∈ l, I.rt R x z ∧ I.c e z := by
          intro z hz
          refine ⟨up_rt hI hRR (hl z hz).1, ?_⟩
          rcases hprev je hje x z (under_rt hI hun (hl z hz).1) (fun a' ha' => hB a' (subA_mem hPB ha'))
            (fun a' ha' => by rw [mem_B_single hBb ha']; exact (hl z hz).2) with ⟨g, hg, hgz⟩ | hq'
          · rw [← mem_B_single (c := ⟨#[], #[], (prem S je).H, #[], #[]⟩) hHe hg]; exact hgz
          · exact absurd hq' hq
        have := hI _ (clause_of_get hgu) x (hB a (mem_of_contains ha)) l hnd he
        omega
    · simp at h
  | sib gu gl je jr =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hje, hjr⟩, h⟩ := h
    split at h
    · next a nn R e a₂ k R₂ b₂ hgu hgl =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnn, hk⟩, hRR⟩, hBb⟩, hHe⟩, hune⟩, hunr⟩, hl⟩, ha⟩, ha₂⟩, hPe⟩, hPr⟩, he⟩,
        hBr⟩, hHr⟩, hQe⟩, hQr⟩ := h
      obtain ⟨cl, hcl, hlo⟩ := Option.bind_eq_some_iff.1 hgl
      obtain ⟨z, hRz, hbz⟩ := lowOf_wit hI (clause_of_get hcl) hlo hk (hP a₂ (mem_of_contains ha₂))
      rcases hprev je hje y z (under_rt hI hune hRz) (fun a' ha' => hP a' (subA_mem hPe ha'))
        (fun a' ha' => by rw [mem_B_single hBb ha']; exact hbz) with ⟨g, hg, hgz⟩ | ⟨g, hg, hgy⟩
      · have hez : I.c e z := by
          rw [← mem_B_single (c := ⟨#[], #[], (prem S je).H, #[], #[]⟩) hHe hg]; exact hgz
        have hxz : x = z := amo_eq hI (clause_of_get hgu) hnn (hP a (mem_of_contains ha))
          (hL R (mem_of_contains hl)) (hB e (mem_of_contains he)) (up_rt hI hRR hRz) hez
        subst hxz
        rcases hprev jr hjr y x (under_rt hI hunr hRz) (fun a' ha' => hP a' (subA_mem hPr ha'))
          (fun a' ha' => by
            rcases subAx_mem hBr ha' with h' | h'
            · rw [fin_eq_of_val h']; exact hbz
            · exact hB a' h') with ⟨g', hg', hg'x⟩ | ⟨g', hg', hg'y⟩
        · exact Or.inl ⟨g', subA_mem hHr hg', hg'x⟩
        · exact Or.inr ⟨g', subA_mem hQr hg', hg'y⟩
      · exact Or.inr ⟨g, subA_mem hQe hg, hgy⟩
    · simp at h
  | par gu gl je jr =>
    simp only [ruleOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hje, hjr⟩, h⟩ := h
    split at h
    · next a nn R e a₂ k R₂ b₂ hgu hgl =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnn, hk⟩, hRR⟩, hBb⟩, hHe⟩, hune⟩, hunr⟩, hl⟩, he⟩, hBr⟩, ha⟩, ha₂⟩, hPe⟩, hPr⟩, hQe⟩, hQr⟩, hHr⟩ := h
      obtain ⟨cl, hcl, hlo⟩ := Option.bind_eq_some_iff.1 hgl
      obtain ⟨z, hRz, hbz⟩ := lowOf_wit hI (clause_of_get hcl) hlo hk (hB a₂ (mem_of_contains ha₂))
      rcases hprev je hje x z (under_rt hI hune hRz) (fun a' ha' => hB a' (subA_mem hPe ha'))
        (fun a' ha' => by rw [mem_B_single hBb ha']; exact hbz) with ⟨g, hg, hgz⟩ | ⟨g, hg, hgx⟩
      · have hez : I.c e z := by
          rw [← mem_B_single (c := ⟨#[], #[], (prem S je).H, #[], #[]⟩) hHe hg]; exact hgz
        have hyz : y = z := amo_eq hI (clause_of_get hgu) hnn (hB a (mem_of_contains ha))
          (rt_flip_iff.1 (hL R.flip (mem_of_contains hl))) (hP e (mem_of_contains he))
          (up_rt hI hRR hRz) hez
        subst hyz
        rcases hprev jr hjr x y (under_rt hI hunr hRz) (fun a' ha' => hB a' (subA_mem hPr ha'))
          (fun a' ha' => by
            rcases subAx_mem hBr ha' with h' | h'
            · rw [fin_eq_of_val h']; exact hbz
            · exact hP a' h') with ⟨g', hg', hg'y⟩ | ⟨g', hg', hg'x⟩
        · exact Or.inr ⟨g', subA_mem hHr hg', hg'y⟩
        · exact Or.inl ⟨g', subA_mem hQr hg', hg'x⟩
      · exact Or.inl ⟨g, subA_mem hQe hg, hgx⟩
    · simp at h

/-- **Derivation soundness.** In every model, every clause of an accepted
certificate holds. -/
theorem checkCert_sound (hI : models I O) {S : Array CStep}
    (h : checkCert (mkIxF O (mkIx O)) O.toArray S = true) : ∀ i, i < S.size → (prem S i).Sat I := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hs := List.all_eq_true.1 h i (List.mem_range.2 hi)
    exact ruleOK_sound hI hs (fun j hj => ih j hj (by omega))

end Sound

end ContextCalculus.SRIQ.CB

#print axioms ContextCalculus.SRIQ.CB.ruleOK_sound
#print axioms ContextCalculus.SRIQ.CB.checkCert_sound
