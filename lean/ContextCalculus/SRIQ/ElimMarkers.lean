import ContextCalculus.SRIQ.NormalForm

/-!
# Eliminating body markers by resolution (stage C1e)

The translation turns a number restriction or a universal on the left of
an axiom into a fresh name `x` and a top disjunction `⊤ ⊑ x ⊔ W₁ ⊔ …`
with definers `Wᵢ`; `x` then occurs only in the bodies of gcis
(`x ⊓ C ⊓ … ⊑ A`). Every type of the fast procedure branches on each such
disjunction, so `k` of them give up to `3ᵏ` branches in every context.

A name `x` that occurs in the head of one gci `B ⊑ H` only (every gci with
`x` in its head is that one), in no other clause than gci bodies, and in
neither `B` nor another eliminated head, can be removed: every gci
`B' ⊑ H'` with `x ∈ B'` becomes `B' ∖ {x} ∪ B ⊑ H' ∪ (H ∖ {x})` (the
resolvent with the defining gci) and the defining gci goes away
(`elimO`). The result has the same models up to the interpretation of the
eliminated names (`models_elimO`, `models_of_elimO`), so the same
subsumptions between the other names (`entailsSub_elimO`).

The hint (which names to eliminate, with their defining gcis) is computed
without proof (`elimHint`) and checked (`hintOK`).
-/

namespace ContextCalculus.SRIQ.Elim

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-- For each name, the defining gci `(body, head)` when the name is
eliminated (the head holds the name). -/
abbrev Hint (n : Nat) := Array (Option (List (Fin n) × List (Fin n)))

def defOf (S : Hint n) (x : Fin n) : Option (List (Fin n) × List (Fin n)) := (S[x.val]?).getD none

def inS (S : Hint n) (x : Fin n) : Bool := (defOf S x).isSome

/-- The body of the defining gci. -/
def dBody (S : Hint n) (x : Fin n) : List (Fin n) := ((defOf S x).map (·.1)).getD []

/-- The head of the defining gci without the name itself. -/
def dHead (S : Hint n) (x : Fin n) : List (Fin n) := ((defOf S x).map fun d => d.2.filter (· != x)).getD []

/-- The resolvent of a gci with the defining gcis of its eliminated body names. -/
def resolve (S : Hint n) (B H : List (Fin n)) : List (Fin n) × List (Fin n) :=
  let xs := B.filter (inS S)
  (B.filter (fun a => !inS S a) ++ xs.flatMap (dBody S), H ++ xs.flatMap (dHead S))

def elimClause (S : Hint n) : Clause (Fin n) (Fin m) → List (Clause (Fin n) (Fin m))
  | .gci B H =>
    if H.any (inS S) then []
    else if B.any (inS S) then [.gci (resolve S B H).1 (resolve S B H).2] else [.gci B H]
  | cl => [cl]

/-- **The elimination.** -/
def elimO (S : Hint n) (O : Ontology (Fin n) (Fin m)) : Ontology (Fin n) (Fin m) :=
  O.flatMap (elimClause S)

/-- A clause other than a gci mentions no eliminated name; a gci with an
eliminated head name is that name's defining gci. -/
def clauseOK (S : Hint n) : Clause (Fin n) (Fin m) → Bool
  | .gci B H => H.all fun h => !inS S h || decide (defOf S h = some (B, H))
  | .exRight a _ b => !inS S a && !inS S b
  | .allRight a _ b => !inS S a && !inS S b
  | .atLeast a _ _ b => !inS S a && !inS S b
  | .atMost a _ _ b => !inS S a && !inS S b
  | .chain _ _ => true

/-- The names whose defining gci occurs in the ontology. -/
def foundArr (S : Hint n) (O : Ontology (Fin n) (Fin m)) : Array Bool :=
  O.foldl (fun acc cl => match cl with
    | .gci B H => H.foldl (fun acc h =>
        if decide (defOf S h = some (B, H)) then acc.set! h.val true else acc) acc
    | _ => acc) (Array.replicate n false)

/-- An eliminated name is at least `bound`, its defining gci is in the
ontology (`found`), holds it in the head, and mentions no other
eliminated name. -/
def defOK (found : Array Bool) (bound : Nat) (S : Hint n) (x : Fin n) : Bool :=
  match defOf S x with
  | none => true
  | some (B, H) =>
    decide (bound ≤ x.val) && H.contains x && B.all (fun a => !inS S a) &&
      H.all (fun h => !inS S h || h == x) && found[x.val]?.getD false

/-- **The hint check.** -/
def hintOK (O : Ontology (Fin n) (Fin m)) (bound : Nat) (S : Hint n) : Bool :=
  (List.finRange n).all (defOK (foundArr S O) bound S) && O.all (clauseOK S)

/-! ## The hint (unproved) -/

/-- Names at least `bound` that occur only in gci bodies and in the heads of
copies of one gci, with that gci when it mentions no other candidate. -/
def elimHint (O : Ontology (Fin n) (Fin m)) (bound : Nat) : Hint n := Id.run do
  let mut bad : Array Bool := Array.replicate n false
  let mut dfn : Array (Option (List (Fin n) × List (Fin n))) := Array.replicate n none
  for cl in O do
    match cl with
    | .gci B H =>
      for h in H do
        if B.contains h then bad := bad.set! h.val true
        match dfn[h.val]?.getD none with
        | none => dfn := dfn.set! h.val (some (B, H))
        | some d => if d != (B, H) then bad := bad.set! h.val true
    | .exRight a _ b | .allRight a _ b | .atLeast a _ _ b | .atMost a _ _ b =>
      bad := (bad.set! a.val true).set! b.val true
    | .chain _ _ => pure ()
  let cand : Array Bool := (Array.range n).map fun i =>
    decide (bound ≤ i) && !(bad[i]?.getD true) && (dfn[i]?.getD none).isSome
  let mut out : Hint n := Array.replicate n none
  for i in [0:n] do
    if cand[i]?.getD false then
      match dfn[i]?.getD none with
      | none => pure ()
      | some (B, H) =>
        if B.all (fun a => !(cand[a.val]?.getD false)) &&
            H.all (fun h => h.val == i || !(cand[h.val]?.getD false)) then
          out := out.set! i (some (B, H))
  return out

/-- The elimination when the hint passes the check, else the ontology. -/
def elimChecked (O : Ontology (Fin n) (Fin m)) (bound : Nat) : Ontology (Fin n) (Fin m) :=
  let S := elimHint O bound
  if hintOK O bound S then elimO S O else O

/-! ## Correctness -/

section Proofs

variable {D : Type} {O : Ontology (Fin n) (Fin m)} {bound : Nat} {S : Hint n}

theorem defOK_of (hS : hintOK O bound S = true) (x : Fin n) :
    defOK (foundArr S O) bound S x = true := by
  unfold hintOK at hS
  simp only [Bool.and_eq_true, List.all_eq_true] at hS
  exact hS.1 x (List.mem_finRange x)

theorem clauseOK_of (hS : hintOK O bound S = true) {cl : Clause (Fin n) (Fin m)} (h : cl ∈ O) :
    clauseOK S cl = true := by
  unfold hintOK at hS
  simp only [Bool.and_eq_true, List.all_eq_true] at hS
  exact hS.2 cl h

/-- What a set entry of the found array means. -/
def FoundInv (S : Hint n) (O : Ontology (Fin n) (Fin m)) (acc : Array Bool) : Prop :=
  ∀ x : Fin n, acc[x.val]? = some true → ∃ B H, defOf S x = some (B, H) ∧ Clause.gci B H ∈ O

theorem foundInv_heads {B H : List (Fin n)} (hg : Clause.gci B H ∈ O) :
    ∀ (l : List (Fin n)) (acc : Array Bool), FoundInv S O acc →
      FoundInv S O (l.foldl (fun acc h =>
        if decide (defOf S h = some (B, H)) then acc.set! h.val true else acc) acc)
  | [], acc, h => h
  | y :: l, acc, h => by
    rw [List.foldl_cons]
    refine foundInv_heads hg l _ ?_
    split
    · next hy =>
      intro x hx
      rw [Array.set!, Array.getElem?_setIfInBounds] at hx
      split at hx
      · next hxy =>
        have : x = y := Fin.ext hxy.symm
        subst this
        exact ⟨B, H, of_decide_eq_true hy, hg⟩
      · exact h x hx
    · exact h

theorem foundInv_foldl : ∀ (l : Ontology (Fin n) (Fin m)), (∀ cl ∈ l, cl ∈ O) →
    ∀ acc : Array Bool, FoundInv S O acc →
      FoundInv S O (l.foldl (fun acc cl => match cl with
        | .gci B H => H.foldl (fun acc h =>
            if decide (defOf S h = some (B, H)) then acc.set! h.val true else acc) acc
        | _ => acc) acc)
  | [], _, acc, h => h
  | cl :: l, hl, acc, h => by
    rw [List.foldl_cons]
    refine foundInv_foldl l (fun c hc => hl c (List.mem_cons_of_mem _ hc)) _ ?_
    cases cl with
    | gci B H => exact foundInv_heads (hl _ List.mem_cons_self) H acc h
    | _ => exact h

theorem found_sound {x : Fin n} (h : (foundArr S O)[x.val]?.getD false = true) :
    ∃ B H, defOf S x = some (B, H) ∧ Clause.gci B H ∈ O := by
  have hinv : FoundInv S O (foundArr S O) := foundInv_foldl O (fun _ h => h) _ (fun y hy => by
    simp only [Array.getElem?_replicate] at hy
    split at hy <;> simp at hy)
  apply hinv x
  cases hx : (foundArr S O)[x.val]? with
  | none => rw [hx] at h; simp at h
  | some b => rw [hx] at h; simp at h; rw [h]

theorem def_facts (hS : hintOK O bound S = true) {x : Fin n} {B H : List (Fin n)}
    (hd : defOf S x = some (B, H)) :
    bound ≤ x.val ∧ x ∈ H ∧ (∀ a ∈ B, inS S a = false) ∧ (∀ h ∈ H, inS S h = true → h = x) ∧
      Clause.gci B H ∈ O := by
  have h := defOK_of hS x
  unfold defOK at h
  rw [hd] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.all_eq_true,
    Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h5' : Clause.gci B H ∈ O := by
    obtain ⟨B', H', hd', hg⟩ := found_sound h5
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl⟩ := hd'
    exact hg
  refine ⟨h1, h2, h3, fun y hy hyS => ?_, h5'⟩
  rcases h4 y hy with h | h
  · rw [h] at hyS; exact absurd hyS (by simp)
  · exact h

theorem inS_iff {x : Fin n} : inS S x = true ↔ ∃ B H, defOf S x = some (B, H) := by
  unfold inS
  cases h : defOf S x with
  | none => simp
  | some p => simp only [Option.isSome_some, Option.some.injEq, true_iff]; exact ⟨p.1, p.2, rfl⟩

theorem not_inS_of_lt (hS : hintOK O bound S = true) {x : Fin n} (hx : x.val < bound) :
    inS S x = false := by
  cases h : inS S x with
  | false => rfl
  | true =>
    obtain ⟨B, H, hd⟩ := inS_iff.1 h
    have := (def_facts hS hd).1
    omega

theorem dBody_eq {x : Fin n} {B H : List (Fin n)} (hd : defOf S x = some (B, H)) : dBody S x = B := by
  simp [dBody, hd]

theorem mem_dHead {x : Fin n} {B H : List (Fin n)} (hd : defOf S x = some (B, H)) {h : Fin n} :
    h ∈ dHead S x ↔ h ∈ H ∧ h ≠ x := by
  simp [dHead, hd]

/-- **Every model of the ontology models the elimination.** -/
theorem models_elimO (hS : hintOK O bound S = true) {I : Interp D (Fin n) (Fin m)} (hI : models I O) :
    models I (elimO S O) := by
  classical
  intro cl hcl
  obtain ⟨c0, hc0, hcl⟩ := List.mem_flatMap.1 hcl
  cases c0 with
  | gci B H =>
    simp only [elimClause] at hcl
    split at hcl
    · simp at hcl
    · split at hcl
      · rw [List.mem_singleton.1 hcl]
        intro z hz
        by_cases hex : ∃ x ∈ B.filter (inS S), ∃ h ∈ dHead S x, I.c h z
        · obtain ⟨x, hx, h, hh, hhz⟩ := hex
          exact ⟨h, List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hh⟩), hhz⟩
        · push Not at hex
          have hB : ∀ a ∈ B, I.c a z := by
            intro a ha
            cases haS : inS S a with
            | false =>
              exact hz a (List.mem_append_left _ (List.mem_filter.2 ⟨ha, by simp [haS]⟩))
            | true =>
              obtain ⟨Bx, Hx, hd⟩ := inS_iff.1 haS
              have hxf : a ∈ B.filter (inS S) := List.mem_filter.2 ⟨ha, haS⟩
              obtain ⟨-, -, -, -, hg⟩ := def_facts hS hd
              obtain ⟨h, hh, hhz⟩ := hI _ hg z fun b hb => hz b (List.mem_append_right _
                (List.mem_flatMap.2 ⟨a, hxf, by rw [dBody_eq hd]; exact hb⟩))
              by_cases hha : h = a
              · rw [← hha]; exact hhz
              · exact absurd hhz (hex a hxf h ((mem_dHead hd).2 ⟨hh, hha⟩))
          obtain ⟨b, hb, hbz⟩ := hI _ hc0 z hB
          exact ⟨b, List.mem_append_left _ hb, hbz⟩
      · rw [List.mem_singleton.1 hcl]; exact hI _ hc0
  | exRight a R b => simp only [elimClause, List.mem_singleton] at hcl; rw [hcl]; exact hI _ hc0
  | allRight a R b => simp only [elimClause, List.mem_singleton] at hcl; rw [hcl]; exact hI _ hc0
  | atLeast a k R b => simp only [elimClause, List.mem_singleton] at hcl; rw [hcl]; exact hI _ hc0
  | atMost a k R b => simp only [elimClause, List.mem_singleton] at hcl; rw [hcl]; exact hI _ hc0
  | chain body R => simp only [elimClause, List.mem_singleton] at hcl; rw [hcl]; exact hI _ hc0

/-- The interpretation of the eliminated names: a name holds where the body
of its defining gci holds and no other head name does. -/
def ext (S : Hint n) (I : Interp D (Fin n) (Fin m)) : Interp D (Fin n) (Fin m) where
  c x z := if inS S x = true then (∀ a ∈ dBody S x, I.c a z) ∧ ∀ h ∈ dHead S x, ¬ I.c h z
    else I.c x z
  r := I.r

theorem ext_c_of {I : Interp D (Fin n) (Fin m)} {x : Fin n} (hx : inS S x = false) (z : D) :
    (ext S I).c x z ↔ I.c x z := by
  simp [ext, hx]

theorem ext_rt (I : Interp D (Fin n) (Fin m)) (R : RoleT (Fin m)) : (ext S I).rt R = I.rt R := by
  cases R <;> rfl

theorem ext_path (I : Interp D (Fin n) (Fin m)) :
    ∀ body : List (RoleT (Fin m)), (ext S I).path body = I.path body
  | [] => rfl
  | R :: Rs => by
    funext x z
    simp only [Interp.path, ext_rt, ext_path I Rs]

theorem mem_elimO {cl c0 : Clause (Fin n) (Fin m)} (hc0 : c0 ∈ O) (h : cl ∈ elimClause S c0) :
    cl ∈ elimO S O :=
  List.mem_flatMap.2 ⟨c0, hc0, h⟩

/-- **A model of the elimination gives a model of the ontology** that agrees
on every other name and on the roles. -/
theorem models_ext (hS : hintOK O bound S = true) {I : Interp D (Fin n) (Fin m)}
    (hI : models I (elimO S O)) : models (ext S I) O := by
  classical
  intro cl hcl
  have hok := clauseOK_of hS hcl
  cases cl with
  | gci B H =>
    simp only [clauseOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
    by_cases hH : ∃ x ∈ H, inS S x = true
    · obtain ⟨x, hx, hxS⟩ := hH
      have hd : defOf S x = some (B, H) := by
        rcases hok x hx with h | h
        · rw [h] at hxS; exact absurd hxS (by simp)
        · exact h
      obtain ⟨-, -, hB, hHS, -⟩ := def_facts hS hd
      intro z hz
      have hzB : ∀ a ∈ B, I.c a z := fun a ha => (ext_c_of (hB a ha) z).1 (hz a ha)
      by_cases hex : ∃ h ∈ dHead S x, I.c h z
      · obtain ⟨h, hh, hhz⟩ := hex
        obtain ⟨hh1, hh2⟩ := (mem_dHead hd).1 hh
        have hhS : inS S h = false := by
          cases hc : inS S h with
          | false => rfl
          | true => exact absurd (hHS h hh1 hc) hh2
        exact ⟨h, hh1, (ext_c_of hhS z).2 hhz⟩
      · push Not at hex
        refine ⟨x, hx, ?_⟩
        simp only [ext, hxS, if_true]
        exact ⟨by rw [dBody_eq hd]; exact hzB, hex⟩
    · push Not at hH
      have hHf : ∀ x ∈ H, inS S x = false := fun x hx => by simpa using hH x hx
      have hany : H.any (inS S) = false := by
        rw [List.any_eq_false]; intro x hx; simp [hHf x hx]
      intro z hz
      by_cases hBS : B.any (inS S) = true
      · have hres : Clause.gci (resolve S B H).1 (resolve S B H).2 ∈ elimO S O :=
          mem_elimO hcl (by simp [elimClause, hany, hBS])
        have hB' : ∀ a ∈ (resolve S B H).1, I.c a z := by
          intro a ha
          simp only [resolve, List.mem_append, List.mem_filter, List.mem_flatMap] at ha
          rcases ha with ⟨ha, haS⟩ | ⟨x, ⟨hx, hxS⟩, hax⟩
          · have : inS S a = false := by simpa using haS
            exact (ext_c_of this z).1 (hz a ha)
          · have := hz x hx
            simp only [ext, hxS, if_true] at this
            exact this.1 a hax
        obtain ⟨b, hb, hbz⟩ := hI _ hres z hB'
        simp only [resolve, List.mem_append, List.mem_flatMap] at hb
        rcases hb with hb | ⟨x, hx, hbx⟩
        · exact ⟨b, hb, (ext_c_of (hHf b hb) z).2 hbz⟩
        · obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
          have := hz x hx1
          simp only [ext, hx2, if_true] at this
          exact absurd hbz (this.2 b hbx)
      · have hBf : ∀ a ∈ B, inS S a = false := fun a ha => by
          cases hc : inS S a with
          | false => rfl
          | true => exact absurd (List.any_eq_true.2 ⟨a, ha, hc⟩) hBS
        have hmem : Clause.gci B H ∈ elimO S O :=
          mem_elimO hcl (by simp [elimClause, hany, hBS])
        obtain ⟨b, hb, hbz⟩ := hI _ hmem z fun a ha => (ext_c_of (hBf a ha) z).1 (hz a ha)
        exact ⟨b, hb, (ext_c_of (hHf b hb) z).2 hbz⟩
  | exRight a R b =>
    simp only [clauseOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    have h := hI _ (mem_elimO (cl := .exRight a R b) hcl (by simp [elimClause]))
    intro x hx
    obtain ⟨y, hy1, hy2⟩ := h x ((ext_c_of hok.1 x).1 hx)
    exact ⟨y, by rw [ext_rt]; exact hy1, (ext_c_of hok.2 y).2 hy2⟩
  | allRight a R b =>
    simp only [clauseOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    have h := hI _ (mem_elimO (cl := .allRight a R b) hcl (by simp [elimClause]))
    intro x hx y hy
    rw [ext_rt] at hy
    exact (ext_c_of hok.2 y).2 (h x ((ext_c_of hok.1 x).1 hx) y hy)
  | atLeast a k R b =>
    simp only [clauseOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    have h := hI _ (mem_elimO (cl := .atLeast a k R b) hcl (by simp [elimClause]))
    intro x hx
    obtain ⟨l, hl1, hl2, hl3⟩ := h x ((ext_c_of hok.1 x).1 hx)
    exact ⟨l, hl1, hl2, fun y hy => ⟨by rw [ext_rt]; exact (hl3 y hy).1,
      (ext_c_of hok.2 y).2 (hl3 y hy).2⟩⟩
  | atMost a k R b =>
    simp only [clauseOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
    have h := hI _ (mem_elimO (cl := .atMost a k R b) hcl (by simp [elimClause]))
    intro x hx l hl hs
    exact h x ((ext_c_of hok.1 x).1 hx) l hl fun y hy =>
      ⟨by rw [← ext_rt (S := S)]; exact (hs y hy).1, (ext_c_of hok.2 y).1 (hs y hy).2⟩
  | chain body R =>
    have h := hI _ (mem_elimO (cl := .chain body R) hcl (by simp [elimClause]))
    intro x y hxy
    rw [ext_path] at hxy
    rw [ext_rt]
    exact h x y hxy

/-- **Subsumptions between names below the bound are unchanged.** -/
theorem entailsSub_elimO (hS : hintOK O bound S = true) {a b : Fin n} (ha : a.val < bound)
    (hb : b.val < bound) : EntailsSub (elimO S O) a b ↔ EntailsSub O a b := by
  constructor
  · intro h D _ I hI x hx
    exact h D I (models_elimO hS hI) x hx
  · intro h D _ I hI x hx
    have := h D (ext S I) (models_ext hS hI) x ((ext_c_of (not_inS_of_lt hS ha) x).2 hx)
    exact (ext_c_of (not_inS_of_lt hS hb) x).1 this

theorem isALCHIQ_elimO {S : Hint n} (h : IsALCHIQ O) : IsALCHIQ (elimO S O) := by
  intro body R hcl
  obtain ⟨c0, hc0, hcl⟩ := List.mem_flatMap.1 hcl
  cases c0 with
  | gci B H =>
    simp only [elimClause] at hcl
    split at hcl
    · simp at hcl
    · split at hcl <;> simp at hcl
  | chain body' R' =>
    simp only [elimClause, List.mem_singleton, Clause.chain.injEq] at hcl
    obtain ⟨rfl, rfl⟩ := hcl
    exact h _ _ hc0
  | _ => simp [elimClause] at hcl

theorem entailsSub_elimChecked {a b : Fin n} (ha : a.val < bound) (hb : b.val < bound) :
    EntailsSub (elimChecked O bound) a b ↔ EntailsSub O a b := by
  unfold elimChecked
  dsimp only
  split
  · next h => exact entailsSub_elimO h ha hb
  · exact Iff.rfl

theorem isALCHIQ_elimChecked (h : IsALCHIQ O) : IsALCHIQ (elimChecked O bound) := by
  unfold elimChecked
  dsimp only
  split
  · exact isALCHIQ_elimO h
  · exact h

end Proofs

end ContextCalculus.SRIQ.Elim

#print axioms ContextCalculus.SRIQ.Elim.entailsSub_elimChecked
#print axioms ContextCalculus.SRIQ.Elim.isALCHIQ_elimChecked
