import ContextCalculus.OWLFrontend.SRITranslate
import ContextCalculus.OWLFrontend.ALCTranslateCorrect

/-!
# Correctness of the OWL SRI translation

`translateSRI_named`, `translateSRI_isSome` and `translateSRI_correct`
(`docs/V1.6.3-HT-PLAN.md`).

The proof follows the ALC route (`ALCTranslateCorrect`) step by step and
reuses its lemmas about indices and the EL lemmas about the maps and meaning
tables.

- (⇒, OWL entailment gives clause entailment) a model `J` of the clauses
  restricts to an OWL interpretation `restrict F J` on the same domain with
  the same role relations. By induction on a class expression `E`, a
  negative occurrence with result `X` gives `ext E ⊆ J X` and a positive one
  `J X ⊆ ext E` (`transExpr_restrict`). Every axiom then holds in
  `restrict F J`.
- (⇐) a model `I` of `O` extends to a clause interpretation `extend I F`:
  index `k` stands for `F.b.cdefs[k]`, role index `k` for its property IRI.
  Every emitted clause holds (`transExpr_extend`, `transAxiom_extend`).
- Role terms: the role term `R` of an object-property expression `r` has
  the relation of `r` on both sides (`restrict_prop`, `extend_prop`), and a
  list of role terms composes like the OWL chain (`chain_iff_path`).
- Every index of every emitted clause has an entry in the meaning tables
  (the invariant `WF`), so the conversion to `Fin` indices drops no clause.
-/

namespace ContextCalculus.OWLFrontend.SRIT

open ContextCalculus.OWL

/-! ## Role terms -/

/-- The role index of a role term. -/
def rIx : RT → Nat
  | .pos k => k
  | .inv k => k

@[simp] theorem rIx_flip (R : RT) : rIx R.flip = rIx R := by cases R <;> rfl

@[simp] theorem rIx_mkRT (r : ObjProp) (k : Nat) : rIx (mkRT r k) = k := by
  cases r <;> rfl

/-- `R` is the role term of `r` under the property map of `b`. -/
def RoleOK (b : EL.St) (r : ObjProp) (R : RT) : Prop :=
  ∃ k, b.rmap[EL.propIRI r]? = some k ∧ R = mkRT r k

/-- `R` is the role term of `r` under the meaning table of `b`. -/
def RoleDef (b : EL.St) (r : ObjProp) (R : RT) : Prop :=
  ∃ k, b.rdefs[k]? = some [EL.propIRI r] ∧ R = mkRT r k

theorem RoleOK.mono {b b' : EL.St} {r : ObjProp} {R : RT} (h : RoleOK b r R)
    (hle : EL.Le b b') : RoleOK b' r R :=
  let ⟨k, hk, hR⟩ := h; ⟨k, hle.rmap _ _ hk, hR⟩

theorem RoleDef.mono {b b' : EL.St} {r : ObjProp} {R : RT} (h : RoleDef b r R)
    (hle : EL.Le b b') : RoleDef b' r R :=
  let ⟨k, hk, hR⟩ := h; ⟨k, hle.rdefs _ _ hk, hR⟩

theorem RoleOK.def {b : EL.St} {r : ObjProp} {R : RT} (h : RoleOK b r R)
    (hb : EL.WF b) : RoleDef b r R :=
  let ⟨k, hk, hR⟩ := h; ⟨k, hb.rmap _ _ hk, hR⟩

theorem RoleOK.in {b : EL.St} {r : ObjProp} {R : RT} (h : RoleOK b r R)
    (hb : EL.WF b) : ALC.RIn b (rIx R) := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨_, by rw [rIx_mkRT]; exact hb.rmap _ _ hk⟩

theorem forall₂_mono {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → List.Forall₂ Q l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h₁ h₂ => .cons (h _ _ h₁) (forall₂_mono h h₂)

theorem forall₂_left {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, P a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons h₁ h₂, a, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, List.mem_cons_self, h₁⟩
      · obtain ⟨b, hb, hab⟩ := forall₂_left h₂ a h
        exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem forall₂_right {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, P a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons h₁ h₂, b, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, List.mem_cons_self, h₁⟩
      · obtain ⟨a, ha, hab⟩ := forall₂_right h₂ b h
        exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- A list of role terms whose members have the relations of a list of
object-property expressions composes to the OWL chain. -/
theorem chain_iff_path {D : Type} (I : OWL.Interp D) {CN : Type} (J : SRI.Interp D CN Nat) :
    ∀ {rs : List ObjProp} {Rs : List RT},
      List.Forall₂ (fun r R => ∀ x y, I.prop r x y ↔ J.rt R x y) rs Rs →
      ∀ x y, I.chain rs x y ↔ J.path Rs x y
  | _, _, .nil, x, y => by simp [Interp.chain, SRI.Interp.path]
  | _, _, .cons h₁ h₂, x, y => by
      simp only [Interp.chain, SRI.Interp.path, h₁, chain_iff_path I J h₂]

theorem path_single {D CN Role : Type} (J : SRI.Interp D CN Role) (R : SRI.RoleT Role)
    (x y : D) : J.path [R] x y ↔ J.rt R x y := by
  simp [SRI.Interp.path]

theorem path_pair {D CN Role : Type} (J : SRI.Interp D CN Role) (R S : SRI.RoleT Role)
    (x z : D) : J.path [R, S] x z ↔ ∃ y, J.rt R x y ∧ J.rt S y z := by
  simp [SRI.Interp.path]

/-! ## The extension order and the invariant -/

/-- `s'` extends `s`. -/
structure Le (s s' : St) : Prop where
  b : EL.Le s.b s'.b
  out : ∀ c : SC, c ∈ s.out → c ∈ s'.out

theorem Le.rfl {s : St} : Le s s := ⟨EL.Le.rfl, fun _ h => h⟩

theorem Le.trans {s t u : St} (h₁ : Le s t) (h₂ : Le t u) : Le s u :=
  ⟨h₁.b.trans h₂.b, fun c h => h₂.out c (h₁.out c h)⟩

/-- Concept indices of a clause. -/
def cIdx : SC → List Nat
  | .gci body head => body ++ head
  | .exRight a _ c => [a, c]
  | .allRight a _ c => [a, c]
  | .chain _ _ => []

/-- Role indices of a clause. -/
def rIdx : SC → List Nat
  | .gci _ _ => []
  | .exRight _ R _ => [rIx R]
  | .allRight _ R _ => [rIx R]
  | .chain body S => body.map rIx ++ [rIx S]

open ALC (CIn RIn CIn.mono RIn.mono)

/-- Every index of the clause has a meaning. -/
def Valid (b : EL.St) (c : SC) : Prop :=
  (∀ k ∈ cIdx c, CIn b k) ∧ ∀ k ∈ rIdx c, RIn b k

theorem Valid.mono {b b' : EL.St} {c : SC} (h : Valid b c) (hle : EL.Le b b') : Valid b' c :=
  ⟨fun k hk => (h.1 k hk).mono hle, fun k hk => (h.2 k hk).mono hle⟩

theorem valid_gci {b : EL.St} {body head : List Nat} (h₁ : ∀ k ∈ body, CIn b k)
    (h₂ : ∀ k ∈ head, CIn b k) : Valid b (.gci body head) := by
  refine ⟨fun k hk => ?_, fun k hk => by simp [rIdx] at hk⟩
  simp only [cIdx, List.mem_append] at hk
  rcases hk with hk | hk
  · exact h₁ k hk
  · exact h₂ k hk

theorem valid_exRight {b : EL.St} {a c : Nat} {R : RT} (ha : CIn b a) (hr : RIn b (rIx R))
    (hc : CIn b c) : Valid b (.exRight a R c) :=
  ⟨fun k hk => by simp [cIdx] at hk; rcases hk with rfl | rfl <;> assumption,
   fun k hk => by simp [rIdx] at hk; subst hk; exact hr⟩

theorem valid_allRight {b : EL.St} {a c : Nat} {R : RT} (ha : CIn b a) (hr : RIn b (rIx R))
    (hc : CIn b c) : Valid b (.allRight a R c) :=
  ⟨fun k hk => by simp [cIdx] at hk; rcases hk with rfl | rfl <;> assumption,
   fun k hk => by simp [rIdx] at hk; subst hk; exact hr⟩

theorem valid_chain {b : EL.St} {body : List RT} {S : RT} (h₁ : ∀ R ∈ body, RIn b (rIx R))
    (h₂ : RIn b (rIx S)) : Valid b (.chain body S) := by
  refine ⟨fun k hk => by simp [cIdx] at hk, fun k hk => ?_⟩
  simp only [rIdx, List.mem_append, List.mem_map, List.mem_singleton] at hk
  rcases hk with ⟨R, hR, rfl⟩ | rfl
  · exact h₁ R hR
  · exact h₂

/-- The EL invariant, the meaning of `top` and `bottom`, and every emitted
index has a meaning. -/
structure WF (s : St) : Prop where
  b : EL.WF s.b
  top : s.b.cdefs[s.b.top]? = some .thing
  bottom : s.b.cdefs[s.b.bottom]? = some .nothing
  valid : ∀ c ∈ s.out, Valid s.b c

theorem WF.of_b {s s' : St} (hs : WF s) (hle : EL.Le s.b s'.b) (hwf : EL.WF s'.b)
    (hout : s'.out = s.out) : WF s' :=
  ⟨hwf, by rw [hle.top]; exact hle.cdefs _ _ hs.top,
   by rw [hle.bottom]; exact hle.cdefs _ _ hs.bottom,
   fun c hc => (hs.valid c (hout ▸ hc)).mono hle⟩

theorem WF.top_in {s : St} (hs : WF s) : CIn s.b s.b.top := ⟨_, hs.top⟩
theorem WF.bottom_in {s : St} (hs : WF s) : CIn s.b s.b.bottom := ⟨_, hs.bottom⟩

/-! ## Primitive steps -/

theorem internC_le (a : IRI) (s : St) : Le s (internC a s).2 :=
  ⟨EL.internC_le a s.b, fun _ h => h⟩

theorem internC_wf {a : IRI} {s : St} (hs : WF s) : WF (internC a s).2 :=
  hs.of_b (EL.internC_le a s.b) (EL.internC_wf hs.b) rfl

theorem internC_cmap (a : IRI) (s : St) :
    (internC a s).2.b.cmap[a]? = some (internC a s).1 :=
  EL.internC_cmap a s.b

theorem internC_cdefs {a : IRI} {s : St} (hs : WF s) :
    (internC a s).2.b.cdefs[(internC a s).1]? = some (.cls a) :=
  EL.internC_cdefs hs.b

theorem internR_le (r : IRI) (s : St) : Le s (internR r s).2 :=
  ⟨EL.internR_le r s.b, fun _ h => h⟩

theorem internR_wf {r : IRI} {s : St} (hs : WF s) : WF (internR r s).2 :=
  hs.of_b (EL.internR_le r s.b) (EL.internR_wf hs.b) rfl

theorem internR_rmap (r : IRI) (s : St) :
    (internR r s).2.b.rmap[r]? = some (internR r s).1 :=
  EL.internR_rmap r s.b

theorem internR_rdefs {r : IRI} {s : St} (hs : WF s) :
    (internR r s).2.b.rdefs[(internR r s).1]? = some [r] :=
  EL.internR_rdefs hs.b

theorem freshC_le (e : ClassExpr) (s : St) : Le s (freshC e s).2 :=
  ⟨EL.freshC_le e s.b, fun _ h => h⟩

theorem freshC_wf {e : ClassExpr} {s : St} (hs : WF s) : WF (freshC e s).2 :=
  hs.of_b (EL.freshC_le e s.b) (EL.freshC_wf hs.b) rfl

theorem freshC_cdefs (e : ClassExpr) (s : St) :
    (freshC e s).2.b.cdefs[(freshC e s).1]? = some e :=
  EL.freshC_cdefs e s.b

theorem freshC_in (e : ClassExpr) (s : St) : CIn (freshC e s).2.b (freshC e s).1 :=
  ⟨_, freshC_cdefs e s⟩

theorem emit_le (c : SC) (s : St) : Le s (emit c s) :=
  ⟨EL.Le.rfl, fun _ h => List.mem_cons_of_mem _ h⟩

theorem emit_wf {c : SC} {s : St} (hs : WF s) (hc : Valid s.b c) : WF (emit c s) :=
  ⟨hs.b, hs.top, hs.bottom, fun d hd => by
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hc
    · exact hs.valid d hd⟩

theorem mem_emit (c : SC) (s : St) : c ∈ (emit c s).out := List.mem_cons_self

theorem emitEach_b (f : Nat → SC) : ∀ (qs : List (ClassExpr × Nat)) (s : St),
    (emitEach f qs s).b = s.b
  | [], _ => rfl
  | q :: qs, s => by simp only [emitEach]; rw [emitEach_b f qs]; rfl

theorem mem_emitEach (f : Nat → SC) : ∀ (qs : List (ClassExpr × Nat)) (s : St) (c : SC),
    c ∈ (emitEach f qs s).out ↔ c ∈ s.out ∨ ∃ q ∈ qs, c = f q.2
  | [], s, c => by simp [emitEach]
  | q :: qs, s, c => by
      simp only [emitEach]
      rw [mem_emitEach f qs]
      simp only [emit, List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h

theorem emitEach_le (f : Nat → SC) (qs : List (ClassExpr × Nat)) (s : St) :
    Le s (emitEach f qs s) :=
  ⟨by rw [emitEach_b]; exact EL.Le.rfl,
   fun c hc => (mem_emitEach f qs s c).2 (Or.inl hc)⟩

theorem emitEach_wf {f : Nat → SC} {qs : List (ClassExpr × Nat)} {s : St} (hs : WF s)
    (hq : ∀ q ∈ qs, Valid s.b (f q.2)) : WF (emitEach f qs s) := by
  have hb := emitEach_b f qs s
  refine ⟨hb ▸ hs.b, hb ▸ hs.top, hb ▸ hs.bottom, fun c hc => ?_⟩
  rw [hb]
  rcases (mem_emitEach f qs s c).1 hc with hc | ⟨q, hq', rfl⟩
  · exact hs.valid c hc
  · exact hq q hq'


theorem roleT_le (r : ObjProp) (s : St) : Le s (roleT r s).2 := internR_le _ s

theorem roleT_wf {r : ObjProp} {s : St} (hs : WF s) : WF (roleT r s).2 := internR_wf hs

theorem roleT_ok (r : ObjProp) (s : St) : RoleOK (roleT r s).2.b r (roleT r s).1 :=
  ⟨_, internR_rmap (EL.propIRI r) s, rfl⟩

theorem roleT_in {r : ObjProp} {s : St} (hs : WF s) : RIn (roleT r s).2.b (rIx (roleT r s).1) :=
  (roleT_ok r s).in (roleT_wf hs).b

theorem roleTs_le : ∀ (rs : List ObjProp) (s : St) acc, Le s (roleTs rs s acc).2
  | [], _, _ => Le.rfl
  | r :: rs, s, _ => (roleT_le r s).trans (roleTs_le rs _ _)

theorem roleTs_wf : ∀ (rs : List ObjProp) (s : St) acc, WF s → WF (roleTs rs s acc).2
  | [], _, _, hs => hs
  | _ :: rs, _, _, hs => roleTs_wf rs _ _ (roleT_wf hs)

theorem roleTs_ok : ∀ (rs : List ObjProp) (s : St) acc, ∃ L,
    (roleTs rs s acc).1 = acc.reverse ++ L ∧ List.Forall₂ (RoleOK (roleTs rs s acc).2.b) rs L
  | [], s, acc => ⟨[], by simp [roleTs], .nil⟩
  | r :: rs, s, acc => by
      obtain ⟨L, hL, hF⟩ := roleTs_ok rs (roleT r s).2 ((roleT r s).1 :: acc)
      refine ⟨(roleT r s).1 :: L, ?_, .cons ?_ hF⟩
      · simp only [roleTs]; rw [hL]; simp
      · exact (roleT_ok r s).mono (roleTs_le rs _ _).b

/-- The role terms of a list, with their facts. -/
theorem roleTs_ok' (rs : List ObjProp) (s : St) :
    List.Forall₂ (RoleOK (roleTs rs s []).2.b) rs (roleTs rs s []).1 := by
  obtain ⟨L, hL, hF⟩ := roleTs_ok rs s []
  rw [hL]; simpa using hF

theorem roleTs_in {rs : List ObjProp} {s : St} (hs : WF s) :
    ∀ R ∈ (roleTs rs s []).1, RIn (roleTs rs s []).2.b (rIx R) := by
  intro R hR
  obtain ⟨r, _, hok⟩ := forall₂_right (roleTs_ok' rs s) R hR
  exact hok.in (roleTs_wf rs s [] hs).b
/-! ## Monotonicity and the invariant through the transformation -/

theorem transList_fst : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc,
    (transList cs p s acc).1.map Prod.fst = acc.reverse.map Prod.fst ++ cs
  | [], p, s, acc => by simp [transList]
  | c :: cs, p, s, acc => by
      simp only [transList]
      rw [transList_fst cs]
      simp

theorem transList_mem_fst {cs : List ClassExpr} {p : Bool} {s : St}
    {q : ClassExpr × Nat} (hq : q ∈ (transList cs p s []).1) : q.1 ∈ cs := by
  have := transList_fst cs p s []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at this
  exact this ▸ List.mem_map_of_mem hq

theorem transList_fst_mem {cs : List ClassExpr} {p : Bool} {s : St} {c : ClassExpr}
    (hc : c ∈ cs) : ∃ q ∈ (transList cs p s []).1, q.1 = c := by
  have := transList_fst cs p s []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at this
  rw [← this] at hc
  exact List.mem_map.1 hc

mutual

theorem transExpr_le : ∀ (E : ClassExpr) (p : Bool) (s : St), Le s (transExpr E p s).2
  | .cls a, _, s => by simp only [transExpr]; exact internC_le a s
  | .thing, _, s => by simp only [transExpr]; exact Le.rfl
  | .nothing, _, s => by simp only [transExpr]; exact Le.rfl
  | .and [], _, s => by simp only [transExpr]; exact Le.rfl
  | .or [], _, s => by simp only [transExpr]; exact Le.rfl
  | .and (c :: cs), false, s => by
      simp only [transExpr]
      exact (transList_le _ false s []).trans ((freshC_le _ _).trans (emit_le _ _))
  | .and (c :: cs), true, s => by
      simp only [transExpr]
      exact (transList_le _ true s []).trans ((freshC_le _ _).trans (emitEach_le _ _ _))
  | .or (c :: cs), false, s => by
      simp only [transExpr]
      exact (transList_le _ false s []).trans ((freshC_le _ _).trans (emitEach_le _ _ _))
  | .or (c :: cs), true, s => by
      simp only [transExpr]
      exact (transList_le _ true s []).trans ((freshC_le _ _).trans (emit_le _ _))
  | .not c, false, s => by
      simp only [transExpr]
      exact (transExpr_le c true s).trans ((freshC_le _ _).trans (emit_le _ _))
  | .not c, true, s => by
      simp only [transExpr]
      exact (transExpr_le c false s).trans ((freshC_le _ _).trans (emit_le _ _))
  | .some r c, false, s => by
      simp only [transExpr]
      exact (roleT_le r s).trans ((transExpr_le c false _).trans
        ((freshC_le _ _).trans (emit_le _ _)))
  | .some r c, true, s => by
      simp only [transExpr]
      exact (roleT_le r s).trans ((transExpr_le c true _).trans
        ((freshC_le _ _).trans (emit_le _ _)))
  | .all r c, false, s => by
      simp only [transExpr]
      exact (roleT_le r s).trans ((transExpr_le c false _).trans
        ((freshC_le _ _).trans ((freshC_le _ _).trans ((freshC_le _ _).trans
        ((emit_le _ _).trans ((emit_le _ _).trans (emit_le _ _)))))))
  | .all r c, true, s => by
      simp only [transExpr]
      exact (roleT_le r s).trans ((transExpr_le c true _).trans
        ((freshC_le _ _).trans (emit_le _ _)))

theorem transList_le : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc,
    Le s (transList cs p s acc).2
  | [], _, s, acc => by simp only [transList]; exact Le.rfl
  | c :: cs, p, s, acc => by
      simp only [transList]
      exact (transExpr_le c p s).trans (transList_le cs p _ _)

end

mutual

theorem transExpr_wf : ∀ (E : ClassExpr) (p : Bool) (s : St), WF s →
    WF (transExpr E p s).2 ∧ CIn (transExpr E p s).2.b (transExpr E p s).1
  | .cls a, _, s, hs => by
      simp only [transExpr]; exact ⟨internC_wf hs, _, internC_cdefs hs⟩
  | .thing, _, s, hs => by simp only [transExpr]; exact ⟨hs, hs.top_in⟩
  | .nothing, _, s, hs => by simp only [transExpr]; exact ⟨hs, hs.bottom_in⟩
  | .and [], _, s, hs => by simp only [transExpr]; exact ⟨hs, hs.top_in⟩
  | .or [], _, s, hs => by simp only [transExpr]; exact ⟨hs, hs.bottom_in⟩
  | .and (c :: cs), false, s, hs => by
      simp only [transExpr]
      have hL := transList_wf (c :: cs) false s [] hs (by simp)
      have hle := (freshC_le (.and (c :: cs)) (transList (c :: cs) false s []).2).b
      refine ⟨emit_wf (freshC_wf hL.1) (valid_gci ?_ ?_), freshC_in _ _⟩
      · intro k hk
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
        exact (hL.2 q hq).mono hle
      · intro k hk; simp at hk; subst hk; exact freshC_in _ _
  | .and (c :: cs), true, s, hs => by
      simp only [transExpr]
      have hL := transList_wf (c :: cs) true s [] hs (by simp)
      have hle := (freshC_le (.and (c :: cs)) (transList (c :: cs) true s []).2).b
      refine ⟨emitEach_wf (freshC_wf hL.1) (fun q hq => valid_gci ?_ ?_), ?_⟩
      · intro k hk; simp at hk; subst hk; exact freshC_in _ _
      · intro k hk; simp at hk; subst hk; exact (hL.2 q hq).mono hle
      · rw [emitEach_b]; exact freshC_in _ _
  | .or (c :: cs), false, s, hs => by
      simp only [transExpr]
      have hL := transList_wf (c :: cs) false s [] hs (by simp)
      have hle := (freshC_le (.or (c :: cs)) (transList (c :: cs) false s []).2).b
      refine ⟨emitEach_wf (freshC_wf hL.1) (fun q hq => valid_gci ?_ ?_), ?_⟩
      · intro k hk; simp at hk; subst hk; exact (hL.2 q hq).mono hle
      · intro k hk; simp at hk; subst hk; exact freshC_in _ _
      · rw [emitEach_b]; exact freshC_in _ _
  | .or (c :: cs), true, s, hs => by
      simp only [transExpr]
      have hL := transList_wf (c :: cs) true s [] hs (by simp)
      have hle := (freshC_le (.or (c :: cs)) (transList (c :: cs) true s []).2).b
      refine ⟨emit_wf (freshC_wf hL.1) (valid_gci ?_ ?_), freshC_in _ _⟩
      · intro k hk; simp at hk; subst hk; exact freshC_in _ _
      · intro k hk
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
        exact (hL.2 q hq).mono hle
  | .not c, false, s, hs => by
      simp only [transExpr]
      have ih := transExpr_wf c true s hs
      have hle := (freshC_le (.not c) (transExpr c true s).2).b
      refine ⟨emit_wf (freshC_wf ih.1) (valid_gci (by simp) ?_), freshC_in _ _⟩
      intro k hk; simp at hk
      rcases hk with rfl | rfl
      · exact freshC_in _ _
      · exact ih.2.mono hle
  | .not c, true, s, hs => by
      simp only [transExpr]
      have ih := transExpr_wf c false s hs
      have hle := (freshC_le (.not c) (transExpr c false s).2).b
      refine ⟨emit_wf (freshC_wf ih.1) (valid_gci ?_ (by simp)), freshC_in _ _⟩
      intro k hk; simp at hk
      rcases hk with rfl | rfl
      · exact freshC_in _ _
      · exact ih.2.mono hle
  | .some r c, false, s, hs => by
      simp only [transExpr]
      have ha := roleT_in (r := r) hs
      have ih := transExpr_wf c false _ (roleT_wf (r := r) hs)
      have hle₁ := (transExpr_le c false (roleT r s).2).b
      have hle₂ := (freshC_le (.some r c) (transExpr c false (roleT r s).2).2).b
      refine ⟨emit_wf (freshC_wf ih.1) (valid_allRight (ih.2.mono hle₂) ?_ (freshC_in _ _)),
        freshC_in _ _⟩
      rw [rIx_flip]; exact (ha.mono hle₁).mono hle₂
  | .some r c, true, s, hs => by
      simp only [transExpr]
      have ha := roleT_in (r := r) hs
      have ih := transExpr_wf c true _ (roleT_wf (r := r) hs)
      have hle₁ := (transExpr_le c true (roleT r s).2).b
      have hle₂ := (freshC_le (.some r c) (transExpr c true (roleT r s).2).2).b
      exact ⟨emit_wf (freshC_wf ih.1) (valid_exRight (freshC_in _ _)
        ((ha.mono hle₁).mono hle₂) (ih.2.mono hle₂)), freshC_in _ _⟩
  | .all r c, false, s, hs => by
      simp only [transExpr]
      have ha := roleT_in (r := r) hs
      have ih := transExpr_wf c false _ (roleT_wf (r := r) hs)
      have hle₁ := (transExpr_le c false (roleT r s).2).b
      have hx := freshC_wf (e := .all r c) ih.1
      have hw := freshC_wf (e := .some r (.not c)) hx
      have hn := freshC_wf (e := .not c) hw
      have l₂ := (freshC_le (.all r c) (transExpr c false (roleT r s).2).2).b
      have l₃ := (freshC_le (.some r (.not c)) (freshC (.all r c)
        (transExpr c false (roleT r s).2).2).2).b
      have l₄ := (freshC_le (.not c) (freshC (.some r (.not c)) (freshC (.all r c)
        (transExpr c false (roleT r s).2).2).2).2).b
      have hX := ((freshC_in (.all r c) _).mono l₃).mono l₄
      have hW := (freshC_in (.some r (.not c)) _).mono l₄
      have hN := freshC_in (.not c) (freshC (.some r (.not c)) (freshC (.all r c)
        (transExpr c false (roleT r s).2).2).2).2
      have hA := (((ha.mono hle₁).mono l₂).mono l₃).mono l₄
      have hZ := ((ih.2.mono l₂).mono l₃).mono l₄
      refine ⟨emit_wf (emit_wf (emit_wf hn ?_) ?_) ?_, ?_⟩
      · refine valid_gci (by simp) ?_
        intro k hk; simp at hk; rcases hk with rfl | rfl
        · exact hX
        · exact hW
      · exact valid_exRight hW hA hN
      · refine valid_gci ?_ (by simp)
        intro k hk; simp at hk; rcases hk with rfl | rfl
        · exact hN
        · exact hZ
      · exact hX
  | .all r c, true, s, hs => by
      simp only [transExpr]
      have ha := roleT_in (r := r) hs
      have ih := transExpr_wf c true _ (roleT_wf (r := r) hs)
      have hle₁ := (transExpr_le c true (roleT r s).2).b
      have hle₂ := (freshC_le (.all r c) (transExpr c true (roleT r s).2).2).b
      exact ⟨emit_wf (freshC_wf ih.1) (valid_allRight (freshC_in _ _)
        ((ha.mono hle₁).mono hle₂) (ih.2.mono hle₂)), freshC_in _ _⟩

theorem transList_wf : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc, WF s →
    (∀ q ∈ acc, CIn s.b q.2) →
    WF (transList cs p s acc).2 ∧ ∀ q ∈ (transList cs p s acc).1, CIn (transList cs p s acc).2.b q.2
  | [], _, s, acc, hs, hacc => by
      simp only [transList]
      exact ⟨hs, fun q hq => hacc q (List.mem_reverse.1 hq)⟩
  | c :: cs, p, s, acc, hs, hacc => by
      simp only [transList]
      have ih := transExpr_wf c p s hs
      have hle := (transExpr_le c p s).b
      refine transList_wf cs p _ _ ih.1 ?_
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ih.2
      · exact (hacc q hq).mono hle

end

open ALC (ext_not ext_all ext_and_nil ext_or_nil)

theorem isALCI_and {cs : List ClassExpr} :
    (ClassExpr.and cs).isALCI = true ↔ ∀ c ∈ cs, c.isALCI = true := by
  rw [ClassExpr.isALCI]; simp
theorem isALCI_or {cs : List ClassExpr} :
    (ClassExpr.or cs).isALCI = true ↔ ∀ c ∈ cs, c.isALCI = true := by
  rw [ClassExpr.isALCI]; simp
theorem isALCI_not {c : ClassExpr} : (ClassExpr.not c).isALCI = c.isALCI := by
  rw [ClassExpr.isALCI]
theorem isALCI_some {r : ObjProp} {c : ClassExpr} :
    (ClassExpr.some r c).isALCI = true ↔ c.isALCI = true := by
  rw [ClassExpr.isALCI]
theorem isALCI_all {r : ObjProp} {c : ClassExpr} :
    (ClassExpr.all r c).isALCI = true ↔ c.isALCI = true := by
  rw [ClassExpr.isALCI]

/-! ## (⇒) A model of the clauses restricts to an OWL interpretation -/

/-- The OWL interpretation read off a clause interpretation through the
final maps. IRIs without an index get `bottom` and role `0`; they do not
occur. -/
def restrict (F : St) {D : Type} (J : SRI.Interp D Nat Nat) : OWL.Interp D where
  cls a := J.c (F.b.cmap[a]?.getD F.b.bottom)
  role r := J.r (F.b.rmap[r]?.getD 0)

theorem restrict_cls {F : St} {D : Type} {J : SRI.Interp D Nat Nat}
    {a : IRI} {k : Nat} (h : F.b.cmap[a]? = some k) (x : D) :
    (restrict F J).cls a x ↔ J.c k x := by
  simp [restrict, h]

/-- The role term of `r` has the relation of `r`. -/
theorem restrict_prop {F : St} {D : Type} {J : SRI.Interp D Nat Nat}
    {r : ObjProp} {R : RT} (h : RoleOK F.b r R) (x y : D) :
    (restrict F J).prop r x y ↔ J.rt R x y := by
  obtain ⟨k, hk, rfl⟩ := h
  cases r with
  | named r =>
      simp only [EL.propIRI] at hk
      simp [Interp.prop, restrict, mkRT, SRI.Interp.rt, hk]
  | inv r =>
      simp only [EL.propIRI] at hk
      simp [Interp.prop, restrict, mkRT, SRI.Interp.rt, hk]

section Restrict

variable (F : St) {D : Type} (J : SRI.Interp D Nat Nat)
  (hJ : ∀ c ∈ F.out, SRI.satClause J c)
  (hT : ∀ x, J.c F.b.top x) (hB : ∀ x, ¬ J.c F.b.bottom x)

include hJ hT hB

-- `transList_restrict` reaches the section hypotheses only through the mutual
-- call to `transExpr_restrict`, which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

theorem transExpr_restrict : ∀ (E : ClassExpr) (p : Bool) (s : St),
    Le (transExpr E p s).2 F → E.isALCI = true →
      EL.Covers (restrict F J) J.c p E (transExpr E p s).1
  | .cls a, p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      have hk := hle.b.cmap _ _ (internC_cmap a s)
      cases p <;> intro x <;> simp only [EL.ext_cls, restrict_cls hk] <;> exact id
  | .thing, p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      cases p
      · intro x _; rw [← hle.b.top]; exact hT x
      · intro x _; simp [EL.ext_thing]
  | .nothing, p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      cases p
      · intro x h; simp [EL.ext_nothing] at h
      · intro x h; rw [← hle.b.bottom] at h; exact absurd h (hB x)
  | .and [], p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      cases p
      · intro x _; rw [← hle.b.top]; exact hT x
      · intro x _; simp [ext_and_nil]
  | .or [], p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      cases p
      · intro x h; simp [ext_or_nil] at h
      · intro x h; rw [← hle.b.bottom] at h; exact absurd h (hB x)
  | .and (c :: cs), false, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₁ := (freshC_le _ _).trans ((emit_le _ _).trans hle)
      have ih := transList_restrict (c :: cs) false s [] hle₁ (isALCI_and.1 hA) (by simp)
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      rw [Interp.ext_and] at hx
      obtain ⟨b, hb, hbx⟩ := hcl x (by
        intro k hk
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
        exact ih q hq x (hx q.1 (transList_mem_fst hq)))
      simp only [List.mem_singleton] at hb
      subst hb; exact hbx
  | .and (c :: cs), true, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₁ := (freshC_le _ _).trans ((emitEach_le _ _ _).trans hle)
      have ih := transList_restrict (c :: cs) true s [] hle₁ (isALCI_and.1 hA) (by simp)
      intro x hx
      rw [Interp.ext_and]
      intro d hd
      obtain ⟨q, hq, rfl⟩ := transList_fst_mem (p := true) (s := s) hd
      have hcl := hJ _ (hle.out _ ((mem_emitEach _ _ _ _).2 (Or.inr ⟨q, hq, rfl⟩)))
      obtain ⟨b, hb, hbx⟩ := hcl x (by simpa using hx)
      simp only [List.mem_singleton] at hb
      subst hb
      exact ih q hq x hbx
  | .or (c :: cs), false, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₁ := (freshC_le _ _).trans ((emitEach_le _ _ _).trans hle)
      have ih := transList_restrict (c :: cs) false s [] hle₁ (isALCI_or.1 hA) (by simp)
      intro x hx
      rw [Interp.ext_or] at hx
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨q, hq, rfl⟩ := transList_fst_mem (p := false) (s := s) hd
      have hcl := hJ _ (hle.out _ ((mem_emitEach _ _ _ _).2 (Or.inr ⟨q, hq, rfl⟩)))
      obtain ⟨b, hb, hbx⟩ := hcl x (by simpa using ih q hq x hdx)
      simp only [List.mem_singleton] at hb
      subst hb; exact hbx
  | .or (c :: cs), true, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₁ := (freshC_le _ _).trans ((emit_le _ _).trans hle)
      have ih := transList_restrict (c :: cs) true s [] hle₁ (isALCI_or.1 hA) (by simp)
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      obtain ⟨b, hb, hbx⟩ := hcl x (by simpa using hx)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb
      rw [Interp.ext_or]
      exact ⟨q.1, transList_mem_fst hq, ih q hq x hbx⟩
  | .not c, false, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      rw [isALCI_not] at hA
      have hle₁ := (freshC_le _ _).trans ((emit_le _ _).trans hle)
      have ih := transExpr_restrict c true s hle₁ hA
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      rw [ext_not] at hx
      obtain ⟨b, hb, hbx⟩ := hcl x (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hbx
      · exact absurd (ih x hbx) hx
  | .not c, true, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      rw [isALCI_not] at hA
      have hle₁ := (freshC_le _ _).trans ((emit_le _ _).trans hle)
      have ih := transExpr_restrict c false s hle₁ hA
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      rw [ext_not]
      intro hc
      obtain ⟨b, hb, _⟩ := hcl x (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hx
        · exact ih x hc)
      simp at hb
  | .some r c, false, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_some.1 hA
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c false _).trans hle₂
      have hrk := (roleT_ok r s).mono hle₁.b
      have ih := transExpr_restrict c false _ hle₂ hc
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      rw [EL.ext_some] at hx
      obtain ⟨y, hxy, hy⟩ := hx
      exact hcl y (ih y hy) x ((SRI.Interp.rt_flip _ _ _ _).2 ((restrict_prop hrk x y).1 hxy))
  | .some r c, true, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_some.1 hA
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := (roleT_ok r s).mono hle₁.b
      have ih := transExpr_restrict c true _ hle₂ hc
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      obtain ⟨y, hxy, hy⟩ := hcl x hx
      rw [EL.ext_some]
      exact ⟨y, (restrict_prop hrk x y).2 hxy, ih y hy⟩
  | .all r c, false, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_all.1 hA
      have hle₆ := (emit_le _ _).trans hle
      have hle₅ := (emit_le _ _).trans hle₆
      have hle₂ := (freshC_le _ _).trans ((freshC_le _ _).trans ((freshC_le _ _).trans
        ((emit_le _ _).trans hle₅)))
      have hle₁ := (transExpr_le c false _).trans hle₂
      have hrk := (roleT_ok r s).mono hle₁.b
      have ih := transExpr_restrict c false _ hle₂ hc
      have hcl₃ := hJ _ (hle.out _ (mem_emit _ _))
      have hcl₂ := hJ _ (hle₆.out _ (mem_emit _ _))
      have hcl₁ := hJ _ (hle₅.out _ (mem_emit _ _))
      intro x hx
      rw [ext_all] at hx
      obtain ⟨b, hb, hbx⟩ := hcl₁ x (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hbx
      · obtain ⟨y, hxy, hny⟩ := hcl₂ x hbx
        have hcy := hx y ((restrict_prop hrk x y).2 hxy)
        obtain ⟨b', hb', _⟩ := hcl₃ y (by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · exact hny
          · exact ih y hcy)
        simp at hb'
  | .all r c, true, s, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_all.1 hA
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := (roleT_ok r s).mono hle₁.b
      have ih := transExpr_restrict c true _ hle₂ hc
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      rw [ext_all]
      intro y hxy
      exact ih y (hcl x hx y ((restrict_prop hrk x y).1 hxy))

theorem transList_restrict : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc,
    Le (transList cs p s acc).2 F → (∀ c ∈ cs, c.isALCI = true) →
    (∀ q ∈ acc, EL.Covers (restrict F J) J.c p q.1 q.2) →
    ∀ q ∈ (transList cs p s acc).1, EL.Covers (restrict F J) J.c p q.1 q.2
  | [], _, s, acc, _, _, hacc => by
      simp only [transList]; intro q hq; exact hacc q (List.mem_reverse.1 hq)
  | c :: cs, p, s, acc, hle, hA, hacc => by
      simp only [transList] at hle ⊢
      have hle₁ := (transList_le cs p _ _).trans hle
      have ih := transExpr_restrict c p s hle₁ (hA c List.mem_cons_self)
      refine transList_restrict cs p _ _ hle (fun d hd => hA d (List.mem_cons_of_mem _ hd)) ?_
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ih
      · exact hacc q hq

end

end Restrict

/-! ## (⇐) A model of the ontology extends to a model of the clauses -/

/-- The clause interpretation of a model `I`: index `k` stands for the class
expression `F.b.cdefs[k]`, role index `k` for the composition of
`F.b.rdefs[k].reverse` (a single property IRI here). -/
def extend {D : Type} (I : OWL.Interp D) (F : St) : SRI.Interp D Nat Nat where
  c k x := I.ext (F.b.cdefs[k]?.getD .nothing) x
  r k x y := I.chain ((F.b.rdefs[k]?.getD []).reverse.map ObjProp.named) x y

section Extend

variable {D : Type} (I : OWL.Interp D) (F : St)

theorem extend_c {k : Nat} {e : ClassExpr} (h : F.b.cdefs[k]? = some e) (x : D) :
    (extend I F).c k x ↔ I.ext e x := by
  simp [extend, h]

theorem extend_role {k : Nat} {r : IRI} (h : F.b.rdefs[k]? = some [r]) (x y : D) :
    (extend I F).r k x y ↔ I.role r x y := by
  simp only [extend, h, Option.getD_some, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.map_cons, List.map_nil]
  exact EL.chain_single I r x y

/-- The role term of `r` has the relation of `r`. -/
theorem extend_prop {r : ObjProp} {R : RT} (h : RoleDef F.b r R) (x y : D) :
    (extend I F).rt R x y ↔ I.prop r x y := by
  obtain ⟨k, hk, rfl⟩ := h
  cases r with
  | named r =>
      simp only [EL.propIRI] at hk
      simp only [mkRT, SRI.Interp.rt, Interp.prop]
      exact extend_role I F hk x y
  | inv r =>
      simp only [EL.propIRI] at hk
      simp only [mkRT, SRI.Interp.rt, Interp.prop]
      exact extend_role I F hk y x

/-- Every clause emitted so far holds in `extend I F`. -/
def Good (s : St) : Prop := ∀ c ∈ s.out, SRI.satClause (extend I F) c

theorem good_emit {s : St} {c : SC} (hs : Good I F s)
    (hc : SRI.satClause (extend I F) c) : Good I F (emit c s) := by
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact hc
  · exact hs d hd

theorem good_emitEach {f : Nat → SC} {qs : List (ClassExpr × Nat)} {s : St} (hs : Good I F s)
    (hq : ∀ q ∈ qs, SRI.satClause (extend I F) (f q.2)) : Good I F (emitEach f qs s) := by
  intro c hc
  rcases (mem_emitEach f qs s c).1 hc with hc | ⟨q, hq', rfl⟩
  · exact hs c hc
  · exact hq q hq'

/-- The index of `q` stands for its expression. -/
def Exact (q : ClassExpr × Nat) : Prop := ∀ x, (extend I F).c q.2 x ↔ I.ext q.1 x

theorem extend_top {s : St} (hs : WF s) (hle : Le s F) (x : D) :
    (extend I F).c s.b.top x := by
  rw [extend_c I F (hle.b.cdefs _ _ hs.top), EL.ext_thing]; trivial

theorem extend_bottom {s : St} (hs : WF s) (hle : Le s F) (x : D) :
    ¬ (extend I F).c s.b.bottom x := by
  rw [extend_c I F (hle.b.cdefs _ _ hs.bottom), EL.ext_nothing]; exact id

mutual

theorem transExpr_extend : ∀ (E : ClassExpr) (p : Bool) (s : St), WF s →
    Le (transExpr E p s).2 F → E.isALCI = true →
      (Good I F s → Good I F (transExpr E p s).2) ∧
      ∀ x, (extend I F).c (transExpr E p s).1 x ↔ I.ext E x
  | .cls a, p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      exact ⟨id, extend_c I F (hle.b.cdefs _ _ (internC_cdefs hs))⟩
  | .thing, p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      exact ⟨id, fun x => by simp [extend_top I F hs hle x, EL.ext_thing]⟩
  | .nothing, p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      exact ⟨id, fun x => by simp [extend_bottom I F hs hle x, EL.ext_nothing]⟩
  | .and [], p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      exact ⟨id, fun x => by simp [extend_top I F hs hle x, ext_and_nil]⟩
  | .or [], p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      exact ⟨id, fun x => by simp [extend_bottom I F hs hle x, ext_or_nil]⟩
  | .and (c :: cs), false, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transList_extend (c :: cs) false s [] hs hle₁ (isALCI_and.1 hA)
      have hq := ih.2 (by simp)
      have hX := extend_c I F (hle₂.b.cdefs _ _ (freshC_cdefs (.and (c :: cs)) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro x hall
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hX, Interp.ext_and]
      intro d hd
      obtain ⟨q, hq', rfl⟩ := transList_fst_mem (p := false) (s := s) hd
      exact (hq q hq' x).1 (hall q.2 (List.mem_map_of_mem hq'))
  | .and (c :: cs), true, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₂ := (emitEach_le _ _ _).trans hle
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transList_extend (c :: cs) true s [] hs hle₁ (isALCI_and.1 hA)
      have hq := ih.2 (by simp)
      have hX := extend_c I F (hle₂.b.cdefs _ _ (freshC_cdefs (.and (c :: cs)) _))
      refine ⟨fun hg => good_emitEach I F (ih.1 hg) ?_, hX⟩
      intro q hq' x hx
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      have hx' := (hX x).1 (hx _ (List.mem_singleton_self _))
      rw [Interp.ext_and] at hx'
      exact (hq q hq' x).2 (hx' q.1 (transList_mem_fst hq'))
  | .or (c :: cs), false, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₂ := (emitEach_le _ _ _).trans hle
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transList_extend (c :: cs) false s [] hs hle₁ (isALCI_or.1 hA)
      have hq := ih.2 (by simp)
      have hX := extend_c I F (hle₂.b.cdefs _ _ (freshC_cdefs (.or (c :: cs)) _))
      refine ⟨fun hg => good_emitEach I F (ih.1 hg) ?_, hX⟩
      intro q hq' x hx
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hX, Interp.ext_or]
      exact ⟨q.1, transList_mem_fst hq', (hq q hq' x).1 (hx _ (List.mem_singleton_self _))⟩
  | .or (c :: cs), true, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transList_extend (c :: cs) true s [] hs hle₁ (isALCI_or.1 hA)
      have hq := ih.2 (by simp)
      have hX := extend_c I F (hle₂.b.cdefs _ _ (freshC_cdefs (.or (c :: cs)) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro x hx
      have hx' := (hX x).1 (hx _ (List.mem_singleton_self _))
      rw [Interp.ext_or] at hx'
      obtain ⟨d, hd, hdx⟩ := hx'
      obtain ⟨q, hq', rfl⟩ := transList_fst_mem (p := true) (s := s) hd
      exact ⟨q.2, List.mem_map_of_mem hq', (hq q hq' x).2 hdx⟩
  | .not c, false, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      rw [isALCI_not] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transExpr_extend c true s hs hle₁ hA
      have hX := extend_c I F (hle₂.b.cdefs _ _ (freshC_cdefs (.not c) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro x _
      by_cases h : I.ext c x
      · exact ⟨_, by simp, (ih.2 x).2 h⟩
      · exact ⟨_, by simp, (hX x).2 ((ext_not I c x).2 h)⟩
  | .not c, true, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      rw [isALCI_not] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transExpr_extend c false s hs hle₁ hA
      have hX := extend_c I F (hle₂.b.cdefs _ _ (freshC_cdefs (.not c) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro x hx
      have h₁ := (hX x).1 (hx _ (by simp))
      have h₂ := (ih.2 x).1 (hx _ (by simp))
      exact absurd h₂ ((ext_not I c x).1 h₁)
  | .some r c, false, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_some.1 hA
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c false _).trans hle₂
      have hs₁ := roleT_wf (r := r) hs
      have hrk := extend_prop I F (((roleT_ok r s).def (roleT_wf hs).b).mono hle₁.b)
      have ih := transExpr_extend c false _ hs₁ hle₂ hc
      have hX := extend_c I F (hle₃.b.cdefs _ _ (freshC_cdefs (.some r c) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro y hy x hyx
      rw [hX, EL.ext_some]
      exact ⟨y, (hrk x y).1 ((SRI.Interp.rt_flip _ _ _ _).1 hyx), (ih.2 y).1 hy⟩
  | .some r c, true, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_some.1 hA
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hs₁ := roleT_wf (r := r) hs
      have hrk := extend_prop I F (((roleT_ok r s).def (roleT_wf hs).b).mono hle₁.b)
      have ih := transExpr_extend c true _ hs₁ hle₂ hc
      have hX := extend_c I F (hle₃.b.cdefs _ _ (freshC_cdefs (.some r c) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro x hx
      rw [hX, EL.ext_some] at hx
      obtain ⟨y, hxy, hy⟩ := hx
      exact ⟨y, (hrk x y).2 hxy, (ih.2 y).2 hy⟩
  | .all r c, false, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_all.1 hA
      have hle₆ := (emit_le _ _).trans hle
      have hle₅ := (emit_le _ _).trans hle₆
      have hle₄ := (emit_le _ _).trans hle₅
      have hle₃ := (freshC_le _ _).trans hle₄
      have hle₂' := (freshC_le _ _).trans hle₃
      have hle₂ := (freshC_le _ _).trans hle₂'
      have hle₁ := (transExpr_le c false _).trans hle₂
      have hs₁ := roleT_wf (r := r) hs
      have hrk := extend_prop I F (((roleT_ok r s).def (roleT_wf hs).b).mono hle₁.b)
      have ih := transExpr_extend c false _ hs₁ hle₂ hc
      have hX := extend_c I F (hle₂'.b.cdefs _ _ (freshC_cdefs (.all r c) _))
      have hW := extend_c I F (hle₃.b.cdefs _ _ (freshC_cdefs (.some r (.not c)) _))
      have hN := extend_c I F (hle₄.b.cdefs _ _ (freshC_cdefs (.not c) _))
      refine ⟨fun hg => good_emit I F (good_emit I F (good_emit I F (ih.1 hg) ?_) ?_) ?_, hX⟩
      · intro x _
        by_cases h : I.ext (.all r c) x
        · exact ⟨_, by simp, (hX x).2 h⟩
        · refine ⟨_, by simp, (hW x).2 ?_⟩
          rw [ext_all] at h
          push Not at h
          obtain ⟨y, hxy, hy⟩ := h
          rw [EL.ext_some]
          exact ⟨y, hxy, (ext_not I c y).2 hy⟩
      · intro x hx
        rw [hW, EL.ext_some] at hx
        obtain ⟨y, hxy, hy⟩ := hx
        exact ⟨y, (hrk x y).2 hxy, (hN y).2 hy⟩
      · intro x hx
        have h₁ := (hN x).1 (hx _ (by simp))
        have h₂ := (ih.2 x).1 (hx _ (by simp))
        exact absurd h₂ ((ext_not I c x).1 h₁)
  | .all r c, true, s, hs, hle, hA => by
      simp only [transExpr] at hle ⊢
      have hc := isALCI_all.1 hA
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hs₁ := roleT_wf (r := r) hs
      have hrk := extend_prop I F (((roleT_ok r s).def (roleT_wf hs).b).mono hle₁.b)
      have ih := transExpr_extend c true _ hs₁ hle₂ hc
      have hX := extend_c I F (hle₃.b.cdefs _ _ (freshC_cdefs (.all r c) _))
      refine ⟨fun hg => good_emit I F (ih.1 hg) ?_, hX⟩
      intro x hx y hxy
      rw [hX, ext_all] at hx
      exact (ih.2 y).2 (hx y ((hrk x y).1 hxy))

theorem transList_extend : ∀ (cs : List ClassExpr) (p : Bool) (s : St) acc, WF s →
    Le (transList cs p s acc).2 F → (∀ c ∈ cs, c.isALCI = true) →
      (Good I F s → Good I F (transList cs p s acc).2) ∧
      ((∀ q ∈ acc, Exact I F q) → ∀ q ∈ (transList cs p s acc).1, Exact I F q)
  | [], _, s, acc, _, _, _ => by
      simp only [transList]
      exact ⟨id, fun h q hq => h q (List.mem_reverse.1 hq)⟩
  | c :: cs, p, s, acc, hs, hle, hA => by
      simp only [transList] at hle ⊢
      have hle₁ := (transList_le cs p _ _).trans hle
      have ih := transExpr_extend c p s hs hle₁ (hA c List.mem_cons_self)
      have ih' := transList_extend cs p _ ((c, (transExpr c p s).1) :: acc)
        (transExpr_wf c p s hs).1 hle (fun d hd => hA d (List.mem_cons_of_mem _ hd))
      refine ⟨fun hg => ih'.1 (ih.1 hg), fun hacc => ih'.2 ?_⟩
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ih.2
      · exact hacc q hq

end

end Extend

/-! ## Axiom-level helpers -/

theorem mem_emitEquiv (negs poss : List (ClassExpr × Nat)) (out : List SC) (c : SC) :
    c ∈ emitEquiv negs poss out ↔
      c ∈ out ∨ ∃ n ∈ negs, ∃ p ∈ poss, n.2 ≠ p.2 ∧ c = .gci [n.2] [p.2] := by
  unfold emitEquiv
  refine EL.mem_foldl _ (fun n c => ∃ p ∈ poss, n.2 ≠ p.2 ∧ c = .gci [n.2] [p.2])
    (fun o n c => ?_) negs out c
  refine (EL.mem_foldl _ (fun p c => n.2 ≠ p.2 ∧ c = .gci [n.2] [p.2])
    (fun o p c => ?_) poss o c)
  split <;> simp_all [or_comm]

theorem mem_emitDisjoint :
    ∀ (L : List (ClassExpr × Nat)) (o : List SC) (c : SC),
      c ∈ emitDisjoint L o ↔ c ∈ o ∨ ∃ m n, List.Sublist [m, n] L ∧ c = .gci [m.2, n.2] []
  | [], o, c => by simp [emitDisjoint]
  | h :: t, o, c => by
      rw [emitDisjoint, mem_emitDisjoint t,
        EL.mem_foldl _ (fun m c => c = .gci [h.2, m.2] []) (fun o m c => by simp [or_comm]) t o c]
      simp only [EL.pair_sublist_cons]
      constructor
      · rintro ((h₁ | ⟨m, hm, rfl⟩) | ⟨m, n, hmn, rfl⟩)
        · exact Or.inl h₁
        · exact Or.inr ⟨h, m, Or.inl ⟨rfl, hm⟩, rfl⟩
        · exact Or.inr ⟨m, n, Or.inr hmn, rfl⟩
      · rintro (h₁ | ⟨m, n, (⟨rfl, hn⟩ | hmn), rfl⟩)
        · exact Or.inl (Or.inl h₁)
        · exact Or.inl (Or.inr ⟨n, hn, rfl⟩)
        · exact Or.inr ⟨m, n, hmn, rfl⟩

theorem mem_emitRoleEquiv (Rs : List RT) (out : List SC) (c : SC) :
    c ∈ emitRoleEquiv Rs out ↔
      c ∈ out ∨ ∃ R ∈ Rs, ∃ S ∈ Rs, R ≠ S ∧ c = .chain [R] S := by
  unfold emitRoleEquiv
  refine EL.mem_foldl _ (fun R c => ∃ S ∈ Rs, R ≠ S ∧ c = .chain [R] S)
    (fun o R c => ?_) Rs out c
  refine (EL.mem_foldl _ (fun S c => R ≠ S ∧ c = .chain [R] S) (fun o S c => ?_) Rs o c)
  split <;> simp_all [or_comm]

theorem setOut_le {s : St} {o : List SC} (h : ∀ c ∈ s.out, c ∈ o) :
    Le s { s with out := o } :=
  ⟨EL.Le.rfl, h⟩

theorem setOut_wf {s : St} {o : List SC} (hs : WF s) (h : ∀ c ∈ o, Valid s.b c) :
    WF { s with out := o } :=
  ⟨hs.b, hs.top, hs.bottom, h⟩

theorem transAxiom_le (s : St) (ax : Axiom) : Le s (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom]
      exact (transExpr_le c false s).trans ((transExpr_le d true _).trans (emit_le _ _))
  | equivalentClasses cs =>
      simp only [transAxiom]
      exact (transList_le cs false s []).trans ((transList_le cs true _ []).trans
        (setOut_le fun c hc => (mem_emitEquiv _ _ _ c).2 (Or.inl hc)))
  | disjointClasses cs =>
      simp only [transAxiom]
      exact (transList_le cs false s []).trans
        (setOut_le fun c hc => (mem_emitDisjoint _ _ c).2 (Or.inl hc))
  | domain r c =>
      simp only [transAxiom]
      exact (roleT_le r s).trans ((transExpr_le c true _).trans (emit_le _ _))
  | range r c =>
      simp only [transAxiom]
      exact (roleT_le r s).trans ((transExpr_le c true _).trans (emit_le _ _))
  | subObjectPropertyOf rs r =>
      simp only [transAxiom]
      exact (roleTs_le rs s []).trans ((roleT_le r _).trans (emit_le _ _))
  | equivalentObjectProperties rs =>
      simp only [transAxiom]
      exact (roleTs_le rs s []).trans
        (setOut_le fun c hc => (mem_emitRoleEquiv _ _ c).2 (Or.inl hc))
  | inverseObjectProperties r r' =>
      simp only [transAxiom]
      exact (roleT_le r s).trans ((roleT_le r' _).trans ((emit_le _ _).trans (emit_le _ _)))
  | transitive r | symmetric r =>
      simp only [transAxiom]
      exact (roleT_le r s).trans (emit_le _ _)
  | declareClass _ | declareObjectProperty _ =>
      simp only [transAxiom]; exact Le.rfl

theorem transAxiom_wf {s : St} (hs : WF s) (ax : Axiom) : WF (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom]
      have hn := transExpr_wf c false s hs
      have hp := transExpr_wf d true _ hn.1
      exact emit_wf hp.1 (valid_gci (by
        intro k hk; simp at hk; subst hk; exact hn.2.mono (transExpr_le d true _).b)
        (by intro k hk; simp at hk; subst hk; exact hp.2))
  | equivalentClasses cs =>
      simp only [transAxiom]
      have hn := transList_wf cs false s [] hs (by simp)
      have hp := transList_wf cs true _ [] hn.1 (by simp)
      have hle := (transList_le cs true (transList cs false s []).2 []).b
      refine setOut_wf hp.1 fun c hc => ?_
      rcases (mem_emitEquiv _ _ _ c).1 hc with hc | ⟨qn, hqn, qp, hqp, _, rfl⟩
      · exact hp.1.valid c hc
      · exact valid_gci (by intro k hk; simp at hk; subst hk; exact (hn.2 qn hqn).mono hle)
          (by intro k hk; simp at hk; subst hk; exact hp.2 qp hqp)
  | disjointClasses cs =>
      simp only [transAxiom]
      have hn := transList_wf cs false s [] hs (by simp)
      refine setOut_wf hn.1 fun c hc => ?_
      rcases (mem_emitDisjoint _ _ c).1 hc with hc | ⟨m, n, hmn, rfl⟩
      · exact hn.1.valid c hc
      · refine valid_gci ?_ (by simp)
        intro k hk; simp at hk
        rcases hk with rfl | rfl
        · exact hn.2 m (hmn.subset (by simp))
        · exact hn.2 n (hmn.subset (by simp))
  | domain r c =>
      simp only [transAxiom]
      have ha := roleT_in (r := r) hs
      have hp := transExpr_wf c true _ (roleT_wf (r := r) hs)
      exact emit_wf hp.1 (valid_allRight hp.1.top_in
        (by rw [rIx_flip]; exact ha.mono (transExpr_le c true _).b) hp.2)
  | range r c =>
      simp only [transAxiom]
      have ha := roleT_in (r := r) hs
      have hp := transExpr_wf c true _ (roleT_wf (r := r) hs)
      exact emit_wf hp.1 (valid_allRight hp.1.top_in (ha.mono (transExpr_le c true _).b) hp.2)
  | subObjectPropertyOf rs r =>
      simp only [transAxiom]
      have hl := roleTs_wf rs s [] hs
      have hL := roleTs_in (rs := rs) hs
      have hle := (roleT_le r (roleTs rs s []).2).b
      exact emit_wf (roleT_wf hl) (valid_chain (fun R hR => (hL R hR).mono hle) (roleT_in hl))
  | equivalentObjectProperties rs =>
      simp only [transAxiom]
      have hl := roleTs_wf rs s [] hs
      have hL := roleTs_in (rs := rs) hs
      refine setOut_wf hl fun c hc => ?_
      rcases (mem_emitRoleEquiv _ _ c).1 hc with hc | ⟨R, hR, S, hS, _, rfl⟩
      · exact hl.valid c hc
      · exact valid_chain (by simpa using hL R hR) (hL S hS)
  | inverseObjectProperties r r' =>
      simp only [transAxiom]
      have h₁ := roleT_wf (r := r) hs
      have h₂ := roleT_wf (r := r') h₁
      have hA := (roleT_in (r := r) hs).mono (roleT_le r' (roleT r s).2).b
      have hB := roleT_in (r := r') h₁
      refine emit_wf (emit_wf h₂ (valid_chain (by simpa using hA) (by simpa using hB))) ?_
      exact valid_chain (by simpa using hB) (by simpa using hA)
  | transitive r =>
      simp only [transAxiom]
      have hA := roleT_in (r := r) hs
      exact emit_wf (roleT_wf hs) (valid_chain (by simpa using hA) hA)
  | symmetric r =>
      simp only [transAxiom]
      have hA := roleT_in (r := r) hs
      exact emit_wf (roleT_wf hs) (valid_chain (by simpa using hA) (by simpa using hA))
  | declareClass _ | declareObjectProperty _ =>
      simp only [transAxiom]; exact hs

/-! ## (⇒) at the axiom level -/

section RestrictAxiom

variable (F : St) {D : Type} (J : SRI.Interp D Nat Nat)
  (hJ : ∀ c ∈ F.out, SRI.satClause J c)
  (hT : ∀ x, J.c F.b.top x) (hB : ∀ x, ¬ J.c F.b.bottom x)

include hJ hT hB

theorem transList_restrict' {cs : List ClassExpr} {p : Bool} {s : St}
    (hle : Le (transList cs p s []).2 F) (hA : ∀ c ∈ cs, c.isALCI = true) :
    ∀ q ∈ (transList cs p s []).1, EL.Covers (restrict F J) J.c p q.1 q.2 :=
  transList_restrict F J hJ hT hB cs p s [] hle hA (by simp)

theorem transAxiom_restrict (s : St) (ax : Axiom) (hle : Le (transAxiom s ax) F)
    (hA : ax.isSRI = true) : (restrict F J).sat ax := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom] at hle
      simp only [Axiom.isSRI, Bool.and_eq_true] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hn := transExpr_restrict F J hJ hT hB c false s
        ((transExpr_le d true _).trans hle₂) hA.1
      have hp := transExpr_restrict F J hJ hT hB d true _ hle₂ hA.2
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      obtain ⟨b, hb, hbx⟩ := hcl x (by simpa using hn x hx)
      simp only [List.mem_singleton] at hb
      subst hb
      exact hp x hbx
  | equivalentClasses cs =>
      simp only [transAxiom] at hle
      simp only [Axiom.isSRI, List.all_eq_true] at hA
      have hle₂ := (setOut_le fun c hc => (mem_emitEquiv _ _ _ c).2 (Or.inl hc)).trans hle
      have hle₁ := (transList_le cs true _ []).trans hle₂
      have hN := transList_restrict' F J hJ hT hB hle₁ hA
      have hP := transList_restrict' F J hJ hT hB hle₂ hA
      intro c hc d hd x hx
      obtain ⟨qn, hqn, rfl⟩ := transList_fst_mem (p := false) (s := s) hc
      obtain ⟨qp, hqp, rfl⟩ := transList_fst_mem (p := true) (s := (transList cs false s []).2) hd
      have hxn := hN qn hqn x hx
      refine hP qp hqp x ?_
      by_cases heq : qn.2 = qp.2
      · rw [← heq]; exact hxn
      · have hcl := hJ _ (hle.out _ ((mem_emitEquiv _ _ _ _).2
          (Or.inr ⟨qn, hqn, qp, hqp, heq, rfl⟩)))
        obtain ⟨b, hb, hbx⟩ := hcl x (by simpa using hxn)
        simp only [List.mem_singleton] at hb
        subst hb; exact hbx
  | disjointClasses cs =>
      simp only [transAxiom] at hle
      simp only [Axiom.isSRI, List.all_eq_true] at hA
      have hle₁ := (setOut_le fun c hc => (mem_emitDisjoint _ _ c).2 (Or.inl hc)).trans hle
      have hN := transList_restrict' F J hJ hT hB hle₁ hA
      have hfst := transList_fst cs false s []
      simp only [List.reverse_nil, List.map_nil, List.nil_append] at hfst
      show cs.Pairwise fun c d => ∀ x, ¬ ((restrict F J).ext c x ∧ (restrict F J).ext d x)
      rw [← hfst, List.pairwise_map, List.pairwise_iff_forall_sublist]
      intro m n hmn x ⟨hm, hn⟩
      have hcl := hJ _ (hle.out _ ((mem_emitDisjoint _ _ _).2 (Or.inr ⟨m, n, hmn, rfl⟩)))
      obtain ⟨b, hb, _⟩ := hcl x (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact hN m (hmn.subset (by simp)) x hm
        · exact hN n (hmn.subset (by simp)) x hn)
      simp at hb
  | domain r c =>
      simp only [transAxiom] at hle
      simp only [Axiom.isSRI] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := (roleT_ok r s).mono hle₁.b
      have hp := transExpr_restrict F J hJ hT hB c true _ hle₂ hA
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y hxy
      refine hp x (hcl y ?_ x ((SRI.Interp.rt_flip _ _ _ _).2 ((restrict_prop hrk x y).1 hxy)))
      rw [← hle₂.b.top]; exact hT y
  | range r c =>
      simp only [transAxiom] at hle
      simp only [Axiom.isSRI] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := (roleT_ok r s).mono hle₁.b
      have hp := transExpr_restrict F J hJ hT hB c true _ hle₂ hA
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y hxy
      refine hp y (hcl x ?_ y ((restrict_prop hrk x y).1 hxy))
      rw [← hle₂.b.top]; exact hT x
  | subObjectPropertyOf rs r =>
      simp only [transAxiom] at hle
      have hle₁ := (roleT_le r _).trans ((emit_le _ _).trans hle)
      have hL := forall₂_mono (fun r R (h : RoleOK _ r R) => restrict_prop (J := J) (h.mono hle₁.b))
        (roleTs_ok' rs s)
      have hrk := (roleT_ok r (roleTs rs s []).2).mono ((emit_le _ _).trans hle).b
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y hxy
      exact (restrict_prop hrk x y).2 (hcl x y ((chain_iff_path _ J hL x y).1 hxy))
  | equivalentObjectProperties rs =>
      simp only [transAxiom] at hle
      have hle₁ := (setOut_le fun c hc => (mem_emitRoleEquiv _ _ c).2 (Or.inl hc)).trans hle
      have hL := roleTs_ok' rs s
      intro r hr r' hr' x y hxy
      obtain ⟨R, hR, hok⟩ := forall₂_left hL r hr
      obtain ⟨S, hS, hok'⟩ := forall₂_left hL r' hr'
      have h₁ := restrict_prop (J := J) (hok.mono hle₁.b)
      have h₂ := restrict_prop (J := J) (hok'.mono hle₁.b)
      refine (h₂ x y).2 ?_
      by_cases heq : R = S
      · subst heq; exact (h₁ x y).1 hxy
      · have hcl := hJ _ (hle.out _ ((mem_emitRoleEquiv _ _ _).2
          (Or.inr ⟨R, hR, S, hS, heq, rfl⟩)))
        exact hcl x y ((path_single _ _ _ _).2 ((h₁ x y).1 hxy))
  | inverseObjectProperties r r' =>
      simp only [transAxiom] at hle
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (emit_le _ _).trans hle₂
      have hA := restrict_prop (J := J) ((roleT_ok r s).mono ((roleT_le r' _).trans hle₁).b)
      have hB := restrict_prop (J := J) ((roleT_ok r' (roleT r s).2).mono hle₁.b)
      have hcl₁ := hJ _ (hle₂.out _ (mem_emit _ _))
      have hcl₂ := hJ _ (hle.out _ (mem_emit _ _))
      intro x y
      constructor
      · intro hxy
        exact (hB y x).2 ((SRI.Interp.rt_flip _ _ _ _).1
          (hcl₁ x y ((path_single _ _ _ _).2 ((hA x y).1 hxy))))
      · intro hyx
        exact (hA x y).2 ((SRI.Interp.rt_flip _ _ _ _).1
          (hcl₂ y x ((path_single _ _ _ _).2 ((hB y x).1 hyx))))
  | transitive r =>
      simp only [transAxiom] at hle
      have hA := restrict_prop (J := J) ((roleT_ok r s).mono ((emit_le _ _).trans hle).b)
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y z hxy hyz
      exact (hA x z).2 (hcl x z ((path_pair _ _ _ _ _).2 ⟨y, (hA x y).1 hxy, (hA y z).1 hyz⟩))
  | symmetric r =>
      simp only [transAxiom] at hle
      have hA := restrict_prop (J := J) ((roleT_ok r s).mono ((emit_le _ _).trans hle).b)
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y hxy
      exact (hA y x).2 ((SRI.Interp.rt_flip _ _ _ _).1
        (hcl x y ((path_single _ _ _ _).2 ((hA x y).1 hxy))))
  | declareClass _ | declareObjectProperty _ => simp [Interp.sat]

end RestrictAxiom

/-! ## (⇐) at the axiom level -/

section ExtendAxiom

variable {D : Type} (I : OWL.Interp D) (F : St)

theorem good_roleTs : ∀ (rs : List ObjProp) (s : St) acc, Good I F s →
    Good I F (roleTs rs s acc).2
  | [], _, _, hg => hg
  | _ :: rs, _, _, hg => good_roleTs rs _ _ hg

theorem transAxiom_extend (s : St) (hs : WF s) (ax : Axiom) (hle : Le (transAxiom s ax) F)
    (hA : ax.isSRI = true) (hI : I.sat ax) (hg : Good I F s) :
    Good I F (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isSRI, Bool.and_eq_true] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hn := transExpr_extend I F c false s hs ((transExpr_le d true _).trans hle₂) hA.1
      have hp := transExpr_extend I F d true _ (transExpr_wf c false s hs).1 hle₂ hA.2
      refine good_emit I F (hp.1 (hn.1 hg)) ?_
      intro x hx
      refine ⟨_, List.mem_singleton_self _, (hp.2 x).2 (hI x ((hn.2 x).1 (hx _ (by simp))))⟩
  | equivalentClasses cs =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isSRI, List.all_eq_true] at hA
      have hle₂ := (setOut_le fun c hc => (mem_emitEquiv _ _ _ c).2 (Or.inl hc)).trans hle
      have hle₁ := (transList_le cs true _ []).trans hle₂
      have hN := transList_extend I F cs false s [] hs hle₁ hA
      have hP := transList_extend I F cs true _ [] (transList_wf cs false s [] hs (by simp)).1
        hle₂ hA
      have hNe := hN.2 (by simp)
      have hPe := hP.2 (by simp)
      intro c hc
      rcases (mem_emitEquiv _ _ _ _).1 hc with hc | ⟨qn, hqn, qp, hqp, _, rfl⟩
      · exact hP.1 (hN.1 hg) c hc
      · intro x hx
        refine ⟨_, List.mem_singleton_self _, (hPe qp hqp x).2 ?_⟩
        exact hI qn.1 (transList_mem_fst hqn) qp.1 (transList_mem_fst hqp) x
          ((hNe qn hqn x).1 (hx _ (by simp)))
  | disjointClasses cs =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isSRI, List.all_eq_true] at hA
      have hle₁ := (setOut_le fun c hc => (mem_emitDisjoint _ _ c).2 (Or.inl hc)).trans hle
      have hN := transList_extend I F cs false s [] hs hle₁ hA
      have hNe := hN.2 (by simp)
      have hfst := transList_fst cs false s []
      simp only [List.reverse_nil, List.map_nil, List.nil_append] at hfst
      have hI' : cs.Pairwise fun c d => ∀ x, ¬ (I.ext c x ∧ I.ext d x) := hI
      rw [← hfst, List.pairwise_map, List.pairwise_iff_forall_sublist] at hI'
      intro c hc
      rcases (mem_emitDisjoint _ _ _).1 hc with hc | ⟨m, n, hmn, rfl⟩
      · exact hN.1 hg c hc
      · intro x hx
        have hmL : m ∈ (transList cs false s []).1 := hmn.subset (by simp)
        have hnL : n ∈ (transList cs false s []).1 := hmn.subset (by simp)
        exact absurd ⟨(hNe m hmL x).1 (hx _ (by simp)), (hNe n hnL x).1 (hx _ (by simp))⟩
          (hI' hmn x)
  | domain r c =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isSRI] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := extend_prop I F (((roleT_ok r s).def (roleT_wf hs).b).mono hle₁.b)
      have hp := transExpr_extend I F c true _ (roleT_wf hs) hle₂ hA
      refine good_emit I F (hp.1 hg) ?_
      intro y _ x hyx
      exact (hp.2 x).2 (hI x y ((hrk x y).1 ((SRI.Interp.rt_flip _ _ _ _).1 hyx)))
  | range r c =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isSRI] at hA
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := extend_prop I F (((roleT_ok r s).def (roleT_wf hs).b).mono hle₁.b)
      have hp := transExpr_extend I F c true _ (roleT_wf hs) hle₂ hA
      refine good_emit I F (hp.1 hg) ?_
      intro x _ y hxy
      exact (hp.2 y).2 (hI x y ((hrk x y).1 hxy))
  | subObjectPropertyOf rs r =>
      simp only [transAxiom] at hle ⊢
      have hl := roleTs_wf rs s [] hs
      have hle₁ := (roleT_le r _).trans ((emit_le _ _).trans hle)
      have hL := forall₂_mono (fun r R (h : RoleOK _ r R) =>
        fun x y => (extend_prop I F ((h.def hl.b).mono hle₁.b) x y).symm) (roleTs_ok' rs s)
      have hrk := extend_prop I F
        (((roleT_ok r (roleTs rs s []).2).def (roleT_wf hl).b).mono ((emit_le _ _).trans hle).b)
      refine good_emit I F (good_roleTs I F rs s [] hg) ?_
      intro x y hxy
      exact (hrk x y).2 (hI x y ((chain_iff_path I _ hL x y).2 hxy))
  | equivalentObjectProperties rs =>
      simp only [transAxiom] at hle ⊢
      have hl := roleTs_wf rs s [] hs
      have hle₁ := (setOut_le fun c hc => (mem_emitRoleEquiv _ _ c).2 (Or.inl hc)).trans hle
      have hL := roleTs_ok' rs s
      intro c hc
      rcases (mem_emitRoleEquiv _ _ _).1 hc with hc | ⟨R, hR, S, hS, _, rfl⟩
      · exact good_roleTs I F rs s [] hg c hc
      · obtain ⟨r, hr, hok⟩ := forall₂_right hL R hR
        obtain ⟨r', hr', hok'⟩ := forall₂_right hL S hS
        have h₁ := extend_prop I F ((hok.def hl.b).mono hle₁.b)
        have h₂ := extend_prop I F ((hok'.def hl.b).mono hle₁.b)
        intro x y hxy
        exact (h₂ x y).2 (hI r hr r' hr' x y ((h₁ x y).1 ((path_single _ _ _ _).1 hxy)))
  | inverseObjectProperties r r' =>
      simp only [transAxiom] at hle ⊢
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (emit_le _ _).trans hle₂
      have hs₁ := roleT_wf (r := r) hs
      have hA := extend_prop I F
        (((roleT_ok r s).def hs₁.b).mono ((roleT_le r' _).trans hle₁).b)
      have hB := extend_prop I F (((roleT_ok r' (roleT r s).2).def (roleT_wf hs₁).b).mono hle₁.b)
      refine good_emit I F (good_emit I F hg ?_) ?_
      · intro x y hxy
        exact (SRI.Interp.rt_flip _ _ _ _).2
          ((hB y x).2 ((hI x y).1 ((hA x y).1 ((path_single _ _ _ _).1 hxy))))
      · intro x y hxy
        exact (SRI.Interp.rt_flip _ _ _ _).2
          ((hA y x).2 ((hI y x).2 ((hB x y).1 ((path_single _ _ _ _).1 hxy))))
  | transitive r =>
      simp only [transAxiom] at hle ⊢
      have hA := extend_prop I F
        (((roleT_ok r s).def (roleT_wf hs).b).mono ((emit_le _ _).trans hle).b)
      refine good_emit I F hg ?_
      intro x z hxz
      obtain ⟨y, hxy, hyz⟩ := (path_pair _ _ _ _ _).1 hxz
      exact (hA x z).2 (hI x y z ((hA x y).1 hxy) ((hA y z).1 hyz))
  | symmetric r =>
      simp only [transAxiom] at hle ⊢
      have hA := extend_prop I F
        (((roleT_ok r s).def (roleT_wf hs).b).mono ((emit_le _ _).trans hle).b)
      refine good_emit I F hg ?_
      intro x y hxy
      exact (SRI.Interp.rt_flip _ _ _ _).2 ((hA y x).2 (hI x y ((hA x y).1
        ((path_single _ _ _ _).1 hxy))))
  | declareClass _ | declareObjectProperty _ => simpa [transAxiom] using hg

end ExtendAxiom

/-! ## The loop over axioms -/

theorem foldl_trans_le : ∀ (axs : List Axiom) (s : St), Le s (axs.foldl transAxiom s)
  | [], _ => Le.rfl
  | ax :: axs, s => (transAxiom_le s ax).trans (foldl_trans_le axs _)

theorem foldl_trans_wf : ∀ (axs : List Axiom) (s : St), WF s → WF (axs.foldl transAxiom s)
  | [], _, hs => hs
  | ax :: axs, _, hs => foldl_trans_wf axs _ (transAxiom_wf hs ax)

theorem foldl_trans_mem : ∀ (axs : List Axiom) (s : St), WF s → ∀ ax ∈ axs,
    ∃ s', WF s' ∧ Le (transAxiom s' ax) (axs.foldl transAxiom s)
  | [], _, _, ax, h => absurd h List.not_mem_nil
  | ax' :: axs, s, hs, ax, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨s, hs, foldl_trans_le axs _⟩
      · exact foldl_trans_mem axs _ (transAxiom_wf hs ax') ax h

theorem foldl_trans_good {D : Type} (I : OWL.Interp D) (F : St) :
    ∀ (axs : List Axiom) (s : St), WF s → Le (axs.foldl transAxiom s) F →
      (∀ ax ∈ axs, ax.isSRI = true ∧ I.sat ax) →
      Good I F s → Good I F (axs.foldl transAxiom s)
  | [], _, _, _, _, hg => hg
  | ax :: axs, s, hs, hle, hax, hg => by
      simp only [List.foldl_cons] at hle ⊢
      have h₀ := hax ax List.mem_cons_self
      exact foldl_trans_good I F axs _ (transAxiom_wf hs ax) hle
        (fun a ha => hax a (List.mem_cons_of_mem _ ha))
        (transAxiom_extend I F s hs ax ((foldl_trans_le axs _).trans hle) h₀.1 h₀.2 hg)

/-! ## From `Nat` to `Fin` indices -/

/-- A `Nat` interpretation read on `Fin` indices. -/
def lower {D : Type} (n m : Nat) (K : SRI.Interp D Nat Nat) : SRI.Interp D (Fin n) (Fin m) :=
  ⟨fun i => K.c i.val, fun r => K.r r.val⟩

/-- A `Fin` interpretation read on `Nat` indices (out of range: empty). -/
def raise {D : Type} (n m : Nat) (J : SRI.Interp D (Fin n) (Fin m)) : SRI.Interp D Nat Nat :=
  ⟨fun k x => ∃ h : k < n, J.c ⟨k, h⟩ x, fun k x y => ∃ h : k < m, J.r ⟨k, h⟩ x y⟩

theorem lower_raise {D : Type} (n m : Nat) (J : SRI.Interp D (Fin n) (Fin m)) :
    lower n m (raise n m J) = J := by
  cases J with
  | mk c r =>
      simp only [lower, raise, SRI.Interp.mk.injEq]
      constructor
      · funext i x; apply propext; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.isLt, h⟩⟩
      · funext i x y; apply propext; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.isLt, h⟩⟩

theorem finRT_sat {D : Type} (n m : Nat) (K : SRI.Interp D Nat Nat) {R : RT}
    {R' : SRI.RoleT (Fin m)} (h : finRT m R = some R') (x y : D) :
    (lower n m K).rt R' x y ↔ K.rt R x y := by
  cases R with
  | pos r =>
      simp only [finRT] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
  | inv r =>
      simp only [finRT] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · exact absurd h (by simp)

theorem finRTs_spec (m : Nat) : ∀ (Rs : List RT) (acc l : List (SRI.RoleT (Fin m))),
    finRTs m Rs acc = some l →
      ∃ L, l = acc.reverse ++ L ∧ List.Forall₂ (fun R R' => finRT m R = some R') Rs L
  | [], acc, l, h => by
      simp only [finRTs, Option.some.injEq] at h; subst h; exact ⟨[], by simp, .nil⟩
  | R :: Rs, acc, l, h => by
      simp only [finRTs] at h
      split at h
      · rename_i R' hR
        obtain ⟨L, rfl, hL⟩ := finRTs_spec m Rs _ l h
        exact ⟨R' :: L, by simp, .cons hR hL⟩
      · exact absurd h (by simp)

theorem path_congr {D C₁ C₂ R₁ R₂ : Type} (J₁ : SRI.Interp D C₁ R₁) (J₂ : SRI.Interp D C₂ R₂) :
    ∀ {Rs : List (SRI.RoleT R₁)} {Rs' : List (SRI.RoleT R₂)},
      List.Forall₂ (fun R R' => ∀ x y, J₂.rt R' x y ↔ J₁.rt R x y) Rs Rs' →
      ∀ x y, J₂.path Rs' x y ↔ J₁.path Rs x y
  | _, _, .nil, x, y => by simp [SRI.Interp.path]
  | _, _, .cons h₁ h₂, x, y => by
      simp only [SRI.Interp.path, h₁, path_congr J₁ J₂ h₂]

theorem toFin_sat {D : Type} (n m : Nat) (K : SRI.Interp D Nat Nat) (c : SC)
    (c' : SRI.Clause (Fin n) (Fin m)) (h : toFin n m c = some c') :
    SRI.satClause (lower n m K) c' ↔ SRI.satClause K c := by
  cases c with
  | gci body head =>
      simp only [toFin] at h
      split at h
      · rename_i b hd hb hh
        simp only [Option.some.injEq] at h
        subst h
        have hb' := ALC.finList_spec n body [] b hb
        have hh' := ALC.finList_spec n head [] hd hh
        simp only [List.reverse_nil, List.map_nil, List.nil_append] at hb' hh'
        simp only [SRI.satClause, lower]
        rw [← hb', ← hh']
        simp
      · exact absurd h (by simp)
  | exRight a R b =>
      simp only [toFin] at h
      split at h
      · split at h
        · obtain ⟨R', hR, rfl⟩ := Option.map_eq_some_iff.1 h
          simp only [SRI.satClause, finRT_sat n m K hR]; rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | allRight a R b =>
      simp only [toFin] at h
      split at h
      · split at h
        · obtain ⟨R', hR, rfl⟩ := Option.map_eq_some_iff.1 h
          simp only [SRI.satClause, finRT_sat n m K hR]; rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | chain body S =>
      simp only [toFin] at h
      split at h
      · rename_i b S' hb hS
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨L, hbL, hL⟩ := finRTs_spec m body [] b hb
        simp only [List.reverse_nil, List.nil_append] at hbL
        subst hbL
        have hp := path_congr K (lower n m K)
          (forall₂_mono (fun R R' (h : finRT m R = some R') => finRT_sat n m K h) hL)
        simp only [SRI.satClause, hp, finRT_sat n m K hS]
      · exact absurd h (by simp)

theorem finRT_isSome (m : Nat) (R : RT) (h : rIx R < m) : ∃ R', finRT m R = some R' := by
  cases R with
  | pos r => exact ⟨_, by simp only [finRT, dif_pos (show r < m from h)]; rfl⟩
  | inv r => exact ⟨_, by simp only [finRT, dif_pos (show r < m from h)]; rfl⟩

theorem finRTs_isSome (m : Nat) : ∀ (Rs : List RT) (acc : List (SRI.RoleT (Fin m))),
    (∀ R ∈ Rs, rIx R < m) → ∃ l, finRTs m Rs acc = some l
  | [], acc, _ => ⟨_, rfl⟩
  | R :: Rs, acc, h => by
      obtain ⟨R', hR⟩ := finRT_isSome m R (h R List.mem_cons_self)
      simp only [finRTs, hR]
      exact finRTs_isSome m Rs _ (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem toFin_isSome (n m : Nat) (c : SC) (hc : ∀ k ∈ cIdx c, k < n)
    (hr : ∀ k ∈ rIdx c, k < m) : ∃ c', toFin n m c = some c' := by
  cases c with
  | gci body head =>
      obtain ⟨b, hb⟩ := ALC.finList_isSome n body [] (fun k hk => hc k (by simp [cIdx, hk]))
      obtain ⟨h, hh⟩ := ALC.finList_isSome n head [] (fun k hk => hc k (by simp [cIdx, hk]))
      exact ⟨.gci b h, by simp only [toFin, hb, hh]⟩
  | exRight a R b =>
      have h1 : a < n := hc a (by simp [cIdx])
      have h2 : b < n := hc b (by simp [cIdx])
      obtain ⟨R', hR⟩ := finRT_isSome m R (hr _ (by simp [rIdx]))
      exact ⟨.exRight ⟨a, h1⟩ R' ⟨b, h2⟩, by simp [toFin, h1, h2, hR]⟩
  | allRight a R b =>
      have h1 : a < n := hc a (by simp [cIdx])
      have h2 : b < n := hc b (by simp [cIdx])
      obtain ⟨R', hR⟩ := finRT_isSome m R (hr _ (by simp [rIdx]))
      exact ⟨.allRight ⟨a, h1⟩ R' ⟨b, h2⟩, by simp [toFin, h1, h2, hR]⟩
  | chain body S =>
      obtain ⟨b, hb⟩ := finRTs_isSome m body [] (fun R hR => hr _ (by simp [rIdx]; exact Or.inl ⟨R, hR, rfl⟩))
      obtain ⟨S', hS⟩ := finRT_isSome m S (hr _ (by simp [rIdx]))
      exact ⟨.chain b S', by simp only [toFin, hb, hS]⟩

open ALC (CIn.lt RIn.lt)

/-- The `Fin` ontology of the final state and the `Nat` clauses have the same
models: (a) the restriction of a `Nat` model is a `Fin` model; (b) a `Fin`
model read on `Nat` indices satisfies every emitted clause (nothing is
dropped). -/
theorem fin_models {F : St} (hF : WF F) {D : Type} :
    (∀ K : SRI.Interp D Nat Nat, (∀ c ∈ F.out, SRI.satClause K c) →
      SRI.models (lower F.b.cdefs.size F.b.rdefs.size K)
        (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size))) ∧
    (∀ J : SRI.Interp D (Fin F.b.cdefs.size) (Fin F.b.rdefs.size),
      SRI.models J (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size)) →
      ∀ c ∈ F.out, SRI.satClause (raise F.b.cdefs.size F.b.rdefs.size J) c) := by
  constructor
  · intro K hK c' hc'
    obtain ⟨c, hc, h⟩ := List.mem_filterMap.1 hc'
    exact (toFin_sat _ _ K c c' h).2 (hK c (List.mem_reverse.1 hc))
  · intro J hJ c hc
    have hv := hF.valid c hc
    obtain ⟨c', h⟩ := toFin_isSome F.b.cdefs.size F.b.rdefs.size c
      (fun k hk => (hv.1 k hk).lt) (fun k hk => (hv.2 k hk).lt)
    have := hJ c' (List.mem_filterMap.2 ⟨c, List.mem_reverse.2 hc, h⟩)
    rw [← lower_raise _ _ J] at this
    exact (toFin_sat _ _ _ c c' h).1 this

/-! ## The pipeline -/

theorem start_wf {b : EL.St} (hb : EL.WF (EL.setTopBottom b)) : WF (start b) := by
  have hT : (EL.setTopBottom b).cdefs[(EL.setTopBottom b).top]? = some .thing :=
    EL.push_getElem? (EL.push_size_getElem? _ _)
  have hB : (EL.setTopBottom b).cdefs[(EL.setTopBottom b).bottom]? = some .nothing := by
    simp [EL.setTopBottom, Array.getElem_push]
  refine ⟨hb, hT, hB, ?_⟩
  intro c hc
  simp only [start, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact valid_gci (by simp; exact ⟨_, hB⟩) (by simp)
  · exact valid_gci (by simp) (by simp; exact ⟨_, hT⟩)

theorem start_top_mem (b : EL.St) : SRI.Clause.gci [] [(start b).b.top] ∈ (start b).out := by
  simp [start]

theorem start_bottom_mem (b : EL.St) :
    SRI.Clause.gci [(start b).b.bottom] [] ∈ (start b).out := by
  simp [start]

/-- The correctness argument on the states of the pipeline. -/
theorem correct_core (O : Ontology) (hSRI : O.isSRI = true) (b : EL.St) (F : St)
    (L : List IRI) (hb : EL.WF (EL.setTopBottom b))
    (hidxS : ∀ (i : Nat) (h : i < L.length), b.cmap[L[i]]? = some i)
    (hF : O.axioms.foldl transAxiom (start b) = F)
    (i j : Nat) (hi : i < L.length) (hj : j < L.length)
    (hi' : i < F.b.cdefs.size) (hj' : j < F.b.cdefs.size) :
    OWL.EntailsSub O L[i] L[j] ↔
      SRI.EntailsSub (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size))
        ⟨i, hi'⟩ ⟨j, hj'⟩ := by
  have hS := start_wf hb
  have hLe : Le (start b) F := hF ▸ foldl_trans_le O.axioms (start b)
  have hFwf : WF F := hF ▸ foldl_trans_wf O.axioms (start b) hS
  have hA : ∀ ax ∈ O.axioms, ax.isSRI = true := by
    simpa [Ontology.isSRI, List.all_eq_true] using hSRI
  have hidx : ∀ k (hk : k < L.length), F.b.cmap[L[k]]? = some k := fun k hk =>
    hLe.b.cmap _ _ (hidxS k hk)
  constructor
  · intro hsub D _ J hJ x hx
    let K := raise F.b.cdefs.size F.b.rdefs.size J
    have hK : ∀ c ∈ F.out, SRI.satClause K c := (fin_models hFwf).2 J hJ
    have hT : ∀ x, K.c F.b.top x := by
      intro y
      obtain ⟨b', hb', hy⟩ := hK _ (hLe.out _ (start_top_mem b)) y (by simp)
      simp only [List.mem_singleton] at hb'
      rw [hb', ← hLe.b.top] at hy; exact hy
    have hB : ∀ x, ¬ K.c F.b.bottom x := by
      intro y hy
      obtain ⟨b', hb', _⟩ := hK _ (hLe.out _ (start_bottom_mem b)) y (by
        intro k hk; simp only [List.mem_singleton] at hk; rw [hk, ← hLe.b.bottom]
        exact hy)
      simp at hb'
    have hmodel : OWL.Model O (restrict F K) := by
      intro ax hax
      obtain ⟨s', _, hle⟩ := foldl_trans_mem O.axioms (start b) hS ax hax
      exact transAxiom_restrict F K hK hT hB s' ax (hF ▸ hle) (hA ax hax)
    have := hsub D (restrict F K) hmodel x
    rw [restrict_cls (hidx i hi), restrict_cls (hidx j hj)] at this
    obtain ⟨_, hjx⟩ := this ⟨hi', hx⟩
    exact hjx
  · intro hent D _ I hI x hx
    have hgood : Good I F F := by
      have := foldl_trans_good I F O.axioms (start b) hS (hF ▸ Le.rfl)
        (fun ax hax => ⟨hA ax hax, hI ax hax⟩) (by
          intro c hc
          simp only [start, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · intro y hy
            exact absurd (hy _ (by simp [start])) (extend_bottom I F hS hLe y)
          · intro y _
            exact ⟨_, by simp [start], extend_top I F hS hLe y⟩)
      rwa [hF] at this
    have := hent D (lower _ _ (extend I F)) ((fin_models hFwf).1 _ hgood) x
    simp only [lower] at this
    rw [extend_c I F (hFwf.b.cmap _ _ (hidx i hi)),
      extend_c I F (hFwf.b.cmap _ _ (hidx j hj)), EL.ext_cls, EL.ext_cls] at this
    exact this hx

end ContextCalculus.OWLFrontend.SRIT

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SRIT

/-- The facts about `SRIT.run`: the named list, the index of every named IRI,
the final state. -/
theorem SRIT.run_spec (O : Ontology) (requested : List IRI) :
    ∃ b, EL.WF (EL.setTopBottom b) ∧ (SRIT.run O requested).2 = requested.eraseDups ∧
      (∀ (i : Nat) (h : i < (SRIT.run O requested).2.length),
        b.cmap[(SRIT.run O requested).2[i]]? = some i) ∧
      O.axioms.foldl transAxiom (start b) = (SRIT.run O requested).1 := by
  obtain ⟨hL, hwf, _, _, _, hidx⟩ := EL.start_spec O requested
  refine ⟨O.axioms.foldl EL.scanAxiom (EL.internRequested requested {} []).1, ?_, hL, ?_, rfl⟩
  · exact hwf
  · intro i h
    exact hidx i h

theorem translateSRI_named {O : OWL.Ontology} {requested : List OWL.IRI} {T : SRITranslation}
    (h : translateSRI O requested = some T) :
    T.named = requested.eraseDups := by
  simp only [translateSRI] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact (SRIT.run_spec O requested).choose_spec.2.1
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem translateSRI_isSome {O : OWL.Ontology} {requested : List OWL.IRI}
    (hSRI : O.isSRI = true) :
    (translateSRI O requested).isSome = true := by
  obtain ⟨b, hb, _, hidx, hF⟩ := SRIT.run_spec O requested
  have hFwf : SRIT.WF (SRIT.run O requested).1 := hF ▸ foldl_trans_wf O.axioms _ (start_wf hb)
  have hLe : SRIT.Le (start b) (SRIT.run O requested).1 := hF ▸ foldl_trans_le O.axioms _
  have hlen : (SRIT.run O requested).2.length ≤ (SRIT.run O requested).1.b.cdefs.size := by
    cases hn : (SRIT.run O requested).2.length with
    | zero => exact Nat.zero_le _
    | succ k =>
        have hk : k < (SRIT.run O requested).2.length := by omega
        have hc := hLe.b.cmap _ _ (hidx k hk)
        exact (show ALC.CIn _ k from ⟨_, hFwf.b.cmap _ _ hc⟩).lt
  simp [translateSRI, hSRI, hlen]

/-- A requested IRI and its concept index have the same subsumers and
subsumees: OWL entailment between two requested IRIs is entailment between
their indices in the translated clauses. -/
theorem translateSRI_correct {O : OWL.Ontology} {requested : List OWL.IRI} {T : SRITranslation}
    (h : translateSRI O requested = some T)
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWL.EntailsSub O T.named[i] T.named[j] ↔
      SRI.EntailsSub T.ontology
        ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ ⟨j, Nat.lt_of_lt_of_le hj T.hnamed⟩ := by
  simp only [translateSRI] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hSRI
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨b, hb, _, hidx, hF⟩ := SRIT.run_spec O requested
  exact correct_core O hSRI b _ _ hb hidx hF i j hi hj _ _

#print axioms translateSRI_named
#print axioms translateSRI_isSome
#print axioms translateSRI_correct

end ContextCalculus.OWLFrontend
