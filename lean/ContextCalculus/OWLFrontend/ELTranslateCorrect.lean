import ContextCalculus.OWLFrontend.ELTranslate

/-!
# Correctness of the OWL EL translation

`translateEL_named`, `translateEL_isSome` and `translateEL_correct`
(`docs/V1.6.2-FRONTEND-PLAN.md`, section 7).

The proof follows the two-way argument of the plan.

- (⇒, OWL entailment gives NF entailment) a model `J` of the normal forms
  restricts to an OWL interpretation `restrict F J` (`cls a` is the concept
  of the index of `a`, `role r` the role of the index of `r`). By induction
  on a class expression `E`, a negative occurrence with result `X` gives
  `ext E ⊆ J X` and a positive one `J X ⊆ ext E` (`transExpr_restrict`).
  Every axiom then holds in `restrict F J`.
- (⇐) a model `I` of `O` extends to an NF interpretation `extend I F`: index
  `k` stands for the class expression `F.cdefs[k]` (a class IRI, `owl:Thing`,
  `owl:Nothing` or the subexpression a definer abbreviates), and role index
  `k` for the composition of the chain `F.rdefs[k]`. Every emitted clause
  holds (`transExpr_extend`, `transAxiom_extend`).

Both directions read the final state `F` through the extension order `Le`
(maps, meaning tables and emitted clauses only grow) and the invariant `WF`
(the maps agree with the meaning tables).
-/

namespace ContextCalculus.OWLFrontend.EL

open ContextCalculus.OWL

/-! ## The extension order and the invariant -/

/-- `s'` extends `s`. -/
structure Le (s s' : St) : Prop where
  cmap : ∀ (a : IRI) (k : Nat), s.cmap[a]? = some k → s'.cmap[a]? = some k
  rmap : ∀ (r : IRI) (k : Nat), s.rmap[r]? = some k → s'.rmap[r]? = some k
  cdefs : ∀ (k : Nat) (e : ClassExpr), s.cdefs[k]? = some e → s'.cdefs[k]? = some e
  rdefs : ∀ (k : Nat) (e : List IRI), s.rdefs[k]? = some e → s'.rdefs[k]? = some e
  out : ∀ c : NF, c ∈ s.out → c ∈ s'.out
  top : s'.top = s.top
  bottom : s'.bottom = s.bottom

theorem Le.rfl {s : St} : Le s s :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ h => h,
    Eq.refl _, Eq.refl _⟩

theorem Le.trans {s t u : St} (h₁ : Le s t) (h₂ : Le t u) : Le s u :=
  ⟨fun a k h => h₂.cmap a k (h₁.cmap a k h), fun a k h => h₂.rmap a k (h₁.rmap a k h),
   fun a k h => h₂.cdefs a k (h₁.cdefs a k h), fun a k h => h₂.rdefs a k (h₁.rdefs a k h),
   fun c h => h₂.out c (h₁.out c h), h₂.top.trans h₁.top, h₂.bottom.trans h₁.bottom⟩

/-- The maps agree with the meaning tables. -/
structure WF (s : St) : Prop where
  cmap : ∀ (a : IRI) (k : Nat), s.cmap[a]? = some k → s.cdefs[k]? = some (ClassExpr.cls a)
  rmap : ∀ (r : IRI) (k : Nat), s.rmap[r]? = some k → s.rdefs[k]? = some [r]

theorem push_getElem? {α : Type} {xs : Array α} {x : α} {k : Nat} {e : α}
    (h : xs[k]? = some e) : (xs.push x)[k]? = some e := by
  rw [Array.getElem?_push]
  split
  · subst_vars; simp at h
  · exact h

@[simp] theorem push_size_getElem? {α : Type} (xs : Array α) (x : α) :
    (xs.push x)[xs.size]? = some x := by
  simp

/-! ## Primitive steps -/

theorem internC_le (a : IRI) (s : St) : Le s (internC a s).2 := by
  unfold internC
  split
  · exact Le.rfl
  · rename_i hnone
    refine ⟨?_, fun _ _ h => h, fun _ _ h => push_getElem? h, fun _ _ h => h, fun _ h => h,
      rfl, rfl⟩
    intro b k h
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
    split
    · subst_vars; simp_all
    · exact h

theorem internC_wf {a : IRI} {s : St} (hs : WF s) : WF (internC a s).2 := by
  unfold internC
  split
  · exact hs
  · refine ⟨?_, hs.rmap⟩
    intro b k h
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at h
    split at h
    · subst_vars; simp only [Option.some.injEq] at h; subst h; simp
    · exact push_getElem? (hs.cmap b k h)

theorem internC_cmap (a : IRI) (s : St) : (internC a s).2.cmap[a]? = some (internC a s).1 := by
  unfold internC
  split
  · assumption
  · simp

theorem internC_cdefs {a : IRI} {s : St} (hs : WF s) :
    (internC a s).2.cdefs[(internC a s).1]? = some (.cls a) := by
  unfold internC
  split
  · exact hs.cmap _ _ (by assumption)
  · simp

theorem internR_le (r : IRI) (s : St) : Le s (internR r s).2 := by
  unfold internR
  split
  · exact Le.rfl
  · refine ⟨fun _ _ h => h, ?_, fun _ _ h => h, fun _ _ h => push_getElem? h, fun _ h => h,
      rfl, rfl⟩
    intro b k h
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
    split
    · subst_vars; simp_all
    · exact h

theorem internR_wf {r : IRI} {s : St} (hs : WF s) : WF (internR r s).2 := by
  unfold internR
  split
  · exact hs
  · refine ⟨hs.cmap, ?_⟩
    intro b k h
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at h
    split at h
    · subst_vars; simp only [Option.some.injEq] at h; subst h; simp
    · exact push_getElem? (hs.rmap b k h)

theorem internR_rmap (r : IRI) (s : St) : (internR r s).2.rmap[r]? = some (internR r s).1 := by
  unfold internR
  split
  · assumption
  · simp

theorem internR_rdefs {r : IRI} {s : St} (hs : WF s) :
    (internR r s).2.rdefs[(internR r s).1]? = some [r] := by
  unfold internR
  split
  · exact hs.rmap _ _ (by assumption)
  · simp

theorem freshC_le (e : ClassExpr) (s : St) : Le s (freshC e s).2 :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => push_getElem? h, fun _ _ h => h,
    fun _ h => h, rfl, rfl⟩

theorem freshC_wf {e : ClassExpr} {s : St} (hs : WF s) : WF (freshC e s).2 :=
  ⟨fun a k h => push_getElem? (hs.cmap a k h), hs.rmap⟩

theorem freshC_cdefs (e : ClassExpr) (s : St) :
    (freshC e s).2.cdefs[(freshC e s).1]? = some e := by
  simp [freshC]

theorem freshR_le (rev : List IRI) (s : St) : Le s (freshR rev s).2 :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => push_getElem? h,
    fun _ h => h, rfl, rfl⟩

theorem freshR_wf {rev : List IRI} {s : St} (hs : WF s) : WF (freshR rev s).2 :=
  ⟨hs.cmap, fun a k h => push_getElem? (hs.rmap a k h)⟩

theorem freshR_rdefs (rev : List IRI) (s : St) :
    (freshR rev s).2.rdefs[(freshR rev s).1]? = some rev := by
  simp [freshR]

theorem emit_le (c : NF) (s : St) : Le s (emit c s) :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ h => List.mem_cons_of_mem _ h, rfl, rfl⟩

theorem emit_wf {c : NF} {s : St} (hs : WF s) : WF (emit c s) := ⟨hs.cmap, hs.rmap⟩

theorem mem_emit (c : NF) (s : St) : c ∈ (emit c s).out := List.mem_cons_self

/-! ## Monotonicity and the invariant through the transformation -/

mutual

theorem transExpr_le : ∀ (E : ClassExpr) (p : Bool) (s : St), Le s (transExpr E p s).2
  | .cls a, _, s => by simp only [transExpr]; exact internC_le a s
  | .thing, _, s => by simp only [transExpr]; exact Le.rfl
  | .nothing, _, s => by simp only [transExpr]; exact Le.rfl
  | .and cs, false, s => by simp only [transExpr]; exact transNegAnd_le cs none s
  | .and cs, true, s => by
      simp only [transExpr]
      exact (freshC_le _ s).trans (transPosAnd_le cs _ _)
  | .some r c, false, s => by
      simp only [transExpr]
      exact (internR_le _ s).trans ((transExpr_le c false _).trans
        ((freshC_le _ _).trans (emit_le _ _)))
  | .some r c, true, s => by
      simp only [transExpr]
      exact (internR_le _ s).trans ((transExpr_le c true _).trans
        ((freshC_le _ _).trans (emit_le _ _)))
  | .or _, _, s => by simp only [transExpr]; exact Le.rfl
  | .not _, _, s => by simp only [transExpr]; exact Le.rfl
  | .all _ _, _, s => by simp only [transExpr]; exact Le.rfl

theorem transNegAnd_le : ∀ (cs : List ClassExpr) (acc : Option (Nat × ClassExpr)) (s : St),
    Le s (transNegAnd cs acc s).2
  | [], none, s => by simp only [transNegAnd]; exact Le.rfl
  | [], some (a, e), s => by simp only [transNegAnd]; exact Le.rfl
  | c :: cs, none, s => by
      simp only [transNegAnd]
      exact (transExpr_le c false s).trans (transNegAnd_le cs _ _)
  | c :: cs, some (a, e), s => by
      simp only [transNegAnd]
      exact (transExpr_le c false s).trans ((freshC_le _ _).trans
        ((emit_le _ _).trans (transNegAnd_le cs _ _)))

theorem transPosAnd_le : ∀ (cs : List ClassExpr) (x : Nat) (s : St),
    Le s (transPosAnd cs x s)
  | [], _, s => by simp only [transPosAnd]; exact Le.rfl
  | c :: cs, x, s => by
      simp only [transPosAnd]
      exact (transExpr_le c true s).trans ((emit_le _ _).trans (transPosAnd_le cs x _))

end

mutual

theorem transExpr_wf : ∀ (E : ClassExpr) (p : Bool) (s : St), WF s → WF (transExpr E p s).2
  | .cls a, _, s, hs => by simp only [transExpr]; exact internC_wf hs
  | .thing, _, s, hs => by simp only [transExpr]; exact hs
  | .nothing, _, s, hs => by simp only [transExpr]; exact hs
  | .and cs, false, s, hs => by simp only [transExpr]; exact transNegAnd_wf cs none s hs
  | .and cs, true, s, hs => by
      simp only [transExpr]
      exact transPosAnd_wf cs _ _ (freshC_wf hs)
  | .some r c, false, s, hs => by
      simp only [transExpr]
      exact emit_wf (freshC_wf (transExpr_wf c false _ (internR_wf hs)))
  | .some r c, true, s, hs => by
      simp only [transExpr]
      exact emit_wf (freshC_wf (transExpr_wf c true _ (internR_wf hs)))
  | .or _, _, s, hs => by simp only [transExpr]; exact hs
  | .not _, _, s, hs => by simp only [transExpr]; exact hs
  | .all _ _, _, s, hs => by simp only [transExpr]; exact hs

theorem transNegAnd_wf : ∀ (cs : List ClassExpr) (acc : Option (Nat × ClassExpr)) (s : St),
    WF s → WF (transNegAnd cs acc s).2
  | [], none, s, hs => by simp only [transNegAnd]; exact hs
  | [], some (a, e), s, hs => by simp only [transNegAnd]; exact hs
  | c :: cs, none, s, hs => by
      simp only [transNegAnd]
      exact transNegAnd_wf cs _ _ (transExpr_wf c false s hs)
  | c :: cs, some (a, e), s, hs => by
      simp only [transNegAnd]
      exact transNegAnd_wf cs _ _ (emit_wf (freshC_wf (transExpr_wf c false s hs)))

theorem transPosAnd_wf : ∀ (cs : List ClassExpr) (x : Nat) (s : St),
    WF s → WF (transPosAnd cs x s)
  | [], _, s, hs => by simp only [transPosAnd]; exact hs
  | c :: cs, x, s, hs => by
      simp only [transPosAnd]
      exact transPosAnd_wf cs x _ (emit_wf (transExpr_wf c true s hs))

end

/-! ## Unfolding lemmas -/

theorem internC_out (a : IRI) (s : St) : (internC a s).2.out = s.out := by
  unfold internC; split <;> rfl

theorem internR_out (r : IRI) (s : St) : (internR r s).2.out = s.out := by
  unfold internR; split <;> rfl

section Unfold

variable {D : Type} (I : OWL.Interp D)

theorem ext_cls (a : IRI) (x : D) : I.ext (.cls a) x ↔ I.cls a x := by rw [Interp.ext]
theorem ext_thing (x : D) : I.ext .thing x ↔ True := by rw [Interp.ext]
theorem ext_nothing (x : D) : I.ext .nothing x ↔ False := by rw [Interp.ext]
theorem ext_some (r : ObjProp) (c : ClassExpr) (x : D) :
    I.ext (.some r c) x ↔ ∃ y, I.prop r x y ∧ I.ext c y := by rw [Interp.ext]
theorem ext_and2 (e c : ClassExpr) (x : D) :
    I.ext (.and [e, c]) x ↔ I.ext e x ∧ I.ext c x := by
  rw [Interp.ext_and]; simp

end Unfold

theorem isEL_and {cs : List ClassExpr} :
    (ClassExpr.and cs).isEL = true ↔ ∀ c ∈ cs, c.isEL = true := by
  rw [ClassExpr.isEL]; simp

theorem isEL_some {r : ObjProp} {c : ClassExpr} :
    (ClassExpr.some r c).isEL = true ↔ r.isNamed = true ∧ c.isEL = true := by
  rw [ClassExpr.isEL]; simp

theorem isEL_or {cs : List ClassExpr} : (ClassExpr.or cs).isEL = false := by
  rw [ClassExpr.isEL]
theorem isEL_not {c : ClassExpr} : (ClassExpr.not c).isEL = false := by
  rw [ClassExpr.isEL]
theorem isEL_all {r : ObjProp} {c : ClassExpr} : (ClassExpr.all r c).isEL = false := by
  rw [ClassExpr.isEL]

/-! ## (⇒) A model of the normal forms restricts to an OWL interpretation -/

/-- The OWL interpretation read off an NF interpretation through the final
maps. IRIs without an index get `bottom` and role `0`; they do not occur. -/
def restrict (F : St) {D : Type} (J : ELCompletion.Interp D Nat Nat F.top F.bottom) :
    OWL.Interp D where
  cls a := J.concept (F.cmap[a]?.getD F.bottom)
  role r := J.role (F.rmap[r]?.getD 0)

/-- The occurrence invariant: negative `ext E ⊆ Jc X`, positive `Jc X ⊆ ext E`. -/
def Covers {D : Type} (I : OWL.Interp D) (Jc : Nat → D → Prop) :
    Bool → ClassExpr → Nat → Prop
  | false, E, X => ∀ x, I.ext E x → Jc X x
  | true, E, X => ∀ x, Jc X x → I.ext E x

def AccCovers {D : Type} (I : OWL.Interp D) (Jc : Nat → D → Prop) :
    Option (Nat × ClassExpr) → Prop
  | none => True
  | some (a, e) => ∀ x, I.ext e x → Jc a x

def AccHolds {D : Type} (I : OWL.Interp D) : Option (Nat × ClassExpr) → D → Prop
  | none, _ => True
  | some (_, e), x => I.ext e x

theorem restrict_cls {F : St} {D : Type} {J : ELCompletion.Interp D Nat Nat F.top F.bottom}
    {a : IRI} {k : Nat} (h : F.cmap[a]? = some k) (x : D) :
    (restrict F J).cls a x ↔ J.concept k x := by
  simp [restrict, h]

theorem restrict_role {F : St} {D : Type} {J : ELCompletion.Interp D Nat Nat F.top F.bottom}
    {r : IRI} {k : Nat} (h : F.rmap[r]? = some k) (x y : D) :
    (restrict F J).role r x y ↔ J.role k x y := by
  simp [restrict, h]

theorem restrict_prop {F : St} {D : Type} {J : ELCompletion.Interp D Nat Nat F.top F.bottom}
    {r : ObjProp} (hr : r.isNamed = true) {k : Nat} (h : F.rmap[propIRI r]? = some k)
    (x y : D) : (restrict F J).prop r x y ↔ J.role k x y := by
  cases r with
  | named r => exact restrict_role h x y
  | inv r => simp [ObjProp.isNamed] at hr

section Restrict

variable (F : St) {D : Type} (J : ELCompletion.Interp D Nat Nat F.top F.bottom)
  (hJ : ∀ c ∈ F.out, ELCompletion.satClause J c)

include hJ

mutual

theorem transExpr_restrict : ∀ (E : ClassExpr) (p : Bool) (s : St),
    Le (transExpr E p s).2 F → E.isEL = true →
      Covers (restrict F J) J.concept p E (transExpr E p s).1
  | .cls a, p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      have hk := hle.cmap _ _ (internC_cmap a s)
      cases p <;> intro x <;> simp only [ext_cls, restrict_cls hk] <;> exact id
  | .thing, p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      cases p
      · intro x _; rw [← hle.top]; exact J.top_true x
      · intro x _; simp [ext_thing]
  | .nothing, p, s, hle, _ => by
      simp only [transExpr] at hle ⊢
      cases p
      · intro x h; simp [ext_nothing] at h
      · intro x h; rw [← hle.bottom] at h; exact absurd h (J.bottom_false x)
  | .and cs, false, s, hle, hEL => by
      simp only [transExpr] at hle ⊢
      intro x hx
      rw [Interp.ext_and] at hx
      exact transNegAnd_restrict cs none s hle (isEL_and.1 hEL) trivial x trivial hx
  | .and cs, true, s, hle, hEL => by
      simp only [transExpr] at hle ⊢
      intro x hx
      rw [Interp.ext_and]
      exact transPosAnd_restrict cs _ _ hle (isEL_and.1 hEL) x hx
  | .some r c, false, s, hle, hEL => by
      simp only [transExpr] at hle ⊢
      obtain ⟨hr, hc⟩ := isEL_some.1 hEL
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c false _).trans hle₂
      have hrk := hle₁.rmap _ _ (internR_rmap (propIRI r) s)
      have ih := transExpr_restrict c false _ hle₂ hc
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      rw [ext_some] at hx
      obtain ⟨y, hxy, hy⟩ := hx
      exact hcl x ⟨y, (restrict_prop hr hrk x y).1 hxy, ih y hy⟩
  | .some r c, true, s, hle, hEL => by
      simp only [transExpr] at hle ⊢
      obtain ⟨hr, hc⟩ := isEL_some.1 hEL
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := hle₁.rmap _ _ (internR_rmap (propIRI r) s)
      have ih := transExpr_restrict c true _ hle₂ hc
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      obtain ⟨y, hxy, hy⟩ := hcl x hx
      rw [ext_some]
      exact ⟨y, (restrict_prop hr hrk x y).2 hxy, ih y hy⟩
  | .or _, _, _, _, hEL => by simp [isEL_or] at hEL
  | .not _, _, _, _, hEL => by simp [isEL_not] at hEL
  | .all _ _, _, _, _, hEL => by simp [isEL_all] at hEL

theorem transNegAnd_restrict : ∀ (cs : List ClassExpr) (acc : Option (Nat × ClassExpr))
    (s : St), Le (transNegAnd cs acc s).2 F → (∀ c ∈ cs, c.isEL = true) →
      AccCovers (restrict F J) J.concept acc →
      ∀ x, AccHolds (restrict F J) acc x → (∀ c ∈ cs, (restrict F J).ext c x) →
        J.concept (transNegAnd cs acc s).1 x
  | [], none, s, hle, _, _, x, _, _ => by
      simp only [transNegAnd] at hle ⊢
      rw [← hle.top]; exact J.top_true x
  | [], some (a, e), s, hle, _, hacc, x, hx, _ => by
      simp only [transNegAnd] at hle ⊢
      exact hacc x hx
  | c :: cs, none, s, hle, hEL, _, x, _, hcs => by
      simp only [transNegAnd] at hle ⊢
      have hc := hEL c List.mem_cons_self
      have hle₁ := (transNegAnd_le cs _ _).trans hle
      have ih := transExpr_restrict c false s hle₁ hc
      exact transNegAnd_restrict cs _ _ hle (fun d hd => hEL d (List.mem_cons_of_mem _ hd))
        ih x (hcs c List.mem_cons_self) (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
  | c :: cs, some (a, e), s, hle, hEL, hacc, x, hx, hcs => by
      simp only [transNegAnd] at hle ⊢
      have hc := hEL c List.mem_cons_self
      have hle₃ := (transNegAnd_le cs _ _).trans hle
      have hle₂ := (emit_le _ _).trans hle₃
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transExpr_restrict c false s hle₁ hc
      have hcl := hJ _ (hle₃.out _ (mem_emit _ _))
      refine transNegAnd_restrict cs _ _ hle (fun d hd => hEL d (List.mem_cons_of_mem _ hd))
        ?_ x ?_ (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
      · intro z hz
        rw [ext_and2] at hz
        exact hcl z (hacc z hz.1) (ih z hz.2)
      · show (restrict F J).ext (.and [e, c]) x
        rw [ext_and2]
        exact ⟨hx, hcs c List.mem_cons_self⟩

theorem transPosAnd_restrict : ∀ (cs : List ClassExpr) (X : Nat) (s : St),
    Le (transPosAnd cs X s) F → (∀ c ∈ cs, c.isEL = true) →
      ∀ x, J.concept X x → ∀ c ∈ cs, (restrict F J).ext c x
  | [], _, _, _, _, _, _ => by simp
  | c :: cs, X, s, hle, hEL, x, hx => by
      simp only [transPosAnd] at hle
      have hle₂ := (transPosAnd_le cs _ _).trans hle
      have hle₁ := (emit_le _ _).trans hle₂
      have ih := transExpr_restrict c true s hle₁ (hEL c List.mem_cons_self)
      have hcl := hJ _ (hle₂.out _ (mem_emit _ _))
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact ih x (hcl x hx)
      · exact transPosAnd_restrict cs X _ hle (fun d hd => hEL d (List.mem_cons_of_mem _ hd))
          x hx d hd

end

end Restrict

/-! ## (⇐) A model of the ontology extends to a model of the normal forms -/

/-- The NF interpretation of a model `I`: index `k` stands for the class
expression `F.cdefs[k]`, role index `k` for the composition of
`F.rdefs[k].reverse`. -/
def extend {D : Type} (I : OWL.Interp D) (F : St)
    (hT : F.cdefs[F.top]? = some .thing) (hB : F.cdefs[F.bottom]? = some .nothing) :
    ELCompletion.Interp D Nat Nat F.top F.bottom where
  concept k x := I.ext (F.cdefs[k]?.getD .nothing) x
  role k x y := I.chain ((F.rdefs[k]?.getD []).reverse.map ObjProp.named) x y
  top_true x := by simp [hT, ext_thing]
  bottom_false x := by simp [hB, ext_nothing]

theorem chain_append {D : Type} (I : OWL.Interp D) :
    ∀ (l₁ l₂ : List ObjProp) (x z : D),
      I.chain (l₁ ++ l₂) x z ↔ ∃ y, I.chain l₁ x y ∧ I.chain l₂ y z
  | [], l₂, x, z => by simp [Interp.chain]
  | r :: l₁, l₂, x, z => by
      simp only [List.cons_append, Interp.chain, chain_append I l₁ l₂]
      constructor
      · rintro ⟨y, hxy, w, hyw, hwz⟩; exact ⟨w, ⟨y, hxy, hyw⟩, hwz⟩
      · rintro ⟨w, ⟨y, hxy, hyw⟩, hwz⟩; exact ⟨y, hxy, w, hyw, hwz⟩

theorem chain_single {D : Type} (I : OWL.Interp D) (r : IRI) (x y : D) :
    I.chain [ObjProp.named r] x y ↔ I.role r x y := by
  simp [Interp.chain, Interp.prop]

section Extend

variable {D : Type} (I : OWL.Interp D) (F : St)
  (hT : F.cdefs[F.top]? = some .thing) (hB : F.cdefs[F.bottom]? = some .nothing)

theorem extend_concept {k : Nat} {e : ClassExpr} (h : F.cdefs[k]? = some e) (x : D) :
    (extend I F hT hB).concept k x ↔ I.ext e x := by
  simp [extend, h]

theorem extend_role {k : Nat} {rev : List IRI} (h : F.rdefs[k]? = some rev) (x y : D) :
    (extend I F hT hB).role k x y ↔ I.chain (rev.reverse.map ObjProp.named) x y := by
  simp [extend, h]

theorem extend_role_named {k : Nat} {r : IRI} (h : F.rdefs[k]? = some [r]) (x y : D) :
    (extend I F hT hB).role k x y ↔ I.role r x y := by
  rw [extend_role I F hT hB h]; simpa using chain_single I r x y

theorem extend_prop {k : Nat} {r : ObjProp} (hr : r.isNamed = true)
    (h : F.rdefs[k]? = some [propIRI r]) (x y : D) :
    (extend I F hT hB).role k x y ↔ I.prop r x y := by
  cases r with
  | named r => exact extend_role_named I F hT hB h x y
  | inv r => simp [ObjProp.isNamed] at hr

/-- Every clause emitted so far holds in `extend I F`. -/
def Good (s : St) : Prop := ∀ c ∈ s.out, ELCompletion.satClause (extend I F hT hB) c

theorem good_emit {s : St} {c : NF} (hs : Good I F hT hB s)
    (hc : ELCompletion.satClause (extend I F hT hB) c) : Good I F hT hB (emit c s) := by
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact hc
  · exact hs d hd

def AccExact : Option (Nat × ClassExpr) → Prop
  | none => True
  | some (a, e) => ∀ x, (extend I F hT hB).concept a x ↔ I.ext e x

mutual

theorem transExpr_extend : ∀ (E : ClassExpr) (p : Bool) (s : St), WF s →
    Le (transExpr E p s).2 F → E.isEL = true →
      (Good I F hT hB s → Good I F hT hB (transExpr E p s).2) ∧
      ∀ x, (extend I F hT hB).concept (transExpr E p s).1 x ↔ I.ext E x
  | .cls a, p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      refine ⟨fun h => ?_, extend_concept I F hT hB (hle.cdefs _ _ (internC_cdefs hs))⟩
      intro c hc; rw [internC_out] at hc; exact h c hc
  | .thing, p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      refine ⟨id, fun x => ?_⟩
      rw [← hle.top, extend_concept I F hT hB hT]
  | .nothing, p, s, hs, hle, _ => by
      simp only [transExpr] at hle ⊢
      refine ⟨id, fun x => ?_⟩
      rw [← hle.bottom, extend_concept I F hT hB hB]
  | .and cs, false, s, hs, hle, hEL => by
      simp only [transExpr] at hle ⊢
      have := transNegAnd_extend cs none s hs hle (isEL_and.1 hEL) trivial
      refine ⟨this.1, fun x => ?_⟩
      rw [this.2 x, Interp.ext_and]
      simp [AccHolds]
  | .and cs, true, s, hs, hle, hEL => by
      simp only [transExpr] at hle ⊢
      have hle₁ := (transPosAnd_le cs _ _).trans hle
      have hX := extend_concept I F hT hB (hle₁.cdefs _ _ (freshC_cdefs (.and cs) s))
      refine ⟨fun hg => transPosAnd_extend cs _ _ (freshC_wf hs) hle (isEL_and.1 hEL)
        (fun x hx => (Interp.ext_and _ _ _).1 ((hX x).1 hx)) hg, hX⟩
  | .some r c, false, s, hs, hle, hEL => by
      simp only [transExpr] at hle ⊢
      obtain ⟨hr, hc⟩ := isEL_some.1 hEL
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c false _).trans hle₂
      have hs₁ := internR_wf (r := propIRI r) hs
      have hrk := extend_prop I F hT hB hr (hle₁.rdefs _ _ (internR_rdefs hs))
      have ih := transExpr_extend c false _ hs₁ hle₂ hc
      have hX := extend_concept I F hT hB (hle₃.cdefs _ _ (freshC_cdefs (.some r c) _))
      refine ⟨fun hg => good_emit I F hT hB ?_ ?_, hX⟩
      · have := ih.1 (by intro d hd; rw [internR_out] at hd; exact hg d hd)
        exact this
      · intro x ⟨y, hxy, hy⟩
        rw [hX, ext_some]
        exact ⟨y, (hrk x y).1 hxy, (ih.2 y).1 hy⟩
  | .some r c, true, s, hs, hle, hEL => by
      simp only [transExpr] at hle ⊢
      obtain ⟨hr, hc⟩ := isEL_some.1 hEL
      have hle₃ := (emit_le _ _).trans hle
      have hle₂ := (freshC_le _ _).trans hle₃
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hs₁ := internR_wf (r := propIRI r) hs
      have hrk := extend_prop I F hT hB hr (hle₁.rdefs _ _ (internR_rdefs hs))
      have ih := transExpr_extend c true _ hs₁ hle₂ hc
      have hX := extend_concept I F hT hB (hle₃.cdefs _ _ (freshC_cdefs (.some r c) _))
      refine ⟨fun hg => good_emit I F hT hB ?_ ?_, hX⟩
      · have := ih.1 (by intro d hd; rw [internR_out] at hd; exact hg d hd)
        exact this
      · intro x hx
        rw [hX, ext_some] at hx
        obtain ⟨y, hxy, hy⟩ := hx
        exact ⟨y, (hrk x y).2 hxy, (ih.2 y).2 hy⟩
  | .or _, _, _, _, _, hEL => by simp [isEL_or] at hEL
  | .not _, _, _, _, _, hEL => by simp [isEL_not] at hEL
  | .all _ _, _, _, _, _, hEL => by simp [isEL_all] at hEL

theorem transNegAnd_extend : ∀ (cs : List ClassExpr) (acc : Option (Nat × ClassExpr))
    (s : St), WF s → Le (transNegAnd cs acc s).2 F → (∀ c ∈ cs, c.isEL = true) →
      AccExact I F hT hB acc →
      (Good I F hT hB s → Good I F hT hB (transNegAnd cs acc s).2) ∧
      ∀ x, (extend I F hT hB).concept (transNegAnd cs acc s).1 x ↔
        AccHolds I acc x ∧ ∀ c ∈ cs, I.ext c x
  | [], none, s, _, hle, _, _ => by
      simp only [transNegAnd] at hle ⊢
      refine ⟨id, fun x => ?_⟩
      rw [← hle.top, extend_concept I F hT hB hT]
      simp [AccHolds, ext_thing]
  | [], some (a, e), s, _, hle, _, hacc => by
      simp only [transNegAnd] at hle ⊢
      exact ⟨id, fun x => by simp [AccHolds, hacc x]⟩
  | c :: cs, none, s, hs, hle, hEL, _ => by
      simp only [transNegAnd] at hle ⊢
      have hle₁ := (transNegAnd_le cs _ _).trans hle
      have ih := transExpr_extend c false s hs hle₁ (hEL c List.mem_cons_self)
      have := transNegAnd_extend cs _ _ (transExpr_wf c false s hs) hle
        (fun d hd => hEL d (List.mem_cons_of_mem _ hd)) ih.2
      refine ⟨fun hg => this.1 (ih.1 hg), fun x => ?_⟩
      rw [this.2 x]
      simp [AccHolds]
  | c :: cs, some (a, e), s, hs, hle, hEL, hacc => by
      simp only [transNegAnd] at hle ⊢
      have hle₃ := (transNegAnd_le cs _ _).trans hle
      have hle₂ := (emit_le _ _).trans hle₃
      have hle₁ := (freshC_le _ _).trans hle₂
      have ih := transExpr_extend c false s hs hle₁ (hEL c List.mem_cons_self)
      have hX := extend_concept I F hT hB (hle₂.cdefs _ _ (freshC_cdefs (.and [e, c]) _))
      have hacc' : AccExact I F hT hB (some ((freshC (.and [e, c]) (transExpr c false s).2).1,
          .and [e, c])) := hX
      have := transNegAnd_extend cs _ _ (emit_wf (freshC_wf (transExpr_wf c false s hs))) hle
        (fun d hd => hEL d (List.mem_cons_of_mem _ hd)) hacc'
      refine ⟨fun hg => this.1 (good_emit I F hT hB (ih.1 hg) ?_), fun x => ?_⟩
      · intro x ha hc
        rw [hX, ext_and2]
        exact ⟨(hacc x).1 ha, (ih.2 x).1 hc⟩
      · rw [this.2 x]
        simp only [AccHolds, ext_and2, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem transPosAnd_extend : ∀ (cs : List ClassExpr) (X : Nat) (s : St), WF s →
    Le (transPosAnd cs X s) F → (∀ c ∈ cs, c.isEL = true) →
      (∀ x, (extend I F hT hB).concept X x → ∀ c ∈ cs, I.ext c x) →
      Good I F hT hB s → Good I F hT hB (transPosAnd cs X s)
  | [], _, _, _, _, _, _, hg => by simpa [transPosAnd] using hg
  | c :: cs, X, s, hs, hle, hEL, hX, hg => by
      simp only [transPosAnd] at hle ⊢
      have hle₂ := (transPosAnd_le cs _ _).trans hle
      have hle₁ := (emit_le _ _).trans hle₂
      have ih := transExpr_extend c true s hs hle₁ (hEL c List.mem_cons_self)
      refine transPosAnd_extend cs X _ (emit_wf (transExpr_wf c true s hs)) hle
        (fun d hd => hEL d (List.mem_cons_of_mem _ hd))
        (fun x hx d hd => hX x hx d (List.mem_cons_of_mem _ hd))
        (good_emit I F hT hB (ih.1 hg) ?_)
      intro x hx
      exact (ih.2 x).2 (hX x hx c List.mem_cons_self)

end

end Extend

/-! ## Axiom-level helpers -/

theorem mem_foldl {α β : Type} (g : List β → α → List β) (P : α → β → Prop)
    (hg : ∀ o m c, c ∈ g o m ↔ c ∈ o ∨ P m c) :
    ∀ (l : List α) (o : List β) (c : β), c ∈ l.foldl g o ↔ c ∈ o ∨ ∃ m ∈ l, P m c
  | [], o, c => by simp
  | m :: l, o, c => by
      rw [List.foldl_cons, mem_foldl g P hg l, hg]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem mem_emitEquiv (negs poss : List (ClassExpr × Nat)) (out : List NF) (c : NF) :
    c ∈ emitEquiv negs poss out ↔
      c ∈ out ∨ ∃ n ∈ negs, ∃ p ∈ poss, n.2 ≠ p.2 ∧ c = .nf1 n.2 p.2 := by
  unfold emitEquiv
  refine mem_foldl _ (fun n c => ∃ p ∈ poss, n.2 ≠ p.2 ∧ c = .nf1 n.2 p.2)
    (fun o n c => ?_) negs out c
  refine (mem_foldl _ (fun p c => n.2 ≠ p.2 ∧ c = .nf1 n.2 p.2) (fun o p c => ?_) poss o c)
  split <;> simp_all [or_comm]

theorem mem_emitRoleEquiv (roles : List (ObjProp × Nat)) (out : List NF) (c : NF) :
    c ∈ emitRoleEquiv roles out ↔
      c ∈ out ∨ ∃ a ∈ roles, ∃ b ∈ roles, a.2 ≠ b.2 ∧ c = .nf6 a.2 b.2 := by
  unfold emitRoleEquiv
  refine mem_foldl _ (fun a c => ∃ b ∈ roles, a.2 ≠ b.2 ∧ c = .nf6 a.2 b.2)
    (fun o a c => ?_) roles out c
  refine (mem_foldl _ (fun b c => a.2 ≠ b.2 ∧ c = .nf6 a.2 b.2) (fun o b c => ?_) roles o c)
  split <;> simp_all [or_comm]

theorem pair_sublist_cons {α : Type} {m n h : α} {t : List α} :
    List.Sublist [m, n] (h :: t) ↔ (m = h ∧ n ∈ t) ∨ List.Sublist [m, n] t := by
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h' | ⟨r, hr, h'⟩)
    · exact Or.inr h'
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inl ⟨rfl, List.singleton_sublist.1 h'⟩
  · rintro (⟨rfl, hn⟩ | h')
    · exact Or.inr ⟨[n], rfl, List.singleton_sublist.2 hn⟩
    · exact Or.inl h'

theorem mem_emitDisjoint (b : Nat) :
    ∀ (L : List (ClassExpr × Nat)) (o : List NF) (c : NF),
      c ∈ emitDisjoint b L o ↔ c ∈ o ∨ ∃ m n, List.Sublist [m, n] L ∧ c = .nf2 m.2 n.2 b
  | [], o, c => by simp [emitDisjoint]
  | h :: t, o, c => by
      rw [emitDisjoint, mem_emitDisjoint b t,
        mem_foldl _ (fun m c => c = .nf2 h.2 m.2 b) (fun o m c => by simp [or_comm]) t o c]
      simp only [pair_sublist_cons]
      constructor
      · rintro ((h₁ | ⟨m, hm, rfl⟩) | ⟨m, n, hmn, rfl⟩)
        · exact Or.inl h₁
        · exact Or.inr ⟨h, m, Or.inl ⟨rfl, hm⟩, rfl⟩
        · exact Or.inr ⟨m, n, Or.inr hmn, rfl⟩
      · rintro (h₁ | ⟨m, n, (⟨rfl, hn⟩ | hmn), rfl⟩)
        · exact Or.inl (Or.inl h₁)
        · exact Or.inl (Or.inr ⟨n, hn, rfl⟩)
        · exact Or.inr ⟨m, n, hmn, rfl⟩

theorem setOut_le {s : St} {o : List NF} (h : ∀ c ∈ s.out, c ∈ o) :
    Le s { s with out := o } :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, h, rfl, rfl⟩

theorem setOut_wf {s : St} {o : List NF} (hs : WF s) : WF { s with out := o } :=
  ⟨hs.cmap, hs.rmap⟩

theorem transMembers_le (p : Bool) : ∀ (cs : List ClassExpr) (s : St) acc,
    Le s (transMembers p cs s acc).2
  | [], s, acc => by simp only [transMembers]; exact Le.rfl
  | c :: cs, s, acc => by
      simp only [transMembers]
      exact (transExpr_le c p s).trans (transMembers_le p cs _ _)

theorem transMembers_wf (p : Bool) : ∀ (cs : List ClassExpr) (s : St) acc,
    WF s → WF (transMembers p cs s acc).2
  | [], s, acc, hs => by simp only [transMembers]; exact hs
  | c :: cs, s, acc, hs => by
      simp only [transMembers]
      exact transMembers_wf p cs _ _ (transExpr_wf c p s hs)

theorem transMembers_fst (p : Bool) : ∀ (cs : List ClassExpr) (s : St) acc,
    (transMembers p cs s acc).1.map Prod.fst = acc.reverse.map Prod.fst ++ cs
  | [], s, acc => by simp [transMembers]
  | c :: cs, s, acc => by
      simp only [transMembers]
      rw [transMembers_fst p cs]
      simp

theorem internRoles_le : ∀ (rs : List ObjProp) (s : St) acc, Le s (internRoles rs s acc).2
  | [], s, acc => by simp only [internRoles]; exact Le.rfl
  | r :: rs, s, acc => by
      simp only [internRoles]
      exact (internR_le _ s).trans (internRoles_le rs _ _)

theorem internRoles_wf : ∀ (rs : List ObjProp) (s : St) acc, WF s → WF (internRoles rs s acc).2
  | [], s, acc, hs => by simp only [internRoles]; exact hs
  | r :: rs, s, acc, hs => by
      simp only [internRoles]
      exact internRoles_wf rs _ _ (internR_wf hs)

/-- Every role of `internRoles` has its index in the final maps and tables. -/
def RoleOK (F : St) (q : ObjProp × Nat) : Prop :=
  F.rmap[propIRI q.1]? = some q.2 ∧ F.rdefs[q.2]? = some [propIRI q.1]

theorem internRoles_ok (F : St) : ∀ (rs : List ObjProp) (s : St) acc, WF s →
    Le (internRoles rs s acc).2 F → (∀ q ∈ acc, RoleOK F q) →
      (∀ q ∈ (internRoles rs s acc).1, RoleOK F q ∧ (q ∈ acc ∨ q.1 ∈ rs)) ∧
      (∀ r ∈ rs, ∃ q ∈ (internRoles rs s acc).1, q.1 = r)
  | [], s, acc, _, _, hacc => by
      simp only [internRoles]
      exact ⟨fun q hq => ⟨hacc q hq, Or.inl hq⟩, by simp⟩
  | r :: rs, s, acc, hs, hle, hacc => by
      simp only [internRoles] at hle ⊢
      have hle₁ := (internRoles_le rs _ _).trans hle
      have hq : RoleOK F (r, (internR (propIRI r) s).1) :=
        ⟨hle₁.rmap _ _ (internR_rmap _ s), hle₁.rdefs _ _ (internR_rdefs hs)⟩
      have ih := internRoles_ok F rs _ _ (internR_wf hs) hle (by
        intro q hq'
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact hq
        · exact hacc q hq')
      refine ⟨fun q hq' => ?_, ?_⟩
      · obtain ⟨hok, hor⟩ := ih.1 q hq'
        refine ⟨hok, ?_⟩
        rcases hor with hor | hor
        · rcases List.mem_cons.1 hor with rfl | hor
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hor
        · exact Or.inr (List.mem_cons_of_mem _ hor)
      · intro r' hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · obtain ⟨hok, hor⟩ := hq
          -- the role `r` was pushed onto the accumulator; it stays in the result
          have : ∀ (rs : List ObjProp) (s : St) acc, ∀ q ∈ acc, q ∈ (internRoles rs s acc).1 := by
            intro rs
            induction rs with
            | nil => intro s acc q hq; simpa [internRoles] using hq
            | cons r rs ih' =>
                intro s acc q hq
                simp only [internRoles]
                exact ih' _ _ q (List.mem_cons_of_mem _ hq)
          exact ⟨_, this rs _ _ _ List.mem_cons_self, rfl⟩
        · exact ih.2 r' hr'

theorem transChain_le (sup : Nat) : ∀ (acc : Nat) (pre rest : List IRI) (s : St),
    Le s (transChain sup acc pre rest s)
  | acc, _, [], s => by simp only [transChain]; exact emit_le _ _
  | acc, _, [r], s => by
      simp only [transChain]; exact (internR_le r s).trans (emit_le _ _)
  | acc, pre, r :: r' :: rest, s => by
      simp only [transChain]
      exact (internR_le r s).trans ((freshR_le _ _).trans
        ((emit_le _ _).trans (transChain_le sup _ _ _ _)))

theorem transChain_wf (sup : Nat) : ∀ (acc : Nat) (pre rest : List IRI) (s : St),
    WF s → WF (transChain sup acc pre rest s)
  | acc, _, [], s, hs => by simp only [transChain]; exact emit_wf hs
  | acc, _, [r], s, hs => by
      simp only [transChain]; exact emit_wf (internR_wf hs)
  | acc, pre, r :: r' :: rest, s, hs => by
      simp only [transChain]
      exact transChain_wf sup _ _ _ _ (emit_wf (freshR_wf (internR_wf hs)))

theorem transAxiom_le (s : St) (ax : Axiom) : Le s (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom]
      exact (transExpr_le c false s).trans ((transExpr_le d true _).trans (emit_le _ _))
  | equivalentClasses cs =>
      simp only [transAxiom]
      refine (transMembers_le false cs s []).trans ((transMembers_le true cs _ []).trans
        (setOut_le fun c hc => (mem_emitEquiv _ _ _ c).2 (Or.inl hc)))
  | disjointClasses cs =>
      simp only [transAxiom]
      refine (transMembers_le false cs s []).trans
        (setOut_le fun c hc => (mem_emitDisjoint _ _ _ c).2 (Or.inl hc))
  | domain r c =>
      simp only [transAxiom]
      exact (internR_le _ s).trans ((transExpr_le c true _).trans (emit_le _ _))
  | subObjectPropertyOf rs r =>
      simp only [transAxiom]
      cases rs with
      | nil => exact (internR_le _ s).trans (emit_le _ _)
      | cons r1 rest =>
          exact (internR_le _ s).trans ((internR_le _ _).trans (transChain_le _ _ _ _ _))
  | equivalentObjectProperties rs =>
      simp only [transAxiom]
      exact (internRoles_le rs s []).trans
        (setOut_le fun c hc => (mem_emitRoleEquiv _ _ c).2 (Or.inl hc))
  | transitive r =>
      simp only [transAxiom]; exact (internR_le _ s).trans (emit_le _ _)
  | range _ _ | inverseObjectProperties _ _ | symmetric _ | declareClass _
  | declareObjectProperty _ => simp only [transAxiom]; exact Le.rfl

theorem transAxiom_wf {s : St} (hs : WF s) (ax : Axiom) : WF (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom]
      exact emit_wf (transExpr_wf d true _ (transExpr_wf c false s hs))
  | equivalentClasses cs =>
      simp only [transAxiom]
      exact setOut_wf (transMembers_wf true cs _ [] (transMembers_wf false cs s [] hs))
  | disjointClasses cs =>
      simp only [transAxiom]
      exact setOut_wf (transMembers_wf false cs s [] hs)
  | domain r c =>
      simp only [transAxiom]
      exact emit_wf (transExpr_wf c true _ (internR_wf hs))
  | subObjectPropertyOf rs r =>
      simp only [transAxiom]
      cases rs with
      | nil => exact emit_wf (internR_wf hs)
      | cons r1 rest => exact transChain_wf _ _ _ _ _ (internR_wf (internR_wf hs))
  | equivalentObjectProperties rs =>
      simp only [transAxiom]
      exact setOut_wf (internRoles_wf rs s [] hs)
  | transitive r =>
      simp only [transAxiom]; exact emit_wf (internR_wf hs)
  | range _ _ | inverseObjectProperties _ _ | symmetric _ | declareClass _
  | declareObjectProperty _ => simp only [transAxiom]; exact hs

theorem map_named_propIRI : ∀ (rs : List ObjProp), (∀ r ∈ rs, r.isNamed = true) →
    (rs.map propIRI).map ObjProp.named = rs
  | [], _ => rfl
  | r :: rs, h => by
      have hr := h r List.mem_cons_self
      cases r with
      | named r =>
          simp only [List.map_cons, propIRI, List.cons.injEq, true_and]
          exact map_named_propIRI rs (fun q hq => h q (List.mem_cons_of_mem _ hq))
      | inv r => simp [ObjProp.isNamed] at hr

/-! ## (⇒) at the axiom level -/

section RestrictAxiom

variable (F : St) {D : Type} (J : ELCompletion.Interp D Nat Nat F.top F.bottom)
  (hJ : ∀ c ∈ F.out, ELCompletion.satClause J c)

include hJ

theorem transMembers_restrict (p : Bool) : ∀ (cs : List ClassExpr) (s : St) acc,
    Le (transMembers p cs s acc).2 F → (∀ c ∈ cs, c.isEL = true) →
    (∀ q ∈ acc, Covers (restrict F J) J.concept p q.1 q.2) →
    ∀ q ∈ (transMembers p cs s acc).1, Covers (restrict F J) J.concept p q.1 q.2
  | [], s, acc, _, _, hacc => by
      simp only [transMembers]; intro q hq; exact hacc q (List.mem_reverse.1 hq)
  | c :: cs, s, acc, hle, hEL, hacc => by
      simp only [transMembers] at hle ⊢
      have hle₁ := (transMembers_le p cs _ _).trans hle
      have ih := transExpr_restrict F J hJ c p s hle₁ (hEL c List.mem_cons_self)
      refine transMembers_restrict p cs _ _ hle (fun d hd => hEL d (List.mem_cons_of_mem _ hd)) ?_
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ih
      · exact hacc q hq

theorem transChain_restrict (sup : Nat) : ∀ (acc : Nat) (pre rest : List IRI) (s : St),
    Le (transChain sup acc pre rest s) F →
    (∀ x y, (restrict F J).chain (pre.reverse.map .named) x y → J.role acc x y) →
    ∀ x y, (restrict F J).chain ((pre.reverse ++ rest).map .named) x y → J.role sup x y
  | acc, pre, [], s, hle, hacc => by
      simp only [transChain] at hle
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y h
      simp only [List.append_nil] at h
      exact hcl x y (hacc x y h)
  | acc, pre, [r], s, hle, hacc => by
      simp only [transChain] at hle
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      have hrk := ((emit_le _ _).trans hle).rmap _ _ (internR_rmap r s)
      intro x y h
      rw [List.map_append, chain_append] at h
      obtain ⟨w, hxw, hwy⟩ := h
      simp only [List.map_cons, List.map_nil, chain_single] at hwy
      exact hcl x w y (hacc x w hxw) ((restrict_role hrk w y).1 hwy)
  | acc, pre, r :: r' :: rest, s, hle, hacc => by
      simp only [transChain] at hle
      have hle₂ := (transChain_le _ _ _ _ _).trans hle
      have hcl := hJ _ (hle₂.out _ (mem_emit _ _))
      have hrk := ((freshR_le _ _).trans ((emit_le _ _).trans hle₂)).rmap _ _
        (internR_rmap r s)
      have := transChain_restrict sup _ (r :: pre) (r' :: rest) _ hle (by
        intro x y h
        rw [List.reverse_cons, List.map_append, chain_append] at h
        obtain ⟨w, hxw, hwy⟩ := h
        simp only [List.map_cons, List.map_nil, chain_single] at hwy
        exact hcl x w y (hacc x w hxw) ((restrict_role hrk w y).1 hwy))
      intro x y h
      apply this x y
      simpa using h

theorem transAxiom_restrict (s : St) (hs : WF s) (ax : Axiom)
    (hle : Le (transAxiom s ax) F) (hEL : ax.isEL = true) : (restrict F J).sat ax := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom] at hle
      simp only [Axiom.isEL, Bool.and_eq_true] at hEL
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le d true _).trans hle₂
      have hn := transExpr_restrict F J hJ c false s hle₁ hEL.1
      have hp := transExpr_restrict F J hJ d true _ hle₂ hEL.2
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x hx
      exact hp x (hcl x (hn x hx))
  | equivalentClasses cs =>
      simp only [transAxiom] at hle
      simp only [Axiom.isEL, List.all_eq_true] at hEL
      have hle₂ := (setOut_le fun c hc => (mem_emitEquiv _ _ _ c).2 (Or.inl hc)).trans hle
      have hle₁ := (transMembers_le true cs _ []).trans hle₂
      have hN := transMembers_restrict F J hJ false cs s [] hle₁ hEL (by simp)
      have hP := transMembers_restrict F J hJ true cs _ [] hle₂ hEL (by simp)
      have hNf := transMembers_fst false cs s []
      have hPf := transMembers_fst true cs (transMembers false cs s []).2 []
      simp only [List.reverse_nil, List.map_nil, List.nil_append] at hNf hPf
      intro c hc d hd x hx
      obtain ⟨qn, hqn, rfl⟩ := List.mem_map.1 (hNf ▸ hc)
      obtain ⟨qp, hqp, rfl⟩ := List.mem_map.1 (hPf ▸ hd)
      have h₁ := hN qn hqn x hx
      apply hP qp hqp x
      by_cases hq : qn.2 = qp.2
      · exact hq ▸ h₁
      · exact hJ _ (hle.out _ ((mem_emitEquiv _ _ _ _).2 (Or.inr ⟨qn, hqn, qp, hqp, hq, rfl⟩)))
          x h₁
  | disjointClasses cs =>
      simp only [transAxiom] at hle
      simp only [Axiom.isEL, List.all_eq_true] at hEL
      have hle₁ := (setOut_le fun c hc => (mem_emitDisjoint _ _ _ c).2 (Or.inl hc)).trans hle
      have hN := transMembers_restrict F J hJ false cs s [] hle₁ hEL (by simp)
      have hNf := transMembers_fst false cs s []
      simp only [List.reverse_nil, List.map_nil, List.nil_append] at hNf
      show cs.Pairwise _
      rw [← hNf, List.pairwise_map, List.pairwise_iff_forall_sublist]
      intro m n hmn x ⟨hm, hn⟩
      have hmL : m ∈ (transMembers false cs s []).1 := hmn.subset (by simp)
      have hnL : n ∈ (transMembers false cs s []).1 := hmn.subset (by simp)
      have hcl := hJ _ (hle.out _ ((mem_emitDisjoint _ _ _ _).2 (Or.inr ⟨m, n, hmn, rfl⟩)))
      have := hcl x (hN m hmL x hm) (hN n hnL x hn)
      rw [← hle₁.bottom] at this
      exact J.bottom_false x this
  | domain r c =>
      simp only [transAxiom] at hle
      simp only [Axiom.isEL, Bool.and_eq_true] at hEL
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := hle₁.rmap _ _ (internR_rmap (propIRI r) s)
      have hp := transExpr_restrict F J hJ c true _ hle₂ hEL.2
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y hxy
      apply hp x
      apply hcl x
      refine ⟨y, (restrict_prop hEL.1 hrk x y).1 hxy, ?_⟩
      rw [← hle₂.top]; exact J.top_true y
  | subObjectPropertyOf rs r =>
      simp only [Axiom.isEL, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at hEL
      obtain ⟨⟨hne, hrs⟩, hr⟩ := hEL
      cases rs with
      | nil => exact absurd rfl hne
      | cons r1 rest =>
          simp only [transAxiom] at hle
          have hle₂ := (transChain_le _ _ _ _ _).trans hle
          have hle₁ := (internR_le _ _).trans hle₂
          have hrk := hle₁.rmap _ _ (internR_rmap (propIRI r) s)
          have hbk := hle₂.rmap _ _ (internR_rmap (propIRI r1) (internR (propIRI r) s).2)
          have := transChain_restrict F J hJ _ _ [propIRI r1] (rest.map propIRI) _ hle (by
            intro x y h
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
              List.map_nil, chain_single] at h
            exact (restrict_role hbk x y).1 h)
          intro x y h
          rw [← map_named_propIRI (r1 :: rest) hrs] at h
          exact (restrict_prop hr hrk x y).2 (this x y (by simpa using h))
  | equivalentObjectProperties rs =>
      simp only [transAxiom] at hle
      simp only [Axiom.isEL, List.all_eq_true] at hEL
      have hle₁ := (setOut_le fun c hc => (mem_emitRoleEquiv _ _ c).2 (Or.inl hc)).trans hle
      have hok := internRoles_ok F rs s [] hs hle₁ (by simp)
      intro r hr r' hr' x y hxy
      obtain ⟨q, hq, rfl⟩ := hok.2 r hr
      obtain ⟨q', hq', rfl⟩ := hok.2 r' hr'
      have h₁ := (restrict_prop (hEL _ hr) (hok.1 q hq).1.1 x y).1 hxy
      apply (restrict_prop (hEL _ hr') (hok.1 q' hq').1.1 x y).2
      by_cases hqq : q.2 = q'.2
      · exact hqq ▸ h₁
      · exact hJ _ (hle.out _ ((mem_emitRoleEquiv _ _ _).2 (Or.inr ⟨q, hq, q', hq', hqq, rfl⟩)))
          x y h₁
  | transitive r =>
      simp only [transAxiom] at hle
      simp only [Axiom.isEL] at hEL
      have hrk := ((emit_le _ _).trans hle).rmap _ _ (internR_rmap (propIRI r) s)
      have hcl := hJ _ (hle.out _ (mem_emit _ _))
      intro x y z hxy hyz
      exact (restrict_prop hEL hrk x z).2 (hcl x y z ((restrict_prop hEL hrk x y).1 hxy)
        ((restrict_prop hEL hrk y z).1 hyz))
  | range _ _ | inverseObjectProperties _ _ | symmetric _ => simp [Axiom.isEL] at hEL
  | declareClass _ | declareObjectProperty _ => trivial

end RestrictAxiom

/-! ## (⇐) at the axiom level -/

section ExtendAxiom

variable {D : Type} (I : OWL.Interp D) (F : St)
  (hT : F.cdefs[F.top]? = some .thing) (hB : F.cdefs[F.bottom]? = some .nothing)

theorem transMembers_extend (p : Bool) : ∀ (cs : List ClassExpr) (s : St) acc, WF s →
    Le (transMembers p cs s acc).2 F → (∀ c ∈ cs, c.isEL = true) →
    (∀ q ∈ acc, ∀ x, (extend I F hT hB).concept q.2 x ↔ I.ext q.1 x) →
    (Good I F hT hB s → Good I F hT hB (transMembers p cs s acc).2) ∧
    ∀ q ∈ (transMembers p cs s acc).1, ∀ x, (extend I F hT hB).concept q.2 x ↔ I.ext q.1 x
  | [], s, acc, _, _, _, hacc => by
      simp only [transMembers]
      exact ⟨id, fun q hq => hacc q (List.mem_reverse.1 hq)⟩
  | c :: cs, s, acc, hs, hle, hEL, hacc => by
      simp only [transMembers] at hle ⊢
      have hle₁ := (transMembers_le p cs _ _).trans hle
      have ih := transExpr_extend I F hT hB c p s hs hle₁ (hEL c List.mem_cons_self)
      have := transMembers_extend p cs _ _ (transExpr_wf c p s hs) hle
        (fun d hd => hEL d (List.mem_cons_of_mem _ hd)) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact ih.2
          · exact hacc q hq)
      exact ⟨fun hg => this.1 (ih.1 hg), this.2⟩

theorem good_internR {r : IRI} {s : St} (hg : Good I F hT hB s) :
    Good I F hT hB (internR r s).2 := by
  intro c hc; rw [internR_out] at hc; exact hg c hc

theorem transChain_extend (sup : Nat) : ∀ (acc : Nat) (pre rest : List IRI) (s : St), WF s →
    Le (transChain sup acc pre rest s) F → F.rdefs[acc]? = some pre →
    (∀ x y, I.chain ((pre.reverse ++ rest).map .named) x y →
      (extend I F hT hB).role sup x y) →
    Good I F hT hB s → Good I F hT hB (transChain sup acc pre rest s)
  | acc, pre, [], s, _, hle, hacc, H, hg => by
      simp only [transChain] at hle ⊢
      refine good_emit I F hT hB hg ?_
      intro x y hxy
      rw [extend_role I F hT hB hacc] at hxy
      exact H x y (by simpa using hxy)
  | acc, pre, [r], s, hs, hle, hacc, H, hg => by
      simp only [transChain] at hle ⊢
      have hrk := ((emit_le _ _).trans hle).rdefs _ _ (internR_rdefs (r := r) hs)
      refine good_emit I F hT hB (good_internR I F hT hB hg) ?_
      intro x w y hxw hwy
      rw [extend_role I F hT hB hacc] at hxw
      rw [extend_role_named I F hT hB hrk] at hwy
      apply H x y
      rw [List.map_append, chain_append]
      exact ⟨w, hxw, (chain_single I r w y).2 hwy⟩
  | acc, pre, r :: r' :: rest, s, hs, hle, hacc, H, hg => by
      simp only [transChain] at hle ⊢
      have hle₂ := (transChain_le _ _ _ _ _).trans hle
      have hle₁ := (emit_le _ _).trans hle₂
      have hrk := ((freshR_le _ _).trans hle₁).rdefs _ _ (internR_rdefs (r := r) hs)
      have huk := hle₁.rdefs _ _ (freshR_rdefs (r :: pre) (internR r s).2)
      refine transChain_extend sup _ (r :: pre) (r' :: rest) _
        (emit_wf (freshR_wf (internR_wf hs))) hle huk ?_ ?_
      · intro x y h
        exact H x y (by simpa using h)
      · refine good_emit I F hT hB (good_internR I F hT hB hg) ?_
        intro x w y hxw hwy
        rw [extend_role I F hT hB hacc] at hxw
        rw [extend_role_named I F hT hB hrk] at hwy
        rw [extend_role I F hT hB huk, List.reverse_cons, List.map_append, chain_append]
        exact ⟨w, hxw, (chain_single I r w y).2 hwy⟩

theorem transAxiom_extend (s : St) (hs : WF s) (ax : Axiom)
    (hle : Le (transAxiom s ax) F) (hEL : ax.isEL = true) (hI : I.sat ax)
    (hg : Good I F hT hB s) : Good I F hT hB (transAxiom s ax) := by
  cases ax with
  | subClassOf c d =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isEL, Bool.and_eq_true] at hEL
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le d true _).trans hle₂
      have hn := transExpr_extend I F hT hB c false s hs hle₁ hEL.1
      have hp := transExpr_extend I F hT hB d true _ (transExpr_wf c false s hs) hle₂ hEL.2
      exact good_emit I F hT hB (hp.1 (hn.1 hg))
        (fun x hx => (hp.2 x).2 (hI x ((hn.2 x).1 hx)))
  | equivalentClasses cs =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isEL, List.all_eq_true] at hEL
      have hle₂ := (setOut_le fun c hc => (mem_emitEquiv _ _ _ c).2 (Or.inl hc)).trans hle
      have hle₁ := (transMembers_le true cs _ []).trans hle₂
      have hN := transMembers_extend I F hT hB false cs s [] hs hle₁ hEL (by simp)
      have hP := transMembers_extend I F hT hB true cs _ []
        (transMembers_wf false cs s [] hs) hle₂ hEL (by simp)
      have hNf := transMembers_fst false cs s []
      have hPf := transMembers_fst true cs (transMembers false cs s []).2 []
      simp only [List.reverse_nil, List.map_nil, List.nil_append] at hNf hPf
      intro c hc
      rcases (mem_emitEquiv _ _ _ _).1 hc with hc | ⟨qn, hqn, qp, hqp, _, rfl⟩
      · exact hP.1 (hN.1 hg) c hc
      · intro x hx
        have hcn : qn.1 ∈ cs := hNf ▸ List.mem_map_of_mem hqn
        have hcp : qp.1 ∈ cs := hPf ▸ List.mem_map_of_mem hqp
        exact (hP.2 qp hqp x).2 (hI qn.1 hcn qp.1 hcp x ((hN.2 qn hqn x).1 hx))
  | disjointClasses cs =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isEL, List.all_eq_true] at hEL
      have hle₁ := (setOut_le fun c hc => (mem_emitDisjoint _ _ _ c).2 (Or.inl hc)).trans hle
      have hN := transMembers_extend I F hT hB false cs s [] hs hle₁ hEL (by simp)
      have hNf := transMembers_fst false cs s []
      simp only [List.reverse_nil, List.map_nil, List.nil_append] at hNf
      have hI' : cs.Pairwise fun c d => ∀ x, ¬ (I.ext c x ∧ I.ext d x) := hI
      rw [← hNf, List.pairwise_map, List.pairwise_iff_forall_sublist] at hI'
      intro c hc
      rcases (mem_emitDisjoint _ _ _ _).1 hc with hc | ⟨m, n, hmn, rfl⟩
      · exact hN.1 hg c hc
      · intro x hm hn
        have hmL : m ∈ (transMembers false cs s []).1 := hmn.subset (by simp)
        have hnL : n ∈ (transMembers false cs s []).1 := hmn.subset (by simp)
        exact absurd ⟨(hN.2 m hmL x).1 hm, (hN.2 n hnL x).1 hn⟩ (hI' hmn x)
  | domain r c =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isEL, Bool.and_eq_true] at hEL
      have hle₂ := (emit_le _ _).trans hle
      have hle₁ := (transExpr_le c true _).trans hle₂
      have hrk := extend_prop I F hT hB hEL.1 (hle₁.rdefs _ _ (internR_rdefs (r := propIRI r) hs))
      have hp := transExpr_extend I F hT hB c true _ (internR_wf hs) hle₂ hEL.2
      refine good_emit I F hT hB (hp.1 (good_internR I F hT hB hg)) ?_
      rintro x ⟨y, hxy, -⟩
      exact (hp.2 x).2 (hI x y ((hrk x y).1 hxy))
  | subObjectPropertyOf rs r =>
      simp only [Axiom.isEL, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at hEL
      obtain ⟨⟨hne, hrs⟩, hr⟩ := hEL
      cases rs with
      | nil => exact absurd rfl hne
      | cons r1 rest =>
          simp only [transAxiom] at hle ⊢
          have hle₂ := (transChain_le _ _ _ _ _).trans hle
          have hle₁ := (internR_le _ _).trans hle₂
          have hrk := extend_prop I F hT hB hr
            (hle₁.rdefs _ _ (internR_rdefs (r := propIRI r) hs))
          have hbk := hle₂.rdefs _ _ (internR_rdefs (r := propIRI r1) (internR_wf (r := propIRI r) hs))
          refine transChain_extend I F hT hB _ _ [propIRI r1] (rest.map propIRI) _
            (internR_wf (internR_wf hs)) hle hbk ?_
            (good_internR I F hT hB (good_internR I F hT hB hg))
          intro x y h
          apply (hrk x y).2
          apply hI x y
          rw [← map_named_propIRI (r1 :: rest) hrs]
          simpa using h
  | equivalentObjectProperties rs =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isEL, List.all_eq_true] at hEL
      have hle₁ := (setOut_le fun c hc => (mem_emitRoleEquiv _ _ c).2 (Or.inl hc)).trans hle
      have hok := internRoles_ok F rs s [] hs hle₁ (by simp)
      have hg' : Good I F hT hB (internRoles rs s []).2 := by
        intro c hc
        have : ∀ (rs : List ObjProp) (s : St) acc, (internRoles rs s acc).2.out = s.out := by
          intro rs
          induction rs with
          | nil => intro s acc; rfl
          | cons r rs ih' => intro s acc; simp only [internRoles]; rw [ih', internR_out]
        rw [this] at hc
        exact hg c hc
      intro c hc
      rcases (mem_emitRoleEquiv _ _ _).1 hc with hc | ⟨q, hq, q', hq', _, rfl⟩
      · exact hg' c hc
      · intro x y hxy
        obtain ⟨hokq, hmq⟩ := hok.1 q hq
        obtain ⟨hokq', hmq'⟩ := hok.1 q' hq'
        simp only [List.not_mem_nil, false_or] at hmq hmq'
        rw [extend_prop I F hT hB (hEL _ hmq) hokq.2] at hxy
        rw [extend_prop I F hT hB (hEL _ hmq') hokq'.2]
        exact hI q.1 hmq q'.1 hmq' x y hxy
  | transitive r =>
      simp only [transAxiom] at hle ⊢
      simp only [Axiom.isEL] at hEL
      have hrk := extend_prop I F hT hB hEL
        (((emit_le _ _).trans hle).rdefs _ _ (internR_rdefs (r := propIRI r) hs))
      refine good_emit I F hT hB (good_internR I F hT hB hg) ?_
      intro x y z hxy hyz
      exact (hrk x z).2 (hI x y z ((hrk x y).1 hxy) ((hrk y z).1 hyz))
  | range _ _ | inverseObjectProperties _ _ | symmetric _ => simp [Axiom.isEL] at hEL
  | declareClass _ | declareObjectProperty _ => simpa [transAxiom] using hg

end ExtendAxiom

/-! ## The pipeline: prepass, requested names, the loop over axioms -/

mutual

theorem scanExpr_le : ∀ (E : ClassExpr) (s : St), Le s (scanExpr E s)
  | .cls a, s => by simp only [scanExpr]; exact internC_le a s
  | .thing, s => by simp only [scanExpr]; exact Le.rfl
  | .nothing, s => by simp only [scanExpr]; exact Le.rfl
  | .and cs, s => by simp only [scanExpr]; exact scanList_le cs s
  | .or cs, s => by simp only [scanExpr]; exact scanList_le cs s
  | .not c, s => by simp only [scanExpr]; exact scanExpr_le c s
  | .some r c, s => by simp only [scanExpr]; exact (internR_le _ s).trans (scanExpr_le c _)
  | .all r c, s => by simp only [scanExpr]; exact (internR_le _ s).trans (scanExpr_le c _)

theorem scanList_le : ∀ (cs : List ClassExpr) (s : St), Le s (scanList cs s)
  | [], s => by simp only [scanList]; exact Le.rfl
  | c :: cs, s => by simp only [scanList]; exact (scanExpr_le c s).trans (scanList_le cs _)

end

mutual

theorem scanExpr_wf : ∀ (E : ClassExpr) (s : St), WF s → WF (scanExpr E s)
  | .cls a, s, hs => by simp only [scanExpr]; exact internC_wf hs
  | .thing, s, hs => by simp only [scanExpr]; exact hs
  | .nothing, s, hs => by simp only [scanExpr]; exact hs
  | .and cs, s, hs => by simp only [scanExpr]; exact scanList_wf cs s hs
  | .or cs, s, hs => by simp only [scanExpr]; exact scanList_wf cs s hs
  | .not c, s, hs => by simp only [scanExpr]; exact scanExpr_wf c s hs
  | .some r c, s, hs => by simp only [scanExpr]; exact scanExpr_wf c _ (internR_wf hs)
  | .all r c, s, hs => by simp only [scanExpr]; exact scanExpr_wf c _ (internR_wf hs)

theorem scanList_wf : ∀ (cs : List ClassExpr) (s : St), WF s → WF (scanList cs s)
  | [], s, hs => by simp only [scanList]; exact hs
  | c :: cs, s, hs => by simp only [scanList]; exact scanList_wf cs _ (scanExpr_wf c s hs)

end

theorem scanRoles_le_wf : ∀ (rs : List ObjProp) (s : St), Le s (scanRoles rs s) ∧
    (WF s → WF (scanRoles rs s))
  | [], s => ⟨Le.rfl, id⟩
  | r :: rs, s => by
      have ih := scanRoles_le_wf rs (internR (propIRI r) s).2
      exact ⟨(internR_le _ s).trans ih.1, fun hs => ih.2 (internR_wf hs)⟩

theorem scanAxiom_le_wf (s : St) (ax : Axiom) :
    Le s (scanAxiom s ax) ∧ (WF s → WF (scanAxiom s ax)) := by
  cases ax with
  | subClassOf c d =>
      exact ⟨(scanExpr_le c s).trans (scanExpr_le d _),
        fun hs => scanExpr_wf d _ (scanExpr_wf c s hs)⟩
  | equivalentClasses cs | disjointClasses cs => exact ⟨scanList_le cs s, scanList_wf cs s⟩
  | domain r c | range r c =>
      exact ⟨(internR_le _ s).trans (scanExpr_le c _), fun hs => scanExpr_wf c _ (internR_wf hs)⟩
  | subObjectPropertyOf rs r =>
      exact ⟨(scanRoles_le_wf rs s).1.trans (internR_le _ _),
        fun hs => internR_wf ((scanRoles_le_wf rs s).2 hs)⟩
  | equivalentObjectProperties rs => exact scanRoles_le_wf rs s
  | inverseObjectProperties r r' => exact scanRoles_le_wf [r, r'] s
  | transitive r | symmetric r => exact ⟨internR_le _ s, internR_wf⟩
  | declareClass a => exact ⟨internC_le a s, internC_wf⟩
  | declareObjectProperty r => exact ⟨internR_le r s, internR_wf⟩

theorem foldl_scan : ∀ (axs : List Axiom) (s : St),
    Le s (axs.foldl scanAxiom s) ∧ (WF s → WF (axs.foldl scanAxiom s))
  | [], s => ⟨Le.rfl, id⟩
  | ax :: axs, s => by
      have h₁ := scanAxiom_le_wf s ax
      have h₂ := foldl_scan axs (scanAxiom s ax)
      exact ⟨h₁.1.trans h₂.1, fun hs => h₂.2 (h₁.2 hs)⟩

theorem foldl_trans_le : ∀ (axs : List Axiom) (s : St), Le s (axs.foldl transAxiom s)
  | [], s => Le.rfl
  | ax :: axs, s => (transAxiom_le s ax).trans (foldl_trans_le axs _)

theorem foldl_trans_wf : ∀ (axs : List Axiom) (s : St), WF s → WF (axs.foldl transAxiom s)
  | [], s, hs => hs
  | ax :: axs, s, hs => foldl_trans_wf axs _ (transAxiom_wf hs ax)

/-- Every axiom is translated from some well-formed state below the final one. -/
theorem foldl_trans_mem : ∀ (axs : List Axiom) (s : St), WF s → ∀ ax ∈ axs,
    ∃ s', WF s' ∧ Le (transAxiom s' ax) (axs.foldl transAxiom s)
  | [], _, _, ax, h => absurd h List.not_mem_nil
  | ax' :: axs, s, hs, ax, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨s, hs, foldl_trans_le axs _⟩
      · exact foldl_trans_mem axs _ (transAxiom_wf hs ax') ax h

theorem foldl_trans_good {D : Type} (I : OWL.Interp D) (F : St)
    (hT : F.cdefs[F.top]? = some .thing) (hB : F.cdefs[F.bottom]? = some .nothing) :
    ∀ (axs : List Axiom) (s : St), WF s → Le (axs.foldl transAxiom s) F →
      (∀ ax ∈ axs, ax.isEL = true ∧ I.sat ax) →
      Good I F hT hB s → Good I F hT hB (axs.foldl transAxiom s)
  | [], _, _, _, _, hg => hg
  | ax :: axs, s, hs, hle, hax, hg => by
      simp only [List.foldl_cons] at hle ⊢
      have h₀ := hax ax List.mem_cons_self
      exact foldl_trans_good I F hT hB axs _ (transAxiom_wf hs ax) hle
        (fun a ha => hax a (List.mem_cons_of_mem _ ha))
        (transAxiom_extend I F hT hB s hs ax ((foldl_trans_le axs _).trans hle) h₀.1 h₀.2 hg)

/-- The invariant of `internRequested`: the map holds exactly the accumulated
IRIs, and the `i`-th of them (in order) has index `i`. -/
structure ReqInv (s : St) (acc : List IRI) : Prop where
  wf : WF s
  contains : ∀ b, s.cmap.contains b = acc.contains b
  size : s.cdefs.size = acc.length
  idx : ∀ (i : Nat) (b : IRI), acc.reverse[i]? = some b → s.cmap[b]? = some i

theorem reqInv_step {s : St} {acc : List IRI} {a : IRI} (hs : ReqInv s acc)
    (ha : acc.contains a = false) : ReqInv (internC a s).2 (a :: acc) := by
  have hnone : s.cmap[a]? = none :=
    Std.HashMap.getElem?_eq_none_of_contains_eq_false (by rw [hs.contains]; exact ha)
  have hmem : a ∉ acc := by simpa using ha
  refine ⟨internC_wf hs.wf, ?_, ?_, ?_⟩
  · intro b
    simp only [internC, hnone, Std.HashMap.contains_insert, List.contains_cons, hs.contains]
    by_cases hab : a = b
    · subst hab; simp
    · have h₁ : (a == b) = false := by simpa using hab
      have h₂ : (b == a) = false := by simpa using Ne.symm hab
      rw [h₁, h₂]
  · simp [internC, hnone, hs.size]
  · intro i b hb
    simp only [internC, hnone, Std.HashMap.getElem?_insert]
    simp only [List.reverse_cons, List.getElem?_append, List.length_reverse] at hb
    split at hb
    · have hbm : b ∈ acc := List.mem_reverse.1 (List.mem_of_getElem? hb)
      have hne : ¬ (a == b) = true := by
        rw [beq_iff_eq]; rintro rfl; exact hmem hbm
      simp only [hne, if_false]
      exact hs.idx i b hb
    · rename_i hlt
      have hi : i - acc.length < 1 := by
        rcases Nat.lt_or_ge (i - acc.length) 1 with h | h
        · exact h
        · rw [List.getElem?_eq_none (by simpa using h)] at hb; exact absurd hb (by simp)
      have hi' : i = acc.length := by omega
      subst hi'
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      simp [hs.size]

theorem internRequested_spec : ∀ (as : List IRI) (s : St) (acc : List IRI), ReqInv s acc →
    ∃ acc', ReqInv (internRequested as s acc).1 acc' ∧
      (internRequested as s acc).2 = acc'.reverse ∧
      acc'.reverse = acc.reverse ++ (as.filter fun b => !acc.contains b).eraseDups
  | [], s, acc, hs => ⟨acc, hs, rfl, by simp⟩
  | a :: as, s, acc, hs => by
      simp only [internRequested]
      by_cases hc : s.cmap.contains a = true
      · simp only [hc, if_true]
        obtain ⟨acc', h₁, h₂, h₃⟩ := internRequested_spec as s acc hs
        refine ⟨acc', h₁, h₂, ?_⟩
        rw [h₃]
        rw [hs.contains] at hc
        have hc' : a ∈ acc := by simpa using hc
        simp [List.filter_cons, hc']
      · simp only [hc]
        have ha : acc.contains a = false := by rw [← hs.contains]; simpa using hc
        obtain ⟨acc', h₁, h₂, h₃⟩ := internRequested_spec as _ (a :: acc) (reqInv_step hs ha)
        refine ⟨acc', h₁, h₂, ?_⟩
        rw [h₃, List.filter_cons, ha]
        simp only [Bool.not_false, if_true, List.eraseDups_cons, List.filter_filter,
          List.reverse_cons, List.append_assoc, List.singleton_append]
        congr 3
        apply List.filter_congr
        intro b _
        simp only [List.contains_cons, Bool.not_or]

theorem reqInv_empty : ReqInv {} [] :=
  ⟨⟨fun a k h => by simp at h, fun r k h => by simp at h⟩, fun b => by simp, rfl,
    fun i b h => by simp at h⟩

/-- The facts about the state after the prepass and `setTopBottom`. -/
theorem start_spec (O : Ontology) (requested : List IRI) :
    let S := setTopBottom (O.axioms.foldl scanAxiom (internRequested requested {} []).1)
    (internRequested requested {} []).2 = requested.eraseDups ∧ WF S ∧ S.out = [] ∧
      S.cdefs[S.top]? = some .thing ∧ S.cdefs[S.bottom]? = some .nothing ∧
      ∀ (i : Nat) (h : i < (internRequested requested {} []).2.length),
        S.cmap[(internRequested requested {} []).2[i]]? = some i := by
  intro S
  obtain ⟨acc, hinv, hL, hacc⟩ := internRequested_spec requested {} [] reqInv_empty
  simp only [List.reverse_nil, List.nil_append, List.contains_nil, Bool.not_false] at hacc
  have hscan := foldl_scan O.axioms (internRequested requested {} []).1
  have hwf₀ := hscan.2 hinv.wf
  have hft : requested.filter (fun _ => true) = requested := List.filter_eq_self.2 (fun _ _ => rfl)
  rw [hft] at hacc
  refine ⟨hL.trans hacc,
    ⟨fun a k h => push_getElem? (push_getElem? (hwf₀.cmap a k h)), hwf₀.rmap⟩, rfl, ?_, ?_, ?_⟩
  · exact push_getElem? (push_size_getElem? _ _)
  · simp [S, setTopBottom, Array.getElem_push]
  · intro i hi
    refine hscan.1.cmap _ _ (hinv.idx i _ ?_)
    rw [← hL]
    exact List.getElem?_eq_getElem hi

/-- The correctness argument on the states of the pipeline. -/
theorem correct_core (O : Ontology) (hEL : O.isEL = true) (S F : St) (L : List IRI)
    (hSwf : WF S) (hSout : S.out = []) (hStop : S.cdefs[S.top]? = some .thing)
    (hSbot : S.cdefs[S.bottom]? = some .nothing)
    (hSidx : ∀ (i : Nat) (h : i < L.length), S.cmap[L[i]]? = some i)
    (hF : O.axioms.foldl transAxiom S = F)
    (i j : Nat) (hi : i < L.length) (hj : j < L.length) :
    OWL.EntailsSub O L[i] L[j] ↔
      ELCompletion.EntailsSub (top := F.top) (bottom := F.bottom) F.out.reverse i j := by
  have hLe : Le S F := hF ▸ foldl_trans_le O.axioms S
  have hFwf : WF F := hF ▸ foldl_trans_wf O.axioms S hSwf
  have hT : F.cdefs[F.top]? = some .thing := by
    rw [hLe.top]; exact hLe.cdefs _ _ hStop
  have hB : F.cdefs[F.bottom]? = some .nothing := by
    rw [hLe.bottom]; exact hLe.cdefs _ _ hSbot
  have hEL' : ∀ ax ∈ O.axioms, ax.isEL = true := by
    simpa [Ontology.isEL, List.all_eq_true] using hEL
  have hidx : ∀ k (hk : k < L.length), F.cmap[L[k]]? = some k :=
    fun k hk => hLe.cmap _ _ (hSidx k hk)
  constructor
  · intro hsub D J hJ x hx
    have hJ' : ∀ c ∈ F.out, ELCompletion.satClause J c :=
      fun c hc => hJ c (List.mem_reverse.2 hc)
    have hmodel : OWL.Model O (restrict F J) := by
      intro ax hax
      obtain ⟨s', hs', hle⟩ := foldl_trans_mem O.axioms S hSwf ax hax
      exact transAxiom_restrict F J hJ' s' hs' ax (hF ▸ hle) (hEL' ax hax)
    have := @hsub D ⟨x⟩ (restrict F J) hmodel x
    rw [restrict_cls (hidx i hi), restrict_cls (hidx j hj)] at this
    exact this hx
  · intro hent D _ I hI x hx
    have hgood : Good I F hT hB F := by
      have := foldl_trans_good I F hT hB O.axioms S hSwf (hF ▸ Le.rfl)
        (fun ax hax => ⟨hEL' ax hax, hI ax hax⟩) (by intro c hc; simp [hSout] at hc)
      rwa [hF] at this
    have hmodels : ELCompletion.models (extend I F hT hB) F.out.reverse :=
      fun c hc => hgood c (List.mem_reverse.1 hc)
    have := hent (extend I F hT hB) hmodels x
    rw [extend_concept I F hT hB (hFwf.cmap _ _ (hidx i hi)),
      extend_concept I F hT hB (hFwf.cmap _ _ (hidx j hj)), ext_cls, ext_cls] at this
    exact this hx

end ContextCalculus.OWLFrontend.EL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL EL

theorem translateEL_named {O : OWL.Ontology} {requested : List OWL.IRI} {T : ELTranslation}
    (h : translateEL O requested = some T) :
    T.named = requested.eraseDups := by
  unfold translateEL at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact (start_spec O requested).1
  · exact absurd h (by simp)

theorem translateEL_isSome {O : OWL.Ontology} {requested : List OWL.IRI}
    (hEL : O.isEL = true) :
    (translateEL O requested).isSome = true := by
  simp [translateEL, hEL]

theorem translateEL_correct {O : OWL.Ontology} {requested : List OWL.IRI} {T : ELTranslation}
    (h : translateEL O requested = some T)
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWL.EntailsSub O T.named[i] T.named[j] ↔
      ELCompletion.EntailsSub (top := T.top) (bottom := T.bottom) T.ontology i j := by
  unfold translateEL at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hEL
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨_, hSwf, hSout, hStop, hSbot, hSidx⟩ := start_spec O requested
  exact correct_core O hEL _ _ _ hSwf hSout hStop hSbot hSidx rfl i j hi hj

#print axioms translateEL_named
#print axioms translateEL_isSome
#print axioms translateEL_correct

end ContextCalculus.OWLFrontend
