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

end ContextCalculus.OWLFrontend.EL
