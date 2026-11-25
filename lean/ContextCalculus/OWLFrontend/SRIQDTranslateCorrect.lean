import ContextCalculus.OWLFrontend.SRIQDTranslate

/-!
# Correctness of the SHIQ(D) translation (v1.7.0 stage C4, part D)

Part 1: congruence, abstraction and rewriting at the level of one OWL
interpretation.

* `ext_congr_cls`: an ALCIQD class expression depends only on the classes
  of the names it mentions (with the same roles, data properties and
  datatypes).
* `ext_absC`: if every fresh name `nm e` has the extension of its data
  expression `e`, the abstracted class expression has the extension of
  the original.
* `sat_rwAxiom`: an axiom of the SHIQ(D) part holds iff its rewritten
  axioms and its sub-property pairs hold.
-/

namespace ContextCalculus.OWLFrontend.SHIQD

open ContextCalculus.OWL

variable {DM : DatatypeMap} {D : Type}

/-! ## Facts about `isALCIQD` -/

theorem isALCIQD_and {cs : List ClassExpr} :
    (ClassExpr.and cs).isALCIQD = true ↔ ∀ c ∈ cs, c.isALCIQD = true := by
  rw [ClassExpr.isALCIQD]; simp

theorem isALCIQD_or {cs : List ClassExpr} :
    (ClassExpr.or cs).isALCIQD = true ↔ ∀ c ∈ cs, c.isALCIQD = true := by
  rw [ClassExpr.isALCIQD]; simp

theorem names_sub_and {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.names) : a ∈ (ClassExpr.and cs).names := by
  rw [ClassExpr.names]; simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  exact ⟨c, hc, ha⟩

theorem names_sub_or {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.names) : a ∈ (ClassExpr.or cs).names := by
  rw [ClassExpr.names]; simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  exact ⟨c, hc, ha⟩

/-! ## Congruence in the classes -/

/-- An ALCIQD class expression has the same extension in two
interpretations that differ at most on the classes of names it does not
mention. -/
theorem ext_congr_cls {I J : Interp DM D} (hr : I.role = J.role) (hd : I.dprop = J.dprop)
    (ht : I.dtype = J.dtype) :
    ∀ (c : ClassExpr), c.isALCIQD = true → (∀ a ∈ c.names, I.cls a = J.cls a) →
      I.ext c = J.ext c
  | .cls a, _, h => by
    funext x; rw [Interp.ext, Interp.ext, h a (by simp [ClassExpr.names])]
  | .thing, _, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .nothing, _, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .and cs, hc, h => by
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ext_congr_cls hr hd ht c (isALCIQD_and.1 hc c hm) fun a ha => h a (names_sub_and hm ha)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun h' c hm => (ih c hm) ▸ h' c hm, fun h' c hm => (ih c hm).symm ▸ h' c hm⟩
  | .or cs, hc, h => by
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ext_congr_cls hr hd ht c (isALCIQD_or.1 hc c hm) fun a ha => h a (names_sub_or hm ha)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm) ▸ h'⟩,
      fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm).symm ▸ h'⟩⟩
  | .not c, hc, h => by
    rw [ClassExpr.isALCIQD] at hc
    have ih := ext_congr_cls hr hd ht c hc fun a ha => h a (by rw [ClassExpr.names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih]
  | .some r c, hc, h => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_congr_cls hr hd ht c hc.2 fun a ha => h a (by rw [ClassExpr.names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr' hr]
  | .all r c, hc, h => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_congr_cls hr hd ht c hc.2 fun a ha => h a (by rw [ClassExpr.names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr' hr]
  | .min k r c, hc, h => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_congr_cls hr hd ht c hc.2 fun a ha => h a (by rw [ClassExpr.names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr' hr]
  | .max k r c, hc, h => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_congr_cls hr hd ht c hc.2 fun a ha => h a (by rw [ClassExpr.names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr' hr]
  | .exact k r c, hc, h => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_congr_cls hr hd ht c hc.2 fun a ha => h a (by rw [ClassExpr.names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr' hr]
  | .dataSome p R, _, _ => by
    funext x; cases p <;> simp [Interp.ext, Interp.drExt, Interp.dp, hd, ht]
  | .dataAll p R, _, _ => by
    funext x; cases p <;> simp [Interp.ext, Interp.drExt, Interp.dp, hd, ht]
  | .dataHasValue p l, _, _ => by
    funext x; cases p <;> simp [Interp.ext, Interp.dp, hd]
  | .dataMin k p R, _, _ => by
    funext x; cases p <;> simp [Interp.ext, Interp.drExt, Interp.dp, hd, ht]
  | .dataMax k p R, _, _ => by
    funext x; cases p <;> simp [Interp.ext, Interp.drExt, Interp.dp, hd, ht]
  | .dataExact k p R, _, _ => by
    funext x; cases p <;> simp [Interp.ext, Interp.drExt, Interp.dp, hd, ht]
  | .oneOf _, hc, _ | .hasValue .., hc, _ | .hasSelf _, hc, _ => by
    rw [ClassExpr.isALCIQD] at hc; exact absurd hc (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-! ## Abstraction -/

theorem atLeast_zero' {α : Type} (P : α → Prop) : AtLeast 0 P := ⟨[], List.nodup_nil, rfl, by simp⟩

theorem atMost_zero_iff {α : Type} (P : α → Prop) : AtMost 0 P ↔ ∀ y, ¬ P y := by
  constructor
  · intro h y hy
    have := h [y] (List.nodup_singleton y) (by simpa using hy)
    simp at this
  · intro h l _ hl
    cases l with
    | nil => rfl
    | cons y l => exact absurd (hl y List.mem_cons_self) (h y)

theorem dexprs_named {p : DataProp} (hp : p.isNamed = true) : DataProp.named (dpIRI p) = p := by
  cases p <;> simp_all [DataProp.isNamed, dpIRI]

/-- **Abstraction.** If the name of every data expression of `c` has the
extension of the data expression, the abstraction of `c` has the extension
of `c`. -/
theorem ext_absC {I : Interp DM D} {nm : DExpr → IRI} :
    ∀ (c : ClassExpr), c.isALCIQD = true →
      (∀ e ∈ dexprs c, ∀ x, I.cls (nm e) x ↔ I.ext e.toCE x) →
      ∀ x, I.ext (absC nm c) x ↔ I.ext c x
  | .cls a, _, _, x => by rw [absC]
  | .thing, _, _, x => by rw [absC]
  | .nothing, _, _, x => by rw [absC]
  | .and cs, hc, H, x => by
    rw [absC, Interp.ext, Interp.ext]
    have ih : ∀ c ∈ cs, ∀ x, I.ext (absC nm c) x ↔ I.ext c x := fun c hm =>
      ext_absC c (isALCIQD_and.1 hc c hm) fun e he => H e (by
        rw [dexprs]; exact List.mem_flatMap.2 ⟨⟨c, hm⟩, List.mem_attach _ _, he⟩)
    constructor
    · intro h c hm
      exact (ih c hm x).1 (h _ (List.mem_map.2 ⟨⟨c, hm⟩, List.mem_attach _ _, rfl⟩))
    · intro h c' hc'
      obtain ⟨⟨c, hm⟩, -, rfl⟩ := List.mem_map.1 hc'
      exact (ih c hm x).2 (h c hm)
  | .or cs, hc, H, x => by
    rw [absC, Interp.ext, Interp.ext]
    have ih : ∀ c ∈ cs, ∀ x, I.ext (absC nm c) x ↔ I.ext c x := fun c hm =>
      ext_absC c (isALCIQD_or.1 hc c hm) fun e he => H e (by
        rw [dexprs]; exact List.mem_flatMap.2 ⟨⟨c, hm⟩, List.mem_attach _ _, he⟩)
    constructor
    · rintro ⟨c', hc', h⟩
      obtain ⟨⟨c, hm⟩, -, rfl⟩ := List.mem_map.1 hc'
      exact ⟨c, hm, (ih c hm x).1 h⟩
    · rintro ⟨c, hm, h⟩
      exact ⟨_, List.mem_map.2 ⟨⟨c, hm⟩, List.mem_attach _ _, rfl⟩, (ih c hm x).2 h⟩
  | .not c, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, Interp.ext]
    beta_reduce
    rw [ext_absC c hc (fun e he => H e (by rw [dexprs]; exact he)) x]
  | .some r c, hc, H, x => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_absC c hc.2 (fun e he => H e (by rw [dexprs]; exact he))
    rw [absC, Interp.ext, Interp.ext]
    simp only [ih]
  | .all r c, hc, H, x => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_absC c hc.2 (fun e he => H e (by rw [dexprs]; exact he))
    rw [absC, Interp.ext, Interp.ext]
    simp only [ih]
  | .min k r c, hc, H, x => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_absC c hc.2 (fun e he => H e (by rw [dexprs]; exact he))
    rw [absC, Interp.ext, Interp.ext]
    simp only [ih]
  | .max k r c, hc, H, x => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_absC c hc.2 (fun e he => H e (by rw [dexprs]; exact he))
    rw [absC, Interp.ext, Interp.ext]
    simp only [ih]
  | .exact k r c, hc, H, x => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    have ih := ext_absC c hc.2 (fun e he => H e (by rw [dexprs]; exact he))
    rw [absC, Interp.ext, Interp.ext]
    simp only [ih]
  | .dataSome p R, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, H _ (by rw [dexprs]; exact List.mem_singleton_self _)]
    simp only [DExpr.toCE, dexprs_named hc]
  | .dataAll p R, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, H _ (by rw [dexprs]; exact List.mem_singleton_self _)]
    simp only [DExpr.toCE, dexprs_named hc]
  | .dataHasValue p l, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, H _ (by rw [dexprs]; exact List.mem_singleton_self _)]
    simp only [DExpr.toCE, dexprs_named hc, Interp.ext, Interp.drExt]
    rw [DataRange.ext]
    simp only [List.mem_singleton, exists_eq_left]
    exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩⟩
  | .dataMin 0 p R, _, _, x => by
    rw [absC, Interp.ext, Interp.ext]
    exact ⟨fun _ => atLeast_zero' _, fun _ => trivial⟩
  | .dataMin (k + 1) p R, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, H _ (by rw [dexprs]; exact List.mem_singleton_self _)]
    simp only [DExpr.toCE, dexprs_named hc]
  | .dataMax k p R, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, H _ (by rw [dexprs]; exact List.mem_singleton_self _)]
    simp only [DExpr.toCE, dexprs_named hc]
  | .dataExact 0 p R, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext, H _ (by rw [dexprs]; exact List.mem_singleton_self _)]
    simp only [DExpr.toCE, dexprs_named hc, Interp.ext]
    exact ⟨fun h => ⟨atLeast_zero' _, h⟩, fun h => h.2⟩
  | .dataExact (k + 1) p R, hc, H, x => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, Interp.ext]
    have h1 := H ⟨2, k + 1, dpIRI p, R⟩ (by rw [dexprs]; simp)
    have h2 := H ⟨3, k + 1, dpIRI p, R⟩ (by rw [dexprs]; simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.ext, h1, h2]
    simp only [DExpr.toCE, dexprs_named hc, Interp.ext]
  | .oneOf _, hc, _, _ | .hasValue .., hc, _, _ | .hasSelf _, hc, _, _ => by
    rw [ClassExpr.isALCIQD] at hc; exact absurd hc (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- The abstraction of an ALCIQD class expression is ALCIQ. -/
theorem isALCIQ_absC (nm : DExpr → IRI) :
    ∀ (c : ClassExpr), c.isALCIQD = true → (absC nm c).isALCIQ = true
  | .cls a, _ => by rw [absC, ClassExpr.isALCIQ]
  | .thing, _ => by rw [absC, ClassExpr.isALCIQ]
  | .nothing, _ => by rw [absC, ClassExpr.isALCIQ]
  | .and cs, hc => by
    rw [absC, ClassExpr.isALCIQ]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map]
    rintro c' ⟨⟨c, hm⟩, -, rfl⟩
    exact isALCIQ_absC nm c (isALCIQD_and.1 hc c hm)
  | .or cs, hc => by
    rw [absC, ClassExpr.isALCIQ]
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall, List.mem_map]
    rintro c' ⟨⟨c, hm⟩, -, rfl⟩
    exact isALCIQ_absC nm c (isALCIQD_or.1 hc c hm)
  | .not c, hc => by
    rw [ClassExpr.isALCIQD] at hc
    rw [absC, ClassExpr.isALCIQ]; exact isALCIQ_absC nm c hc
  | .some r c, hc => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    rw [absC, ClassExpr.isALCIQ, Bool.and_eq_true]; exact ⟨hc.1, isALCIQ_absC nm c hc.2⟩
  | .all r c, hc => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    rw [absC, ClassExpr.isALCIQ, Bool.and_eq_true]; exact ⟨hc.1, isALCIQ_absC nm c hc.2⟩
  | .min k r c, hc => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    rw [absC, ClassExpr.isALCIQ, Bool.and_eq_true]; exact ⟨hc.1, isALCIQ_absC nm c hc.2⟩
  | .max k r c, hc => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    rw [absC, ClassExpr.isALCIQ, Bool.and_eq_true]; exact ⟨hc.1, isALCIQ_absC nm c hc.2⟩
  | .exact k r c, hc => by
    rw [ClassExpr.isALCIQD, Bool.and_eq_true] at hc
    rw [absC, ClassExpr.isALCIQ, Bool.and_eq_true]; exact ⟨hc.1, isALCIQ_absC nm c hc.2⟩
  | .dataSome .., _ | .dataAll .., _ | .dataHasValue .., _ | .dataMax .., _ => by
    rw [absC, ClassExpr.isALCIQ]
  | .dataMin 0 .., _ | .dataMin (_ + 1) .., _ | .dataExact 0 .., _ => by
    rw [absC, ClassExpr.isALCIQ]
  | .dataExact (k + 1) p R, _ => by
    rw [absC, ClassExpr.isALCIQ]
    simp [ClassExpr.isALCIQ]
  | .oneOf _, hc | .hasValue .., hc | .hasSelf _, hc => by
    rw [ClassExpr.isALCIQD] at hc; exact absurd hc (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- A data property axiom. -/
def isDataPropAx : Axiom → Bool
  | .subDataPropertyOf .. | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataDomain .. | .dataRange .. | .functionalData _ => true
  | _ => false

/-- The abstraction of an axiom of the SHIQ(D) part that is not a data
property axiom is an axiom of the SHIQ part. -/
theorem isSHIQ_absAx (nm : DExpr → IRI) {ax : Axiom} (hax : ax.isSHIQD = true)
    (hd : isDataPropAx ax = false) : (absAx nm ax).isSHIQ = true := by
  cases ax
  case subClassOf c d =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [absAx, Axiom.isSHIQ, Bool.and_eq_true]
    exact ⟨isALCIQ_absC nm c hax.1, isALCIQ_absC nm d hax.2⟩
  case equivalentClasses cs =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [absAx, Axiom.isSHIQ, List.all_eq_true, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact isALCIQ_absC nm c (hax c hc)
  case disjointClasses cs =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [absAx, Axiom.isSHIQ, List.all_eq_true, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact isALCIQ_absC nm c (hax c hc)
  case domain r c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [absAx, Axiom.isSHIQ, Bool.and_eq_true]
    exact ⟨hax.1, isALCIQ_absC nm c hax.2⟩
  case range r c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [absAx, Axiom.isSHIQ, Bool.and_eq_true]
    exact ⟨hax.1, isALCIQ_absC nm c hax.2⟩
  case functional r => simpa [absAx, Axiom.isSHIQ, Axiom.isSHIQD] using hax
  case inverseFunctional r => simpa [absAx, Axiom.isSHIQ, Axiom.isSHIQD] using hax
  all_goals first
    | (simp [isDataPropAx] at hd; done)
    | exact Axiom.isSHIQ_of_isSHI (by simpa [Axiom.isSHIQD] using hax)

/-- **Abstraction of axioms.** -/
theorem sat_absAx {I : Interp DM D} {nm : DExpr → IRI} {ax : Axiom} (hax : ax.isSHIQD = true)
    (H : ∀ e ∈ axDexprs ax, ∀ x, I.cls (nm e) x ↔ I.ext e.toCE x) (N : List IRI) :
    I.sat N (absAx nm ax) ↔ I.sat N ax := by
  cases ax with
  | subClassOf c d =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [axDexprs, List.mem_append] at H
    simp only [absAx, Interp.sat, ext_absC c hax.1 (fun e he => H e (Or.inl he)),
      ext_absC d hax.2 (fun e he => H e (Or.inr he))]
  | equivalentClasses cs =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [axDexprs, List.mem_flatMap] at H
    have ih : ∀ c ∈ cs, ∀ x, I.ext (absC nm c) x ↔ I.ext c x := fun c hc =>
      ext_absC c (hax c hc) fun e he => H e ⟨c, hc, he⟩
    simp only [absAx, Interp.sat, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact ⟨fun h c hc d hd x hx => (ih d hd x).1 (h c hc d hd x ((ih c hc x).2 hx)),
      fun h c hc d hd x hx => (ih d hd x).2 (h c hc d hd x ((ih c hc x).1 hx))⟩
  | disjointClasses cs =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [axDexprs, List.mem_flatMap] at H
    have ih : ∀ c ∈ cs, ∀ x, I.ext (absC nm c) x ↔ I.ext c x := fun c hc =>
      ext_absC c (hax c hc) fun e he => H e ⟨c, hc, he⟩
    simp only [absAx, Interp.sat, List.pairwise_map]
    constructor
    · intro h
      exact h.imp_of_mem fun hc hd h' x ⟨h1, h2⟩ => h' x ⟨(ih _ hc x).2 h1, (ih _ hd x).2 h2⟩
    · intro h
      exact h.imp_of_mem fun hc hd h' x ⟨h1, h2⟩ => h' x ⟨(ih _ hc x).1 h1, (ih _ hd x).1 h2⟩
  | domain r c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [absAx, Interp.sat, ext_absC c hax.2 (fun e he => H e (by simpa [axDexprs] using he))]
  | range r c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [absAx, Interp.sat, ext_absC c hax.2 (fun e he => H e (by simpa [axDexprs] using he))]
  | _ => exact Iff.rfl

/-! ## Rewriting the data property axioms -/

theorem drExt_litRange (I : Interp DM D) (v : DM.Val) : I.drExt litRange v := by
  simp [Interp.drExt, litRange, DataRange.ext, DatatypeMap.dtExt]

theorem atMost_one_iff {α : Type} (P : α → Prop) :
    AtMost 1 P ↔ ∀ v w, P v → P w → v = w := by
  constructor
  · intro h v w hv hw
    by_contra hne
    have := h [v, w] (by simp [hne]) (by simp [hv, hw])
    simp at this
  · intro h l hl hP
    exact SRIQT.length_le_one hl fun y hy z hz => h y z (hP y hy) (hP z hz)

theorem dp_named (I : Interp DM D) {p : DataProp} (hp : p.isNamed = true) :
    I.dp p = I.dprop (dpIRI p) := by
  cases p <;> simp_all [DataProp.isNamed, dpIRI, Interp.dp]

/-- **Rewriting.** An axiom of the SHIQ(D) part holds iff its rewritten
axioms and its sub-property pairs hold. -/
theorem sat_rwAxiom (I : Interp DM D) {ax : Axiom} (hax : ax.isSHIQD = true) (N : List IRI) :
    I.sat N ax ↔ (∀ ax' ∈ rwAxiom ax, I.sat N ax') ∧
      ∀ pq ∈ subPairs ax, ∀ x v, I.dprop pq.1 x v → I.dprop pq.2 x v := by
  cases ax
  case dataDomain p c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [rwAxiom, subPairs, List.mem_singleton, forall_eq, List.not_mem_nil,
      false_implies, implies_true, and_true, Interp.sat, Interp.ext]
    constructor
    · rintro h x ⟨v, hv, -⟩; exact h x v hv
    · intro h x v hv; exact h x ⟨v, hv, drExt_litRange I v⟩
  case dataRange p R =>
    simp only [rwAxiom, subPairs, List.mem_singleton, forall_eq, List.not_mem_nil,
      false_implies, implies_true, and_true, Interp.sat, Interp.ext]
    exact ⟨fun h x _ v hv => h x v hv, fun h x v hv => h x trivial v hv⟩
  case functionalData p =>
    simp only [rwAxiom, subPairs, List.mem_singleton, forall_eq, List.not_mem_nil,
      false_implies, implies_true, and_true, Interp.sat, Interp.ext, atMost_one_iff]
    constructor
    · intro h x _ v w hv hw; exact h x v w hv.1 hw.1
    · intro h x v w hv hw
      exact h x trivial v w ⟨hv, drExt_litRange I v⟩ ⟨hw, drExt_litRange I w⟩
  case subDataPropertyOf p q =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [rwAxiom, subPairs, List.mem_singleton, forall_eq, List.not_mem_nil,
      false_implies, implies_true, true_and, Interp.sat, dp_named I hax.1, dp_named I hax.2]
  case equivalentDataProperties ps =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [rwAxiom, subPairs, List.not_mem_nil, false_implies, implies_true, true_and,
      Interp.sat, List.mem_flatMap, List.mem_map]
    constructor
    · rintro h pq ⟨p, hp, q, hq, rfl⟩ x v hv
      have := h p hp q hq x v
      rw [dp_named I (hax p hp), dp_named I (hax q hq)] at this
      exact this hv
    · intro h p hp q hq x v hv
      rw [dp_named I (hax p hp)] at hv
      rw [dp_named I (hax q hq)]
      exact h _ ⟨p, hp, q, hq, rfl⟩ x v hv
  all_goals simp [rwAxiom, subPairs]

/-! ## Congruence of axioms in the classes -/

theorem names_sub_classNames_eq {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.names) : a ∈ cs.flatMap ClassExpr.names := List.mem_flatMap.2 ⟨c, hc, ha⟩

/-- An axiom of the SHIQ(D) part holds in two interpretations that differ at
most on the classes of names it does not mention. -/
theorem sat_congr_cls {I J : Interp DM D} (hr : I.role = J.role) (hd : I.dprop = J.dprop)
    (ht : I.dtype = J.dtype) {ax : Axiom} (hax : ax.isSHIQD = true)
    (hc : ∀ a ∈ ax.classNames, I.cls a = J.cls a) (N N' : List IRI) :
    I.sat N ax ↔ J.sat N' ax := by
  have hp := Interp.prop_congr' hr
  have hch := Interp.chain_congr' hr
  have he := ext_congr_cls hr hd ht
  have hdp : ∀ p : DataProp, I.dp p = J.dp p := fun p => by cases p <;> simp [Interp.dp, hd]
  have hdr : ∀ R : DataRange, I.drExt R = J.drExt R := fun R => by simp [Interp.drExt, ht]
  cases ax
  case subClassOf c d =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [Axiom.classNames, List.mem_append] at hc
    rw [Interp.sat, Interp.sat, he c hax.1 fun a ha => hc a (Or.inl ha),
      he d hax.2 fun a ha => hc a (Or.inr ha)]
  case equivalentClasses cs =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [Axiom.classNames] at hc
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      he c (hax c hm) fun a ha => hc a (names_sub_classNames_eq hm ha)
    simp only [Interp.sat]
    exact ⟨fun h c hm d hd x => (ih c hm) ▸ (ih d hd) ▸ h c hm d hd x,
      fun h c hm d hd x => (ih c hm).symm ▸ (ih d hd).symm ▸ h c hm d hd x⟩
  case disjointClasses cs =>
    simp only [Axiom.isSHIQD, List.all_eq_true] at hax
    simp only [Axiom.classNames] at hc
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      he c (hax c hm) fun a ha => hc a (names_sub_classNames_eq hm ha)
    simp only [Interp.sat]
    constructor
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc) ▸ (ih _ hd) ▸ h' x
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x
  case domain r c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    rw [Interp.sat, Interp.sat, he c hax.2 hc, hp]
  case range r c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    rw [Interp.sat, Interp.sat, he c hax.2 hc, hp]
  case dataDomain p c =>
    simp only [Axiom.isSHIQD, Bool.and_eq_true] at hax
    simp only [Axiom.classNames] at hc
    rw [Interp.sat, Interp.sat, he c hax.2 hc, hdp]
  case dataRange p R => rw [Interp.sat, Interp.sat, hdp, hdr]
  case functionalData p => rw [Interp.sat, Interp.sat, hdp]
  case subDataPropertyOf p q => rw [Interp.sat, Interp.sat, hdp, hdp]
  case equivalentDataProperties ps => simp only [Interp.sat, hdp]
  case subObjectPropertyOf rs r => simp only [Interp.sat, hp, hch]
  case equivalentObjectProperties rs => simp only [Interp.sat, hp]
  case inverseObjectProperties r s => simp only [Interp.sat, hp]
  case transitive r => simp only [Interp.sat, hp]
  case symmetric r => simp only [Interp.sat, hp]
  case functional r => simp only [Interp.sat, hp]
  case inverseFunctional r => simp only [Interp.sat, hp]
  all_goals first
    | (simp only [Interp.sat]; done)
    | simp [Axiom.isSHIQD, Axiom.isSHI, Axiom.isSRI] at hax

end ContextCalculus.OWLFrontend.SHIQD
