import ContextCalculus.OWLFrontend.SRIQKBTranslate
import ContextCalculus.OWLFrontend.SRIQTranslateCorrect
import ContextCalculus.SRIQ.Realization
import ContextCalculus.OWLFrontend.SRIQComplete

/-!
# Correctness of the OWL SHIQ knowledge-base translation

`translateSRIQKB` (`SRIQKBTranslate`) on the OWL 2 direct semantics.

* `translateSRIQKB_up`: a model of `O` gives a model of the clauses and
  the assertions, with the individuals at the values the model gives them,
  and each requested index standing for its IRI.
* `translateSRIQKB_down`: a model of the clauses and the assertions gives
  a model of `O` (over the trivial datatype map) with the same two
  properties.
* Consequences: `translateSRIQKB_entailsSub` (OWL subsumption between
  requested IRIs is `SRIQ.EntailsSubKB`), `translateSRIQKB_inconsistent`
  (`OWL.Inconsistent O` is `¬ SRIQ.ConsistentKB`),
  `translateSRIQKB_entailsType` (an entailed class assertion of a requested
  IRI is `SRIQ.EntailsTypeKB`) and `translateSRIQKB_entailsSame` (an
  entailed equality of two individuals is `SRIQ.EntailsSameKB`).

The proof reuses the model maps of the SHIQ translation
(`SRIQT.extend`, `SRIQT.restrict`, `transAxiom_extend`,
`transAxiom_restrict`) on the ontology `kbTBox O base`. Up: the model of
`O` first extends to the definition names (`extI`: `defName base j`
stands for the class expression of the class assertion at position `j`),
which leaves every other class IRI unchanged because the definition names
are fresh. Down: the restriction `SRIQT.restrict` gets the individuals of
the ABox (`indMap`). Satisfaction of an axiom of the SHIQ part depends only
on the roles and on the class IRIs the axiom mentions (`Axiom.sat_congr`).
-/

namespace ContextCalculus.OWL

variable {DM : DatatypeMap} {Dom : Type}


theorem Interp.prop_congr {I J : Interp DM Dom} (h : I.role = J.role) (r : ObjProp) :
    I.prop r = J.prop r := by
  cases r <;> simp only [Interp.prop, h]

theorem Interp.chain_congr {I J : Interp DM Dom} (h : I.role = J.role) :
    ∀ rs : List ObjProp, I.chain rs = J.chain rs
  | [] => rfl
  | r :: rs => by
    funext x z
    simp only [Interp.chain, Interp.prop_congr h r, Interp.chain_congr h rs]

theorem ClassExpr.mem_names_and {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.names) : a ∈ (ClassExpr.and cs).names := by
  rw [ClassExpr.names]; simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  exact ⟨c, hc, ha⟩

theorem ClassExpr.mem_names_or {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {a : IRI}
    (ha : a ∈ c.names) : a ∈ (ClassExpr.or cs).names := by
  rw [ClassExpr.names]; simp only [List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
  exact ⟨c, hc, ha⟩

/-- Two interpretations with the same roles that agree on the class IRIs of
an ALCIQ class expression give it the same extension. -/
theorem ClassExpr.ext_congr {I J : Interp DM Dom} (hr : I.role = J.role) :
    ∀ (c : ClassExpr), c.isALCIQ = true → (∀ a ∈ c.names, I.cls a = J.cls a) →
      I.ext c = J.ext c
  | .cls a, _, h => by
    funext x; rw [Interp.ext, Interp.ext, h a (by simp [ClassExpr.names])]
  | .thing, _, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .nothing, _, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .and cs, hc, h => by
    rw [isALCIQ] at hc
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at hc
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ext_congr hr c (hc c hm) fun a ha => h a (mem_names_and hm ha)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun h' c hm => (ih c hm) ▸ h' c hm, fun h' c hm => (ih c hm).symm ▸ h' c hm⟩
  | .or cs, hc, h => by
    rw [isALCIQ] at hc
    simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at hc
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ext_congr hr c (hc c hm) fun a ha => h a (mem_names_or hm ha)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm) ▸ h'⟩, fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm).symm ▸ h'⟩⟩
  | .not c, hc, h => by
    rw [isALCIQ] at hc
    have ih := ext_congr hr c hc fun a ha => h a (by rw [names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih]
  | .some r c, hc, h => by
    rw [isALCIQ, Bool.and_eq_true] at hc
    have ih := ext_congr hr c hc.2 fun a ha => h a (by rw [names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .all r c, hc, h => by
    rw [isALCIQ, Bool.and_eq_true] at hc
    have ih := ext_congr hr c hc.2 fun a ha => h a (by rw [names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .min k r c, hc, h => by
    rw [isALCIQ, Bool.and_eq_true] at hc
    have ih := ext_congr hr c hc.2 fun a ha => h a (by rw [names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .max k r c, hc, h => by
    rw [isALCIQ, Bool.and_eq_true] at hc
    have ih := ext_congr hr c hc.2 fun a ha => h a (by rw [names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .exact k r c, hc, h => by
    rw [isALCIQ, Bool.and_eq_true] at hc
    have ih := ext_congr hr c hc.2 fun a ha => h a (by rw [names]; exact ha)
    funext x; rw [Interp.ext, Interp.ext, ih, Interp.prop_congr hr]
  | .oneOf _, hc, _ | .hasValue .., hc, _ | .hasSelf _, hc, _ | .dataSome .., hc, _
  | .dataAll .., hc, _ | .dataHasValue .., hc, _ | .dataMin .., hc, _ | .dataMax .., hc, _
  | .dataExact .., hc, _ => by rw [isALCIQ] at hc; exact absurd hc (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- Satisfaction of an axiom of the SHIQ part depends only on the roles and
on the class IRIs the axiom mentions (not on the individuals, the data, or
the list of named individuals). -/
theorem Axiom.sat_congr {I J : Interp DM Dom} (hr : I.role = J.role) {ax : Axiom}
    (hax : ax.isSHIQ = true) (hc : ∀ a ∈ ax.classNames, I.cls a = J.cls a) (N N' : List IRI) :
    I.sat N ax ↔ J.sat N' ax := by
  have hp := Interp.prop_congr hr
  have hch := Interp.chain_congr hr
  cases ax with
  | subClassOf c d =>
    simp only [isSHIQ, Bool.and_eq_true] at hax
    simp only [classNames, List.mem_append] at hc
    rw [Interp.sat, Interp.sat, ClassExpr.ext_congr hr c hax.1 fun a ha => hc a (Or.inl ha),
      ClassExpr.ext_congr hr d hax.2 fun a ha => hc a (Or.inr ha)]
  | equivalentClasses cs =>
    simp only [isSHIQ, List.all_eq_true] at hax
    simp only [classNames, List.mem_flatMap] at hc
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ClassExpr.ext_congr hr c (hax c hm) fun a ha => hc a ⟨c, hm, ha⟩
    simp only [Interp.sat]
    exact ⟨fun h c hm d hd x => (ih c hm) ▸ (ih d hd) ▸ h c hm d hd x,
      fun h c hm d hd x => (ih c hm).symm ▸ (ih d hd).symm ▸ h c hm d hd x⟩
  | disjointClasses cs =>
    simp only [isSHIQ, List.all_eq_true] at hax
    simp only [classNames, List.mem_flatMap] at hc
    have ih : ∀ c ∈ cs, I.ext c = J.ext c := fun c hm =>
      ClassExpr.ext_congr hr c (hax c hm) fun a ha => hc a ⟨c, hm, ha⟩
    simp only [Interp.sat]
    constructor
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc) ▸ (ih _ hd) ▸ h' x
    · intro h
      exact h.imp_of_mem fun hc hd h' x => (ih _ hc).symm ▸ (ih _ hd).symm ▸ h' x
  | domain r c =>
    simp only [isSHIQ, Bool.and_eq_true] at hax
    simp only [classNames] at hc
    rw [Interp.sat, Interp.sat, ClassExpr.ext_congr hr c hax.2 hc, hp]
  | range r c =>
    simp only [isSHIQ, Bool.and_eq_true] at hax
    simp only [classNames] at hc
    rw [Interp.sat, Interp.sat, ClassExpr.ext_congr hr c hax.2 hc, hp]
  | subObjectPropertyOf rs r => simp only [Interp.sat, hp, hch]
  | equivalentObjectProperties rs => simp only [Interp.sat, hp]
  | inverseObjectProperties r s => simp only [Interp.sat, hp]
  | transitive r => simp only [Interp.sat, hp]
  | symmetric r => simp only [Interp.sat, hp]
  | functional r => simp only [Interp.sat, hp]
  | inverseFunctional r => simp only [Interp.sat, hp]
  | declareClass _ | declareObjectProperty _ | declareDataProperty _ | declareNamedIndividual _
  | declareDatatype _ | declareAnnotationProperty _ => simp only [Interp.sat]
  | _ => simp [isSHIQ, isSHI, isSRI] at hax

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend.SRIQKB

open ContextCalculus.OWL

/-! ## Lists -/

theorem collect_mem {α β : Type} {f : α → Option (List β)} :
    ∀ {xs : List α} {L : List β}, collect f xs = some L →
      ∀ y ∈ L, ∃ x ∈ xs, ∃ l, f x = some l ∧ y ∈ l
  | [], L, h, y, hy => by simp only [collect, Option.some.injEq] at h; subst h; simp at hy
  | x :: xs, L, h, y, hy => by
    simp only [collect] at h
    split at h
    · next l l' hx hxs =>
      simp only [Option.some.injEq] at h; subst h
      rcases List.mem_append.1 hy with hy | hy
      · exact ⟨x, List.mem_cons_self, l, hx, hy⟩
      · obtain ⟨x', hx', l'', h1, h2⟩ := collect_mem hxs y hy
        exact ⟨x', List.mem_cons_of_mem _ hx', l'', h1, h2⟩
    · exact absurd h (by simp)

theorem collect_some {α β : Type} {f : α → Option (List β)} :
    ∀ {xs : List α} {L : List β}, collect f xs = some L →
      ∀ x ∈ xs, ∃ l, f x = some l ∧ ∀ y ∈ l, y ∈ L
  | [], _, _, x, hx => by simp at hx
  | x :: xs, L, h, x', hx' => by
    simp only [collect] at h
    split at h
    · next l l' hx hxs =>
      simp only [Option.some.injEq] at h; subst h
      rcases List.mem_cons.1 hx' with rfl | hx'
      · exact ⟨l, hx, fun y hy => List.mem_append_left _ hy⟩
      · obtain ⟨l'', h1, h2⟩ := collect_some hxs x' hx'
        exact ⟨l'', h1, fun y hy => List.mem_append_right _ (h2 y hy)⟩
    · exact absurd h (by simp)

theorem collect_isSome {α β : Type} {f : α → Option (List β)} :
    ∀ {xs : List α}, (∀ x ∈ xs, (f x).isSome = true) → (collect f xs).isSome = true
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1
      (collect_isSome (f := f) fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))
    simp [collect, hl, hl']

theorem mem_allPairs {α : Type} {as : List α} {p : α × α} :
    p ∈ allPairs as ↔ p.1 ∈ as ∧ p.2 ∈ as := by
  obtain ⟨a, b⟩ := p
  simp [allPairs]

theorem pairwise_iff_pairsOf {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R ↔ ∀ p ∈ pairsOf l, R p.1 p.2
  | [] => by simp [pairsOf]
  | a :: l => by
    rw [List.pairwise_cons, pairwise_iff_pairsOf]
    simp only [pairsOf, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨h1, h2⟩ p (⟨b, hb, rfl⟩ | hp)
      · exact h1 b hb
      · exact h2 p hp
    · intro h
      exact ⟨fun b hb => h (a, b) (Or.inl ⟨b, hb, rfl⟩), fun p hp => h p (Or.inr hp)⟩

theorem mem_pairsOf {α : Type} : ∀ {l : List α} {p : α × α}, p ∈ pairsOf l → p.1 ∈ l ∧ p.2 ∈ l
  | [], p, h => by simp [pairsOf] at h
  | a :: l, p, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hb⟩
    · have := mem_pairsOf h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

/-! ## Fresh names -/

theorem le_foldl_max : ∀ (l : List IRI) (k : Nat), k ≤ l.foldl (fun k s => max k s.length) k
  | [], _ => le_refl _
  | _ :: l, _ => le_trans (le_max_left _ _) (le_foldl_max l _)

theorem length_le_maxLen : ∀ {l : List IRI} {s : IRI}, s ∈ l → s.length ≤ maxLen l := by
  intro l s hs
  unfold maxLen
  generalize 0 = k
  induction l generalizing k with
  | nil => simp at hs
  | cons t l ih =>
    rcases List.mem_cons.1 hs with rfl | hs
    · exact le_trans (le_max_right _ _) (le_foldl_max l _)
    · exact ih hs _

theorem defName_length (base : String) (j : Nat) : (defName base j).length = base.length + j := by
  simp [defName, String.length_pushn]

theorem defName_inj {base : String} {j j' : Nat} (h : defName base j = defName base j') : j = j' := by
  have := congrArg String.length h
  rw [defName_length, defName_length] at this
  omega

/-- A name no longer than the padding of `base` is not a definition name. -/
theorem ne_defName_of_length {O : Ontology} {requested : List IRI} {a : IRI}
    (h : a ∈ O.axioms.flatMap Axiom.classNames ++ requested) (j : Nat) :
    a ≠ defName (defBase O requested) j := by
  intro he
  have h1 := length_le_maxLen h
  have h2 := congrArg String.length he
  rw [defName_length] at h2
  simp only [defBase, String.length_pushn] at h2
  have : "urn:km:owl-kb:def:".length = 18 := by decide
  omega

theorem fresh_ax {O : Ontology} {requested : List IRI} {ax : Axiom} (hax : ax ∈ O.axioms)
    {a : IRI} (ha : a ∈ ax.classNames) (j : Nat) : a ≠ defName (defBase O requested) j :=
  ne_defName_of_length (List.mem_append_left _ (List.mem_flatMap.2 ⟨ax, hax, ha⟩)) j

theorem fresh_req {O : Ontology} {requested : List IRI} {a : IRI} (ha : a ∈ requested)
    (j : Nat) : a ≠ defName (defBase O requested) j :=
  ne_defName_of_length (List.mem_append_right _ ha) j

/-! ## The TBox of the knowledge base -/

theorem mem_kbTBox {O : Ontology} {base : String} {ax : Axiom} :
    ax ∈ (kbTBox O base).axioms ↔
      (ax ∈ O.axioms ∧ ax.isAssertion = false) ∨ ∃ p ∈ O.axioms.zipIdx, ax ∈ defAxioms base p := by
  simp [kbTBox, List.mem_append, List.mem_filter, List.mem_flatMap]

theorem mem_of_zipIdx {O : Ontology} {ax : Axiom} {j : Nat} (h : (ax, j) ∈ O.axioms.zipIdx) :
    ax ∈ O.axioms := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  exact List.mem_of_getElem? h

theorem exists_zipIdx {O : Ontology} {ax : Axiom} (h : ax ∈ O.axioms) :
    ∃ j, (ax, j) ∈ O.axioms.zipIdx := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, List.mem_zipIdx_iff_getElem?.2 (by simp [hj])⟩

theorem kbTBox_isSHIQ {O : Ontology} (hO : O.isSHIQKB = true) (base : String) :
    (kbTBox O base).isSHIQ = true := by
  simp only [Ontology.isSHIQ, List.all_eq_true]
  intro ax hax
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQKB = true := by
    simpa [Ontology.isSHIQKB, List.all_eq_true] using hO
  rcases mem_kbTBox.1 hax with ⟨h1, h2⟩ | ⟨⟨ax', j⟩, hp, hd⟩
  · exact Axiom.isSHIQ_of_isSHIQKB (hO' ax h1) h2
  · have hk := hO' ax' (mem_of_zipIdx hp)
    cases ax' <;> simp only [defAxioms, List.mem_singleton, List.not_mem_nil] at hd
    · subst hd
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      simp [Axiom.isSHIQ, ClassExpr.isALCIQ, hk.1]
    · subst hd
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      simp [Axiom.isSHIQ, Axiom.isSHI, hk.1.1]
    · subst hd
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      simp [Axiom.isSHIQ, Axiom.isSHI, hk.1.1]

/-! ## Individuals -/

theorem indIx_spec {inds : List IRI} {a : Individual} {i : Fin inds.length}
    (h : indIx inds a = some i) : ∃ a', a = .named a' ∧ inds[i] = a' ∧ i.val = inds.idxOf a' := by
  cases a with
  | anon _ => simp [indIx] at h
  | named a' =>
    simp only [indIx] at h
    split at h
    · next hl =>
      simp only [Option.some.injEq] at h; subst h
      exact ⟨a', rfl, List.getElem_idxOf hl, rfl⟩
    · exact absurd h (by simp)

/-- The values of the individuals in an OWL interpretation, from a map on
the indices (`ind0` for an IRI outside `inds` and for anonymous
individuals). -/
def indMap {D : Type} (inds : List IRI) (ind : Fin inds.length → D) (ind0 : D) : Individual → D
  | .named a => if h : inds.idxOf a < inds.length then ind ⟨_, h⟩ else ind0
  | .anon _ => ind0

theorem indMap_of_indIx {D : Type} {inds : List IRI} {ind : Fin inds.length → D} {ind0 : D}
    {a : Individual} {i : Fin inds.length} (h : indIx inds a = some i) :
    indMap inds ind ind0 a = ind i := by
  cases a with
  | anon _ => simp [indIx] at h
  | named a' =>
    simp only [indIx] at h
    split at h
    · next hl =>
      simp only [Option.some.injEq] at h; subst h
      simp [indMap, hl]
    · exact absurd h (by simp)

/-! ## Up: a model of `O` gives a model of the clauses and assertions -/

open Classical in
/-- `I` with `defName base j` standing for the class expression of the
class assertion at position `j` of `O`. -/
noncomputable def extI {DM : DatatypeMap} {D : Type} (O : Ontology) (base : String)
    (I : Interp DM D) : Interp DM D :=
  { I with cls := fun a x =>
      if ∃ j, a = defName base j then
        ∃ j c b, a = defName base j ∧ O.axioms[j]? = some (.classAssertion c b) ∧ I.ext c x
      else I.cls a x }

section Up

variable {DM : DatatypeMap} {D : Type} {O : Ontology} {base : String} (I : Interp DM D)

theorem extI_cls_of_ne {a : IRI} (h : ∀ j, a ≠ defName base j) : (extI O base I).cls a = I.cls a := by
  funext x
  have : ¬ ∃ j, a = defName base j := fun ⟨j, hj⟩ => h j hj
  simp only [extI, this, if_false]

theorem extI_cls_def {j : Nat} {c : ClassExpr} {b : Individual}
    (hj : O.axioms[j]? = some (.classAssertion c b)) (x : D) :
    (extI O base I).cls (defName base j) x ↔ I.ext c x := by
  simp only [extI, show ∃ j', defName base j = defName base j' from ⟨j, rfl⟩, if_true]
  constructor
  · rintro ⟨j', c', b', he, hj', hx⟩
    cases defName_inj he
    rw [hj] at hj'
    cases hj'
    exact hx
  · intro hx
    exact ⟨j, c, b, rfl, hj, hx⟩

end Up

theorem assertName_cases (base : String) (j : Nat) (c : ClassExpr) :
    (∃ a, c = .cls a ∧ assertName base j c = a) ∨ assertName base j c = defName base j := by
  cases c <;> simp [assertName]

theorem clsIx_spec {F : SRIQT.St} {n : Nat} {a : IRI} {x : Fin n} (h : clsIx F n a = some x) :
    F.b.cmap[a]? = some x.val := by
  simp only [clsIx, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact hk
  · exact absurd h (by simp)

theorem roleIx_spec {F : SRIQT.St} {m : Nat} {r : ObjProp} {R : SRI.RoleT (Fin m)}
    (h : roleIx F m r = some R) :
    ∃ k, F.b.rmap[EL.propIRI r]? = some k ∧ SRIT.finRT m (SRIT.mkRT r k) = some R := by
  simpa [roleIx, Option.bind_eq_some_iff] using h

theorem pairAssert_spec {n m : Nat} {inds : List IRI}
    {mk : Fin inds.length → Fin inds.length → KA n m inds.length} {p : Individual × Individual}
    {l : List (KA n m inds.length)} (h : pairAssert inds mk p = some l) :
    ∃ i i', indIx inds p.1 = some i ∧ indIx inds p.2 = some i' ∧ l = [mk i i'] := by
  simp only [pairAssert] at h
  split at h
  · next i i' h1 h2 =>
    simp only [Option.some.injEq] at h
    exact ⟨i, i', h1, h2, h.symm⟩
  · exact absurd h (by simp)

open SRIQT in
/-- **Up.** A model of `O` gives a model of the translated clauses that
satisfies the translated assertions, with individual `j` at the value of
`inds[j]` and each requested index standing for its IRI. -/
theorem core_up {O : Ontology} {requested inds : List IRI} (hO : O.isSHIQKB = true)
    {b : EL.St} {F : SRIQT.St} (hb : EL.WF (EL.setTopBottom b))
    (hF : (kbTBox O (defBase O requested)).axioms.foldl transAxiom (start b) = F)
    {L : List IRI} (hL : L = requested.eraseDups)
    (hidxS : ∀ (i : Nat) (h : i < L.length), b.cmap[L[i]]? = some i)
    {A : List (KA F.b.cdefs.size F.b.rdefs.size inds.length)}
    (hA : collect (assertsOf F (defBase O requested) inds F.b.cdefs.size F.b.rdefs.size)
      O.axioms.zipIdx = some A)
    {DM : DatatypeMap} {D : Type} [Nonempty D] (I : Interp DM D) (hI : OWL.Model O I) :
    ∃ J : SRI.Interp D (Fin F.b.cdefs.size) (Fin F.b.rdefs.size),
      SRIQ.models J (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size)) ∧
      SRIQ.satABox J (fun j => I.ind (.named inds[j])) A ∧
      ∀ (i : Nat) (hi : i < L.length) (hi' : i < F.b.cdefs.size) (x : D),
        J.c ⟨i, hi'⟩ x ↔ I.cls L[i] x := by
  set base := defBase O requested
  set I' := extI O base I
  have hS := start_wf hb
  have hLe : Le (start b) F := hF ▸ foldl_trans_le _ (start b)
  have hFwf : WF F := hF ▸ foldl_trans_wf _ (start b) hS
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQKB = true := by
    simpa [Ontology.isSHIQKB, List.all_eq_true] using hO
  have hKA : ∀ ax ∈ (kbTBox O base).axioms, ax.isSHIQ = true := by
    simpa [Ontology.isSHIQ, List.all_eq_true] using kbTBox_isSHIQ hO base
  have hext : ∀ ax ∈ O.axioms, ∀ c, c.isALCIQ = true → (∀ a ∈ c.names, a ∈ ax.classNames) →
      I'.ext c = I.ext c := fun ax hax c hc hn =>
    ClassExpr.ext_congr (I := I') (J := I) rfl c hc fun a ha => extI_cls_of_ne I (fresh_ax hax (hn a ha))
  -- The class name of a class assertion stands for its expression.
  have hname : ∀ j c bb, O.axioms[j]? = some (.classAssertion c bb) →
      ∀ x, I'.cls (assertName base j c) x ↔ I.ext c x := by
    intro j c bb hj x
    rcases assertName_cases base j c with ⟨a, rfl, he⟩ | he
    · rw [he, EL.ext_cls]
      have hax := List.mem_of_getElem? hj
      rw [extI_cls_of_ne I (fresh_ax hax (a := a) (by simp [Axiom.classNames, ClassExpr.names]))]
    · rw [he]; exact extI_cls_def I hj x
  have hsat : ∀ ax ∈ (kbTBox O base).axioms, I'.sat [] ax := by
    intro ax hax
    rcases mem_kbTBox.1 hax with ⟨h1, _⟩ | ⟨⟨ax', j⟩, hp, hd⟩
    · exact (Axiom.sat_congr (I := I') (J := I) rfl (hKA ax hax)
        (fun a ha => extI_cls_of_ne I (fresh_ax h1 ha)) [] O.namedIndividuals).2 (hI ax h1)
    · have hj : O.axioms[j]? = some ax' := List.mem_zipIdx_iff_getElem?.1 hp
      have hax' := mem_of_zipIdx hp
      have hk := hO' ax' hax'
      cases ax' <;> simp only [defAxioms, List.mem_singleton, List.not_mem_nil] at hd
      · next c bb =>
        subst hd
        simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
        intro x hx
        rw [EL.ext_cls, hname j c bb hj] at hx
        rw [hext _ hax' c hk.1 fun a ha => by simpa [Axiom.classNames] using ha]
        exact hx
      · subst hd
        intro x y hxy
        simp only [Interp.chain] at hxy
        obtain ⟨y', h1, rfl⟩ := hxy
        exact h1
      · subst hd
        intro x y hxy
        simp only [Interp.chain] at hxy
        obtain ⟨y', h1, rfl⟩ := hxy
        exact h1
  have hgood : Good I' F F := by
    have := foldl_trans_good I' F (N := []) (kbTBox O base).axioms (start b) hS (hF ▸ Le.rfl)
      (fun ax hax => ⟨hKA ax hax, hsat ax hax⟩) (by
        intro c hc
        simp only [start, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · intro y hy
          exact absurd (hy _ (by simp [start])) (extend_bottom I' F hS hLe y)
        · intro y _
          exact ⟨_, by simp [start], extend_top I' F hS hLe y⟩)
    rwa [hF] at this
  refine ⟨SRIT.lower _ _ (extend I' F), (fin_models hFwf).1 _ hgood, ?_, ?_⟩
  · intro y hy
    obtain ⟨⟨ax, j⟩, hp, l, hl, hyl⟩ := collect_mem hA y hy
    have hj : O.axioms[j]? = some ax := List.mem_zipIdx_iff_getElem?.1 hp
    have hax := mem_of_zipIdx hp
    have hk := hO' ax hax
    have hsx := hI ax hax
    cases ax with
    | classAssertion c a =>
      simp only [assertsOf] at hl
      split at hl
      · next i x hi hx =>
        simp only [Option.some.injEq] at hl; subst hl
        simp only [List.mem_singleton] at hyl; subst hyl
        obtain ⟨a', rfl, hia, -⟩ := indIx_spec hi
        show (extend I' F).c x.val _
        rw [extend_c I' F (hFwf.b.cmap _ _ (clsIx_spec hx)), EL.ext_cls, hname j c _ hj]
        beta_reduce; rw [hia]
        exact hsx
      · exact absurd hl (by simp)
    | objectPropertyAssertion r a a₂ =>
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      simp only [assertsOf] at hl
      split at hl
      · next i R i' hi hR hi' =>
        simp only [Option.some.injEq] at hl; subst hl
        simp only [List.mem_singleton] at hyl; subst hyl
        obtain ⟨a', rfl, hia, -⟩ := indIx_spec hi
        obtain ⟨a₂', rfl, hia₂, -⟩ := indIx_spec hi'
        obtain ⟨k, hk', hfin⟩ := roleIx_spec hR
        show (SRIT.lower _ _ (extend I' F)).rt R _ _
        rw [SRIT.finRT_sat _ _ _ hfin, extend_prop I' F hk.1.1 ⟨k, hFwf.b.rmap _ _ hk', rfl⟩,
          Interp.prop_congr rfl]
        beta_reduce; rw [hia, hia₂]
        exact hsx
      · exact absurd hl (by simp)
    | negativeObjectPropertyAssertion r a a₂ =>
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      simp only [assertsOf] at hl
      split at hl
      · next i R i' hi hR hi' =>
        simp only [Option.some.injEq] at hl; subst hl
        simp only [List.mem_singleton] at hyl; subst hyl
        obtain ⟨a', rfl, hia, -⟩ := indIx_spec hi
        obtain ⟨a₂', rfl, hia₂, -⟩ := indIx_spec hi'
        obtain ⟨k, hk', hfin⟩ := roleIx_spec hR
        show ¬ (SRIT.lower _ _ (extend I' F)).rt R _ _
        rw [SRIT.finRT_sat _ _ _ hfin, extend_prop I' F hk.1.1 ⟨k, hFwf.b.rmap _ _ hk', rfl⟩,
          Interp.prop_congr rfl]
        beta_reduce; rw [hia, hia₂]
        exact hsx
      · exact absurd hl (by simp)
    | sameIndividual as =>
      simp only [assertsOf] at hl
      obtain ⟨p, hpm, l', hl', hyl'⟩ := collect_mem hl y hyl
      obtain ⟨i, i', hi, hi', rfl⟩ := pairAssert_spec hl'
      simp only [List.mem_singleton] at hyl'; subst hyl'
      obtain ⟨a', ha', hia, -⟩ := indIx_spec hi
      obtain ⟨a₂', ha₂', hia₂, -⟩ := indIx_spec hi'
      have hpm' := mem_allPairs.1 hpm
      show I.ind (.named inds[i]) = I.ind (.named inds[i'])
      rw [hia, hia₂, ← ha', ← ha₂']
      exact hsx _ hpm'.1 _ hpm'.2
    | differentIndividuals as =>
      simp only [assertsOf] at hl
      obtain ⟨p, hpm, l', hl', hyl'⟩ := collect_mem hl y hyl
      obtain ⟨i, i', hi, hi', rfl⟩ := pairAssert_spec hl'
      simp only [List.mem_singleton] at hyl'; subst hyl'
      obtain ⟨a', ha', hia, -⟩ := indIx_spec hi
      obtain ⟨a₂', ha₂', hia₂, -⟩ := indIx_spec hi'
      show I.ind (.named inds[i]) ≠ I.ind (.named inds[i'])
      rw [hia, hia₂, ← ha', ← ha₂']
      exact (pairwise_iff_pairsOf.1 hsx) p hpm
    | _ => simp [assertsOf] at hl; subst hl; simp at hyl
  · intro i hi hi' x
    have hc := hFwf.b.cmap _ _ (hLe.b.cmap _ _ (hidxS i hi))
    have hreq : L[i] ∈ requested := by
      have h2 : ∀ y ∈ L, y ∈ requested := by
        rw [hL]; intro y hy; exact List.mem_eraseDups.1 hy
      exact h2 _ (List.getElem_mem hi)
    show (extend I' F).c i x ↔ _
    rw [extend_c I' F hc, EL.ext_cls, extI_cls_of_ne I (fresh_req hreq)]

open SRIQT in
/-- **Down.** A model of the translated clauses that satisfies the
translated assertions gives a model of `O`, with the individual `a` at the
value of its index `inds.idxOf a` and each requested IRI standing for its
index. -/
theorem core_down {O : Ontology} {requested inds : List IRI} (hO : O.isSHIQKB = true)
    {b : EL.St} {F : SRIQT.St} (hb : EL.WF (EL.setTopBottom b))
    (hF : (kbTBox O (defBase O requested)).axioms.foldl transAxiom (start b) = F)
    {L : List IRI} (hidxS : ∀ (i : Nat) (h : i < L.length), b.cmap[L[i]]? = some i)
    {A : List (KA F.b.cdefs.size F.b.rdefs.size inds.length)}
    (hA : collect (assertsOf F (defBase O requested) inds F.b.cdefs.size F.b.rdefs.size)
      O.axioms.zipIdx = some A)
    {D : Type} [Nonempty D] (J : SRI.Interp D (Fin F.b.cdefs.size) (Fin F.b.rdefs.size))
    (ind : Fin inds.length → D)
    (hJ : SRIQ.models J (F.out.reverse.filterMap (toFin F.b.cdefs.size F.b.rdefs.size)))
    (hAs : SRIQ.satABox J ind A) :
    ∃ I : Interp DatatypeMap.trivial D, OWL.Model O I ∧
      (∀ (a : IRI) (h : inds.idxOf a < inds.length), I.ind (.named a) = ind ⟨_, h⟩) ∧
      ∀ (i : Nat) (hi : i < L.length) (hi' : i < F.b.cdefs.size) (x : D),
        I.cls L[i] x ↔ J.c ⟨i, hi'⟩ x := by
  set base := defBase O requested
  have hS := start_wf hb
  have hLe : Le (start b) F := hF ▸ foldl_trans_le _ (start b)
  have hFwf : WF F := hF ▸ foldl_trans_wf _ (start b) hS
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQKB = true := by
    simpa [Ontology.isSHIQKB, List.all_eq_true] using hO
  have hKA : ∀ ax ∈ (kbTBox O base).axioms, ax.isSHIQ = true := by
    simpa [Ontology.isSHIQ, List.all_eq_true] using kbTBox_isSHIQ hO base
  let K := SRIT.raise F.b.cdefs.size F.b.rdefs.size J
  have hK : ∀ c ∈ F.out, SRIQ.satClause K c := (fin_models hFwf).2 J hJ
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
  have hR : ∀ ax ∈ (kbTBox O base).axioms, (restrict F K).sat [] ax := by
    intro ax hax
    obtain ⟨s', _, hle⟩ := foldl_trans_mem _ (start b) hS ax hax
    exact transAxiom_restrict F K hK hT hB s' ax (hF ▸ hle) (hKA ax hax)
  let ind0 : D := Classical.choice inferInstance
  let I : Interp DatatypeMap.trivial D := { restrict F K with ind := indMap inds ind ind0 }
  have hrt : ∀ (r : ObjProp), r.isBasic = true → ∀ k, F.b.rmap[EL.propIRI r]? = some k →
      ∀ R, SRIT.finRT F.b.rdefs.size (SRIT.mkRT r k) = some R →
      ∀ x y, I.prop r x y ↔ J.rt R x y := by
    intro r hr k hk R hfin x y
    have h1 := SRIT.finRT_sat F.b.cdefs.size F.b.rdefs.size K hfin x y
    rw [SRIT.lower_raise] at h1
    rw [h1, ← restrict_prop hr ⟨k, hk, rfl⟩]
    exact Iff.of_eq (congrFun (congrFun (Interp.prop_congr (I := I) (J := restrict F K) rfl r) x) y)
  refine ⟨I, ?_, ?_, ?_⟩
  · intro ax hax
    have hk := hO' ax hax
    cases hn : ax.isAssertion
    · have hm : ax ∈ (kbTBox O base).axioms := mem_kbTBox.2 (Or.inl ⟨hax, hn⟩)
      exact (Axiom.sat_congr (I := I) (J := restrict F K) rfl (hKA ax hm) (fun _ _ => rfl)
        _ []).2 (hR ax hm)
    · obtain ⟨j, hp⟩ := exists_zipIdx hax
      obtain ⟨l, hl, hlA⟩ := collect_some hA _ hp
      cases ax with
      | classAssertion c a =>
        simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
        simp only [assertsOf] at hl
        split at hl
        · next i x hi hx =>
          simp only [Option.some.injEq] at hl; subst hl
          have hs : J.c x (ind i) := hAs _ (hlA _ (List.mem_singleton_self _))
          have hdm : Axiom.subClassOf (.cls (assertName base j c)) c ∈ (kbTBox O base).axioms :=
            mem_kbTBox.2 (Or.inr ⟨_, hp, by simp [defAxioms]⟩)
          have hd : (restrict F K).ext c (ind i) := hR _ hdm (ind i) (by
            rw [EL.ext_cls, restrict_cls (clsIx_spec hx)]
            exact ⟨x.isLt, hs⟩)
          show I.ext c (indMap inds ind ind0 a)
          rw [indMap_of_indIx hi, ClassExpr.ext_congr (I := I) (J := restrict F K) rfl c hk.1
            (fun _ _ => rfl)]
          exact hd
        · exact absurd hl (by simp)
      | objectPropertyAssertion r a a₂ =>
        simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
        simp only [assertsOf] at hl
        split at hl
        · next i R i' hi hR' hi' =>
          simp only [Option.some.injEq] at hl; subst hl
          have hs : J.rt R (ind i) (ind i') := hAs _ (hlA _ (List.mem_singleton_self _))
          obtain ⟨k, hk', hfin⟩ := roleIx_spec hR'
          show I.prop r (indMap inds ind ind0 a) (indMap inds ind ind0 a₂)
          rw [indMap_of_indIx hi, indMap_of_indIx hi', hrt r hk.1.1 k hk' R hfin]
          exact hs
        · exact absurd hl (by simp)
      | negativeObjectPropertyAssertion r a a₂ =>
        simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
        simp only [assertsOf] at hl
        split at hl
        · next i R i' hi hR' hi' =>
          simp only [Option.some.injEq] at hl; subst hl
          have hs : ¬ J.rt R (ind i) (ind i') := hAs _ (hlA _ (List.mem_singleton_self _))
          obtain ⟨k, hk', hfin⟩ := roleIx_spec hR'
          show ¬ I.prop r (indMap inds ind ind0 a) (indMap inds ind ind0 a₂)
          rw [indMap_of_indIx hi, indMap_of_indIx hi', hrt r hk.1.1 k hk' R hfin]
          exact hs
        · exact absurd hl (by simp)
      | sameIndividual as =>
        simp only [assertsOf] at hl
        intro a ha a₂ ha₂
        obtain ⟨l', hl', hlA'⟩ := collect_some hl (a, a₂) (mem_allPairs.2 ⟨ha, ha₂⟩)
        obtain ⟨i, i', hi, hi', rfl⟩ := pairAssert_spec hl'
        have hs : ind i = ind i' := hAs _ (hlA _ (hlA' _ (List.mem_singleton_self _)))
        show indMap inds ind ind0 a = indMap inds ind ind0 a₂
        rw [indMap_of_indIx hi, indMap_of_indIx hi']
        exact hs
      | differentIndividuals as =>
        simp only [assertsOf] at hl
        refine pairwise_iff_pairsOf.2 fun p hpm => ?_
        obtain ⟨l', hl', hlA'⟩ := collect_some hl p hpm
        obtain ⟨i, i', hi, hi', rfl⟩ := pairAssert_spec hl'
        have hs : ind i ≠ ind i' := hAs _ (hlA _ (hlA' _ (List.mem_singleton_self _)))
        show indMap inds ind ind0 p.1 ≠ indMap inds ind ind0 p.2
        rw [indMap_of_indIx hi, indMap_of_indIx hi']
        exact hs
      | declareNamedIndividual _ => trivial
      | _ => simp [Axiom.isAssertion] at hn
  · intro a h
    simp [I, indMap, h]
  · intro i hi hi' x
    show (restrict F K).cls L[i] x ↔ _
    rw [restrict_cls (hLe.b.cmap _ _ (hidxS i hi))]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hi', h⟩⟩

end ContextCalculus.OWLFrontend.SRIQKB

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SRIQKB

variable {O : OWL.Ontology} {requested extra : List OWL.IRI} {T : SRIQKBTranslation}

theorem translateSRIQKB_spec (h : translateSRIQKB O requested extra = some T) :
    O.isSHIQKB = true ∧ T.named = requested.eraseDups ∧ T.inds = (O.individualNames ++ extra).eraseDups := by
  simp only [translateSRIQKB] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hO
  split at h
  case isFalse => exact absurd h (by simp)
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨hO, (SRIQT.run_spec (kbTBox O (defBase O requested)) requested).choose_spec.2.1, rfl⟩

/-- **Up.** A model of `O` gives a model of the translated knowledge base,
with the individual of index `j` at the value of `T.inds[j]` and each
requested index standing for its IRI. -/
theorem translateSRIQKB_up (h : translateSRIQKB O requested extra = some T)
    {DM : DatatypeMap} {D : Type} [Nonempty D] (I : Interp DM D) (hI : OWL.Model O I) :
    ∃ J : SRI.Interp D (Fin T.conceptCount) (Fin T.roleCount),
      SRIQ.models J T.ontology ∧ SRIQ.satABox J (fun j => I.ind (.named T.inds[j])) T.abox ∧
      ∀ (i : Nat) (hi : i < T.named.length) (x : D),
        J.c ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ x ↔ I.cls T.named[i] x := by
  simp only [translateSRIQKB] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hO
  split at h
  case isFalse => exact absurd h (by simp)
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨b, hb, hL, hidx, hF⟩ := SRIQT.run_spec (kbTBox O (defBase O requested)) requested
  obtain ⟨J, h1, h2, h3⟩ := core_up hO hb hF hL hidx hA I hI
  exact ⟨J, h1, h2, fun i hi x => h3 i hi _ x⟩

/-- **Down.** A model of the translated knowledge base gives a model of
`O`, with each individual `a` of `T.inds` at the value of its index and
each requested IRI standing for its index. -/
theorem translateSRIQKB_down (h : translateSRIQKB O requested extra = some T)
    {D : Type} [Nonempty D] (J : SRI.Interp D (Fin T.conceptCount) (Fin T.roleCount))
    (ind : Fin T.inds.length → D) (hJ : SRIQ.models J T.ontology)
    (hA : SRIQ.satABox J ind T.abox) :
    ∃ I : Interp DatatypeMap.trivial D, OWL.Model O I ∧
      (∀ (a : IRI) (ha : T.inds.idxOf a < T.inds.length), I.ind (.named a) = ind ⟨_, ha⟩) ∧
      ∀ (i : Nat) (hi : i < T.named.length) (x : D),
        I.cls T.named[i] x ↔ J.c ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ x := by
  simp only [translateSRIQKB] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hO
  split at h
  case isFalse => exact absurd h (by simp)
  obtain ⟨A, hA', rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨b, hb, -, hidx, hF⟩ := SRIQT.run_spec (kbTBox O (defBase O requested)) requested
  obtain ⟨I, h1, h2, h3⟩ := core_down hO hb hF hidx hA' J ind hJ hA
  exact ⟨I, h1, h2, fun i hi x => h3 i hi _ x⟩

/-- Subsumption between requested IRIs is subsumption under the translated
knowledge base. -/
theorem translateSRIQKB_entailsSub (h : translateSRIQKB O requested extra = some T)
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWL.EntailsSub O T.named[i] T.named[j] ↔
      SRIQ.EntailsSubKB T.ontology T.abox ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩
        ⟨j, Nat.lt_of_lt_of_le hj T.hnamed⟩ := by
  constructor
  · intro hs D _ J ind hJ hA x hx
    obtain ⟨I, hI, -, hc⟩ := translateSRIQKB_down h J ind hJ hA
    exact (hc j hj x).1 (hs DatatypeMap.trivial D I hI x ((hc i hi x).2 hx))
  · intro hs DM D _ I hI x hx
    obtain ⟨J, hJ, hA, hc⟩ := translateSRIQKB_up h I hI
    exact (hc j hj x).1 (hs D J _ hJ hA x ((hc i hi x).2 hx))

/-- `O` is inconsistent iff the translated knowledge base is. -/
theorem translateSRIQKB_inconsistent (h : translateSRIQKB O requested extra = some T) :
    OWL.Inconsistent O ↔ ¬ SRIQ.ConsistentKB T.ontology T.abox := by
  constructor
  · rintro hinc ⟨D, hD, J, ind, hJ, hA⟩
    obtain ⟨I, hI, -⟩ := translateSRIQKB_down h J ind hJ hA
    exact hinc DatatypeMap.trivial D I hI
  · intro hn DM D _ I hI
    obtain ⟨J, hJ, hA, -⟩ := translateSRIQKB_up h I hI
    exact hn ⟨D, inferInstance, J, _, hJ, hA⟩

/-- An entailed class assertion of a requested IRI about an individual of
`T.inds` is an entailed type. -/
theorem translateSRIQKB_entailsType (h : translateSRIQKB O requested extra = some T)
    (i : Nat) (hi : i < T.named.length) (a : IRI) (ha : T.inds.idxOf a < T.inds.length) :
    OWL.Entails O (.classAssertion (.cls T.named[i]) (.named a)) ↔
      SRIQ.EntailsTypeKB T.ontology T.abox ⟨_, ha⟩ ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ := by
  constructor
  · intro he D _ J ind hJ hA
    obtain ⟨I, hI, hind, hc⟩ := translateSRIQKB_down h J ind hJ hA
    have := he DatatypeMap.trivial D I hI
    simp only [Interp.sat, EL.ext_cls] at this
    rw [hind a ha] at this
    exact (hc i hi _).1 this
  · intro he DM D _ I hI
    obtain ⟨J, hJ, hA, hc⟩ := translateSRIQKB_up h I hI
    have := (hc i hi _).1 (he D J _ hJ hA)
    simp only [Interp.sat, EL.ext_cls]
    simp only [Fin.getElem_fin, List.getElem_idxOf] at this
    exact this

/-- An entailed equality of two individuals of `T.inds` is an entailed
equality of their indices. -/
theorem translateSRIQKB_entailsSame (h : translateSRIQKB O requested extra = some T)
    (a b : IRI) (ha : T.inds.idxOf a < T.inds.length) (hb : T.inds.idxOf b < T.inds.length) :
    OWL.Entails O (.sameIndividual [.named a, .named b]) ↔
      SRIQ.EntailsSameKB T.ontology T.abox ⟨_, ha⟩ ⟨_, hb⟩ := by
  have hsat : ∀ {DM : DatatypeMap} {D : Type} (I : Interp DM D) (N : List IRI),
      I.sat N (.sameIndividual [.named a, .named b]) ↔ I.ind (.named a) = I.ind (.named b) := by
    intro DM D I N
    simp only [Interp.sat]
    constructor
    · intro h; exact h _ (by simp) _ (by simp)
    · intro h x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl
  constructor
  · intro he D _ J ind hJ hA
    obtain ⟨I, hI, hind, -⟩ := translateSRIQKB_down h J ind hJ hA
    have := (hsat I _).1 (he DatatypeMap.trivial D I hI)
    rwa [hind a ha, hind b hb] at this
  · intro he DM D _ I hI
    obtain ⟨J, hJ, hA, -⟩ := translateSRIQKB_up h I hI
    have := he D J _ hJ hA
    simp only [Fin.getElem_fin, List.getElem_idxOf] at this
    exact (hsat I _).2 this

/-! ## The translation succeeds on the fragment -/

open SRIQT in
theorem SRIQKB.lookup_cls {O' : Ontology} {b : EL.St} {F : SRIQT.St}
    (hb : EL.WF (EL.setTopBottom b)) (hF : O'.axioms.foldl transAxiom (start b) = F) {X : IRI}
    {c : ClassExpr} (hm : Axiom.subClassOf (.cls X) c ∈ O'.axioms) :
    ∃ x, clsIx F F.b.cdefs.size X = some x := by
  have hS := start_wf hb
  have hFwf : WF F := hF ▸ foldl_trans_wf _ (start b) hS
  obtain ⟨s', _, hle⟩ := foldl_trans_mem _ (start b) hS _ hm
  rw [hF] at hle
  simp only [transAxiom, transExpr] at hle
  have hle' : Le (internC X s').2 F := (transExpr_le c true _).trans ((emit_le _ _).trans hle)
  have hk := hle'.b.cmap _ _ (internC_cmap X s')
  have hlt : (internC X s').1 < F.b.cdefs.size := ALC.CIn.lt ⟨_, hFwf.b.cmap _ _ hk⟩
  exact ⟨⟨_, hlt⟩, by simp [clsIx, hk, hlt]⟩

open SRIQT in
theorem SRIQKB.lookup_role {O' : Ontology} {b : EL.St} {F : SRIQT.St}
    (hb : EL.WF (EL.setTopBottom b)) (hF : O'.axioms.foldl transAxiom (start b) = F) {r : ObjProp}
    (hm : Axiom.subObjectPropertyOf [r] r ∈ O'.axioms) :
    ∃ R, roleIx F F.b.rdefs.size r = some R := by
  have hS := start_wf hb
  have hFwf : WF F := hF ▸ foldl_trans_wf _ (start b) hS
  obtain ⟨s', _, hle⟩ := foldl_trans_mem _ (start b) hS _ hm
  rw [hF] at hle
  simp only [transAxiom] at hle
  have hle' := (emit_le _ _).trans hle
  obtain ⟨k, hk, -⟩ := roleT_ok r (roleTs [r] s' []).2
  have hk' := hle'.b.rmap _ _ hk
  have hlt : k < F.b.rdefs.size := ALC.RIn.lt ⟨_, hFwf.b.rmap _ _ hk'⟩
  obtain ⟨R, hR⟩ := SRIT.finRT_isSome F.b.rdefs.size (SRIT.mkRT r k) (by
    rw [SRIT.rIx_mkRT]; exact hlt)
  exact ⟨R, by simp [roleIx, hk', hR]⟩

theorem SRIQKB.indIx_isSome {inds : List IRI} {a : IRI} (h : a ∈ inds) :
    ∃ i, indIx inds (.named a) = some i := by
  have := List.idxOf_lt_length_of_mem h
  exact ⟨⟨_, this⟩, by simp [indIx, this]⟩

theorem SRIQKB.mem_inds {O : Ontology} {extra : List IRI} {ax : Axiom} (hax : ax ∈ O.axioms)
    {a : IRI} (ha : a ∈ ax.namedIndividuals) : a ∈ (O.individualNames ++ extra).eraseDups :=
  List.mem_eraseDups.2 (List.mem_append_left _ ((O.mem_namesBy _ a).2 ⟨ax, hax, ha⟩))

/-- On the SHIQ knowledge-base part the translation succeeds. -/
theorem translateSRIQKB_isSome (hO : O.isSHIQKB = true) :
    (translateSRIQKB O requested extra).isSome = true := by
  set base := defBase O requested
  obtain ⟨b, hb, _, hidx, hF⟩ := SRIQT.run_spec (kbTBox O base) requested
  have hS := SRIQT.start_wf hb
  have hFwf : SRIQT.WF (SRIQT.run (kbTBox O base) requested).1 :=
    hF ▸ SRIQT.foldl_trans_wf _ _ hS
  have hLe : SRIQT.Le (SRIQT.start b) (SRIQT.run (kbTBox O base) requested).1 :=
    hF ▸ SRIQT.foldl_trans_le _ _
  have hlen : (SRIQT.run (kbTBox O base) requested).2.length ≤
      (SRIQT.run (kbTBox O base) requested).1.b.cdefs.size := by
    cases hn : (SRIQT.run (kbTBox O base) requested).2.length with
    | zero => exact Nat.zero_le _
    | succ k =>
        have hk : k < (SRIQT.run (kbTBox O base) requested).2.length := by omega
        have hc := hLe.b.cmap _ _ (hidx k hk)
        exact (show ALC.CIn _ k from ⟨_, hFwf.b.cmap _ _ hc⟩).lt
  have hO' : ∀ ax ∈ O.axioms, ax.isSHIQKB = true := by
    simpa [Ontology.isSHIQKB, List.all_eq_true] using hO
  have hcol : (collect (assertsOf (SRIQT.run (kbTBox O base) requested).1 base
      (O.individualNames ++ extra).eraseDups (SRIQT.run (kbTBox O base) requested).1.b.cdefs.size
      (SRIQT.run (kbTBox O base) requested).1.b.rdefs.size) O.axioms.zipIdx).isSome = true := by
    refine collect_isSome fun ⟨ax, j⟩ hp => ?_
    have hax := mem_of_zipIdx hp
    have hk := hO' ax hax
    have hdef : ∀ ax' ∈ defAxioms base (ax, j), ax' ∈ (kbTBox O base).axioms :=
      fun ax' h' => mem_kbTBox.2 (Or.inr ⟨_, hp, h'⟩)
    have hpair : ∀ (as : List Individual), (∀ a ∈ as, a.isNamed = true) →
        (∀ a' ∈ as.flatMap Individual.namedIRI, a' ∈ (O.individualNames ++ extra).eraseDups) →
        ∀ (mk : Fin (O.individualNames ++ extra).eraseDups.length → Fin (O.individualNames ++ extra).eraseDups.length →
          KA (SRIQT.run (kbTBox O base) requested).1.b.cdefs.size
            (SRIQT.run (kbTBox O base) requested).1.b.rdefs.size (O.individualNames ++ extra).eraseDups.length)
          (p : Individual × Individual), p.1 ∈ as → p.2 ∈ as →
          (pairAssert (O.individualNames ++ extra).eraseDups mk p).isSome = true := by
      intro as hn hm mk p h1 h2
      have hn1 := hn _ h1
      have hn2 := hn _ h2
      obtain ⟨p1, p2⟩ := p
      cases p1 with
      | anon _ => simp [Individual.isNamed] at hn1
      | named a1 =>
        cases p2 with
        | anon _ => simp [Individual.isNamed] at hn2
        | named a2 =>
          obtain ⟨i1, hi1⟩ := indIx_isSome (hm a1 (List.mem_flatMap.2 ⟨_, h1, by simp [Individual.namedIRI]⟩))
          obtain ⟨i2, hi2⟩ := indIx_isSome (hm a2 (List.mem_flatMap.2 ⟨_, h2, by simp [Individual.namedIRI]⟩))
          simp [pairAssert, hi1, hi2]
    cases ax with
    | classAssertion c a =>
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      cases a with
      | anon _ => simp [Individual.isNamed] at hk
      | named a =>
        obtain ⟨i, hi⟩ := indIx_isSome (mem_inds (extra := extra) hax
          (a := a) (by simp [Axiom.namedIndividuals, Individual.namedIRI]))
        obtain ⟨x, hx⟩ := lookup_cls hb hF (hdef (.subClassOf (.cls (assertName base j c)) c)
          (by simp [defAxioms]))
        simp [assertsOf, hi, hx]
    | objectPropertyAssertion r a a₂ =>
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      cases a with
      | anon _ => simp [Individual.isNamed] at hk
      | named a =>
        cases a₂ with
        | anon _ => simp [Individual.isNamed] at hk
        | named a₂ =>
          obtain ⟨i, hi⟩ := indIx_isSome (mem_inds (extra := extra) hax
            (a := a) (by simp [Axiom.namedIndividuals, Individual.namedIRI]))
          obtain ⟨i', hi'⟩ := indIx_isSome (mem_inds (extra := extra) hax
            (a := a₂) (by simp [Axiom.namedIndividuals, Individual.namedIRI]))
          obtain ⟨R, hR⟩ := lookup_role hb hF (hdef (.subObjectPropertyOf [r] r)
            (by simp [defAxioms]))
          simp [assertsOf, hi, hi', hR]
    | negativeObjectPropertyAssertion r a a₂ =>
      simp only [Axiom.isSHIQKB, Bool.and_eq_true] at hk
      cases a with
      | anon _ => simp [Individual.isNamed] at hk
      | named a =>
        cases a₂ with
        | anon _ => simp [Individual.isNamed] at hk
        | named a₂ =>
          obtain ⟨i, hi⟩ := indIx_isSome (mem_inds (extra := extra) hax
            (a := a) (by simp [Axiom.namedIndividuals, Individual.namedIRI]))
          obtain ⟨i', hi'⟩ := indIx_isSome (mem_inds (extra := extra) hax
            (a := a₂) (by simp [Axiom.namedIndividuals, Individual.namedIRI]))
          obtain ⟨R, hR⟩ := lookup_role hb hF (hdef (.subObjectPropertyOf [r] r)
            (by simp [defAxioms]))
          simp [assertsOf, hi, hi', hR]
    | sameIndividual as =>
      simp only [Axiom.isSHIQKB, List.all_eq_true] at hk
      simp only [assertsOf]
      refine collect_isSome fun p hp' => ?_
      have := mem_allPairs.1 hp'
      exact hpair as hk (fun a' ha' => mem_inds hax (by simpa [Axiom.namedIndividuals] using ha'))
        _ p this.1 this.2
    | differentIndividuals as =>
      simp only [Axiom.isSHIQKB, List.all_eq_true] at hk
      simp only [assertsOf]
      refine collect_isSome fun p hp' => ?_
      have := mem_pairsOf hp'
      exact hpair as hk (fun a' ha' => mem_inds hax (by simpa [Axiom.namedIndividuals] using ha'))
        _ p this.1 this.2
    | _ => simp [assertsOf]
  simp only [translateSRIQKB, hO, if_true]
  split
  · simp only [Option.isSome_map]
    exact hcol
  · exact absurd hlen ‹_›

open SRIQT in
/-- On the SHIQ knowledge-base part every chain clause of the translation
passes the route's chain check. -/
theorem translateSRIQKB_chainsOK (h : translateSRIQKB O requested extra = some T) :
    T.ontology.all chainOKQ = true := by
  simp only [translateSRIQKB] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hO
  split at h
  case isFalse => exact absurd h (by simp)
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨b, _, _, _, hF⟩ := SRIQT.run_spec (kbTBox O (defBase O requested)) requested
  have hok : ChainsOK (SRIQT.run (kbTBox O (defBase O requested)) requested).1 := by
    rw [← hF]
    refine foldl_trans_chainsOK _ _ (start_chainsOK b) ?_
    simpa [OWL.Ontology.isSHIQ, List.all_eq_true] using kbTBox_isSHIQ hO (defBase O requested)
  simp only [List.all_eq_true, List.mem_filterMap]
  rintro c' ⟨c, hc, hfin⟩
  refine toFin_chainOK (fun body S hcs => ?_) hfin
  subst hcs
  exact hok body S (List.mem_reverse.1 hc)

#print axioms translateSRIQKB_isSome
#print axioms translateSRIQKB_chainsOK
#print axioms translateSRIQKB_up
#print axioms translateSRIQKB_down
#print axioms translateSRIQKB_entailsSub
#print axioms translateSRIQKB_inconsistent
#print axioms translateSRIQKB_entailsType
#print axioms translateSRIQKB_entailsSame

end ContextCalculus.OWLFrontend
