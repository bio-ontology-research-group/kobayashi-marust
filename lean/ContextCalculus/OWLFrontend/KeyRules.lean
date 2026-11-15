import ContextCalculus.OWLFrontend.RuleGround

/-!
# `HasKey` as DL-safe rules (stage C5, item 4)

A key `HasKey(C (r1 ... rm) ())` ranges over named individuals: for named
`x`, `y` in `C` with a named common `ri`-filler for every `i`, `x = y`
(Direct Semantics, `ISNAMED`). That is the DL-safe rule

```
C(x) ∧ C(y) ∧ r1(x, z1) ∧ r1(y, z1) ∧ ... ∧ rm(x, zm) ∧ rm(y, zm) → x = y
```

(`keyRule`). `keyOff` moves every key of an ontology with rules into its
rules; `modelR_keyOff` says the models are the same. The grounding of
`RuleGround.lean` then removes the rules, and every route runs on an
ontology without `HasKey`: the `noKey` restrictions of the earlier layers
(anonymous individuals, rows, datatype definitions) apply to that encoded
ontology only. Anonymous individuals in assertions are allowed together
with keys: they are not named, so neither a key nor a rule reaches them,
and the renaming of `SROIQAnon.lean` runs after the keys are gone.

Not done: keys with data properties (`HasKey(C () (p1 ... pn))`): the common
value is a data variable, which the grounding does not express
(`keyOff` declines); rows over ontologies with keys or rules.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

variable {DM : DatatypeMap} {Dom : Type}

/-- The variable of the `i`-th key property. -/
def keyVar (i : Nat) : IRI := "".pushn 'z' (i + 1)

theorem keyVar_length (i : Nat) : (keyVar i).length = i + 1 := by
  simp [keyVar, String.length_pushn]

theorem keyVar_ne_x (i : Nat) : keyVar i ≠ "x" := by
  intro h
  have hl := congrArg String.length h
  rw [keyVar_length] at hl
  have h1 : ("x" : String).length = 1 := rfl
  have : i = 0 := by omega
  subst this
  revert h; decide

theorem keyVar_ne_y (i : Nat) : keyVar i ≠ "y" := by
  intro h
  have hl := congrArg String.length h
  rw [keyVar_length] at hl
  have h1 : ("y" : String).length = 1 := rfl
  have : i = 0 := by omega
  subst this
  revert h; decide

/-- The body atoms of the key properties. -/
def keyAtoms (rs : List ObjProp) : List RAtom :=
  (List.finRange rs.length).flatMap fun (i : Fin rs.length) =>
    [.obj (rs.get i) (.var "x") (.var (keyVar i)), .obj (rs.get i) (.var "y") (.var (keyVar i))]

/-- **The rule of a key.** -/
def keyRule (c : ClassExpr) (rs : List ObjProp) : DLRule :=
  ⟨.cls c (.var "x") :: .cls c (.var "y") :: keyAtoms rs, [.same (.var "x") (.var "y")]⟩

/-- Satisfaction of a rule depends on the named individuals only through
membership. -/
theorem isNamed_congr (I : Interp DM Dom) {N N' : List IRI} (h : ∀ a, a ∈ N ↔ a ∈ N') (x : Dom) :
    I.IsNamed N x ↔ I.IsNamed N' x := by
  simp only [Interp.IsNamed, h]

theorem ruleSat_congr (bi : BuiltIns DM) (I : Interp DM Dom) {N N' : List IRI}
    (h : ∀ a, a ∈ N ↔ a ∈ N') (ρ : DLRule) : ρ.sat bi I N ↔ ρ.sat bi I N' := by
  simp only [DLRule.sat, isNamed_congr I h]

/-- **A key is its rule.** -/
theorem sat_hasKey_iff [hv : Nonempty DM.Val] (bi : BuiltIns DM) (I : Interp DM Dom) (N : List IRI) (c : ClassExpr)
    (rs : List ObjProp) : I.sat N (.hasKey c rs []) ↔ (keyRule c rs).sat bi I N := by
  classical
  simp only [Interp.sat, List.not_mem_nil, false_implies, implies_true, forall_const]
  have hbody : ∀ (σ : IRI → Dom) (δ : IRI → DM.Val), (∀ a ∈ (keyRule c rs).body, a.sat bi I σ δ) ↔
      I.ext c (σ "x") ∧ I.ext c (σ "y") ∧ ∀ i : Fin rs.length,
        I.prop (rs.get i) (σ "x") (σ (keyVar i)) ∧ I.prop (rs.get i) (σ "y") (σ (keyVar i)) := by
    intro σ δ
    simp only [keyRule, keyAtoms, List.mem_cons, forall_eq_or_imp, List.mem_flatMap,
      List.mem_finRange, true_and, List.not_mem_nil, or_false]
    simp only [RAtom.sat, IArg.val]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun i => ⟨h3 _ ⟨i, Or.inl rfl⟩, h3 _ ⟨i, Or.inr rfl⟩⟩⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun a ⟨i, hi⟩ => ?_⟩
      rcases hi with rfl | rfl
      · exact (h3 i).1
      · exact (h3 i).2
  have hvars : ∀ v ∈ (keyRule c rs).ivars, v = "x" ∨ v = "y" ∨ ∃ i : Fin rs.length, v = keyVar i := by
    intro v hv
    obtain ⟨a, ha, hva⟩ := List.mem_flatMap.1 hv
    simp only [keyRule, List.cons_append, List.mem_cons, List.mem_append, keyAtoms,
      List.mem_flatMap, List.mem_finRange, true_and, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | ⟨i, hi⟩ | rfl
    · simp [RAtom.ivars, IArg.vars] at hva; exact Or.inl hva
    · simp [RAtom.ivars, IArg.vars] at hva; exact Or.inr (Or.inl hva)
    · rcases hi with rfl | rfl <;> simp [RAtom.ivars, IArg.vars] at hva <;> rcases hva with hva | hva
      · exact Or.inl hva
      · exact Or.inr (Or.inr ⟨i, hva⟩)
      · exact Or.inr (Or.inl hva)
      · exact Or.inr (Or.inr ⟨i, hva⟩)
    · simp [RAtom.ivars, IArg.vars] at hva
      rcases hva with hva | hva
      · exact Or.inl hva
      · exact Or.inr (Or.inl hva)
  constructor
  · intro hk σ δ hn hb a ha
    simp only [keyRule, List.mem_singleton] at ha
    subst ha
    obtain ⟨h1, h2, h3⟩ := (hbody σ δ).1 hb
    have hxv : "x" ∈ (keyRule c rs).ivars := by simp [DLRule.ivars, keyRule, RAtom.ivars, IArg.vars]
    have hyv : "y" ∈ (keyRule c rs).ivars := by simp [DLRule.ivars, keyRule, RAtom.ivars, IArg.vars]
    refine hk _ _ (hn _ hxv) (hn _ hyv) h1 h2 fun r hr => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    have hzv : keyVar i ∈ (keyRule c rs).ivars := by
      refine List.mem_flatMap.2 ⟨.obj (rs.get ⟨i, hi⟩) (.var "x") (.var (keyVar i)), ?_,
        by simp [RAtom.ivars, IArg.vars]⟩
      simp only [keyRule, keyAtoms, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_flatMap, List.mem_finRange, true_and]
      exact Or.inr (Or.inr (Or.inl ⟨⟨i, hi⟩, Or.inl rfl⟩))
    exact ⟨_, hn _ hzv, (h3 ⟨i, hi⟩).1, (h3 ⟨i, hi⟩).2⟩
  · intro hr x y hx hy hcx hcy hz
    let zf : Nat → Dom := fun i => if h : i < rs.length then (hz rs[i] (List.getElem_mem h)).choose else x
    let σ : IRI → Dom := fun v => if v = "x" then x else if v = "y" then y else zf (v.length - 1)
    have hσx : σ "x" = x := by simp [σ]
    have hσy : σ "y" = y := by simp [σ]
    have hσz : ∀ i : Fin rs.length, σ (keyVar i) = (hz rs[i] (List.getElem_mem i.2)).choose := by
      intro i
      simp only [σ, keyVar_ne_x, keyVar_ne_y, if_false, keyVar_length, Nat.add_sub_cancel, zf,
        dif_pos i.2]
    have hn : ∀ v ∈ (keyRule c rs).ivars, I.IsNamed N (σ v) := by
      intro v hv
      rcases hvars v hv with rfl | rfl | ⟨i, rfl⟩
      · rw [hσx]; exact hx
      · rw [hσy]; exact hy
      · rw [hσz]; exact (hz rs[i] (List.getElem_mem i.2)).choose_spec.1
    have hb := (hbody σ (fun _ => Classical.choice hv)).2
      ⟨by rw [hσx]; exact hcx, by rw [hσy]; exact hcy, fun i => by
        rw [hσx, hσy, hσz]
        exact (hz rs[i] (List.getElem_mem i.2)).choose_spec.2⟩
    have := hr σ _ hn hb _ (List.mem_singleton_self _)
    simpa [RAtom.sat, IArg.val, hσx, hσy] using this

/-! ## Moving the keys into the rules -/

/-- The rule of a key axiom without data properties. -/
def keyRuleOf : Axiom → Option DLRule
  | .hasKey c rs [] => some (keyRule c rs)
  | _ => none

/-- Every key has no data property. -/
def keysObj (O : Ontology) : Bool :=
  O.axioms.all fun
    | .hasKey _ _ ps => ps.isEmpty
    | _ => true

/-- **The keys as rules**: `none` for a key with data properties. -/
def keyOff (R : OntologyR) : Option OntologyR :=
  if keysObj R.onto then
    some ⟨⟨R.onto.axioms.filter Axiom.noKey⟩, R.rules ++ R.onto.axioms.filterMap keyRuleOf⟩
  else none

theorem named_keyRule (c : ClassExpr) (rs : List ObjProp) (a : IRI) :
    a ∈ (keyRule c rs).named ↔ a ∈ c.namedIndividuals := by
  have h0 : ∀ x ∈ keyAtoms rs, x.named = [] := by
    intro x hx
    simp only [keyAtoms, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    obtain ⟨i, rfl | rfl⟩ := hx <;> rfl
  simp only [DLRule.named, keyRule, List.cons_append, List.flatMap_cons, List.flatMap_append,
    List.mem_append, RAtom.named, IArg.named, List.append_nil]
  have h1 : a ∉ (keyAtoms rs).flatMap RAtom.named := fun hm => by
    obtain ⟨x, hx, ha⟩ := List.mem_flatMap.1 hm
    rw [h0 x hx] at ha; exact absurd ha (List.not_mem_nil)
  simp [h1]

theorem mem_named_keyOff {R R' : OntologyR} (h : keyOff R = some R') (a : IRI) :
    a ∈ R.named ↔ a ∈ R'.named := by
  unfold keyOff at h
  split_ifs at h with hk
  cases h
  simp only [OntologyR.named, Ontology.namedIndividuals, List.mem_append, List.mem_flatMap,
    List.mem_filter, List.flatMap_append, List.mem_filterMap]
  constructor
  · rintro (⟨ax, hax, ha⟩ | hr)
    · cases hn : ax.noKey
      · cases ax with
        | hasKey c rs ps =>
          have hps : ps = [] := by
            have := List.all_eq_true.1 hk _ hax
            simpa using this
          subst hps
          exact Or.inr (Or.inr ⟨_, ⟨_, hax, rfl⟩, (named_keyRule c rs a).2 (by simpa [Axiom.namedIndividuals] using ha)⟩)
        | _ => simp [Axiom.noKey] at hn
      · exact Or.inl ⟨ax, ⟨hax, hn⟩, ha⟩
    · exact Or.inr (Or.inl hr)
  · rintro (⟨ax, ⟨hax, -⟩, ha⟩ | hr | ⟨ρ, ⟨ax, hax, hρ⟩, ha⟩)
    · exact Or.inl ⟨ax, hax, ha⟩
    · exact Or.inr hr
    · cases ax with
      | hasKey c rs ps =>
        cases ps with
        | nil =>
          simp only [keyRuleOf, Option.some.injEq] at hρ
          subst hρ
          exact Or.inl ⟨_, hax, by simpa [Axiom.namedIndividuals] using (named_keyRule c rs a).1 ha⟩
        | cons _ _ => simp [keyRuleOf] at hρ
      | _ => simp [keyRuleOf] at hρ

/-- **The keys as rules keep the models.** -/
theorem modelR_keyOff [Nonempty DM.Val] (bi : BuiltIns DM) {R R' : OntologyR}
    (h : keyOff R = some R') (I : Interp DM Dom) : ModelR bi R I ↔ ModelR bi R' I := by
  have hN := mem_named_keyOff h
  have hk : keysObj R.onto = true := by unfold keyOff at h; split_ifs at h with hk; exact hk
  unfold keyOff at h
  rw [if_pos hk] at h
  cases h
  simp only [ModelR, List.mem_filter, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun ax ⟨hax, hn⟩ => (sat_N_noKey I hn _ _).1 (h1 ax hax), ?_⟩
    rintro ρ (hρ | ⟨ax, hax, hρ⟩)
    · exact (ruleSat_congr bi I hN ρ).1 (h2 ρ hρ)
    · cases ax with
      | hasKey c rs ps =>
        cases ps with
        | nil =>
          simp only [keyRuleOf, Option.some.injEq] at hρ
          subst hρ
          exact (ruleSat_congr bi I hN _).1 ((sat_hasKey_iff bi I _ c rs).1 (h1 _ hax))
        | cons _ _ => simp [keyRuleOf] at hρ
      | _ => simp [keyRuleOf] at hρ
  · rintro ⟨h1, h2⟩
    refine ⟨fun ax hax => ?_, fun ρ hρ => (ruleSat_congr bi I hN ρ).2 (h2 ρ (Or.inl hρ))⟩
    cases hn : ax.noKey
    · cases ax with
      | hasKey c rs ps =>
        have hps : ps = [] := by
          have := List.all_eq_true.1 hk _ hax
          simpa using this
        subst hps
        exact (sat_hasKey_iff bi I _ c rs).2 ((ruleSat_congr bi I hN _).2
          (h2 _ (Or.inr ⟨_, hax, rfl⟩)))
      | _ => simp [Axiom.noKey] at hn
    · exact (sat_N_noKey I hn _ _).1 (h1 ax ⟨hax, hn⟩)

/-! ## The routes with keys -/

/-- The ontology a route checks, with the keys moved into the rules first
(only when there are keys, so the indices of key-free inputs stay). -/
def rulesOntoK (R : OntologyR) : Option Ontology :=
  if R.onto.noKey then rulesOnto R else (keyOff R).bind rulesOnto

theorem consistentAtR_rulesOntoK [Nonempty DM.Val] (bi : BuiltIns DM) {R : OntologyR}
    {O' : Ontology} (h : rulesOntoK R = some O') : ConsistentAtR DM bi R ↔ ConsistentAt DM O' := by
  unfold rulesOntoK at h
  split_ifs at h
  · exact consistentAtR_rulesOnto bi h
  · obtain ⟨R', hR', h'⟩ := Option.bind_eq_some_iff.1 h
    rw [← consistentAtR_rulesOnto bi h']
    unfold ConsistentAtR
    simp only [modelR_keyOff bi hR']

/-- **The complete route with keys and rules.** -/
def owlKeysC2a (R : OntologyR) (hint : Option RawHint) : Option Bool :=
  (rulesOntoK R).bind fun O' => owlC3DConsistent O' hint

theorem owlKeysC2a_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {R : OntologyR} {hint : Option RawHint} {v : Bool} (h : owlKeysC2a R hint = some v) :
    v = true ↔ ConsistentAtR (owl2MapP pat) bi R := by
  obtain ⟨O', hO', h'⟩ := Option.bind_eq_some_iff.1 h
  rw [consistentAtR_rulesOntoK bi hO']
  exact owlC3DConsistent_sound pat h'

/-- **The hint route with keys and rules.** -/
def owlKeysHint (R : OntologyR) (hint : RawHint) : Option Bool :=
  (rulesOntoK R).bind fun O' => owlHintConsistent O' hint

theorem owlKeysHint_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {R : OntologyR} {hint : RawHint} (h : owlKeysHint R hint = some true) :
    ConsistentAtR (owl2MapP pat) bi R := by
  obtain ⟨O', hO', h'⟩ := Option.bind_eq_some_iff.1 h
  exact (consistentAtR_rulesOntoK bi hO').2 (owlHintConsistent_sound pat h')

/-- An ontology with keys and no rules: consistency as an OWL ontology. -/
theorem consistentAtR_nil (bi : BuiltIns DM) (O : Ontology) :
    ConsistentAtR DM bi ⟨O, []⟩ ↔ ConsistentAt DM O := by
  unfold ConsistentAtR ConsistentAt
  simp only [modelR_nil]

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.sat_hasKey_iff
#print axioms ContextCalculus.OWLFrontend.modelR_keyOff
#print axioms ContextCalculus.OWLFrontend.owlKeysC2a_sound
#print axioms ContextCalculus.OWLFrontend.owlKeysHint_sound
