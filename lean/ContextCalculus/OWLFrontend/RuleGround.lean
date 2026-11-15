import ContextCalculus.OWL.Rules
import ContextCalculus.OWLFrontend.HintRoute

/-!
# DL-safe rules by grounding (stage C5, item 3)

`OWL/Rules.lean` gives DL-safe rules their semantics: individual variables
range over the named individuals. A rule is then equivalent to its ground
instances over the named individuals, and a ground instance is one OWL
axiom with nominals, read at a fresh individual `h0` through a fresh object
property `u` with `u(h0, b)` asserted for every named individual `b`:

```
SubClassOf(ObjectIntersectionOf({h0} ∃u.({b1} ⊓ B1) ... ) ObjectIntersectionOf(∀u.(¬{c1} ⊔ H1) ...))
```

(`B1` the class of the body atom on `b1`, `ObjectHasValue(r b')` for a
property atom, `DataHasValue(p l)` for a data atom with a literal, `{b'}` and
`¬{b'}` for same and different; the head atoms likewise under `∀u`). The
encoded ontology is an OWL ontology without rules, so every route applies to
it.

* `consistentAtR_encRules`: for every datatype map with a value and every
  reading `bi` of the built-ins, the ontology with its rules is consistent
  iff the encoding is. Conditions (checked by `encRules`): no `HasKey`; every
  instance kept has no data variable, no data range atom and no built-in
  atom, and no anonymous individual; at most `ruleCap` instances. A rule with
  an individual variable and no named individual in the ontology has no
  instance, so any atom is allowed there.
* `owlRulesC2a_sound`: the complete route `owlC3DConsistent` on the
  encoding, exact for every hint and every `bi`.
* `owlRulesHint_sound`: the hint route on the encoding.

Not done: rows over ontologies with rules, and an encoding without
grounding (the instance count is the number of named individuals to the
power of the number of variables of a rule).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

variable {DM : DatatypeMap} {Dom : Type}

/-! ## A fresh object property -/

/-- `I` with the object property `u` read as `R`. -/
def withRole (I : Interp DM Dom) (u : IRI) (R : Dom → Dom → Prop) : Interp DM Dom :=
  { I with role := fun x => if x = u then R else I.role x }

theorem prop_withRole (I : Interp DM Dom) {u : IRI} (R : Dom → Dom → Prop) {r : ObjProp}
    (h : u ∉ r.names) : (withRole I u R).prop r = I.prop r := by
  cases r with
  | named a =>
    have : a ≠ u := fun e => h (by simp [ObjProp.names, e])
    funext x y; simp [Interp.prop, withRole, this]
  | inv a =>
    have : a ≠ u := fun e => h (by simp [ObjProp.names, e])
    funext x y; simp [Interp.prop, withRole, this]
  | top => rfl
  | bot => rfl

theorem chain_withRole (I : Interp DM Dom) {u : IRI} (R : Dom → Dom → Prop) :
    ∀ {rs : List ObjProp}, (∀ r ∈ rs, u ∉ r.names) → (withRole I u R).chain rs = I.chain rs
  | [], _ => rfl
  | r :: rs, h => by
    funext x z
    simp only [Interp.chain]
    rw [prop_withRole I R (h r (List.mem_cons_self ..)),
      chain_withRole I R fun s hs => h s (List.mem_cons_of_mem _ hs)]

theorem roleNames_and {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {u : IRI}
    (h : u ∈ c.roleNames) : u ∈ (ClassExpr.and cs).roleNames := by
  rw [ClassExpr.roleNames]
  exact List.mem_flatMap.2 ⟨⟨c, hc⟩, List.mem_attach _ _, h⟩

theorem roleNames_or {cs : List ClassExpr} {c : ClassExpr} (hc : c ∈ cs) {u : IRI}
    (h : u ∈ c.roleNames) : u ∈ (ClassExpr.or cs).roleNames := by
  rw [ClassExpr.roleNames]
  exact List.mem_flatMap.2 ⟨⟨c, hc⟩, List.mem_attach _ _, h⟩

/-- A class expression that does not mention `u` keeps its extension. -/
theorem ext_withRole (I : Interp DM Dom) {u : IRI} (R : Dom → Dom → Prop) :
    ∀ c : ClassExpr, u ∉ c.roleNames → (withRole I u R).ext c = I.ext c
  | .cls a, _ => by funext x; rw [Interp.ext, Interp.ext]; rfl
  | .thing, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .nothing, _ => by funext x; rw [Interp.ext, Interp.ext]
  | .and cs, h => by
    have ih : ∀ c ∈ cs, (withRole I u R).ext c = I.ext c := fun c hm =>
      ext_withRole I R c fun hu => h (roleNames_and hm hu)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun h' c hm => (ih c hm) ▸ h' c hm, fun h' c hm => (ih c hm).symm ▸ h' c hm⟩
  | .or cs, h => by
    have ih : ∀ c ∈ cs, (withRole I u R).ext c = I.ext c := fun c hm =>
      ext_withRole I R c fun hu => h (roleNames_or hm hu)
    funext x; rw [Interp.ext, Interp.ext]
    apply propext
    exact ⟨fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm) ▸ h'⟩,
      fun ⟨c, hm, h'⟩ => ⟨c, hm, (ih c hm).symm ▸ h'⟩⟩
  | .not c, h => by
    have ih := ext_withRole I R c fun hu => h (by rw [ClassExpr.roleNames]; exact hu)
    funext x; rw [Interp.ext, Interp.ext, ih]
  | .some r c, h => by
    have ih := ext_withRole I R c fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_right _ hu)
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_left _ hu)
    funext x; rw [Interp.ext, Interp.ext, ih, hr]
  | .all r c, h => by
    have ih := ext_withRole I R c fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_right _ hu)
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_left _ hu)
    funext x; rw [Interp.ext, Interp.ext, ih, hr]
  | .min k r c, h => by
    have ih := ext_withRole I R c fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_right _ hu)
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_left _ hu)
    funext x; rw [Interp.ext, Interp.ext, ih, hr]
  | .max k r c, h => by
    have ih := ext_withRole I R c fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_right _ hu)
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_left _ hu)
    funext x; rw [Interp.ext, Interp.ext, ih, hr]
  | .exact k r c, h => by
    have ih := ext_withRole I R c fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_right _ hu)
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact List.mem_append_left _ hu)
    funext x; rw [Interp.ext, Interp.ext, ih, hr]
  | .oneOf as, _ => by funext x; rw [Interp.ext, Interp.ext]; rfl
  | .hasValue r i, h => by
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact hu)
    funext x; rw [Interp.ext, Interp.ext, hr]; rfl
  | .hasSelf r, h => by
    have hr := prop_withRole I R (r := r) fun hu => h (by rw [ClassExpr.roleNames]; exact hu)
    funext x; rw [Interp.ext, Interp.ext, hr]
  | .dataSome p r, _ | .dataAll p r, _ | .dataHasValue p r, _ | .dataMin _ p r, _
  | .dataMax _ p r, _ | .dataExact _ p r, _ => by
    funext x
    rw [Interp.ext, Interp.ext]
    rfl
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

theorem withRole_ind (I : Interp DM Dom) (u : IRI) (R : Dom → Dom → Prop) :
    (withRole I u R).ind = I.ind := rfl

/-- An axiom that does not mention `u` keeps its satisfaction. -/
theorem sat_withRole (I : Interp DM Dom) {u : IRI} (R : Dom → Dom → Prop) (N : List IRI)
    {ax : Axiom} (h : u ∉ ax.objectPropertyNames) : (withRole I u R).sat N ax ↔ I.sat N ax := by
  have hl : ∀ cs : List ClassExpr, u ∉ cs.flatMap ClassExpr.roleNames →
      ∀ c ∈ cs, (withRole I u R).ext c = I.ext c := fun cs h c hc =>
    ext_withRole I R c fun hu => h (List.mem_flatMap.2 ⟨c, hc, hu⟩)
  have hp : ∀ rs : List ObjProp, u ∉ rs.flatMap ObjProp.names → ∀ r ∈ rs,
      (withRole I u R).prop r = I.prop r := fun rs h r hr =>
    prop_withRole I R fun hu => h (List.mem_flatMap.2 ⟨r, hr, hu⟩)
  cases ax with
  | subClassOf c d =>
    simp only [Axiom.objectPropertyNames, List.mem_append, not_or] at h
    simp only [Interp.sat, ext_withRole I R c h.1, ext_withRole I R d h.2]
  | equivalentClasses cs =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat]
    exact ⟨fun h' c hc d hd x hx => (hl cs h d hd) ▸ h' c hc d hd x ((hl cs h c hc).symm ▸ hx),
      fun h' c hc d hd x hx => (hl cs h d hd).symm ▸ h' c hc d hd x ((hl cs h c hc) ▸ hx)⟩
  | disjointClasses cs =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat]
    constructor
    · exact fun h' => h'.imp_of_mem fun hc hd h'' x => (hl cs h _ hc) ▸ (hl cs h _ hd) ▸ h'' x
    · exact fun h' => h'.imp_of_mem fun hc hd h'' x =>
        (hl cs h _ hc).symm ▸ (hl cs h _ hd).symm ▸ h'' x
  | disjointUnion a cs =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat]
    refine and_congr (forall_congr' fun y => ?_) ⟨fun h' => h'.imp_of_mem fun hc hd h'' x =>
      (hl cs h _ hc) ▸ (hl cs h _ hd) ▸ h'' x, fun h' => h'.imp_of_mem fun hc hd h'' x =>
      (hl cs h _ hc).symm ▸ (hl cs h _ hd).symm ▸ h'' x⟩
    refine iff_congr Iff.rfl ⟨fun ⟨c, hc, hy⟩ => ⟨c, hc, hl cs h c hc ▸ hy⟩,
      fun ⟨c, hc, hy⟩ => ⟨c, hc, (hl cs h c hc).symm ▸ hy⟩⟩
  | domain r c | range r c =>
    simp only [Axiom.objectPropertyNames, List.mem_append, not_or] at h
    simp only [Interp.sat, ext_withRole I R c h.2, prop_withRole I R h.1]
  | subObjectPropertyOf rs r =>
    simp only [Axiom.objectPropertyNames, List.mem_append, not_or] at h
    simp only [Interp.sat, prop_withRole I R h.2,
      chain_withRole I R fun s hs hu => h.1 (List.mem_flatMap.2 ⟨s, hs, hu⟩)]
  | equivalentObjectProperties rs =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat]
    exact ⟨fun h' r hr s hs x y hx => (hp rs h s hs) ▸ h' r hr s hs x y ((hp rs h r hr).symm ▸ hx),
      fun h' r hr s hs x y hx => (hp rs h s hs).symm ▸ h' r hr s hs x y ((hp rs h r hr) ▸ hx)⟩
  | disjointObjectProperties rs =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat]
    constructor
    · exact fun h' => h'.imp_of_mem fun hr hs h'' x y => (hp rs h _ hr) ▸ (hp rs h _ hs) ▸ h'' x y
    · exact fun h' => h'.imp_of_mem fun hr hs h'' x y =>
        (hp rs h _ hr).symm ▸ (hp rs h _ hs).symm ▸ h'' x y
  | inverseObjectProperties r s =>
    simp only [Axiom.objectPropertyNames, List.mem_append, not_or] at h
    simp only [Interp.sat, prop_withRole I R h.1, prop_withRole I R h.2]
  | transitive r | symmetric r | functional r | inverseFunctional r | reflexive r
  | irreflexive r | asymmetric r =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat, prop_withRole I R h]
  | hasKey c rs ps =>
    simp only [Axiom.objectPropertyNames, List.mem_append, not_or] at h
    simp only [Interp.sat, Interp.IsNamed, withRole_ind, ext_withRole I R c h.1]
    constructor
    · intro h' x y hx hy hcx hcy hr hd
      exact h' x y hx hy hcx hcy (fun r hr' => by rw [hp rs h.2 r hr']; exact hr r hr') hd
    · intro h' x y hx hy hcx hcy hr hd
      exact h' x y hx hy hcx hcy (fun r hr' => by rw [← hp rs h.2 r hr']; exact hr r hr') hd
  | classAssertion c a =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat, ext_withRole I R c h, withRole_ind]
  | objectPropertyAssertion r a b | negativeObjectPropertyAssertion r a b =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat, prop_withRole I R h, withRole_ind]
  | dataDomain p c =>
    simp only [Axiom.objectPropertyNames] at h
    simp only [Interp.sat, ext_withRole I R c h]
    rfl
  | _ => exact Iff.rfl

/-! ## Assignments -/

/-- All assignments of the names `N` to the variables `V`, as association
lists. -/
def assigns (N : List IRI) : List IRI → List (List (IRI × IRI))
  | [] => [[]]
  | v :: V => (assigns N V).flatMap fun g => N.map fun a => (v, a) :: g

theorem mem_assigns {N : List IRI} (f : IRI → IRI) :
    ∀ {V : List IRI}, (∀ v ∈ V, f v ∈ N) →
      ∃ g ∈ assigns N V, ∀ v ∈ V, g.lookup v = some (f v)
  | [], _ => ⟨[], List.mem_singleton_self _, fun v hv => absurd hv (List.not_mem_nil)⟩
  | v :: V, h => by
    obtain ⟨g, hg, hl⟩ := mem_assigns f (V := V) fun w hw => h w (List.mem_cons_of_mem _ hw)
    refine ⟨(v, f v) :: g, List.mem_flatMap.2 ⟨g, hg, List.mem_map.2 ⟨f v,
      h v (List.mem_cons_self ..), rfl⟩⟩, fun w hw => ?_⟩
    by_cases hwv : w = v
    · subst hwv; simp [List.lookup]
    · have hw' : w ∈ V := (List.mem_cons.1 hw).resolve_left hwv
      have hb : (w == v) = false := by simp [hwv]
      simp only [List.lookup, hb]
      exact hl w hw'

theorem lookup_assigns {N : List IRI} :
    ∀ {V : List IRI} {g : List (IRI × IRI)}, g ∈ assigns N V →
      ∀ v ∈ V, ∃ a ∈ N, g.lookup v = some a
  | [], g, _, v, hv => absurd hv (List.not_mem_nil)
  | w :: V, g, hg, v, hv => by
    obtain ⟨g', hg', hm⟩ := List.mem_flatMap.1 hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    by_cases hvw : v = w
    · subst hvw; exact ⟨a, ha, by simp [List.lookup]⟩
    · have hv' : v ∈ V := (List.mem_cons.1 hv).resolve_left hvw
      have hb : (v == w) = false := by simp [hvw]
      simp only [List.lookup, hb]
      exact lookup_assigns hg' v hv'

/-! ## Ground instances as axioms -/

/-- The individual of a ground argument (`none` for an anonymous
individual). -/
def gI (g : List (IRI × IRI)) : IArg → Option IRI
  | .var v => g.lookup v
  | .ind (.named a) => some a
  | .ind (.anon _) => none

/-- The class expression of a body atom of an instance, read at `h0`. -/
def bodyCE (u : IRI) (g : List (IRI × IRI)) : RAtom → Option ClassExpr
  | .cls c x => (gI g x).map fun a => .some (.named u) (.and [.oneOf [.named a], c])
  | .obj r x y => (gI g x).bind fun a => (gI g y).map fun b =>
      .some (.named u) (.and [.oneOf [.named a], .hasValue r (.named b)])
  | .data p x (.lit l) => (gI g x).map fun a =>
      .some (.named u) (.and [.oneOf [.named a], .dataHasValue p l])
  | .same x y => (gI g x).bind fun a => (gI g y).map fun b =>
      .some (.named u) (.and [.oneOf [.named a], .oneOf [.named b]])
  | .diff x y => (gI g x).bind fun a => (gI g y).map fun b =>
      .some (.named u) (.and [.oneOf [.named a], .not (.oneOf [.named b])])
  | _ => none

/-- The class expression of a head atom of an instance, read at `h0`. -/
def headCE (u : IRI) (g : List (IRI × IRI)) : RAtom → Option ClassExpr
  | .cls c x => (gI g x).map fun a => .all (.named u) (.or [.not (.oneOf [.named a]), c])
  | .obj r x y => (gI g x).bind fun a => (gI g y).map fun b =>
      .all (.named u) (.or [.not (.oneOf [.named a]), .hasValue r (.named b)])
  | .data p x (.lit l) => (gI g x).map fun a =>
      .all (.named u) (.or [.not (.oneOf [.named a]), .dataHasValue p l])
  | .same x y => (gI g x).bind fun a => (gI g y).map fun b =>
      .all (.named u) (.or [.not (.oneOf [.named a]), .oneOf [.named b]])
  | .diff x y => (gI g x).bind fun a => (gI g y).map fun b =>
      .all (.named u) (.or [.not (.oneOf [.named a]), .not (.oneOf [.named b])])
  | _ => none

/-- The axiom of one instance. -/
def instAx (u h0 : IRI) (ρ : DLRule) (g : List (IRI × IRI)) : Option Axiom :=
  (ρ.body.mapM (bodyCE u g)).bind fun bs => (ρ.head.mapM (headCE u g)).map fun hs =>
    .subClassOf (.and (.oneOf [.named h0] :: bs)) (.and hs)

/-- The axioms of all instances of a rule over the names `N`. -/
def ruleAxs (u h0 : IRI) (N : List IRI) (ρ : DLRule) : Option (List Axiom) :=
  (assigns N ρ.ivars.eraseDups).mapM (instAx u h0 ρ)

theorem mapM_some_fwd {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y ∈ l', f x = some y
  | [], _, _, x, hx => absurd hx (List.not_mem_nil)
  | a :: l, l', h, x, hx => by
    cases hfa : f a with
    | none => simp [List.mapM_cons, hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, hfa, hl] at h
      | some l'' =>
        simp only [List.mapM_cons, hfa, hl, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨b, List.mem_cons_self .., hfa⟩
        · obtain ⟨y, hy, hfy⟩ := mapM_some_fwd hl x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem mapM_some_bwd {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h
    exact absurd hy (List.not_mem_nil)
  | a :: l, l', h, y, hy => by
    cases hfa : f a with
    | none => simp [List.mapM_cons, hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, hfa, hl] at h
      | some l'' =>
        simp only [List.mapM_cons, hfa, hl, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., hfa⟩
        · obtain ⟨x, hx, hfx⟩ := mapM_some_bwd hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-! ## The encoding -/

/-- The object-property IRIs a rule mentions. -/
def _root_.ContextCalculus.OWL.RAtom.roleNames : RAtom → List IRI
  | .cls c _ => c.roleNames
  | .obj r _ _ => r.names
  | _ => []

def _root_.ContextCalculus.OWL.DLRule.roleNames (ρ : DLRule) : List IRI := (ρ.body ++ ρ.head).flatMap RAtom.roleNames

/-- An IRI longer than every IRI of `W`. -/
def freshOf (c : Char) (W : List IRI) : IRI := "".pushn c (SRIQKB.maxLen W + 1)

theorem freshOf_not_mem (c : Char) (W : List IRI) : freshOf c W ∉ W := by
  intro h
  have h1 := SRIQKB.length_le_maxLen h
  simp only [freshOf, String.length_pushn] at h1
  have : "".length = 0 := rfl
  omega

/-- The largest number of instances the encoding builds. -/
def ruleCap : Nat := 200000

/-- The object-property IRIs of an ontology with rules. -/
def _root_.ContextCalculus.OWL.OntologyR.roleNames (O : OntologyR) : List IRI :=
  O.onto.axioms.flatMap Axiom.objectPropertyNames ++ O.rules.flatMap DLRule.roleNames

/-- The fresh property and individual of the encoding. -/
def ruleU (O : OntologyR) : IRI := freshOf '%' O.roleNames
def ruleH (O : OntologyR) : IRI := freshOf '%' O.named

/-- **The grounding encoding**: `none` with `HasKey`, too many instances, or
an instance with an atom the encoding does not express. -/
def encRules (O : OntologyR) : Option Ontology :=
  let N := O.named.eraseDups
  let u := ruleU O
  let h0 := ruleH O
  if O.onto.noKey && (O.rules.map fun ρ => N.length ^ ρ.ivars.eraseDups.length).sum ≤ ruleCap then
    (O.rules.mapM (ruleAxs u h0 N)).map fun ras =>
      ⟨O.onto.axioms ++ N.map (fun b => .objectPropertyAssertion (.named u) (.named h0) (.named b)) ++
        ras.flatten⟩
  else none

/-- Consistency of an ontology with rules at a datatype map, for a reading
of the built-ins. -/
def ConsistentAtR (DM : DatatypeMap) (bi : BuiltIns DM) (O : OntologyR) : Prop :=
  ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp DM Dom), ModelR bi O I

/-- The individual arguments of an atom (the first is the one an
instance's class is read at). -/
def _root_.ContextCalculus.OWL.RAtom.iargs : RAtom → List IArg
  | .cls _ x | .data _ x _ => [x]
  | .obj _ x y | .same x y | .diff x y => [x, y]
  | .drange .. | .builtin .. => []

/-! ## Correctness of the atoms -/

section Atoms

variable (bi : BuiltIns DM) (J : Interp DM Dom) (u : IRI) (g : List (IRI × IRI))
  (σ : IRI → Dom) (δ : IRI → DM.Val)

/-- `σ` agrees with the instance `g` on its ground arguments. -/
def Agrees : Prop := ∀ v a, g.lookup v = some a → σ v = J.ind (.named a)

theorem val_of_gI {J : Interp DM Dom} {g : List (IRI × IRI)} {σ : IRI → Dom} (hg : Agrees J g σ)
    {x : IArg} {a : IRI} (h : gI g x = some a) : x.val J σ = J.ind (.named a) := by
  cases x with
  | var v => exact hg v a h
  | ind i =>
    cases i with
    | named b => simp only [gI, Option.some.injEq] at h; subst h; rfl
    | anon _ => cases h

theorem ext_oneOf1 (J : Interp DM Dom) (i : Individual) (y : Dom) :
    J.ext (.oneOf [i]) y ↔ y = J.ind i := by
  rw [Interp.ext]; simp

theorem ext_and2 (J : Interp DM Dom) (c d : ClassExpr) (y : Dom) :
    J.ext (.and [c, d]) y ↔ J.ext c y ∧ J.ext d y := by
  rw [Interp.ext]; simp

theorem ext_or2 (J : Interp DM Dom) (c d : ClassExpr) (y : Dom) :
    J.ext (.or [c, d]) y ↔ J.ext c y ∨ J.ext d y := by
  rw [Interp.ext]; simp

theorem ext_not' (J : Interp DM Dom) (c : ClassExpr) (y : Dom) : J.ext (.not c) y ↔ ¬ J.ext c y := by
  rw [Interp.ext]

theorem key_body {J : Interp DM Dom} {u : IRI} {x0 : Dom} {a : IRI}
    (hu : J.prop (.named u) x0 (J.ind (.named a))) (C : ClassExpr) :
    J.ext (.some (.named u) (.and [.oneOf [.named a], C])) x0 ↔ J.ext C (J.ind (.named a)) := by
  rw [Interp.ext]
  simp only [ext_and2, ext_oneOf1]
  constructor
  · rintro ⟨y, -, rfl, hy⟩; exact hy
  · intro h; exact ⟨_, hu, rfl, h⟩

theorem key_head {J : Interp DM Dom} {u : IRI} {x0 : Dom} {a : IRI}
    (hu : J.prop (.named u) x0 (J.ind (.named a))) (C : ClassExpr) :
    J.ext (.all (.named u) (.or [.not (.oneOf [.named a]), C])) x0 ↔ J.ext C (J.ind (.named a)) := by
  rw [Interp.ext]
  simp only [ext_or2, ext_not', ext_oneOf1]
  constructor
  · intro h
    exact (h _ hu).resolve_left (fun h' => h' rfl)
  · intro h y _
    by_cases hy : y = J.ind (.named a)
    · subst hy; exact Or.inr h
    · exact Or.inl hy

/-- Body atoms: the atom holds iff its class holds at an element with
`u`-edges to the ground individuals. -/
theorem bodyCE_iff {J : Interp DM Dom} {g : List (IRI × IRI)} {σ : IRI → Dom} (hg : Agrees J g σ)
    {x0 : Dom} {at_ : RAtom}
    (hu : ∀ t ∈ at_.iargs, ∀ a, gI g t = some a → J.prop (.named u) x0 (J.ind (.named a)))
    {c : ClassExpr} (h : bodyCE u g at_ = some c) : J.ext c x0 ↔ at_.sat bi J σ δ := by
  cases at_ with
  | cls c' x =>
    simp only [bodyCE, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    rw [key_body (hu _ (List.mem_cons_self ..) _ ha)]
    simp only [RAtom.sat, val_of_gI hg ha]
  | obj r x y =>
    simp only [bodyCE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [key_body (hu _ (List.mem_cons_self ..) _ ha), Interp.ext]
    simp only [RAtom.sat, val_of_gI hg ha, val_of_gI hg hb]
  | data p x d =>
    cases d with
    | var _ => cases h
    | lit l =>
      simp only [bodyCE, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [key_body (hu _ (List.mem_cons_self ..) _ ha), Interp.ext]
      simp only [RAtom.sat, DArg.is, val_of_gI hg ha]
  | same x y =>
    simp only [bodyCE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [key_body (hu _ (List.mem_cons_self ..) _ ha), ext_oneOf1]
    simp only [RAtom.sat, val_of_gI hg ha, val_of_gI hg hb]
  | diff x y =>
    simp only [bodyCE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [key_body (hu _ (List.mem_cons_self ..) _ ha), ext_not', ext_oneOf1]
    simp only [RAtom.sat, val_of_gI hg ha, val_of_gI hg hb]
  | drange _ _ | builtin _ _ => cases h

/-- Head atoms likewise. -/
theorem headCE_iff {J : Interp DM Dom} {g : List (IRI × IRI)} {σ : IRI → Dom} (hg : Agrees J g σ)
    {x0 : Dom} {at_ : RAtom}
    (hu : ∀ t ∈ at_.iargs, ∀ a, gI g t = some a → J.prop (.named u) x0 (J.ind (.named a)))
    {c : ClassExpr} (h : headCE u g at_ = some c) : J.ext c x0 ↔ at_.sat bi J σ δ := by
  cases at_ with
  | cls c' x =>
    simp only [headCE, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    rw [key_head (hu _ (List.mem_cons_self ..) _ ha)]
    simp only [RAtom.sat, val_of_gI hg ha]
  | obj r x y =>
    simp only [headCE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [key_head (hu _ (List.mem_cons_self ..) _ ha), Interp.ext]
    simp only [RAtom.sat, val_of_gI hg ha, val_of_gI hg hb]
  | data p x d =>
    cases d with
    | var _ => cases h
    | lit l =>
      simp only [headCE, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [key_head (hu _ (List.mem_cons_self ..) _ ha), Interp.ext]
      simp only [RAtom.sat, DArg.is, val_of_gI hg ha]
  | same x y =>
    simp only [headCE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [key_head (hu _ (List.mem_cons_self ..) _ ha), ext_oneOf1]
    simp only [RAtom.sat, val_of_gI hg ha, val_of_gI hg hb]
  | diff x y =>
    simp only [headCE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [key_head (hu _ (List.mem_cons_self ..) _ ha), ext_not', ext_oneOf1]
    simp only [RAtom.sat, val_of_gI hg ha, val_of_gI hg hb]
  | drange _ _ | builtin _ _ => cases h

end Atoms

/-! ## Correctness of the encoding -/

theorem ext_andL (J : Interp DM Dom) (cs : List ClassExpr) (y : Dom) :
    J.ext (.and cs) y ↔ ∀ c ∈ cs, J.ext c y := by
  rw [Interp.ext]

theorem atom_withRole (bi : BuiltIns DM) (I : Interp DM Dom) {u : IRI} (R : Dom → Dom → Prop)
    (σ : IRI → Dom) (δ : IRI → DM.Val) {a : RAtom} (h : u ∉ a.roleNames) :
    a.sat bi (withRole I u R) σ δ ↔ a.sat bi I σ δ := by
  cases a with
  | cls c x => simp only [RAtom.sat, ext_withRole I R c h]; rfl
  | obj r x y => simp only [RAtom.sat, prop_withRole I R (r := r) h]; rfl
  | _ => exact Iff.rfl

theorem key_of_assigns {N : List IRI} :
    ∀ {V : List IRI} {g : List (IRI × IRI)}, g ∈ assigns N V →
      ∀ v a, g.lookup v = some a → v ∈ V
  | [], g, hg, v, a, h => by
    simp only [assigns, List.mem_singleton] at hg; subst hg; cases h
  | w :: V, g, hg, v, a, h => by
    obtain ⟨g', hg', hm⟩ := List.mem_flatMap.1 hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hm
    by_cases hvw : v = w
    · subst hvw; exact List.mem_cons_self ..
    · have hb : (v == w) = false := by simp [hvw]
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (key_of_assigns hg' v a h)

theorem mem_iargs_vars {a : RAtom} {t : IArg} (ht : t ∈ a.iargs) {v : IRI} (hv : t = .var v) :
    v ∈ a.ivars := by
  subst hv
  cases a <;> simp only [RAtom.iargs, List.mem_cons, List.not_mem_nil, or_false] at ht <;>
    (try rcases ht with ht | ht) <;> (try subst ht) <;> simp [RAtom.ivars, IArg.vars]

theorem mem_iargs_named {a : RAtom} {t : IArg} (ht : t ∈ a.iargs) {b : IRI}
    (hv : t = .ind (.named b)) : b ∈ a.named := by
  subst hv
  cases a <;> simp only [RAtom.iargs, List.mem_cons, List.not_mem_nil, or_false] at ht <;>
    (try rcases ht with ht | ht) <;> (try subst ht) <;>
    simp [RAtom.named, IArg.named, Individual.namedIRI]

/-- **The grounding encoding is exact**, at every datatype map with a value
and for every reading of the built-ins. -/
theorem consistentAtR_encRules [hv : Nonempty DM.Val] (bi : BuiltIns DM) {O : OntologyR}
    {O' : Ontology} (h : encRules O = some O') : ConsistentAtR DM bi O ↔ ConsistentAt DM O' := by
  classical
  unfold encRules at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨ras, hras, rfl⟩ := Option.map_eq_some_iff.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hk, -⟩ := hc
  have hk' : ∀ ax ∈ O.onto.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  set N := O.named.eraseDups with hN
  set u := ruleU O with hu
  set h0 := ruleH O with hh0
  have hfu : u ∉ O.roleNames := freshOf_not_mem _ _
  have hu_ax : ∀ ax ∈ O.onto.axioms, u ∉ ax.objectPropertyNames := fun ax hax hm =>
    hfu (List.mem_append_left _ (List.mem_flatMap.2 ⟨ax, hax, hm⟩))
  have hu_at : ∀ ρ ∈ O.rules, ∀ a ∈ ρ.body ++ ρ.head, u ∉ a.roleNames := fun ρ hρ a ha hm =>
    hfu (List.mem_append_right _ (List.mem_flatMap.2 ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, hm⟩⟩))
  -- the instance axioms of a rule
  have hinst : ∀ ρ ∈ O.rules, ∀ g ∈ assigns N ρ.ivars.eraseDups, ∃ ax,
      instAx u h0 ρ g = some ax ∧ ax ∈ ras.flatten := by
    intro ρ hρ g hg
    obtain ⟨L, hL, hrL⟩ := mapM_some_fwd hras ρ hρ
    obtain ⟨ax, hax, hia⟩ := mapM_some_fwd hrL g hg
    exact ⟨ax, hia, List.mem_flatten.2 ⟨L, hL, hax⟩⟩
  constructor
  · -- a model with rules gives a model of the encoding: read `u` as the full relation
    rintro ⟨Dom, hD, I, hI1, hI2⟩
    let J := withRole I u fun _ _ => True
    have hJu : ∀ x y, J.prop (.named u) x y := fun x y => by
      simp [J, withRole, Interp.prop]
    refine ⟨Dom, hD, J, fun ax hax => ?_⟩
    rcases List.mem_append.1 hax with hax | hax
    · rcases List.mem_append.1 hax with hax | hax
      · rw [sat_withRole I _ _ (hu_ax ax hax), sat_N_noKey I (hk' ax hax) _ O.named]
        exact hI1 ax hax
      · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hax
        exact hJu _ _
    · obtain ⟨L, hL, hax⟩ := List.mem_flatten.1 hax
      obtain ⟨ρ, hρ, hrL⟩ := mapM_some_bwd hras L hL
      obtain ⟨g, hg, hia⟩ := mapM_some_bwd hrL ax hax
      unfold instAx at hia
      obtain ⟨bs, hbs, hia⟩ := Option.bind_eq_some_iff.1 hia
      obtain ⟨hs, hhs, rfl⟩ := Option.map_eq_some_iff.1 hia
      intro x hx
      rw [ext_andL] at hx ⊢
      let σ : IRI → Dom := fun v => I.ind (.named ((g.lookup v).getD v))
      let δ : IRI → DM.Val := fun _ => Classical.choice hv
      have hag : Agrees J g σ := fun v a hl => by simp [σ, hl, J, withRole]
      have hall : ∀ t ∈ (RAtom.cls .thing (.var "")).iargs, ∀ a, gI g t = some a →
          J.prop (.named u) x (J.ind (.named a)) := fun _ _ _ _ => hJu _ _
      have hb : ∀ a ∈ ρ.body, a.sat bi I σ δ := by
        intro a ha
        obtain ⟨c, hc, hca⟩ := mapM_some_fwd hbs a ha
        have := (bodyCE_iff bi u δ hag (x0 := x) (fun _ _ _ _ => hJu _ _) hca).1
          (hx c (List.mem_cons_of_mem _ hc))
        exact (atom_withRole bi I _ σ δ (hu_at ρ hρ a (List.mem_append_left _ ha))).1 this
      have hnm : ∀ v ∈ ρ.ivars, I.IsNamed O.named (σ v) := by
        intro v hv'
        obtain ⟨a, ha, hl⟩ := lookup_assigns hg v (List.mem_eraseDups.2 hv')
        exact ⟨a, (List.mem_eraseDups.1 ha), by simp [σ, hl]⟩
      have hhd := hI2 ρ hρ σ δ hnm hb
      intro c hc
      obtain ⟨a, ha, hca⟩ := mapM_some_bwd hhs c hc
      exact (headCE_iff bi u δ hag (x0 := x) (fun _ _ _ _ => hJu _ _) hca).2
        ((atom_withRole bi I _ σ δ (hu_at ρ hρ a (List.mem_append_right _ ha))).2 (hhd a ha))
  · -- a model of the encoding is a model with rules
    rintro ⟨Dom, hD, J, hJ⟩
    refine ⟨Dom, hD, J, fun ax hax => ?_, fun ρ hρ σ δ hnm hbody a ha => ?_⟩
    · rw [sat_N_noKey J (hk' ax hax) _ (Ontology.namedIndividuals _)]
      exact hJ ax (List.mem_append_left _ (List.mem_append_left _ hax))
    · -- the instance of the assignment
      let f : IRI → IRI := fun v => if hv' : v ∈ ρ.ivars then (hnm v hv').choose else v
      have hf : ∀ v ∈ ρ.ivars, f v ∈ O.named ∧ σ v = J.ind (.named (f v)) := fun v hv' => by
        simp only [f, dif_pos hv']
        exact (hnm v hv').choose_spec
      obtain ⟨g, hg, hgl⟩ := mem_assigns f (N := N) (V := ρ.ivars.eraseDups) fun v hv' =>
        List.mem_eraseDups.2 (hf v (List.mem_eraseDups.1 hv')).1
      have hag : Agrees J g σ := fun v b hl => by
        have hvV := key_of_assigns hg v b hl
        rw [hgl v hvV] at hl
        cases hl
        exact (hf v (List.mem_eraseDups.1 hvV)).2
      obtain ⟨ax, hia, haxm⟩ := hinst ρ hρ g hg
      have hJax := hJ ax (List.mem_append_right _ haxm)
      unfold instAx at hia
      obtain ⟨bs, hbs, hia⟩ := Option.bind_eq_some_iff.1 hia
      obtain ⟨hs, hhs, rfl⟩ := Option.map_eq_some_iff.1 hia
      let x0 := J.ind (.named h0)
      -- `u`-edges from `x0` to the ground individuals
      have hux : ∀ b ∈ N, J.prop (.named u) x0 (J.ind (.named b)) := fun b hb =>
        hJ _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩)))
      have hua : ∀ a ∈ ρ.body ++ ρ.head, ∀ t ∈ a.iargs, ∀ b, gI g t = some b →
          J.prop (.named u) x0 (J.ind (.named b)) := by
        intro a ha t ht b hb
        refine hux b ?_
        cases t with
        | var v =>
          have hvV : v ∈ ρ.ivars.eraseDups := List.mem_eraseDups.2
            (List.mem_flatMap.2 ⟨a, ha, mem_iargs_vars ht rfl⟩)
          obtain ⟨c, hc, hl⟩ := lookup_assigns hg v hvV
          simp only [gI] at hb
          rw [hl] at hb; cases hb; exact hc
        | ind i =>
          cases i with
          | named b' =>
            simp only [gI, Option.some.injEq] at hb; subst hb
            refine List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_flatMap.2
              ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, mem_iargs_named ht rfl⟩⟩))
          | anon _ => cases hb
      have hx0 : J.ext (.and (.oneOf [.named h0] :: bs)) x0 := by
        rw [ext_andL]
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact (ext_oneOf1 J _ _).2 rfl
        · obtain ⟨a', ha', hca⟩ := mapM_some_bwd hbs c hc
          exact (bodyCE_iff bi u δ hag (hua a' (List.mem_append_left _ ha')) hca).2 (hbody a' ha')
      have hh := hJax x0 hx0
      rw [ext_andL] at hh
      obtain ⟨c, hc, hca⟩ := mapM_some_fwd hhs a ha
      exact (headCE_iff bi u δ hag (hua a (List.mem_append_right _ ha)) hca).1 (hh c hc)

/-! ## The routes -/

/-- The ontology a route checks: the ontology itself without rules, its
encoding with rules. -/
def rulesOnto (O : OntologyR) : Option Ontology :=
  if O.rules.isEmpty then some O.onto else encRules O

theorem consistentAtR_rulesOnto [Nonempty DM.Val] (bi : BuiltIns DM) {O : OntologyR}
    {O' : Ontology} (h : rulesOnto O = some O') : ConsistentAtR DM bi O ↔ ConsistentAt DM O' := by
  unfold rulesOnto at h
  split_ifs at h with he
  · cases h
    have hr : O.rules = [] := List.isEmpty_iff.1 he
    unfold ConsistentAtR ConsistentAt
    have : ∀ (Dom : Type) (I : Interp DM Dom), ModelR bi O I ↔ OWL.Model O.onto I := by
      intro Dom I
      have hO : O = ⟨O.onto, []⟩ := by cases O; simp_all
      rw [hO]
      exact modelR_nil bi O.onto I
    simp only [this]
  · exact consistentAtR_encRules bi h

instance (pat : String → String → Prop) : Nonempty (owl2MapP pat).Val :=
  ⟨toVal (.str "a" none)⟩

/-- **The complete route with rules**: `owlC3DConsistent` on the encoding. -/
def owlRulesC2a (O : OntologyR) (hint : Option RawHint) : Option Bool :=
  (rulesOnto O).bind fun O' => owlC3DConsistent O' hint

/-- **Soundness and exactness**, for every reading of `xsd:pattern`, of the
built-ins, and every hint. -/
theorem owlRulesC2a_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {O : OntologyR} {hint : Option RawHint} {v : Bool} (h : owlRulesC2a O hint = some v) :
    v = true ↔ ConsistentAtR (owl2MapP pat) bi O := by
  obtain ⟨O', hO', h'⟩ := Option.bind_eq_some_iff.1 h
  rw [consistentAtR_rulesOnto bi hO']
  exact owlC3DConsistent_sound pat h'

/-- **The hint route with rules.** -/
def owlRulesHint (O : OntologyR) (hint : RawHint) : Option Bool :=
  (rulesOnto O).bind fun O' => owlHintConsistent O' hint

theorem owlRulesHint_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {O : OntologyR} {hint : RawHint} (h : owlRulesHint O hint = some true) :
    ConsistentAtR (owl2MapP pat) bi O := by
  obtain ⟨O', hO', h'⟩ := Option.bind_eq_some_iff.1 h
  exact (consistentAtR_rulesOnto bi hO').2 (owlHintConsistent_sound pat h')

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.consistentAtR_encRules
#print axioms ContextCalculus.OWLFrontend.owlRulesC2a_sound
#print axioms ContextCalculus.OWLFrontend.owlRulesHint_sound
