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

/-! ## Variable elimination and single-variable rule encoding (stage H7, item 2) -/

/-- The inverse of an object property expression. -/
def _root_.ContextCalculus.OWL.ObjProp.flip : ObjProp → ObjProp
  | .named r => .inv r
  | .inv r => .named r
  | .top => .top
  | .bot => .bot

theorem prop_flip (I : Interp DM Dom) (r : ObjProp) (x y : Dom) :
    I.prop r.flip x y ↔ I.prop r y x := by
  cases r <;> rfl

theorem names_flip (r : ObjProp) : r.flip.names = r.names := by
  cases r <;> rfl

/-- Turn a binary object-property atom with a constant endpoint into a unary
class atom. -/
def unifyAtom : RAtom → RAtom
  | .obj r (.var v) (.ind (.named b)) => .cls (.hasValue r (.named b)) (.var v)
  | .obj r (.ind (.named b)) (.var w) => .cls (.hasValue r.flip (.named b)) (.var w)
  | a => a

def unifyRule (ρ : DLRule) : DLRule :=
  ⟨ρ.body.map unifyAtom, ρ.head.map unifyAtom⟩

/-- Classify a body atom with respect to variable `v`: a binary link `(dir, x)`
to `x` (where `v ∉ x.vars`), a unary class `c` on `v`, or an atom not mentioning
`v`. -/
def stepAtomV (v : IRI) (a : RAtom) :
    Option (Sum (ObjProp × IArg) (Sum ClassExpr RAtom)) :=
  if v ∈ a.ivars then
    match a with
    | .cls c (.var w) => if w = v then some (.inr (.inl c)) else none
    | .obj r x1 x2 =>
      if x2 = .var v && !(v ∈ x1.vars) then some (.inl (r, x1))
      else if x1 = .var v && !(v ∈ x2.vars) then some (.inl (r.flip, x2))
      else none
    | _ => none
  else some (.inr (.inr a))

/-- Partition body atoms into binary links on `v`, unary classes on `v`, and
atoms not mentioning `v`. -/
def splitBodyV (v : IRI) : List RAtom → Option (List (ObjProp × IArg) × List ClassExpr × List RAtom)
  | [] => some ([], [], [])
  | a :: as =>
    (splitBodyV v as).bind fun (bins, cs, rest) =>
      match stepAtomV v a with
      | some (.inl bx) => some (bx :: bins, cs, rest)
      | some (.inr (.inl c)) => some (bins, c :: cs, rest)
      | some (.inr (.inr a')) => some (bins, cs, a' :: rest)
      | none => none

/-- Eliminate a degree-1 body-only variable `v` by rolling it into an
existential restriction on its neighbor, using `∃u⁻.{h0}` for named-individual
membership. -/
def rollVar (u h0 : IRI) (v : IRI) (ρ : DLRule) : Option DLRule :=
  if v ∈ ρ.head.flatMap RAtom.ivars then none
  else match splitBodyV v ρ.body with
    | some ([(dir, x)], cs, rest) =>
      some ⟨.cls (.some dir (.and (.hasValue (.inv u) (.named h0) :: cs))) x :: rest, ρ.head⟩
    | _ => none

def findRoll (u h0 : IRI) (ρ : DLRule) : List IRI → Option DLRule
  | [] => none
  | v :: vs => match rollVar u h0 v ρ with
    | some ρ' => some ρ'
    | none => findRoll u h0 ρ vs

def rollLoop (u h0 : IRI) : Nat → DLRule → DLRule
  | 0, ρ => ρ
  | k + 1, ρ => match findRoll u h0 ρ ρ.ivars.eraseDups with
    | some ρ' => rollLoop u h0 k ρ'
    | none => ρ

def rollAll (u h0 : IRI) (ρ : DLRule) : DLRule :=
  let ρ0 := unifyRule ρ
  rollLoop u h0 ρ0.ivars.length ρ0

/-- Substitute `.var v ↦ .ind (.named b)` in an individual argument. -/
def substIArg (v b : IRI) : IArg → IArg
  | .var w => if w = v then .ind (.named b) else .var w
  | .ind i => .ind i

/-- Substitute `.var v ↦ .ind (.named b)` in an atom. -/
def substAtom (v b : IRI) : RAtom → RAtom
  | .cls c x => .cls c (substIArg v b x)
  | .obj r x y => .obj r (substIArg v b x) (substIArg v b y)
  | .data p x d => .data p (substIArg v b x) d
  | .same x y => .same (substIArg v b x) (substIArg v b y)
  | .diff x y => .diff (substIArg v b x) (substIArg v b y)
  | .drange r d => .drange r d
  | .builtin f args => .builtin f args

def substRule (v b : IRI) (ρ : DLRule) : DLRule :=
  ⟨ρ.body.map (substAtom v b), ρ.head.map (substAtom v b)⟩

/-- Pick an element of a non-empty list minimizing `cost`. -/
def pickMinBy {α : Type} (cost : α → Nat) : List α → Option α
  | [] => none
  | [x] => some x
  | x :: y :: rest =>
    match pickMinBy cost (y :: rest) with
    | none => some x
    | some z => if cost x ≤ cost z then some x else some z

/-- Roll degree-1 body-only variables, then if multiple variables remain,
split one variable over `N` and roll again. -/
def splitStep (u h0 : IRI) (N : List IRI) (ρ : DLRule) : List DLRule :=
  let ρ1 := rollAll u h0 ρ
  match N with
  | [] => [ρ1]
  | b0 :: _ =>
    let vs := ρ1.ivars.eraseDups
    if vs.length ≤ 1 then [ρ1]
    else match pickMinBy (fun v => (rollAll u h0 (substRule v b0 ρ1)).ivars.eraseDups.length) vs with
      | none => [ρ1]
      | some v =>
        if (rollAll u h0 (substRule v b0 ρ1)).ivars.eraseDups.length ≤ 1 || N.length ≤ 64 then
          N.map fun b => rollAll u h0 (substRule v b ρ1)
        else [ρ1]

def splitRule (u h0 : IRI) (N : List IRI) (ρ : DLRule) : List DLRule :=
  ((splitStep u h0 N ρ).flatMap (splitStep u h0 N)).flatMap (splitStep u h0 N)

/-- Class expression of a unary class atom on `v`. -/
def asUnaryV (v : IRI) : RAtom → Option ClassExpr
  | .cls c (.var w) => if w = v then some c else none
  | _ => none

def headVar : List RAtom → Option IRI
  | .cls _ (.var v) :: _ => some v
  | _ => none

def oneVarHeadCE (u : IRI) (vbs : List ClassExpr) (H : ClassExpr) : ClassExpr :=
  .all (.named u) (.or (vbs.map .not ++ [H]))

/-- Encode a rule whose only variable `v` appears solely in unary class atoms
as a single axiom. When no 0-variable body atoms remain (`rest = []`), emit a
direct Horn GCI `∃u⁻.{h0} ⊓ B₁ ⊓ ... ⊓ Bₖ ⊑ H₁ ⊓ ... ⊓ Hₘ`. -/
def instOneVar (u h0 : IRI) (ρ : DLRule) : Option Axiom :=
  match headVar ρ.head with
  | none => none
  | some v =>
    match splitBodyV v ρ.body with
    | some ([], vbs, []) =>
      (ρ.head.mapM (asUnaryV v)).map fun vhs =>
        .subClassOf (.and (.hasValue (.inv u) (.named h0) :: vbs)) (.and vhs)
    | some ([], vbs, rest) =>
      (rest.mapM (bodyCE u [])).bind fun gbs =>
        (ρ.head.mapM (asUnaryV v)).map fun vhs =>
          .subClassOf (.and (.oneOf [.named h0] :: gbs)) (.and (vhs.map (oneVarHeadCE u vbs)))
    | _ => none

def oneRuleInstCount (u h0 : IRI) (N : List IRI) (ρ' : DLRule) : Nat :=
  match instOneVar u h0 ρ' with
  | some _ => 1
  | none => N.length ^ ρ'.ivars.eraseDups.length

def ruleInstCount (u h0 : IRI) (N : List IRI) (ρ : DLRule) : Nat :=
  ((splitRule u h0 N ρ).map (oneRuleInstCount u h0 N)).sum

def oneRuleAxs (u h0 : IRI) (N : List IRI) (ρ' : DLRule) : Option (List Axiom) :=
  match instOneVar u h0 ρ' with
  | some ax => some [ax]
  | none => (assigns N ρ'.ivars.eraseDups).mapM (instAx u h0 ρ')

/-- The axioms of all instances of a rule over the names `N`. -/
def ruleAxs (u h0 : IRI) (N : List IRI) (ρ : DLRule) : Option (List Axiom) :=
  ((splitRule u h0 N ρ).mapM (oneRuleAxs u h0 N)).map List.flatten

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
  if O.onto.noKey && (O.rules.map (ruleInstCount u h0 N)).sum ≤ ruleCap then
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

/-! ## Correctness of variable elimination and single-variable encoding -/

theorem sat_unifyAtom (bi : BuiltIns DM) (J : Interp DM Dom) (σ : IRI → Dom) (δ : IRI → DM.Val)
    (a : RAtom) : (unifyAtom a).sat bi J σ δ ↔ a.sat bi J σ δ := by
  cases a with
  | obj r x y =>
    cases x with
    | var v =>
      cases y with
      | var w => rfl
      | ind j => cases j <;> simp [unifyAtom, RAtom.sat, Interp.ext, IArg.val]
    | ind i =>
      cases i with
      | named b =>
        cases y with
        | var w => simp [unifyAtom, RAtom.sat, Interp.ext, IArg.val, prop_flip]
        | ind _ => rfl
      | anon _ => rfl
  | _ => rfl

theorem ivars_unifyAtom (a : RAtom) : (unifyAtom a).ivars = a.ivars := by
  cases a with
  | obj r x y =>
    cases x with
    | var v =>
      cases y with
      | var w => rfl
      | ind j => cases j <;> simp [unifyAtom, RAtom.ivars, IArg.vars]
    | ind i =>
      cases i with
      | named b =>
        cases y with
        | var w => simp [unifyAtom, RAtom.ivars, IArg.vars]
        | ind _ => rfl
      | anon _ => rfl
  | _ => rfl

theorem ivars_unifyRule (ρ : DLRule) : (unifyRule ρ).ivars = ρ.ivars := by
  simp only [DLRule.ivars, unifyRule, ← List.map_append, List.flatMap_map, ivars_unifyAtom]

theorem sat_unifyRule (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI) (ρ : DLRule) :
    (unifyRule ρ).sat bi J O_named ↔ ρ.sat bi J O_named := by
  rw [DLRule.sat, DLRule.sat, ivars_unifyRule]
  simp only [unifyRule, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, sat_unifyAtom]

def NoU (u : IRI) (ρ : DLRule) : Prop :=
  ∀ a ∈ ρ.body ++ ρ.head, u ∉ a.roleNames

def NamedIn (N : List IRI) (ρ : DLRule) : Prop :=
  ∀ a ∈ ρ.body ++ ρ.head, ∀ t ∈ a.iargs, ∀ b, t = .ind (.named b) → b ∈ N

theorem sat_rule_withRole (bi : BuiltIns DM) (I : Interp DM Dom) (O_named : List IRI)
    {u : IRI} (R : Dom → Dom → Prop) {ρ : DLRule} (hnu : NoU u ρ) :
    ρ.sat bi (withRole I u R) O_named ↔ ρ.sat bi I O_named := by
  constructor
  · intro h σ δ hnm hbody a ha
    have hbody' : ∀ a0 ∈ ρ.body, a0.sat bi (withRole I u R) σ δ := fun a0 ha0 =>
      (atom_withRole bi I R σ δ (hnu a0 (List.mem_append_left _ ha0))).2 (hbody a0 ha0)
    exact (atom_withRole bi I R σ δ (hnu a (List.mem_append_right _ ha))).1 (h σ δ hnm hbody' a ha)
  · intro h σ δ hnm hbody a ha
    have hbody' : ∀ a0 ∈ ρ.body, a0.sat bi I σ δ := fun a0 ha0 =>
      (atom_withRole bi I R σ δ (hnu a0 (List.mem_append_left _ ha0))).1 (hbody a0 ha0)
    exact (atom_withRole bi I R σ δ (hnu a (List.mem_append_right _ ha))).2 (h σ δ hnm hbody' a ha)

theorem iargs_unifyAtom (a : RAtom) {t : IArg} (ht : t ∈ (unifyAtom a).iargs) :
    t ∈ a.iargs := by
  cases a with
  | obj r x y =>
    cases x with
    | var v =>
      cases y with
      | var w => exact ht
      | ind j =>
        cases j with
        | named b =>
          simp only [unifyAtom, RAtom.iargs, List.mem_singleton] at ht
          subst ht; exact List.mem_cons_self ..
        | anon _ => exact ht
    | ind i =>
      cases i with
      | named b =>
        cases y with
        | var w =>
          simp only [unifyAtom, RAtom.iargs, List.mem_singleton] at ht
          subst ht; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
        | ind _ => exact ht
      | anon _ => exact ht
  | _ => exact ht

theorem namedIn_unifyRule {N : List IRI} {ρ : DLRule} (h : NamedIn N ρ) : NamedIn N (unifyRule ρ) := by
  intro a ha t ht b hb
  rw [unifyRule, ← List.map_append, List.mem_map] at ha
  obtain ⟨a0, ha0, rfl⟩ := ha
  exact h a0 ha0 t (iargs_unifyAtom a0 ht) b hb

theorem val_upd_of_not_mem (J : Interp DM Dom) (σ : IRI → Dom) (v : IRI) (y : Dom)
    {x : IArg} (hx : v ∉ x.vars) :
    x.val J (fun w => if w = v then y else σ w) = x.val J σ := by
  cases x with
  | var w =>
    have hne : w ≠ v := fun h => hx (by simp [IArg.vars, h])
    simp [IArg.val, hne]
  | ind _ => rfl

theorem sat_upd_of_not_mem (bi : BuiltIns DM) (J : Interp DM Dom) (σ : IRI → Dom)
    (δ : IRI → DM.Val) (v : IRI) (y : Dom) {a : RAtom} (ha : v ∉ a.ivars) :
    a.sat bi J (fun w => if w = v then y else σ w) δ ↔ a.sat bi J σ δ := by
  cases a with
  | cls c x =>
    simp only [RAtom.ivars] at ha
    simp only [RAtom.sat, val_upd_of_not_mem J σ v y ha]
  | obj r x1 x2 =>
    simp only [RAtom.ivars, List.mem_append, not_or] at ha
    simp only [RAtom.sat, val_upd_of_not_mem J σ v y ha.1, val_upd_of_not_mem J σ v y ha.2]
  | same x1 x2 =>
    simp only [RAtom.ivars, List.mem_append, not_or] at ha
    simp only [RAtom.sat, val_upd_of_not_mem J σ v y ha.1, val_upd_of_not_mem J σ v y ha.2]
  | diff x1 x2 =>
    simp only [RAtom.ivars, List.mem_append, not_or] at ha
    simp only [RAtom.sat, val_upd_of_not_mem J σ v y ha.1, val_upd_of_not_mem J σ v y ha.2]
  | data p x d =>
    simp only [RAtom.ivars] at ha
    simp only [RAtom.sat, val_upd_of_not_mem J σ v y ha]
  | drange r d => simp [RAtom.sat]
  | builtin f args => simp [RAtom.sat]

theorem stepAtomV_inl {v : IRI} {a : RAtom} {dir : ObjProp} {x : IArg}
    (h : stepAtomV v a = some (.inl (dir, x))) :
    v ∈ a.ivars ∧ v ∉ x.vars ∧
    (∀ w ∈ a.ivars, w = v ∨ w ∈ x.vars) ∧ (∀ w ∈ x.vars, w ∈ a.ivars) ∧
    x ∈ a.iargs ∧
    ∀ {DM : DatatypeMap} {Dom : Type} (bi : BuiltIns DM) (J : Interp DM Dom)
      (σ : IRI → Dom) (δ : IRI → DM.Val) (y : Dom),
      a.sat bi J (fun w => if w = v then y else σ w) δ ↔ J.prop dir (x.val J σ) y := by
  unfold stepAtomV at h
  split_ifs at h with hv
  · cases a with
    | cls _ x1 => cases x1 <;> (try dsimp only at h; split_ifs at h) <;> cases h
    | data _ _ _ => cases h
    | drange _ _ => cases h
    | same _ _ => cases h
    | diff _ _ => cases h
    | builtin _ _ => cases h
    | obj r x1 x2 =>
      dsimp only at h
      split_ifs at h with h1 h2
      · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at h1
        obtain ⟨rfl, hx⟩ := h1
        refine ⟨hv, hx, ?_, ?_, List.mem_cons_self .., fun bi J σ δ y => ?_⟩
        · intro w hw
          simp only [RAtom.ivars, IArg.vars, List.mem_append, List.mem_singleton] at hw
          exact hw.symm
        · intro w hw
          exact List.mem_append_left _ hw
        · simp only [RAtom.sat, val_upd_of_not_mem J σ v y hx]
          simp [IArg.val]
      · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at h2
        obtain ⟨rfl, hx⟩ := h2
        refine ⟨hv, hx, ?_, ?_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
          fun bi J σ δ y => ?_⟩
        · intro w hw
          simp only [RAtom.ivars, IArg.vars, List.mem_append, List.mem_singleton] at hw
          exact hw
        · intro w hw
          exact List.mem_append_right _ hw
        · simp only [RAtom.sat, val_upd_of_not_mem J σ v y hx, prop_flip]
          simp [IArg.val]
  · cases h

theorem stepAtomV_inr_inl {v : IRI} {a : RAtom} {c : ClassExpr}
    (h : stepAtomV v a = some (.inr (.inl c))) :
    a = .cls c (.var v) := by
  unfold stepAtomV at h
  split_ifs at h with hv
  · cases a with
    | cls c' x =>
      cases x with
      | var w =>
        dsimp only at h
        split_ifs at h with hw
        simp only [Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at h
        subst h hw; rfl
      | ind _ => cases h
    | obj r x1 x2 =>
      dsimp only at h; split_ifs at h <;> cases h
    | _ => cases h
  · cases h

theorem stepAtomV_inr_inr {v : IRI} {a a' : RAtom}
    (h : stepAtomV v a = some (.inr (.inr a'))) :
    a' = a ∧ v ∉ a.ivars := by
  unfold stepAtomV at h
  split_ifs at h with hv
  · cases a with
    | cls _ x => cases x <;> (try dsimp only at h; split_ifs at h) <;> cases h
    | obj _ x1 x2 => dsimp only at h; split_ifs at h <;> cases h
    | _ => cases h
  · simp only [Option.some.injEq, Sum.inr.injEq] at h
    exact ⟨h.symm, hv⟩

theorem splitBodyV_sat (bi : BuiltIns DM) (J : Interp DM Dom) {v : IRI} :
    ∀ {bs : List RAtom} {bins : List (ObjProp × IArg)} {cs : List ClassExpr} {rest : List RAtom},
      splitBodyV v bs = some (bins, cs, rest) →
      ∀ (σ : IRI → Dom) (δ : IRI → DM.Val) (y : Dom),
        (∀ a ∈ bs, a.sat bi J (fun w => if w = v then y else σ w) δ) ↔
          (∀ p ∈ bins, J.prop p.1 (p.2.val J σ) y) ∧
          (∀ c ∈ cs, J.ext c y) ∧
          (∀ a ∈ rest, a.sat bi J σ δ)
  | [], _, _, _, h, σ, δ, y => by
    simp only [splitBodyV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | a :: as, bins, cs, rest, h, σ, δ, y => by
    simp only [splitBodyV, Option.bind_eq_some_iff] at h
    obtain ⟨⟨bins0, cs0, rest0⟩, has, hstep⟩ := h
    have ih := splitBodyV_sat bi J has σ δ y
    cases hs : stepAtomV v a with
    | none => rw [hs] at hstep; cases hstep
    | some s =>
      rw [hs] at hstep
      rcases s with ⟨dir, x⟩ | (c | a')
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        have h1 := (stepAtomV_inl hs).2.2.2.2.2 bi J σ δ y
        simp only [List.mem_cons, forall_eq_or_imp, h1, ih]
        tauto
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        have rfl_a := stepAtomV_inr_inl hs
        subst rfl_a
        rw [List.forall_mem_cons, List.forall_mem_cons (p := fun c => J.ext c y), ih]
        simp only [RAtom.sat, IArg.val, ↓reduceIte]
        tauto
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        obtain ⟨rfl, hnv⟩ := stepAtomV_inr_inr hs
        have h1 := sat_upd_of_not_mem bi J σ δ v y hnv
        simp only [List.mem_cons, forall_eq_or_imp, h1, ih]
        tauto

theorem splitBodyV_props {v : IRI} :
    ∀ {bs : List RAtom} {bins : List (ObjProp × IArg)} {cs : List ClassExpr} {rest : List RAtom},
      splitBodyV v bs = some (bins, cs, rest) →
      (∀ p ∈ bins, v ∈ bs.flatMap RAtom.ivars ∧
        (∀ w ∈ p.2.vars, w ∈ bs.flatMap RAtom.ivars ∧ w ≠ v) ∧
        (∃ a ∈ bs, p.2 ∈ a.iargs)) ∧
      (∀ a ∈ rest, a ∈ bs ∧ v ∉ a.ivars) ∧
      (∀ w ∈ bs.flatMap RAtom.ivars,
        w = v ∨ (∃ p ∈ bins, w ∈ p.2.vars) ∨ (∃ a ∈ rest, w ∈ a.ivars))
  | [], _, _, _, h => by
    simp only [splitBodyV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | a :: as, bins, cs, rest, h => by
    simp only [splitBodyV, Option.bind_eq_some_iff] at h
    obtain ⟨⟨bins0, cs0, rest0⟩, has, hstep⟩ := h
    obtain ⟨ih1, ih3, ih4⟩ := splitBodyV_props has
    cases hs : stepAtomV v a with
    | none => rw [hs] at hstep; cases hstep
    | some s =>
      rw [hs] at hstep
      rcases s with ⟨dir, x⟩ | (c | a')
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        obtain ⟨hva, hvx, hvars, hx_ivars, hxi, -⟩ := stepAtomV_inl hs
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨List.mem_append_left _ hva,
              fun w hw => ⟨List.mem_append_left _ (hx_ivars w hw), fun h => hvx (h ▸ hw)⟩,
              ⟨a, List.mem_cons_self .., hxi⟩⟩
          · obtain ⟨h1, h2, a0, ha0, h3⟩ := ih1 p hp
            exact ⟨List.mem_append_right _ h1,
              fun w hw => ⟨List.mem_append_right _ (h2 w hw).1, (h2 w hw).2⟩,
              ⟨a0, List.mem_cons_of_mem _ ha0, h3⟩⟩
        · intro a0 ha0
          obtain ⟨h1, h2⟩ := ih3 a0 ha0
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩
        · intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rcases hvars w hw with rfl | hwx
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨(dir, x), List.mem_cons_self .., hwx⟩)
          · rcases ih4 w hw with rfl | ⟨p, hp, hwp⟩ | ⟨a0, ha0, hwa⟩
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨p, List.mem_cons_of_mem _ hp, hwp⟩)
            · exact Or.inr (Or.inr ⟨a0, ha0, hwa⟩)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        have rfl_a := stepAtomV_inr_inl hs
        subst rfl_a
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          obtain ⟨h1, h2, a0, ha0, h3⟩ := ih1 p hp
          exact ⟨List.mem_append_right _ h1,
            fun w hw => ⟨List.mem_append_right _ (h2 w hw).1, (h2 w hw).2⟩,
            ⟨a0, List.mem_cons_of_mem _ ha0, h3⟩⟩
        · intro a0 ha0
          obtain ⟨h1, h2⟩ := ih3 a0 ha0
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩
        · intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · simp only [RAtom.ivars, IArg.vars, List.mem_singleton] at hw
            exact Or.inl hw
          · exact ih4 w hw
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl, rfl⟩ := hstep
        obtain ⟨rfl, hnv⟩ := stepAtomV_inr_inr hs
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          obtain ⟨h1, h2, a0, ha0, h3⟩ := ih1 p hp
          exact ⟨List.mem_append_right _ h1,
            fun w hw => ⟨List.mem_append_right _ (h2 w hw).1, (h2 w hw).2⟩,
            ⟨a0, List.mem_cons_of_mem _ ha0, h3⟩⟩
        · intro a0 ha0
          rcases List.mem_cons.1 ha0 with rfl | ha0
          · exact ⟨List.mem_cons_self .., hnv⟩
          · obtain ⟨h1, h2⟩ := ih3 a0 ha0
            exact ⟨List.mem_cons_of_mem _ h1, h2⟩
        · intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inr (Or.inr ⟨a', List.mem_cons_self .., hw⟩)
          · rcases ih4 w hw with rfl | ⟨p, hp, hwp⟩ | ⟨a0, ha0, hwa⟩
            · exact Or.inl rfl
            · exact Or.inr (Or.inl ⟨p, hp, hwp⟩)
            · exact Or.inr (Or.inr ⟨a0, List.mem_cons_of_mem _ ha0, hwa⟩)

theorem ext_hasValue_inv_u (J : Interp DM Dom) (u h0 : IRI) (y : Dom) :
    J.ext (.hasValue (.inv u) (.named h0)) y ↔ J.prop (.named u) (J.ind (.named h0)) y := by
  rw [Interp.ext]; rfl

theorem sat_rolledAtom (bi : BuiltIns DM) (J : Interp DM Dom) (u h0 : IRI)
    (dir : ObjProp) (cs : List ClassExpr) (x : IArg) (σ : IRI → Dom) (δ : IRI → DM.Val) :
    (RAtom.cls (.some dir (.and (.hasValue (.inv u) (.named h0) :: cs))) x).sat bi J σ δ ↔
      ∃ y, J.prop dir (x.val J σ) y ∧ J.prop (.named u) (J.ind (.named h0)) y ∧ ∀ c ∈ cs, J.ext c y := by
  simp only [RAtom.sat]
  rw [Interp.ext]
  simp only [ext_andL, List.mem_cons, forall_eq_or_imp, ext_hasValue_inv_u]

theorem rollVar_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI) {u h0 v : IRI}
    {ρ ρ' : DLRule} (h : rollVar u h0 v ρ = some ρ') :
    ((∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))) →
      ρ'.sat bi J O_named → ρ.sat bi J O_named) ∧
    ((∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y) →
      ρ.sat bi J O_named → ρ'.sat bi J O_named) ∧
    (NamedIn O_named.eraseDups ρ → NamedIn O_named.eraseDups ρ') := by
  unfold rollVar at h
  split_ifs at h with hvh
  cases hs : splitBodyV v ρ.body with
  | none => rw [hs] at h; cases h
  | some t =>
    rw [hs] at h
    rcases t with ⟨bins, cs, rest⟩
    cases bins with
    | nil => cases h
    | cons bx bins' =>
      cases bins' with
      | cons _ _ => cases h
      | nil =>
        rcases bx with ⟨dir, x⟩
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hp1, hp3, hp4⟩ := splitBodyV_props hs
        obtain ⟨hv_body, hwx_body, a_bin, ha_bin, hx_bin⟩ := hp1 (dir, x) (List.mem_singleton_self _)
        refine ⟨?_, ?_, ?_⟩
        · -- ρ'.sat → ρ.sat
          intro hux hρ' σ δ hnm hbody a ha
          have hid : (fun w => if w = v then σ v else σ w) = σ := by
            funext w; split_ifs with hw <;> [subst hw; rfl] <;> rfl
          have hbs := (splitBodyV_sat bi J hs σ δ (σ v)).1 (hid.symm ▸ hbody)
          have hnm_v : J.IsNamed O_named (σ v) :=
            hnm v (by rw [DLRule.ivars, List.flatMap_append]; exact List.mem_append_left _ hv_body)
          obtain ⟨b_v, hbv, hσv⟩ := hnm_v
          have hu_v : J.prop (.named u) (J.ind (.named h0)) (σ v) :=
            hσv ▸ hux b_v (List.mem_eraseDups.2 hbv)
          have hnm' : ∀ w ∈ (DLRule.mk (.cls (.some dir (.and (.hasValue (.inv u) (.named h0) :: cs))) x :: rest) ρ.head).ivars,
              J.IsNamed O_named (σ w) := by
            intro w hw
            simp only [DLRule.ivars, List.cons_append, List.flatMap_cons, RAtom.ivars,
              List.mem_append, List.mem_flatMap] at hw
            rcases hw with hwx | ⟨a0, ha0, hwa⟩
            · exact hnm w (by rw [DLRule.ivars, List.flatMap_append]; exact List.mem_append_left _ (hwx_body w hwx).1)
            · rcases ha0 with ha0 | ha0
              · exact hnm w (by rw [DLRule.ivars, List.flatMap_append]; exact List.mem_append_left _ (List.mem_flatMap.2 ⟨a0, (hp3 a0 ha0).1, hwa⟩))
              · exact hnm w (by rw [DLRule.ivars, List.flatMap_append]; exact List.mem_append_right _ (List.mem_flatMap.2 ⟨a0, ha0, hwa⟩))
          refine hρ' σ δ hnm' (fun a0 ha0 => ?_) a ha
          rcases List.mem_cons.1 ha0 with rfl | ha0
          · exact (sat_rolledAtom bi J u h0 dir cs x σ δ).2
              ⟨σ v, hbs.1 (dir, x) (List.mem_singleton_self _), hu_v, hbs.2.1⟩
          · exact hbs.2.2 a0 ha0
        · -- ρ.sat → ρ'.sat
          intro hu hρ σ δ hnm' hbody' a ha
          have hhead := (sat_rolledAtom bi J u h0 dir cs x σ δ).1 (hbody' _ (List.mem_cons_self ..))
          obtain ⟨y, hdir, hyu, hcs⟩ := hhead
          have hyN : J.IsNamed O_named y := (hu _ y).1 hyu
          have hrest : ∀ a0 ∈ rest, a0.sat bi J σ δ := fun a0 ha0 =>
            hbody' a0 (List.mem_cons_of_mem _ ha0)
          let σ' : IRI → Dom := fun w => if w = v then y else σ w
          have hnm : ∀ w ∈ ρ.ivars, J.IsNamed O_named (σ' w) := by
            intro w hw
            dsimp only [σ']
            split_ifs with hwv
            · exact hyN
            · refine hnm' w ?_
              simp only [DLRule.ivars, List.flatMap_append, List.mem_append] at hw
              simp only [DLRule.ivars, List.cons_append, List.flatMap_cons, RAtom.ivars,
                List.mem_append]
              rcases hw with hw | hw
              · rcases hp4 w hw with rfl | ⟨p, hp, hwp⟩ | ⟨a0, ha0, hwa⟩
                · exact absurd rfl hwv
                · rw [List.mem_singleton.1 hp] at hwp
                  exact Or.inl hwp
                · exact Or.inr (List.mem_flatMap.2 ⟨a0, List.mem_append_left _ ha0, hwa⟩)
              · exact Or.inr (List.mem_flatMap.2 (by
                  obtain ⟨a0, ha0, hwa⟩ := List.mem_flatMap.1 hw
                  exact ⟨a0, List.mem_append_right _ ha0, hwa⟩))
          have hbody : ∀ a0 ∈ ρ.body, a0.sat bi J σ' δ :=
            (splitBodyV_sat bi J hs σ δ y).2
              ⟨fun p hp => by rw [List.mem_singleton.1 hp]; exact hdir, hcs, hrest⟩
          have hvh_a : v ∉ a.ivars := fun hv => hvh (List.mem_flatMap.2 ⟨a, ha, hv⟩)
          exact (sat_upd_of_not_mem bi J σ δ v y hvh_a).1 (hρ σ' δ hnm hbody a ha)
        · -- NamedIn
          intro hni a ha t ht b hb
          simp only [List.cons_append, List.mem_cons, List.mem_append] at ha
          rcases ha with rfl | ha | ha
          · simp only [RAtom.iargs, List.mem_singleton] at ht
            subst ht
            exact hni a_bin (List.mem_append_left _ ha_bin) t hx_bin b hb
          · exact hni a (List.mem_append_left _ (hp3 a ha).1) t ht b hb
          · exact hni a (List.mem_append_right _ ha) t ht b hb

theorem findRoll_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI) {u h0 : IRI}
    {ρ : DLRule} :
    ∀ {vs : List IRI} {ρ' : DLRule},
      findRoll u h0 ρ vs = some ρ' →
      ((∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))) →
        ρ'.sat bi J O_named → ρ.sat bi J O_named) ∧
      ((∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y) →
        ρ.sat bi J O_named → ρ'.sat bi J O_named) ∧
      (NamedIn O_named.eraseDups ρ → NamedIn O_named.eraseDups ρ')
  | [], _, h => by cases h
  | v :: vs, ρ', h => by
    unfold findRoll at h
    cases hr : rollVar u h0 v ρ with
    | some ρ1 =>
      rw [hr] at h; simp only [Option.some.injEq] at h; subst h
      exact rollVar_spec bi J O_named hr
    | none =>
      rw [hr] at h
      exact findRoll_spec bi J O_named h

theorem rollLoop_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI) (u h0 : IRI) :
    ∀ (k : Nat) (ρ : DLRule),
      ((∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))) →
        (rollLoop u h0 k ρ).sat bi J O_named → ρ.sat bi J O_named) ∧
      ((∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y) →
        ρ.sat bi J O_named → (rollLoop u h0 k ρ).sat bi J O_named) ∧
      (NamedIn O_named.eraseDups ρ → NamedIn O_named.eraseDups (rollLoop u h0 k ρ))
  | 0, ρ => ⟨fun _ => id, fun _ => id, id⟩
  | k + 1, ρ => by
    unfold rollLoop
    cases hf : findRoll u h0 ρ ρ.ivars.eraseDups with
    | none => exact ⟨fun _ => id, fun _ => id, id⟩
    | some ρ1 =>
      obtain ⟨h1, h2, h3⟩ := findRoll_spec bi J O_named hf
      obtain ⟨ih1, ih2, ih3⟩ := rollLoop_spec bi J O_named u h0 k ρ1
      exact ⟨fun hux h => h1 hux (ih1 hux h), fun hu h => ih2 hu (h2 hu h), fun h => ih3 (h3 h)⟩

theorem rollAll_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI) (u h0 : IRI)
    (ρ : DLRule) :
    ((∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))) →
      (rollAll u h0 ρ).sat bi J O_named → ρ.sat bi J O_named) ∧
    ((∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y) →
      ρ.sat bi J O_named → (rollAll u h0 ρ).sat bi J O_named) ∧
    (NamedIn O_named.eraseDups ρ → NamedIn O_named.eraseDups (rollAll u h0 ρ)) := by
  unfold rollAll
  obtain ⟨h1, h2, h3⟩ := rollLoop_spec bi J O_named u h0 (unifyRule ρ).ivars.length (unifyRule ρ)
  exact ⟨fun hux h => (sat_unifyRule bi J O_named ρ).1 (h1 hux h),
    fun hu h => h2 hu ((sat_unifyRule bi J O_named ρ).2 h),
    fun h => h3 (namedIn_unifyRule h)⟩

theorem val_substIArg {J : Interp DM Dom} {σ : IRI → Dom} {v b : IRI}
    (h : σ v = J.ind (.named b)) (x : IArg) :
    (substIArg v b x).val J σ = x.val J σ := by
  cases x with
  | var w =>
    simp only [substIArg]
    split_ifs with hw
    · subst hw; simp [IArg.val, h]
    · rfl
  | ind _ => rfl

theorem sat_substAtom (bi : BuiltIns DM) {J : Interp DM Dom} {σ : IRI → Dom} {δ : IRI → DM.Val}
    {v b : IRI} (h : σ v = J.ind (.named b)) (a : RAtom) :
    (substAtom v b a).sat bi J σ δ ↔ a.sat bi J σ δ := by
  cases a <;> simp [substAtom, RAtom.sat, val_substIArg h]

theorem val_substIArg_upd (J : Interp DM Dom) (σ : IRI → Dom) (v b : IRI) (x : IArg) :
    (substIArg v b x).val J σ = x.val J (fun w => if w = v then J.ind (.named b) else σ w) := by
  cases x with
  | var w => simp only [substIArg, IArg.val]; split_ifs <;> rfl
  | ind _ => rfl

theorem sat_substAtom_upd (bi : BuiltIns DM) (J : Interp DM Dom) (σ : IRI → Dom)
    (δ : IRI → DM.Val) (v b : IRI) (a : RAtom) :
    (substAtom v b a).sat bi J σ δ ↔
      a.sat bi J (fun w => if w = v then J.ind (.named b) else σ w) δ := by
  cases a <;> simp [substAtom, RAtom.sat, val_substIArg_upd]

theorem mem_vars_substIArg (v b : IRI) (x : IArg) (w : IRI) :
    w ∈ (substIArg v b x).vars ↔ w ∈ x.vars ∧ w ≠ v := by
  cases x with
  | var u =>
    simp only [substIArg]
    split_ifs with h
    · subst h; simp [IArg.vars]
    · simp only [IArg.vars, List.mem_singleton, ne_eq]
      exact ⟨fun hwu => ⟨hwu, hwu ▸ h⟩, fun hwu => hwu.1⟩
  | ind _ => simp [substIArg, IArg.vars]

theorem mem_ivars_substAtom (v b : IRI) (a : RAtom) (w : IRI) :
    w ∈ (substAtom v b a).ivars ↔ w ∈ a.ivars ∧ w ≠ v := by
  cases a <;> simp [substAtom, RAtom.ivars, mem_vars_substIArg] <;> tauto

theorem mem_ivars_substRule (v b : IRI) (ρ : DLRule) (w : IRI) :
    w ∈ (substRule v b ρ).ivars ↔ w ∈ ρ.ivars ∧ w ≠ v := by
  simp only [DLRule.ivars, substRule, ← List.map_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨a0, ha0, rfl⟩, hw⟩
    obtain ⟨hwa, hne⟩ := (mem_ivars_substAtom v b a0 w).1 hw
    exact ⟨⟨a0, ha0, hwa⟩, hne⟩
  · rintro ⟨⟨a0, ha0, hwa⟩, hne⟩
    exact ⟨substAtom v b a0, ⟨a0, ha0, rfl⟩, (mem_ivars_substAtom v b a0 w).2 ⟨hwa, hne⟩⟩

theorem iargs_substAtom (v b : IRI) (a : RAtom) :
    (substAtom v b a).iargs = a.iargs.map (substIArg v b) := by
  cases a <;> rfl

theorem substIArg_eq_named {v b c : IRI} {x : IArg} (h : substIArg v b x = .ind (.named c)) :
    c = b ∨ x = .ind (.named c) := by
  cases x with
  | var w =>
    simp only [substIArg] at h
    split_ifs at h
    simp only [IArg.ind.injEq, Individual.named.injEq] at h
    exact Or.inl h.symm
  | ind i => exact Or.inr h

theorem substRule_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI)
    {v : IRI} {ρ : DLRule} (hv : v ∈ ρ.ivars) :
    ((∀ b ∈ O_named.eraseDups, (substRule v b ρ).sat bi J O_named) ↔ ρ.sat bi J O_named) ∧
    (∀ b ∈ O_named.eraseDups, NamedIn O_named.eraseDups ρ → NamedIn O_named.eraseDups (substRule v b ρ)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hall σ δ hnm hbody a ha
    obtain ⟨b, hb, hσv⟩ := hnm v hv
    have hbN : b ∈ O_named.eraseDups := List.mem_eraseDups.2 hb
    have hnm' : ∀ w ∈ (substRule v b ρ).ivars, J.IsNamed O_named (σ w) := fun w hw =>
      hnm w ((mem_ivars_substRule v b ρ w).1 hw).1
    have hbody' : ∀ a0 ∈ (substRule v b ρ).body, a0.sat bi J σ δ := by
      intro a0 ha0
      obtain ⟨a1, ha1, rfl⟩ := List.mem_map.1 ha0
      exact (sat_substAtom bi hσv a1).2 (hbody a1 ha1)
    have hhead' := hall b hbN σ δ hnm' hbody' (substAtom v b a) (List.mem_map_of_mem ha)
    exact (sat_substAtom bi hσv a).1 hhead'
  · intro hρ b hbN σ δ hnm' hbody' a ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
    let σ' : IRI → Dom := fun w => if w = v then J.ind (.named b) else σ w
    have hnm : ∀ w ∈ ρ.ivars, J.IsNamed O_named (σ' w) := by
      intro w hw
      dsimp only [σ']
      split_ifs with hwv
      · exact ⟨b, List.mem_eraseDups.1 hbN, rfl⟩
      · exact hnm' w ((mem_ivars_substRule v b ρ w).2 ⟨hw, hwv⟩)
    have hbody : ∀ a1 ∈ ρ.body, a1.sat bi J σ' δ := fun a1 ha1 =>
      (sat_substAtom_upd bi J σ δ v b a1).1 (hbody' _ (List.mem_map_of_mem ha1))
    exact (sat_substAtom_upd bi J σ δ v b a0).2 (hρ σ' δ hnm hbody a0 ha0)
  · intro b hbN hni a ha t ht c hc
    rw [substRule, ← List.map_append, List.mem_map] at ha
    obtain ⟨a0, ha0, rfl⟩ := ha
    rw [iargs_substAtom, List.mem_map] at ht
    obtain ⟨t0, ht0, rfl⟩ := ht
    rcases substIArg_eq_named hc with rfl | ht0c
    · exact hbN
    · exact hni a0 ha0 t0 ht0 c ht0c

theorem pickMinBy_mem {α : Type} (cost : α → Nat) :
    ∀ {l : List α} {x : α}, pickMinBy cost l = some x → x ∈ l
  | [], _, h => by cases h
  | [a], x, h => by
    simp only [pickMinBy, Option.some.injEq] at h; subst h; exact List.mem_singleton_self _
  | a :: b :: rest, x, h => by
    unfold pickMinBy at h
    cases hm : pickMinBy cost (b :: rest) with
    | none =>
      rw [hm] at h; simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self ..
    | some z =>
      rw [hm] at h; dsimp only at h
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (pickMinBy_mem cost hm)

theorem splitStep_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI)
    (u h0 : IRI) (ρ : DLRule) :
    ((∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))) →
      (∀ ρ' ∈ splitStep u h0 O_named.eraseDups ρ, ρ'.sat bi J O_named) → ρ.sat bi J O_named) ∧
    ((∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y) →
      ρ.sat bi J O_named → ∀ ρ' ∈ splitStep u h0 O_named.eraseDups ρ, ρ'.sat bi J O_named) ∧
    (NamedIn O_named.eraseDups ρ → ∀ ρ' ∈ splitStep u h0 O_named.eraseDups ρ, NamedIn O_named.eraseDups ρ') := by
  unfold splitStep
  dsimp only
  obtain ⟨hr_bwd, hr_fwd, hni1⟩ := rollAll_spec bi J O_named u h0 ρ
  cases hN : O_named.eraseDups with
  | nil =>
    rw [hN] at hni1
    simp only [List.mem_singleton, forall_eq]
    exact ⟨fun hux => hr_bwd (hN ▸ hux), hr_fwd, hni1⟩
  | cons b0 restN =>
    split_ifs
    · rw [hN] at hni1
      simp only [List.mem_singleton, forall_eq]
      exact ⟨fun hux => hr_bwd (hN ▸ hux), hr_fwd, hni1⟩
    · dsimp only
      cases hp : pickMinBy (fun v => (rollAll u h0 (substRule v b0 (rollAll u h0 ρ))).ivars.eraseDups.length)
        (rollAll u h0 ρ).ivars.eraseDups with
      | none =>
        dsimp only
        rw [hN] at hni1
        simp only [List.mem_singleton, forall_eq]
        exact ⟨fun hux => hr_bwd (hN ▸ hux), hr_fwd, hni1⟩
      | some v =>
        dsimp only
        split_ifs
        · have hv : v ∈ (rollAll u h0 ρ).ivars :=
            List.mem_eraseDups.1 (pickMinBy_mem _ hp)
          rw [← hN]
          obtain ⟨hs1, hs2⟩ := substRule_spec bi J O_named hv
          simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          refine ⟨?_, ?_, ?_⟩
          · intro hux hall
            exact hr_bwd hux (hs1.1 fun b hb =>
              (rollAll_spec bi J O_named u h0 (substRule v b _)).1 hux (hall b hb))
          · intro hu hρ b hb
            exact (rollAll_spec bi J O_named u h0 (substRule v b _)).2.1 hu (hs1.2 (hr_fwd hu hρ) b hb)
          · intro hni b hb
            exact (rollAll_spec bi J O_named u h0 (substRule v b _)).2.2 (hs2 b hb (hni1 hni))
        · rw [hN] at hni1
          simp only [List.mem_singleton, forall_eq]
          exact ⟨fun hux => hr_bwd (hN ▸ hux), hr_fwd, hni1⟩

theorem splitRule_spec (bi : BuiltIns DM) (J : Interp DM Dom) (O_named : List IRI)
    (u h0 : IRI) (ρ : DLRule) :
    ((∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))) →
      (∀ ρ' ∈ splitRule u h0 O_named.eraseDups ρ, ρ'.sat bi J O_named) → ρ.sat bi J O_named) ∧
    ((∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y) →
      ρ.sat bi J O_named → ∀ ρ' ∈ splitRule u h0 O_named.eraseDups ρ, ρ'.sat bi J O_named) ∧
    (NamedIn O_named.eraseDups ρ → ∀ ρ' ∈ splitRule u h0 O_named.eraseDups ρ, NamedIn O_named.eraseDups ρ') := by
  unfold splitRule
  simp only [List.mem_flatMap, forall_exists_index, and_imp]
  refine ⟨?_, ?_, ?_⟩
  · intro hux hall
    refine (splitStep_spec bi J O_named u h0 ρ).1 hux fun ρ1 hρ1 => ?_
    refine (splitStep_spec bi J O_named u h0 ρ1).1 hux fun ρ2 hρ2 => ?_
    exact (splitStep_spec bi J O_named u h0 ρ2).1 hux fun ρ3 hρ3 => hall ρ3 ρ2 ρ1 hρ1 hρ2 hρ3
  · intro hu hρ ρ3 ρ2 ρ1 hρ1 hρ2 hρ3
    have h1 := (splitStep_spec bi J O_named u h0 ρ).2.1 hu hρ ρ1 hρ1
    have h2 := (splitStep_spec bi J O_named u h0 ρ1).2.1 hu h1 ρ2 hρ2
    exact (splitStep_spec bi J O_named u h0 ρ2).2.1 hu h2 ρ3 hρ3
  · intro hni ρ3 ρ2 ρ1 hρ1 hρ2 hρ3
    have h1 := (splitStep_spec bi J O_named u h0 ρ).2.2 hni ρ1 hρ1
    have h2 := (splitStep_spec bi J O_named u h0 ρ1).2.2 h1 ρ2 hρ2
    exact (splitStep_spec bi J O_named u h0 ρ2).2.2 h2 ρ3 hρ3

theorem asUnaryV_eq {v : IRI} {a : RAtom} {c : ClassExpr} (h : asUnaryV v a = some c) :
    a = .cls c (.var v) := by
  cases a with
  | cls c' x =>
    cases x with
    | var w =>
      unfold asUnaryV at h
      dsimp only at h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h; subst h hw; rfl
    | ind _ => cases h
  | _ => cases h

theorem ext_or_cons (J : Interp DM Dom) (c : ClassExpr) (cs : List ClassExpr) (y : Dom) :
    J.ext (.or (c :: cs)) y ↔ J.ext c y ∨ J.ext (.or cs) y := by
  conv_lhs => rw [Interp.ext]
  conv_rhs => rw [Interp.ext]
  simp [exists_eq_or_imp]

theorem ext_or_not_list (J : Interp DM Dom) :
    ∀ (vbs : List ClassExpr) (H : ClassExpr) (y : Dom),
      J.ext (.or (vbs.map .not ++ [H])) y ↔ ((∀ B ∈ vbs, J.ext B y) → J.ext H y)
  | [], H, y => by
    rw [Interp.ext]; simp
  | B :: vbs, H, y => by
    simp only [List.map_cons, List.cons_append, List.mem_cons, forall_eq_or_imp]
    rw [ext_or_cons, ext_not', ext_or_not_list J vbs H y]
    tauto

theorem ext_oneVarHeadCE (J : Interp DM Dom) (u : IRI)
    (vbs : List ClassExpr) (H : ClassExpr) (x0 : Dom) :
    J.ext (oneVarHeadCE u vbs H) x0 ↔
      ∀ y, J.prop (.named u) x0 y → (∀ B ∈ vbs, J.ext B y) → J.ext H y := by
  unfold oneVarHeadCE
  rw [Interp.ext]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  exact ext_or_not_list J vbs H y

theorem instOneVar_fwd [hv : Nonempty DM.Val] (bi : BuiltIns DM) {J : Interp DM Dom}
    {O_named NN : List IRI} {u h0 : IRI} {ρ : DLRule} {ax : Axiom}
    (h : instOneVar u h0 ρ = some ax)
    (hni : NamedIn O_named.eraseDups ρ)
    (hu : ∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y)
    (hρ : ρ.sat bi J O_named) :
    J.sat NN ax := by
  unfold instOneVar at h
  cases hh : headVar ρ.head with
  | none => rw [hh] at h; cases h
  | some v =>
    rw [hh] at h; dsimp only at h
    cases hs : splitBodyV v ρ.body with
    | none => rw [hs] at h; cases h
    | some t =>
      rw [hs] at h
      rcases t with ⟨bins, vbs, rest⟩
      cases bins with
      | cons _ _ => cases h
      | nil =>
        cases rest with
        | nil =>
          dsimp only at h
          obtain ⟨vhs, hvhs, rfl⟩ := Option.map_eq_some_iff.1 h
          intro y hy
          rw [ext_andL] at hy ⊢
          have hyu : J.prop (.named u) (J.ind (.named h0)) y :=
            (ext_hasValue_inv_u J u h0 y).1 (hy _ (List.mem_cons_self ..))
          have hyN : J.IsNamed O_named y := (hu _ y).1 hyu
          have hyB : ∀ B ∈ vbs, J.ext B y := fun B hB => hy B (List.mem_cons_of_mem _ hB)
          let σ : IRI → Dom := fun _ => y
          let δ : IRI → DM.Val := fun _ => Classical.choice hv
          have hid : (fun w => if w = v then y else σ w) = σ := by
            funext w; dsimp only [σ]; split_ifs <;> rfl
          have hbody : ∀ a ∈ ρ.body, a.sat bi J σ δ := by
            rw [← hid]
            exact (splitBodyV_sat bi J hs σ δ y).2 ⟨by simp, hyB, by simp⟩
          have hnm : ∀ w ∈ ρ.ivars, J.IsNamed O_named (σ w) := fun _ _ => hyN
          intro H hH
          obtain ⟨a, ha, haH⟩ := mapM_some_bwd hvhs H hH
          have rfl_a := asUnaryV_eq haH
          subst rfl_a
          exact hρ σ δ hnm hbody (.cls H (.var v)) ha
        | cons r0 rest' =>
          dsimp only at h
          obtain ⟨gbs, hgbs, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨vhs, hvhs, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨-, hp3, -⟩ := splitBodyV_props hs
          intro x hx
          rw [ext_andL] at hx ⊢
          intro c hc
          obtain ⟨H, hH, rfl⟩ := List.mem_map.1 hc
          rw [ext_oneVarHeadCE]
          intro y hyu hyB
          have hyN : J.IsNamed O_named y := (hu x y).1 hyu
          let σ : IRI → Dom := fun _ => y
          let δ : IRI → DM.Val := fun _ => Classical.choice hv
          have hag : Agrees J [] σ := fun _ _ hl => by cases hl
          have hid : (fun w => if w = v then y else σ w) = σ := by
            funext w; dsimp only [σ]; split_ifs <;> rfl
          have hbody : ∀ a ∈ ρ.body, a.sat bi J σ δ := by
            rw [← hid]
            refine (splitBodyV_sat bi J hs σ δ y).2 ⟨by simp, hyB, fun a ha => ?_⟩
            obtain ⟨c0, hc0, hca0⟩ := mapM_some_fwd hgbs a ha
            have hua : ∀ t ∈ a.iargs, ∀ b, gI [] t = some b →
                J.prop (.named u) x (J.ind (.named b)) := by
              intro t ht b hb
              cases t with
              | var _ => cases hb
              | ind i =>
                cases i with
                | named b' =>
                  simp only [gI, Option.some.injEq] at hb; subst hb
                  exact (hu x _).2 ⟨b', List.mem_eraseDups.1
                    (hni a (List.mem_append_left _ (hp3 a ha).1) _ ht b' rfl), rfl⟩
                | anon _ => cases hb
            exact (bodyCE_iff bi u δ hag hua hca0).1 (hx c0 (List.mem_cons_of_mem _ hc0))
          have hnm : ∀ w ∈ ρ.ivars, J.IsNamed O_named (σ w) := fun _ _ => hyN
          obtain ⟨a, ha, haH⟩ := mapM_some_bwd hvhs H hH
          have rfl_a := asUnaryV_eq haH
          subst rfl_a
          exact hρ σ δ hnm hbody (.cls H (.var v)) ha

theorem instOneVar_bwd (bi : BuiltIns DM) {J : Interp DM Dom}
    {O_named NN : List IRI} {u h0 : IRI} {ρ : DLRule} {ax : Axiom}
    (h : instOneVar u h0 ρ = some ax)
    (hni : NamedIn O_named.eraseDups ρ)
    (hux : ∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b)))
    (hJax : J.sat NN ax) :
    ρ.sat bi J O_named := by
  unfold instOneVar at h
  cases hh : headVar ρ.head with
  | none => rw [hh] at h; cases h
  | some v =>
    rw [hh] at h; dsimp only at h
    cases hs : splitBodyV v ρ.body with
    | none => rw [hs] at h; cases h
    | some t =>
      rw [hs] at h
      rcases t with ⟨bins, vbs, rest⟩
      cases bins with
      | cons _ _ => cases h
      | nil =>
        cases rest with
        | nil =>
          dsimp only at h
          obtain ⟨vhs, hvhs, rfl⟩ := Option.map_eq_some_iff.1 h
          intro σ δ hnm hbody a ha
          obtain ⟨H, hH, haH⟩ := mapM_some_fwd hvhs a ha
          have rfl_a := asUnaryV_eq haH
          subst rfl_a
          have hv_mem : v ∈ ρ.ivars := List.mem_flatMap.2
            ⟨.cls H (.var v), List.mem_append_right _ ha, List.mem_singleton_self _⟩
          obtain ⟨b_v, hbv, hσv⟩ := hnm v hv_mem
          have hid : (fun w => if w = v then σ v else σ w) = σ := by
            funext w; split_ifs with hw <;> [subst hw; rfl] <;> rfl
          obtain ⟨-, hvbs, -⟩ := (splitBodyV_sat bi J hs σ δ (σ v)).1 (hid.symm ▸ hbody)
          have hy : J.ext (.and (.hasValue (.inv u) (.named h0) :: vbs)) (σ v) := by
            rw [ext_andL]
            intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · exact (ext_hasValue_inv_u J u h0 (σ v)).2 (hσv ▸ hux b_v (List.mem_eraseDups.2 hbv))
            · exact hvbs c hc
          have hh := hJax (σ v) hy
          rw [ext_andL] at hh
          exact hh H hH
        | cons r0 rest' =>
          dsimp only at h
          obtain ⟨gbs, hgbs, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨vhs, hvhs, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨-, hp3, -⟩ := splitBodyV_props hs
          intro σ δ hnm hbody a ha
          obtain ⟨H, hH, haH⟩ := mapM_some_fwd hvhs a ha
          have rfl_a := asUnaryV_eq haH
          subst rfl_a
          have hv_mem : v ∈ ρ.ivars := List.mem_flatMap.2
            ⟨.cls H (.var v), List.mem_append_right _ ha, List.mem_singleton_self _⟩
          obtain ⟨b_v, hbv, hσv⟩ := hnm v hv_mem
          have hid : (fun w => if w = v then σ v else σ w) = σ := by
            funext w; split_ifs with hw <;> [subst hw; rfl] <;> rfl
          obtain ⟨-, hvbs, hrest⟩ := (splitBodyV_sat bi J hs σ δ (σ v)).1 (hid.symm ▸ hbody)
          let x0 := J.ind (.named h0)
          have hag : Agrees J [] σ := fun _ _ hl => by cases hl
          have hx0 : J.ext (.and (.oneOf [.named h0] :: gbs)) x0 := by
            rw [ext_andL]
            intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · exact (ext_oneOf1 J _ _).2 rfl
            · obtain ⟨a', ha', hca'⟩ := mapM_some_bwd hgbs c hc
              have hua' : ∀ t ∈ a'.iargs, ∀ b, gI [] t = some b →
                  J.prop (.named u) x0 (J.ind (.named b)) := by
                intro t ht b hb
                cases t with
                | var _ => cases hb
                | ind i =>
                  cases i with
                  | named b' =>
                    simp only [gI, Option.some.injEq] at hb; subst hb
                    exact hux b' (hni a' (List.mem_append_left _ (hp3 a' ha').1) _ ht b' rfl)
                  | anon _ => cases hb
              exact (bodyCE_iff bi u δ hag hua' hca').2 (hrest a' ha')
          have hhx0 := hJax x0 hx0
          rw [ext_andL] at hhx0
          have hce := hhx0 (oneVarHeadCE u vbs H) (List.mem_map_of_mem hH)
          rw [ext_oneVarHeadCE] at hce
          exact hce (σ v) (hσv ▸ hux b_v (List.mem_eraseDups.2 hbv)) hvbs

theorem oneRuleAxs_fwd [hv : Nonempty DM.Val] (bi : BuiltIns DM) {J : Interp DM Dom}
    {O_named NN : List IRI} {u h0 : IRI} {ρ : DLRule} {L : List Axiom}
    (h : oneRuleAxs u h0 O_named.eraseDups ρ = some L)
    (hni : NamedIn O_named.eraseDups ρ)
    (hu : ∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y)
    (hρ : ρ.sat bi J O_named) :
    ∀ ax ∈ L, J.sat NN ax := by
  unfold oneRuleAxs at h
  cases ho : instOneVar u h0 ρ with
  | some ax0 =>
    rw [ho] at h; simp only [Option.some.injEq] at h; subst h
    intro ax hax
    rw [List.mem_singleton.1 hax]
    exact instOneVar_fwd bi ho hni hu hρ
  | none =>
    rw [ho] at h
    intro ax hax
    obtain ⟨g, hg, hia⟩ := mapM_some_bwd h ax hax
    unfold instAx at hia
    obtain ⟨bs, hbs, hia⟩ := Option.bind_eq_some_iff.1 hia
    obtain ⟨hs, hhs, rfl⟩ := Option.map_eq_some_iff.1 hia
    intro x hx
    rw [ext_andL] at hx ⊢
    let σ : IRI → Dom := fun v => J.ind (.named ((g.lookup v).getD v))
    let δ : IRI → DM.Val := fun _ => Classical.choice hv
    have hag : Agrees J g σ := fun v a hl => by simp [σ, hl]
    have hua : ∀ a0 ∈ ρ.body ++ ρ.head, ∀ t ∈ a0.iargs, ∀ b, gI g t = some b →
        J.prop (.named u) x (J.ind (.named b)) := by
      intro a0 ha0 t ht b hb
      refine (hu x _).2 ⟨b, List.mem_eraseDups.1 ?_, rfl⟩
      cases t with
      | var v =>
        have hvV : v ∈ ρ.ivars.eraseDups := List.mem_eraseDups.2
          (List.mem_flatMap.2 ⟨a0, ha0, mem_iargs_vars ht rfl⟩)
        obtain ⟨c, hc, hl⟩ := lookup_assigns hg v hvV
        simp only [gI] at hb
        rw [hl] at hb; cases hb; exact hc
      | ind i =>
        cases i with
        | named b' =>
          simp only [gI, Option.some.injEq] at hb; subst hb
          exact hni a0 ha0 _ ht b' rfl
        | anon _ => cases hb
    have hb : ∀ a ∈ ρ.body, a.sat bi J σ δ := by
      intro a ha
      obtain ⟨c, hc, hca⟩ := mapM_some_fwd hbs a ha
      exact (bodyCE_iff bi u δ hag (hua a (List.mem_append_left _ ha)) hca).1
        (hx c (List.mem_cons_of_mem _ hc))
    have hnm : ∀ v ∈ ρ.ivars, J.IsNamed O_named (σ v) := by
      intro v hv'
      obtain ⟨a, ha, hl⟩ := lookup_assigns hg v (List.mem_eraseDups.2 hv')
      exact ⟨a, List.mem_eraseDups.1 ha, by simp [σ, hl]⟩
    have hhd := hρ σ δ hnm hb
    intro c hc
    obtain ⟨a, ha, hca⟩ := mapM_some_bwd hhs c hc
    exact (headCE_iff bi u δ hag (hua a (List.mem_append_right _ ha)) hca).2 (hhd a ha)

theorem oneRuleAxs_bwd (bi : BuiltIns DM) {J : Interp DM Dom}
    {O_named NN : List IRI} {u h0 : IRI} {ρ : DLRule} {L : List Axiom}
    (h : oneRuleAxs u h0 O_named.eraseDups ρ = some L)
    (hni : NamedIn O_named.eraseDups ρ)
    (hux : ∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b)))
    (hJL : ∀ ax ∈ L, J.sat NN ax) :
    ρ.sat bi J O_named := by
  classical
  unfold oneRuleAxs at h
  cases ho : instOneVar u h0 ρ with
  | some ax0 =>
    rw [ho] at h; simp only [Option.some.injEq] at h; subst h
    exact instOneVar_bwd bi ho hni hux (hJL ax0 (List.mem_singleton_self _))
  | none =>
    rw [ho] at h
    intro σ δ hnm hbody a ha
    set N := O_named.eraseDups
    let f : IRI → IRI := fun v => if hv' : v ∈ ρ.ivars then (hnm v hv').choose else v
    have hf : ∀ v ∈ ρ.ivars, f v ∈ O_named ∧ σ v = J.ind (.named (f v)) := fun v hv' => by
      simp only [f, dif_pos hv']
      exact (hnm v hv').choose_spec
    obtain ⟨g, hg, hgl⟩ := mem_assigns f (N := N) (V := ρ.ivars.eraseDups) fun v hv' =>
      List.mem_eraseDups.2 (hf v (List.mem_eraseDups.1 hv')).1
    have hag : Agrees J g σ := fun v b hl => by
      have hvV := key_of_assigns hg v b hl
      rw [hgl v hvV] at hl
      cases hl
      exact (hf v (List.mem_eraseDups.1 hvV)).2
    obtain ⟨ax, hax, hia⟩ := mapM_some_fwd h g hg
    have hJax := hJL ax hax
    unfold instAx at hia
    obtain ⟨bs, hbs, hia⟩ := Option.bind_eq_some_iff.1 hia
    obtain ⟨hs, hhs, rfl⟩ := Option.map_eq_some_iff.1 hia
    let x0 := J.ind (.named h0)
    have hua : ∀ a0 ∈ ρ.body ++ ρ.head, ∀ t ∈ a0.iargs, ∀ b, gI g t = some b →
        J.prop (.named u) x0 (J.ind (.named b)) := by
      intro a0 ha0 t ht b hb
      refine hux b ?_
      cases t with
      | var v =>
        have hvV : v ∈ ρ.ivars.eraseDups := List.mem_eraseDups.2
          (List.mem_flatMap.2 ⟨a0, ha0, mem_iargs_vars ht rfl⟩)
        obtain ⟨c, hc, hl⟩ := lookup_assigns hg v hvV
        simp only [gI] at hb
        rw [hl] at hb; cases hb; exact hc
      | ind i =>
        cases i with
        | named b' =>
          simp only [gI, Option.some.injEq] at hb; subst hb
          exact hni a0 ha0 _ ht b' rfl
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

theorem ruleAxs_fwd [hv : Nonempty DM.Val] (bi : BuiltIns DM) {I : Interp DM Dom}
    {O_named NN : List IRI} {u h0 : IRI} {ρ : DLRule} {L : List Axiom}
    (h : ruleAxs u h0 O_named.eraseDups ρ = some L)
    (hnu : NoU u ρ) (hni : NamedIn O_named.eraseDups ρ) (hρ : ρ.sat bi I O_named) :
    ∀ ax ∈ L, (withRole I u fun _ y => I.IsNamed O_named y).sat NN ax := by
  unfold ruleAxs at h
  obtain ⟨Ls, hLs, rfl⟩ := Option.map_eq_some_iff.1 h
  let J := withRole I u fun _ y => I.IsNamed O_named y
  have hu : ∀ x y, J.prop (.named u) x y ↔ J.IsNamed O_named y := fun _ _ => by
    simp [J, withRole, Interp.prop, Interp.IsNamed]
  have hρJ : ρ.sat bi J O_named := (sat_rule_withRole bi I O_named _ hnu).2 hρ
  obtain ⟨-, hs_fwd, hs_ni⟩ := splitRule_spec bi J O_named u h0 ρ
  intro ax hax
  obtain ⟨L', hL', hax'⟩ := List.mem_flatten.1 hax
  obtain ⟨ρ', hρ', h1⟩ := mapM_some_bwd hLs L' hL'
  exact oneRuleAxs_fwd bi h1 (hs_ni hni ρ' hρ') hu (hs_fwd hu hρJ ρ' hρ') ax hax'

theorem ruleAxs_bwd (bi : BuiltIns DM) {J : Interp DM Dom}
    {O_named NN : List IRI} {u h0 : IRI} {ρ : DLRule} {L : List Axiom}
    (h : ruleAxs u h0 O_named.eraseDups ρ = some L)
    (hni : NamedIn O_named.eraseDups ρ)
    (hux : ∀ b ∈ O_named.eraseDups, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b)))
    (hJL : ∀ ax ∈ L, J.sat NN ax) :
    ρ.sat bi J O_named := by
  unfold ruleAxs at h
  obtain ⟨Ls, hLs, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hs_bwd, -, hs_ni⟩ := splitRule_spec bi J O_named u h0 ρ
  refine hs_bwd hux fun ρ' hρ' => ?_
  obtain ⟨L', hL', h1⟩ := mapM_some_fwd hLs ρ' hρ'
  exact oneRuleAxs_bwd bi h1 (hs_ni hni ρ' hρ') hux fun ax hax =>
    hJL ax (List.mem_flatten.2 ⟨L', hL', hax⟩)

/-- **A model of the encoding is a model of the ontology with its rules.** -/
theorem modelR_of_encRules (bi : BuiltIns DM) {O : OntologyR}
    {O' : Ontology} (h : encRules O = some O') {Dom : Type} (J : Interp DM Dom)
    (hJ : OWL.Model O' J) : ModelR bi O J := by
  unfold encRules at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨ras, hras, rfl⟩ := Option.map_eq_some_iff.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hk, -⟩ := hc
  have hk' : ∀ ax ∈ O.onto.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  set N := O.named.eraseDups
  set u := ruleU O
  set h0 := ruleH O
  have hux : ∀ b ∈ N, J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b)) := fun b hb =>
    hJ _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩)))
  refine ⟨fun ax hax => ?_, fun ρ hρ => ?_⟩
  · rw [sat_N_noKey J (hk' ax hax) _ (Ontology.namedIndividuals _)]
    exact hJ ax (List.mem_append_left _ (List.mem_append_left _ hax))
  · obtain ⟨L, hL, hrL⟩ := mapM_some_fwd hras ρ hρ
    have hni : NamedIn N ρ := fun a ha t ht b hb =>
      List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_flatMap.2
        ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, mem_iargs_named ht hb⟩⟩))
    exact ruleAxs_bwd bi hrL hni hux fun ax hax =>
      hJ ax (List.mem_append_right _ (List.mem_flatten.2 ⟨L, hL, hax⟩))

/-- **The grounding encoding is exact**, at every datatype map with a value
and for every reading of the built-ins. -/
theorem consistentAtR_encRules [hv : Nonempty DM.Val] (bi : BuiltIns DM) {O : OntologyR}
    {O' : Ontology} (h : encRules O = some O') : ConsistentAtR DM bi O ↔ ConsistentAt DM O' := by
  constructor
  · unfold encRules at h
    simp only at h
    split_ifs at h with hc
    obtain ⟨ras, hras, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hk, -⟩ := hc
    have hk' : ∀ ax ∈ O.onto.axioms, ax.noKey = true := by
      simpa [Ontology.noKey, List.all_eq_true] using hk
    set N := O.named.eraseDups
    set u := ruleU O
    set h0 := ruleH O
    have hfu : u ∉ O.roleNames := freshOf_not_mem _ _
    have hu_ax : ∀ ax ∈ O.onto.axioms, u ∉ ax.objectPropertyNames := fun ax hax hm =>
      hfu (List.mem_append_left _ (List.mem_flatMap.2 ⟨ax, hax, hm⟩))
    have hu_at : ∀ ρ ∈ O.rules, NoU u ρ := fun ρ hρ a ha hm =>
      hfu (List.mem_append_right _ (List.mem_flatMap.2 ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, hm⟩⟩))
    rintro ⟨Dom, hD, I, hI1, hI2⟩
    let J := withRole I u fun _ y => I.IsNamed O.named y
    refine ⟨Dom, hD, J, fun ax hax => ?_⟩
    rcases List.mem_append.1 hax with hax | hax
    · rcases List.mem_append.1 hax with hax | hax
      · rw [sat_withRole I _ _ (hu_ax ax hax), sat_N_noKey I (hk' ax hax) _ O.named]
        exact hI1 ax hax
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hax
        show J.prop (.named u) (J.ind (.named h0)) (J.ind (.named b))
        simp only [J, withRole, Interp.prop, ↓reduceIte]
        exact ⟨b, List.mem_eraseDups.1 hb, rfl⟩
    · obtain ⟨L, hL, hax⟩ := List.mem_flatten.1 hax
      obtain ⟨ρ, hρ, hrL⟩ := mapM_some_bwd hras L hL
      have hni : NamedIn N ρ := fun a ha t ht b hb =>
        List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_flatMap.2
          ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, mem_iargs_named ht hb⟩⟩))
      exact ruleAxs_fwd bi hrL (hu_at ρ hρ) hni (hI2 ρ hρ) ax hax
  · rintro ⟨Dom, hD, J, hJ⟩
    exact ⟨Dom, hD, J, modelR_of_encRules bi h J hJ⟩

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
