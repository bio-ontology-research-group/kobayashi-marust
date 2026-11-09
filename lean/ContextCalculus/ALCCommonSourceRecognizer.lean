import ContextCalculus.KMCommonRoutingSource
import ContextCalculus.CBALCEncoding
import ContextCalculus.ALCReferenceSaturation
import Mathlib.Data.List.Dedup

/-!
# Recognising the ALC fragment of the common clause source

The routed source of the automatic supervisor is a list of proper-term clauses
(`List FCL`, `KMCommonRoutingSource`).  The phase 2 ALC reference procedure of
v1.6.0 (`docs/V1.6.0-COMPLETENESS-PLAN.md`) needs that list as a finite-signature
`Ctx.Ontology (Fin conceptCount) (Fin roleCount)` together with a bijection
between source concept identifiers and `Fin conceptCount`.

`recognizeALC` inverts `CBALCEncoding.encode` clause by clause:
- `⟨body.map (C · x), head.map (C · x)⟩` becomes `Ctx.Clause.gci body head`;
- `⟨[C a x], [R r x (app f x)]⟩` paired with `⟨[C a x], [C b (app f x)]⟩`
  (sharing one function symbol `f` and one subject `a`, with each function
  symbol used by at most one pair) becomes `Ctx.Clause.exRight a r b`;
- `⟨[C d y, R r x y], [C c x]⟩` (in either body literal order) becomes
  `Ctx.Clause.exLeft r d c`;
- `⟨[C a x, R r x y], [C b y]⟩` (in either body literal order) becomes
  `Ctx.Clause.allRight a r b`.

Per-clause injective variable renamings of `x` and `y` (`vx ≠ vy`) and both
body literal orders are accepted.  Equalities, inequalities, constants, nested
function applications, unmatched Skolem halves, duplicate Skolem functions, and
role atoms outside the table are rejected (`none`).  Every requested name in
`named` is included in the recognised concept table even when it does not
occur in `source`.

The theorem `recognizeALC_entails_iff` proves that for every recognised source
and every pair of concept identifiers mapped to `i, j : Fin r.conceptCount`,
`KMCommonRoutingSource.Entails source sub sup` is equivalent to
`CBALCEncoding.EntailsSub r.ontology i j`.
-/

namespace ContextCalculus.ALCCommonSourceRecognizer

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.KMCommonRoutingSource

/-! ### Finite index lookup and injective extension of duplicate-free lists -/

/-- Look up the `Fin xs.length` index of `a` in `xs`. -/
def finIndexOf? : (xs : List Nat) → Nat → Option (Fin xs.length)
  | [], _ => none
  | x :: xs, a =>
      if x = a then some ⟨0, Nat.zero_lt_succ _⟩
      else (finIndexOf? xs a).map Fin.succ

theorem finIndexOf?_getElem {xs : List Nat} (hnodup : xs.Nodup)
    (i : Fin xs.length) : finIndexOf? xs xs[i] = some i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hx, hxs⟩
      refine Fin.cases ?_ ?_ i
      · simp [finIndexOf?]
      · intro k
        have hmem : xs[k.val] ∈ xs := List.getElem_mem k.isLt
        have hne : x ≠ xs[k.val] := fun heq => hx (heq ▸ hmem)
        have hih : finIndexOf? xs xs[k.val] = some k := ih hxs k
        simp [finIndexOf?, hne, hih]

theorem getElem_of_finIndexOf?_eq_some {xs : List Nat} {a : Nat}
    {i : Fin xs.length} (h : finIndexOf? xs a = some i) : xs[i] = a := by
  induction xs with
  | nil => simp [finIndexOf?] at h
  | cons x xs ih =>
      simp only [finIndexOf?] at h
      split at h
      · next heq =>
          simp only [Option.some.injEq] at h
          subst h
          simpa using heq
      · next hne =>
          rcases Option.map_eq_some_iff.mp h with ⟨k, hk, rfl⟩
          simpa using ih hk

theorem finIndexOf?_eq_some_iff {xs : List Nat} (hnodup : xs.Nodup)
    {a : Nat} {i : Fin xs.length} :
    finIndexOf? xs a = some i ↔ xs[i] = a := by
  constructor
  · exact getElem_of_finIndexOf?_eq_some
  · rintro rfl
    exact finIndexOf?_getElem hnodup i

theorem finIndexOf?_isSome_of_mem {xs : List Nat} {a : Nat} (h : a ∈ xs) :
    (finIndexOf? xs a).isSome = true := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
      simp only [finIndexOf?]
      by_cases heq : x = a
      · simp [heq]
      · rcases List.mem_cons.mp h with rfl | hmem
        · exact (heq rfl).elim
        · simp [heq, ih hmem]

/-- Maximum element of a list of natural numbers (`0` on `[]`). -/
def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)

theorem le_listMax_of_mem {xs : List Nat} {a : Nat} (h : a ∈ xs) :
    a ≤ listMax xs := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- Extend a duplicate-free list `xs` to a globally injective map `Nat → Nat`. -/
def extendInj (xs : List Nat) (k : Nat) : Nat :=
  if h : k < xs.length then xs[k]
  else listMax xs + 1 + k

@[simp] theorem extendInj_fin (xs : List Nat) (i : Fin xs.length) :
    extendInj xs i.val = xs[i] := by
  simp [extendInj, i.isLt]

theorem extendInj_injective {xs : List Nat} (hnodup : xs.Nodup) :
    Function.Injective (extendInj xs) := by
  intro j k heq
  unfold extendInj at heq
  by_cases hj : j < xs.length <;> by_cases hk : k < xs.length
  · simp only [hj, hk, dite_true] at heq
    exact (List.Nodup.getElem_inj_iff hnodup).mp heq
  · simp only [hj, hk, dite_true, dite_false] at heq
    have hle : xs[j] ≤ listMax xs := le_listMax_of_mem (List.getElem_mem hj)
    omega
  · simp only [hj, hk, dite_true, dite_false] at heq
    have hle : xs[k] ≤ listMax xs := le_listMax_of_mem (List.getElem_mem hk)
    omega
  · simp only [hj, hk, dite_false] at heq
    omega

/-! ### Injective signature renaming of `FCL` ontologies and model transport -/

def mapTerm (fnMap : Nat → Nat) : FTerm → FTerm
  | .var id => .var id
  | .const individual => .const individual
  | .app function argument => .app (fnMap function) (mapTerm fnMap argument)

def mapPred (cMap rMap fnMap : Nat → Nat) : FPred → FPred
  | .concept concept term => .concept (cMap concept) (mapTerm fnMap term)
  | .role role source target =>
      .role (rMap role) (mapTerm fnMap source) (mapTerm fnMap target)

def mapLit (cMap rMap fnMap : Nat → Nat) : FLit → FLit
  | .P predicate => .P (mapPred cMap rMap fnMap predicate)
  | .eq left right => .eq (mapTerm fnMap left) (mapTerm fnMap right)
  | .ineq left right => .ineq (mapTerm fnMap left) (mapTerm fnMap right)

def mapClause (cMap rMap fnMap : Nat → Nat) (clause : FCL) : FCL where
  body := clause.body.map (mapLit cMap rMap fnMap)
  head := clause.head.map (mapLit cMap rMap fnMap)

def mapOntology (cMap rMap fnMap : Nat → Nat) (ontology : List FCL) : List FCL :=
  ontology.map (mapClause cMap rMap fnMap)

/-- Pull back a `TModel` along `(cMap, rMap, fnMap)`. -/
def pullbackSigModel (cMap rMap fnMap : Nat → Nat) (model : TModel D) : TModel D where
  conc c := model.conc (cMap c)
  rol r := model.rol (rMap r)
  const := model.const
  fn f := model.fn (fnMap f)

@[simp] theorem evalTerm_pullbackSig (cMap rMap fnMap : Nat → Nat)
    (model : TModel D) (ρ : Int → D) (term : FTerm) :
    (pullbackSigModel cMap rMap fnMap model).evalT ρ term =
      model.evalT ρ (mapTerm fnMap term) := by
  induction term with
  | var id => rfl
  | const individual => rfl
  | app function argument ih =>
      change model.fn (fnMap function)
          ((pullbackSigModel cMap rMap fnMap model).evalT ρ argument) =
        model.fn (fnMap function) (model.evalT ρ (mapTerm fnMap argument))
      rw [ih]

@[simp] theorem evalLit_pullbackSig (cMap rMap fnMap : Nat → Nat)
    (model : TModel D) (ρ : Int → D) (lit : FLit) :
    (pullbackSigModel cMap rMap fnMap model).evalL ρ lit ↔
      model.evalL ρ (mapLit cMap rMap fnMap lit) := by
  cases lit with
  | P p =>
      cases p with
      | concept c t =>
          change model.conc (cMap c)
              ((pullbackSigModel cMap rMap fnMap model).evalT ρ t) ↔
            model.conc (cMap c) (model.evalT ρ (mapTerm fnMap t))
          rw [evalTerm_pullbackSig]
      | role r s t =>
          change model.rol (rMap r)
              ((pullbackSigModel cMap rMap fnMap model).evalT ρ s)
              ((pullbackSigModel cMap rMap fnMap model).evalT ρ t) ↔
            model.rol (rMap r)
              (model.evalT ρ (mapTerm fnMap s))
              (model.evalT ρ (mapTerm fnMap t))
          rw [evalTerm_pullbackSig, evalTerm_pullbackSig]
  | eq s t =>
      change (pullbackSigModel cMap rMap fnMap model).evalT ρ s =
          (pullbackSigModel cMap rMap fnMap model).evalT ρ t ↔
        model.evalT ρ (mapTerm fnMap s) = model.evalT ρ (mapTerm fnMap t)
      rw [evalTerm_pullbackSig, evalTerm_pullbackSig]
  | ineq s t =>
      change (pullbackSigModel cMap rMap fnMap model).evalT ρ s ≠
          (pullbackSigModel cMap rMap fnMap model).evalT ρ t ↔
        model.evalT ρ (mapTerm fnMap s) ≠ model.evalT ρ (mapTerm fnMap t)
      rw [evalTerm_pullbackSig, evalTerm_pullbackSig]

theorem valid_pullbackSig_iff (cMap rMap fnMap : Nat → Nat)
    (model : TModel D) (clause : FCL) :
    valid (pullbackSigModel cMap rMap fnMap model) clause ↔
      valid model (mapClause cMap rMap fnMap clause) := by
  constructor
  · intro hvalid ρ hbody
    have hsrc : ∀ lit ∈ clause.body,
        (pullbackSigModel cMap rMap fnMap model).evalL ρ lit := by
      intro lit hlit
      exact (evalLit_pullbackSig cMap rMap fnMap model ρ lit).2
        (hbody (mapLit cMap rMap fnMap lit) (List.mem_map.mpr ⟨lit, hlit, rfl⟩))
    rcases hvalid ρ hsrc with ⟨lit, hlit, htrue⟩
    exact ⟨mapLit cMap rMap fnMap lit, List.mem_map.mpr ⟨lit, hlit, rfl⟩,
      (evalLit_pullbackSig cMap rMap fnMap model ρ lit).1 htrue⟩
  · intro hvalid ρ hbody
    have h2 : ∀ lit ∈ (mapClause cMap rMap fnMap clause).body,
        model.evalL ρ lit := by
      intro lit hlit
      rcases List.mem_map.mp hlit with ⟨src, hsrc, rfl⟩
      exact (evalLit_pullbackSig cMap rMap fnMap model ρ src).1 (hbody src hsrc)
    rcases hvalid ρ h2 with ⟨lit, hlit, htrue⟩
    rcases List.mem_map.mp hlit with ⟨src, hsrc, rfl⟩
    exact ⟨src, hsrc, (evalLit_pullbackSig cMap rMap fnMap model ρ src).2 htrue⟩

/-- Push forward a `TModel` along injective maps `(cMap, rMap, fnMap)`. -/
noncomputable def pushforwardSigModel (cMap rMap fnMap : Nat → Nat)
    (model : TModel D) : TModel D := by
  classical
  exact {
    conc := fun c x =>
      if h : ∃ c0, cMap c0 = c then model.conc (Classical.choose h) x else False
    rol := fun r x y =>
      if h : ∃ r0, rMap r0 = r then model.rol (Classical.choose h) x y else False
    const := model.const
    fn := fun f =>
      if h : ∃ f0, fnMap f0 = f then model.fn (Classical.choose h) else model.fn 0
  }

@[simp] theorem pushforwardSig_conc (cMap rMap fnMap : Nat → Nat)
    (hc : Function.Injective cMap) (model : TModel D) (c : Nat) (x : D) :
    (pushforwardSigModel cMap rMap fnMap model).conc (cMap c) x ↔ model.conc c x := by
  simp only [pushforwardSigModel]
  have hex : ∃ c0, cMap c0 = cMap c := ⟨c, rfl⟩
  rw [dif_pos hex]
  have heq : Classical.choose hex = c := hc (Classical.choose_spec hex)
  rw [heq]

@[simp] theorem pushforwardSig_rol (cMap rMap fnMap : Nat → Nat)
    (hr : Function.Injective rMap) (model : TModel D) (r : Nat) (x y : D) :
    (pushforwardSigModel cMap rMap fnMap model).rol (rMap r) x y ↔ model.rol r x y := by
  simp only [pushforwardSigModel]
  have hex : ∃ r0, rMap r0 = rMap r := ⟨r, rfl⟩
  rw [dif_pos hex]
  have heq : Classical.choose hex = r := hr (Classical.choose_spec hex)
  rw [heq]

@[simp] theorem pushforwardSig_fn (cMap rMap fnMap : Nat → Nat)
    (hfn : Function.Injective fnMap) (model : TModel D) (f : Nat) :
    (pushforwardSigModel cMap rMap fnMap model).fn (fnMap f) = model.fn f := by
  simp only [pushforwardSigModel]
  have hex : ∃ f0, fnMap f0 = fnMap f := ⟨f, rfl⟩
  rw [dif_pos hex]
  congr 1
  exact hfn (Classical.choose_spec hex)

@[simp] theorem evalTerm_pushforwardSig (cMap rMap fnMap : Nat → Nat)
    (hfn : Function.Injective fnMap) (model : TModel D) (ρ : Int → D) (term : FTerm) :
    (pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap term) =
      model.evalT ρ term := by
  induction term with
  | var id => rfl
  | const individual => rfl
  | app function argument ih =>
      simp [mapTerm, TModel.evalT, pushforwardSig_fn cMap rMap fnMap hfn, ih]

@[simp] theorem evalLit_pushforwardSig (cMap rMap fnMap : Nat → Nat)
    (hc : Function.Injective cMap) (hr : Function.Injective rMap)
    (hfn : Function.Injective fnMap) (model : TModel D) (ρ : Int → D) (lit : FLit) :
    (pushforwardSigModel cMap rMap fnMap model).evalL ρ (mapLit cMap rMap fnMap lit) ↔
      model.evalL ρ lit := by
  cases lit with
  | P p =>
      cases p with
      | concept c t =>
          change (pushforwardSigModel cMap rMap fnMap model).conc (cMap c)
              ((pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap t)) ↔
            model.conc c (model.evalT ρ t)
          rw [evalTerm_pushforwardSig cMap rMap fnMap hfn,
            pushforwardSig_conc cMap rMap fnMap hc]
      | role r s t =>
          change (pushforwardSigModel cMap rMap fnMap model).rol (rMap r)
              ((pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap s))
              ((pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap t)) ↔
            model.rol r (model.evalT ρ s) (model.evalT ρ t)
          rw [evalTerm_pushforwardSig cMap rMap fnMap hfn,
            evalTerm_pushforwardSig cMap rMap fnMap hfn,
            pushforwardSig_rol cMap rMap fnMap hr]
  | eq s t =>
      change (pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap s) =
          (pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap t) ↔
        model.evalT ρ s = model.evalT ρ t
      rw [evalTerm_pushforwardSig cMap rMap fnMap hfn,
        evalTerm_pushforwardSig cMap rMap fnMap hfn]
  | ineq s t =>
      change (pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap s) ≠
          (pushforwardSigModel cMap rMap fnMap model).evalT ρ (mapTerm fnMap t) ↔
        model.evalT ρ s ≠ model.evalT ρ t
      rw [evalTerm_pushforwardSig cMap rMap fnMap hfn,
        evalTerm_pushforwardSig cMap rMap fnMap hfn]

theorem valid_pushforwardSig_iff (cMap rMap fnMap : Nat → Nat)
    (hc : Function.Injective cMap) (hr : Function.Injective rMap)
    (hfn : Function.Injective fnMap) (model : TModel D) (clause : FCL) :
    valid (pushforwardSigModel cMap rMap fnMap model)
        (mapClause cMap rMap fnMap clause) ↔
      valid model clause := by
  constructor
  · intro hvalid ρ hbody
    have h2 : ∀ lit ∈ (mapClause cMap rMap fnMap clause).body,
        (pushforwardSigModel cMap rMap fnMap model).evalL ρ lit := by
      intro lit hlit
      rcases List.mem_map.mp hlit with ⟨src, hsrc, rfl⟩
      exact (evalLit_pushforwardSig cMap rMap fnMap hc hr hfn model ρ src).2
        (hbody src hsrc)
    rcases hvalid ρ h2 with ⟨lit, hlit, htrue⟩
    rcases List.mem_map.mp hlit with ⟨src, hsrc, rfl⟩
    exact ⟨src, hsrc,
      (evalLit_pushforwardSig cMap rMap fnMap hc hr hfn model ρ src).1 htrue⟩
  · intro hvalid ρ hbody
    have hsrc : ∀ lit ∈ clause.body, model.evalL ρ lit := by
      intro lit hlit
      exact (evalLit_pushforwardSig cMap rMap fnMap hc hr hfn model ρ lit).1
        (hbody (mapLit cMap rMap fnMap lit) (List.mem_map.mpr ⟨lit, hlit, rfl⟩))
    rcases hvalid ρ hsrc with ⟨lit, hlit, htrue⟩
    exact ⟨mapLit cMap rMap fnMap lit, List.mem_map.mpr ⟨lit, hlit, rfl⟩,
      (evalLit_pushforwardSig cMap rMap fnMap hc hr hfn model ρ lit).2 htrue⟩

theorem entails_mapOntology_iff {cMap rMap fnMap : Nat → Nat}
    (hc : Function.Injective cMap) (hr : Function.Injective rMap)
    (hfn : Function.Injective fnMap) (O : List FCL) (sub sup : Nat) :
    Entails (mapOntology cMap rMap fnMap O) (cMap sub) (cMap sup) ↔
      Entails O sub sup := by
  constructor
  · intro hmapped D model hmodels element hsub
    let pushed := pushforwardSigModel cMap rMap fnMap model
    have hsub' : pushed.conc (cMap sub) element :=
      (pushforwardSig_conc cMap rMap fnMap hc model sub element).2 hsub
    have hsup' : pushed.conc (cMap sup) element :=
      hmapped D pushed (by
        intro clause hclause
        rcases List.mem_map.mp hclause with ⟨src, hsrc, rfl⟩
        exact (valid_pushforwardSig_iff cMap rMap fnMap hc hr hfn model src).2
          (hmodels src hsrc)) element hsub'
    exact (pushforwardSig_conc cMap rMap fnMap hc model sup element).1 hsup'
  · intro hsrc D model hmodels element hsub
    let pulled := pullbackSigModel cMap rMap fnMap model
    exact hsrc D pulled (by
      intro clause hclause
      exact (valid_pullbackSig_iff cMap rMap fnMap model clause).2
        (hmodels (mapClause cMap rMap fnMap clause)
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))) element hsub

/-! ### Clause equivalence up to literal order and per-clause variable renaming -/

/-- Literal-set equality of two clauses. -/
def ClauseEquivalent (left right : FCL) : Prop :=
  left.body.toFinset = right.body.toFinset ∧
    left.head.toFinset = right.head.toFinset

instance (left right : FCL) : Decidable (ClauseEquivalent left right) := by
  unfold ClauseEquivalent
  infer_instance

theorem ClauseEquivalent.mem_body_iff {left right : FCL}
    (heq : ClauseEquivalent left right) (lit : FLit) :
    lit ∈ left.body ↔ lit ∈ right.body := by
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp heq.1 lit

theorem ClauseEquivalent.mem_head_iff {left right : FCL}
    (heq : ClauseEquivalent left right) (lit : FLit) :
    lit ∈ left.head ↔ lit ∈ right.head := by
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp heq.2 lit

theorem ClauseEquivalent.valid_iff (model : TModel D)
    {left right : FCL} (heq : ClauseEquivalent left right) :
    valid model left ↔ valid model right := by
  constructor <;> intro hvalid ρ hbody
  · rcases hvalid ρ (fun lit hlit =>
      hbody lit ((heq.mem_body_iff lit).mp hlit)) with ⟨lit, hlit, htrue⟩
    exact ⟨lit, (heq.mem_head_iff lit).mp hlit, htrue⟩
  · rcases hvalid ρ (fun lit hlit =>
      hbody lit ((heq.mem_body_iff lit).mpr hlit)) with ⟨lit, hlit, htrue⟩
    exact ⟨lit, (heq.mem_head_iff lit).mpr hlit, htrue⟩

/-- Find the `(vx, vy)` variable pair of a body role literal `R(r, var vx, var vy)`. -/
def findRoleVars : List FLit → Option (Int × Int)
  | [] => none
  | .P (.role _ (.var vx) (.var vy)) :: _ => some (vx, vy)
  | _ :: rest => findRoleVars rest

def termVars : FTerm → List Int
  | .var id => [id]
  | .const _ => []
  | .app _ arg => termVars arg

def literalVars : FLit → List Int
  | .P (.concept _ t) => termVars t
  | .P (.role _ s t) => termVars s ++ termVars t
  | .eq s t => termVars s ++ termVars t
  | .ineq s t => termVars s ++ termVars t

/-- First variable occurring in `cl` (or `0` when `cl` has no variables). -/
def firstClauseVar (cl : FCL) : Int :=
  match (cl.body ++ cl.head).flatMap literalVars with
  | vx :: _ => vx
  | [] => 0

/-- Candidate variable substitution from `cl` to canonical variables `(0, -1)`. -/
def alcSubstToCanonical (cl : FCL) : List (Int × FTerm) :=
  match findRoleVars cl.body with
  | some (vx, vy) => [(vx, .var 0), (vy, .var (-1))]
  | none => [(firstClauseVar cl, .var 0)]

/-- Candidate variable substitution from canonical variables `(0, -1)` back to `cl`. -/
def alcSubstFromCanonical (cl : FCL) : List (Int × FTerm) :=
  match findRoleVars cl.body with
  | some (vx, vy) => [(0, .var vx), (-1, .var vy)]
  | none => [(0, .var (firstClauseVar cl))]

/-- `left` and `right` are mutual substitution instances up to literal-set equality. -/
def ALCClauseVariant (left right : FCL) : Prop :=
  ClauseEquivalent (substCl (alcSubstToCanonical left) left) right ∧
    ClauseEquivalent (substCl (alcSubstFromCanonical left) right) left

instance (left right : FCL) : Decidable (ALCClauseVariant left right) := by
  unfold ALCClauseVariant
  infer_instance

theorem ALCClauseVariant.valid_iff (model : TModel D)
    {left right : FCL} (hvariant : ALCClauseVariant left right) :
    valid model left ↔ valid model right := by
  constructor
  · intro hleft
    exact (hvariant.1.valid_iff model).1
      (inst_valid model hleft (alcSubstToCanonical left))
  · intro hright
    exact (hvariant.2.valid_iff model).1
      (inst_valid model hright (alcSubstFromCanonical left))

/-- Every clause in `left` is an `ALCClauseVariant` of a clause in `right` and
vice versa. -/
def ALCOntologyVariant (left right : List FCL) : Prop :=
  (∀ clause ∈ left, ∃ encoded ∈ right, ALCClauseVariant clause encoded) ∧
    ∀ encoded ∈ right, ∃ clause ∈ left, ALCClauseVariant clause encoded

instance (left right : List FCL) : Decidable (ALCOntologyVariant left right) := by
  unfold ALCOntologyVariant
  infer_instance

theorem entails_of_alcOntologyVariant {left right : List FCL}
    (hvariant : ALCOntologyVariant left right) (sub sup : Nat) :
    Entails left sub sup ↔ Entails right sub sup := by
  constructor <;> intro hentails D model hmodels element hsub
  · exact hentails D model (fun clause hclause =>
      let ⟨enc, henc, hcv⟩ := hvariant.1 clause hclause
      (hcv.valid_iff model).2 (hmodels enc henc)) element hsub
  · exact hentails D model (fun enc henc =>
      let ⟨clause, hclause, hcv⟩ := hvariant.2 enc henc
      (hcv.valid_iff model).1 (hmodels clause hclause)) element hsub

/-! ### Recognised ALC structure and clause-by-clause parser -/

/-- Concept identifiers occurring in one literal. -/
def literalConcepts : FLit → List Nat
  | .P (.concept iri _) => [iri]
  | _ => []

/-- Role identifiers occurring in one literal. -/
def literalRoles : FLit → List Nat
  | .P (.role iri _ _) => [iri]
  | _ => []

/-- Concept identifiers occurring in the source. -/
def sourceConcepts (source : List FCL) : List Nat :=
  source.flatMap fun clause =>
    clause.body.flatMap literalConcepts ++ clause.head.flatMap literalConcepts

/-- Role identifiers occurring in the source. -/
def sourceRoles (source : List FCL) : List Nat :=
  source.flatMap fun clause =>
    clause.body.flatMap literalRoles ++ clause.head.flatMap literalRoles

/-- The recognised ALC ontology together with its finite concept, role, and
Skolem-function tables and the verified variant witness tying `source` to
`CBALCEncoding.encode ontology`. -/
structure RecognizedALC (named : List Nat := []) (source : List FCL := []) where
  conceptCount : Nat
  roleCount : Nat
  ontology : Ctx.Ontology (Fin conceptCount) (Fin roleCount)
  conceptNames : List Nat
  roleNames : List Nat
  fnNames : List Nat
  conceptNames_length : conceptNames.length = conceptCount
  roleNames_length : roleNames.length = roleCount
  conceptNames_nodup : conceptNames.Nodup
  roleNames_nodup : roleNames.Nodup
  fnNames_nodup : fnNames.Nodup
  named_subset : ∀ a ∈ named, a ∈ conceptNames
  variant : ALCOntologyVariant source
    (mapOntology (extendInj conceptNames) (extendInj roleNames) (extendInj fnNames)
      (CBALCEncoding.encode ontology))
deriving DecidableEq

instance {named : List Nat} {source : List FCL} :
    Repr (RecognizedALC named source) where
  reprPrec r _ :=
    s!"RecognizedALC(conceptCount := {r.conceptCount}, roleCount := {r.roleCount}, " ++
    s!"conceptNames := {repr r.conceptNames}, roleNames := {repr r.roleNames}, " ++
    s!"ontology := {repr r.ontology})"

/-- Map a source concept identifier `a : Nat` to its `Fin r.conceptCount` index. -/
def RecognizedALC.conceptIndex {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) (a : Nat) : Option (Fin r.conceptCount) :=
  (finIndexOf? r.conceptNames a).map (Fin.cast r.conceptNames_length)

/-- Map a `Fin r.conceptCount` index back to its source concept identifier. -/
def RecognizedALC.conceptName {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) (i : Fin r.conceptCount) : Nat :=
  r.conceptNames[Fin.cast r.conceptNames_length.symm i]

/-- Map a source role identifier `rr : Nat` to its `Fin r.roleCount` index. -/
def RecognizedALC.roleIndex {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) (rr : Nat) : Option (Fin r.roleCount) :=
  (finIndexOf? r.roleNames rr).map (Fin.cast r.roleNames_length)

/-- Map a `Fin r.roleCount` index back to its source role identifier. -/
def RecognizedALC.roleName {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) (i : Fin r.roleCount) : Nat :=
  r.roleNames[Fin.cast r.roleNames_length.symm i]

/-- Round-trip: `conceptIndex` inverts `conceptName`. -/
@[simp] theorem RecognizedALC.conceptIndex_conceptName
    {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) (i : Fin r.conceptCount) :
    r.conceptIndex (r.conceptName i) = some i := by
  unfold RecognizedALC.conceptIndex RecognizedALC.conceptName
  rw [finIndexOf?_getElem r.conceptNames_nodup]
  simp

/-- Round-trip: `conceptName` inverts `conceptIndex`. -/
theorem RecognizedALC.conceptName_conceptIndex
    {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) {a : Nat} {i : Fin r.conceptCount}
    (h : r.conceptIndex a = some i) :
    r.conceptName i = a := by
  unfold RecognizedALC.conceptIndex RecognizedALC.conceptName at *
  rcases Option.map_eq_some_iff.mp h with ⟨k, hk, rfl⟩
  simpa using getElem_of_finIndexOf?_eq_some hk

theorem RecognizedALC.conceptIndex_eq_some_iff
    {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) {a : Nat} {i : Fin r.conceptCount} :
    r.conceptIndex a = some i ↔ r.conceptName i = a := by
  constructor
  · exact r.conceptName_conceptIndex
  · rintro rfl
    exact r.conceptIndex_conceptName i

theorem RecognizedALC.extendInj_conceptNames_eq
    {named : List Nat} {source : List FCL}
    (r : RecognizedALC named source) (i : Fin r.conceptCount) :
    extendInj r.conceptNames i.val = r.conceptName i := by
  let k : Fin r.conceptNames.length := Fin.cast r.conceptNames_length.symm i
  have hk : k.val = i.val := rfl
  rw [← hk, extendInj_fin r.conceptNames k]
  rfl

/-- Raw parsed items from individual source clauses before `exRight` pairing. -/
inductive RawClauseItem where
  | gci (body head : List Nat)
  | exLeft (r d c : Nat)
  | allRight (a r b : Nat)
  | exRightRole (f a r : Nat)
  | exRightFiller (f a b : Nat)
deriving DecidableEq, Repr

/-- Extract concept identifiers from a list of `.P (.concept c (.var vx))`
literals sharing variable `vx`. -/
def extractVarConcepts (vx : Int) : List FLit → Option (List Nat)
  | [] => some []
  | .P (.concept c (.var v)) :: rest =>
      if v = vx then
        (extractVarConcepts vx rest).map (c :: ·)
      else none
  | _ => none

def firstConceptVar : List FLit → Option Int
  | [] => none
  | .P (.concept _ (.var v)) :: _ => some v
  | _ :: rest => firstConceptVar rest

/-- Classify a single `FCL` clause into one of the ALC shapes, failing closed
(`none`) on anything outside the table. -/
def classifyClause (cl : FCL) : Option RawClauseItem :=
  match cl.body, cl.head with
  | [.P (.concept a (.var vx))], [.P (.role r (.var vx1) (.app f (.var vx2)))] =>
      if vx = vx1 && vx = vx2 then some (.exRightRole f a r) else none
  | [.P (.concept a (.var vx))], [.P (.concept b (.app f (.var vx1)))] =>
      if vx = vx1 then some (.exRightFiller f a b) else none
  | [.P (.concept c1 (.var v1)), .P (.role r (.var vr1) (.var vr2))],
    [.P (.concept c2 (.var v2))] =>
      if v1 = vr2 && vr1 = v2 && vr1 ≠ vr2 then
        some (.exLeft r c1 c2)
      else if v1 = vr1 && vr2 = v2 && vr1 ≠ vr2 then
        some (.allRight c1 r c2)
      else
        none
  | [.P (.role r (.var vr1) (.var vr2)), .P (.concept c1 (.var v1))],
    [.P (.concept c2 (.var v2))] =>
      if v1 = vr2 && vr1 = v2 && vr1 ≠ vr2 then
        some (.exLeft r c1 c2)
      else if v1 = vr1 && vr2 = v2 && vr1 ≠ vr2 then
        some (.allRight c1 r c2)
      else
        none
  | body, head =>
      let vx := (firstConceptVar (body ++ head)).getD 0
      match extractVarConcepts vx body, extractVarConcepts vx head with
      | some bIds, some hIds => some (.gci bIds hIds)
      | _, _ => none

/-- Pair `exRightRole` items with their unique matching `exRightFiller` item
and translate concept/role identifiers into `Fin` indices. -/
def buildIndexedClauses (cNames rNames : List Nat)
    (fillerHalves : List (Nat × Nat × Nat)) :
    List RawClauseItem →
      Option (List (Option Nat × Ctx.Clause (Fin cNames.length) (Fin rNames.length)))
  | [] => some []
  | item :: rest => do
      let tail ← buildIndexedClauses cNames rNames fillerHalves rest
      match item with
      | .gci body head =>
          let bFin ← body.mapM (finIndexOf? cNames)
          let hFin ← head.mapM (finIndexOf? cNames)
          some ((none, .gci bFin hFin) :: tail)
      | .exLeft r d c =>
          let rFin ← finIndexOf? rNames r
          let dFin ← finIndexOf? cNames d
          let cFin ← finIndexOf? cNames c
          some ((none, .exLeft rFin dFin cFin) :: tail)
      | .allRight a r b =>
          let aFin ← finIndexOf? cNames a
          let rFin ← finIndexOf? rNames r
          let bFin ← finIndexOf? cNames b
          some ((none, .allRight aFin rFin bFin) :: tail)
      | .exRightRole f a r =>
          match fillerHalves.find? (fun entry => entry.1 == f) with
          | none => none
          | some (_, a', b) =>
              if a = a' then
                let aFin ← finIndexOf? cNames a
                let rFin ← finIndexOf? rNames r
                let bFin ← finIndexOf? cNames b
                some ((some f, .exRight aFin rFin bFin) :: tail)
              else none
      | .exRightFiller _ _ _ =>
          some tail

/-- Assign a unique function symbol to every clause index: `exRight` clauses
keep their source Skolem function symbol `f`, and non-`exRight` clauses receive
fresh distinct numbers above `maxFn`. -/
def assignFnNames (maxFn : Nat) : List (Option Nat) → Nat → List Nat
  | [], _ => []
  | some f :: rest, idx => f :: assignFnNames maxFn rest (idx + 1)
  | none :: rest, idx => (maxFn + 1 + idx) :: assignFnNames maxFn rest (idx + 1)

/-- Recognise a common clause source `source : List FCL` as a finite-signature
ALC ontology covering `named`.  Fails closed (`none`) on any non-ALC construct. -/
def recognizeALC (named : List Nat) (source : List FCL) :
    Option (RecognizedALC named source) := do
  let items ← source.mapM classifyClause
  let roleHalves := items.filterMap fun
    | .exRightRole f a r => some (f, a, r)
    | _ => none
  let fillerHalves := items.filterMap fun
    | .exRightFiller f a b => some (f, a, b)
    | _ => none
  let roleFns := roleHalves.map Prod.fst
  let fillerFns := fillerHalves.map Prod.fst
  if !(decide roleFns.Nodup && decide fillerFns.Nodup &&
      decide (roleHalves.length = fillerHalves.length)) then
    none
  else
    let cNames := (named ++ sourceConcepts source).dedup
    let rNames := (sourceRoles source).dedup
    let indexed ← buildIndexedClauses cNames rNames fillerHalves items
    let ontology := indexed.map Prod.snd
    let fnOpts := indexed.map Prod.fst
    let fnNames := assignFnNames (listMax (roleFns ++ fillerFns)) fnOpts 0
    if h : cNames.Nodup ∧ rNames.Nodup ∧ fnNames.Nodup ∧
        (∀ a ∈ named, a ∈ cNames) ∧
        ALCOntologyVariant source
          (mapOntology (extendInj cNames) (extendInj rNames) (extendInj fnNames)
            (CBALCEncoding.encode ontology)) then
      some {
        conceptCount := cNames.length
        roleCount := rNames.length
        ontology := ontology
        conceptNames := cNames
        roleNames := rNames
        fnNames := fnNames
        conceptNames_length := rfl
        roleNames_length := rfl
        conceptNames_nodup := h.1
        roleNames_nodup := h.2.1
        fnNames_nodup := h.2.2.1
        named_subset := h.2.2.2.1
        variant := h.2.2.2.2
      }
    else
      none

/-- Every requested name in `named` receives a valid `Fin r.conceptCount` index
when `recognizeALC named source = some r`. -/
theorem recognizeALC_conceptIndex_of_named (named : List Nat) (source : List FCL)
    (r : RecognizedALC named source)
    (_hrecognized : recognizeALC named source = some r)
    {a : Nat} (ha : a ∈ named) :
    ∃ i : Fin r.conceptCount, r.conceptIndex a = some i := by
  have hmem : a ∈ r.conceptNames := r.named_subset a ha
  have hisSome : (finIndexOf? r.conceptNames a).isSome = true :=
    finIndexOf?_isSome_of_mem hmem
  rcases Option.isSome_iff_exists.mp hisSome with ⟨k, hk⟩
  refine ⟨Fin.cast r.conceptNames_length k, ?_⟩
  simp [RecognizedALC.conceptIndex, hk]

/-- Semantic equivalence of `recognizeALC`: for any concept identifiers `sub`
and `sup` with recognised indices `i` and `j`, first-order entailment over
`source` is equivalent to `CBALCEncoding.EntailsSub r.ontology i j`. -/
theorem recognizeALC_entails_iff (named : List Nat) (source : List FCL)
    (r : RecognizedALC named source)
    (_hrecognized : recognizeALC named source = some r)
    {sub sup : Nat} {i j : Fin r.conceptCount}
    (hi : r.conceptIndex sub = some i) (hj : r.conceptIndex sup = some j) :
    Entails source sub sup ↔ CBALCEncoding.EntailsSub r.ontology i j := by
  have hsub : sub = extendInj r.conceptNames i.val := by
    rw [r.extendInj_conceptNames_eq i, r.conceptName_conceptIndex hi]
  have hsup : sup = extendInj r.conceptNames j.val := by
    rw [r.extendInj_conceptNames_eq j, r.conceptName_conceptIndex hj]
  rw [entails_of_alcOntologyVariant r.variant sub sup, hsub, hsup]
  exact entails_mapOntology_iff
    (extendInj_injective r.conceptNames_nodup)
    (extendInj_injective r.roleNames_nodup)
    (extendInj_injective r.fnNames_nodup)
    (CBALCEncoding.encode r.ontology) i.val j.val

#print axioms recognizeALC_conceptIndex_of_named
#print axioms recognizeALC_entails_iff

end ContextCalculus.ALCCommonSourceRecognizer
