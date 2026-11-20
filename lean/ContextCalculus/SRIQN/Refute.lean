import ContextCalculus.SRIQN.Data

/-!
# Checked refutations of data ontologies with nominals (v1.7.0, task inc1)

`docs/V1.7.0-INCONSISTENCY-CERT.md`. A refutation names finitely many
elements of a would-be model (object elements and data values share one
index space) and derives facts about them, one ground rule instance per
step, from the clauses of a `SRIQN` data ontology. A step cites the clause by
its index in `dbase O` and the facts it uses by their line numbers; the
checker computes the conclusion. Disjunctive conclusions (a gci with several
heads, an at-most restriction, a data universal with several literals) are
lines of their own, and the proof splits on them as a binary tree. Every
leaf closes with a contradiction. The checker does no search.

Facts, at an assignment `e` of object elements and `ev` of data values in a
model `I`:

* `c x a`: `x ∈ a`; `r x k y`: `(x, y) ∈ k`; `eq x y`, `ne x y`;
* `d x u w`: `(x, w) ∈ u`; `lit w j b`: atom `j` holds at `w` iff `b`;
  `veq w w'`, `vne w w'`.

Rules: `nom` (the element of a nominal), `gci`, `ex` (a fresh successor),
`exNom` (the successor is a nominal's element), `all`, `chain`, `atMost`
(two of `k + 1` successors are equal), `nomEq`, equality rewriting
(`eqSym`, `eqRw`), `dEx` (a fresh value), `dAll`, `dAtMost`, `dSub`,
value-equality rewriting (`veqSym`, `veqRw`). Leaves: an empty disjunction,
`eq`/`ne` and `veq`/`vne` clashes, and literals on one value whose
conjunction the data oracle `emp` declares empty.

* `refute_sound`: if `refute O emp pf = true` and `emp` is sound for the data
  theory `Θ`, then `O` has no model (`¬ ConsistentDN Θ O`).
-/

namespace ContextCalculus.SRIQN.Refute

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory litSem rngSem)

variable {n m p q : Nat}

/-! ## Facts and lines -/

inductive Fact (n m p q : Nat) where
  | c (x : Nat) (a : Fin n)
  | r (x : Nat) (k : Fin m) (y : Nat)
  | eq (x y : Nat)
  | ne (x y : Nat)
  | d (x : Nat) (u : Fin p) (w : Nat)
  | lit (w : Nat) (j : Fin q) (b : Bool)
  | veq (w w' : Nat)
  | vne (w w' : Nat)
deriving DecidableEq, Repr

/-- A line: one fact, or a disjunction of facts. -/
inductive Line (n m p q : Nat) where
  | atom (f : Fact n m p q)
  | disj (l : List (Fact n m p q))
deriving DecidableEq, Repr

def Fact.ids : Fact n m p q → List Nat
  | .c x _ => [x]
  | .r x _ y => [x, y]
  | .eq x y => [x, y]
  | .ne x y => [x, y]
  | .d x _ w => [x, w]
  | .lit w _ _ => [w]
  | .veq w w' => [w, w']
  | .vne w w' => [w, w']

def Line.ids : Line n m p q → List Nat
  | .atom f => f.ids
  | .disj l => l.flatMap Fact.ids

/-- The one-line form of a disjunction of facts. -/
def mkLine (l : List (Fact n m p q)) : Line n m p q :=
  match l with
  | [f] => .atom f
  | _ => .disj l

/-- The fact of a role term. -/
def rtF : RoleT (Fin m) → Nat → Nat → Fact n m p q
  | .pos k, x, y => .r x k y
  | .inv k, x, y => .r y k x

def sb (y x i : Nat) : Nat := if i = y then x else i

/-- Replace the object element `y` by `x`. -/
def Fact.substO (y x : Nat) : Fact n m p q → Fact n m p q
  | .c i a => .c (sb y x i) a
  | .r i k j => .r (sb y x i) k (sb y x j)
  | .eq i j => .eq (sb y x i) (sb y x j)
  | .ne i j => .ne (sb y x i) (sb y x j)
  | .d i u w => .d (sb y x i) u w
  | .lit w j b => .lit w j b
  | .veq w w' => .veq w w'
  | .vne w w' => .vne w w'

/-- Replace the data value `y` by `x`. -/
def Fact.substV (y x : Nat) : Fact n m p q → Fact n m p q
  | .c i a => .c i a
  | .r i k j => .r i k j
  | .eq i j => .eq i j
  | .ne i j => .ne i j
  | .d i u w => .d i u (sb y x w)
  | .lit w j b => .lit (sb y x w) j b
  | .veq w w' => .veq (sb y x w) (sb y x w')
  | .vne w w' => .vne (sb y x w) (sb y x w')

/-- The unordered pairs of a list, by position. -/
def pairsOf : List Nat → List (Nat × Nat)
  | [] => []
  | y :: ys => ys.map (fun z => (y, z)) ++ pairsOf ys

/-! ## Semantics -/

section Sem

variable {D V : Type} (atom : Fin q → V → Prop) (I : DInterp D V (Fin n) (Fin m) (Fin p))
  (e : Nat → D) (ev : Nat → V)

def Fact.holds : Fact n m p q → Prop
  | .c x a => I.c a (e x)
  | .r x k y => I.r k (e x) (e y)
  | .eq x y => e x = e y
  | .ne x y => e x ≠ e y
  | .d x u w => I.d u (e x) (ev w)
  | .lit w j b => (atom j (ev w) ↔ b = true)
  | .veq w w' => ev w = ev w'
  | .vne w w' => ev w ≠ ev w'

def Line.holds : Line n m p q → Prop
  | .atom f => f.holds atom I e ev
  | .disj l => ∃ f ∈ l, f.holds atom I e ev

end Sem

section SemLemmas

variable {D V : Type} {atom : Fin q → V → Prop} {I : DInterp D V (Fin n) (Fin m) (Fin p)}
  {e e' : Nat → D} {ev ev' : Nat → V}

theorem Fact.holds_congr {f : Fact n m p q} (h : ∀ i ∈ f.ids, e i = e' i ∧ ev i = ev' i) :
    f.holds atom I e ev ↔ f.holds atom I e' ev' := by
  cases f <;> simp only [Fact.ids, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [Fact.holds, h]

theorem Line.holds_congr {l : Line n m p q} (h : ∀ i ∈ l.ids, e i = e' i ∧ ev i = ev' i) :
    l.holds atom I e ev ↔ l.holds atom I e' ev' := by
  cases l with
  | atom f => exact Fact.holds_congr h
  | disj l =>
    simp only [Line.holds]
    constructor
    · rintro ⟨f, hf, hh⟩
      exact ⟨f, hf, (Fact.holds_congr fun i hi =>
        h i (List.mem_flatMap.2 ⟨f, hf, hi⟩)).1 hh⟩
    · rintro ⟨f, hf, hh⟩
      exact ⟨f, hf, (Fact.holds_congr fun i hi =>
        h i (List.mem_flatMap.2 ⟨f, hf, hi⟩)).2 hh⟩

theorem holds_mkLine {l : List (Fact n m p q)} :
    (mkLine l).holds atom I e ev ↔ ∃ f ∈ l, f.holds atom I e ev := by
  unfold mkLine
  split
  · simp [Line.holds]
  · rfl

theorem holds_rtF {R : RoleT (Fin m)} {x y : Nat} :
    (rtF R x y : Fact n m p q).holds atom I e ev ↔ I.toInterp.rt R (e x) (e y) := by
  cases R <;> rfl

theorem e_sb {x y : Nat} (he : e x = e y) (i : Nat) : e (sb y x i) = e i := by
  unfold sb; split_ifs with h
  · rw [h, he]
  · rfl

theorem holds_substO {f : Fact n m p q} {x y : Nat} (he : e x = e y) :
    (f.substO y x).holds atom I e ev ↔ f.holds atom I e ev := by
  cases f <;> simp only [Fact.substO, Fact.holds, e_sb he]

theorem holds_substV {f : Fact n m p q} {x y : Nat} (he : ev x = ev y) :
    (f.substV y x).holds atom I e ev ↔ f.holds atom I e ev := by
  cases f <;> simp only [Fact.substV, Fact.holds, e_sb he]

theorem nodup_or_pair {α : Type} (e : Nat → α) :
    ∀ l : List Nat, (l.map e).Nodup ∨ ∃ pr ∈ pairsOf l, e pr.1 = e pr.2
  | [] => Or.inl List.nodup_nil
  | y :: ys => by
    rcases nodup_or_pair e ys with h | ⟨pr, hpr, he⟩
    · by_cases hy : e y ∈ ys.map e
      · obtain ⟨z, hz, hez⟩ := List.mem_map.1 hy
        exact Or.inr ⟨(y, z), by simp [pairsOf, hz], hez.symm⟩
      · exact Or.inl (List.nodup_cons.2 ⟨hy, h⟩)
    · exact Or.inr ⟨pr, by simp [pairsOf, hpr], he⟩

end SemLemmas

/-! ## Certificates -/

/-- A step: a ground rule instance. `ci` is a clause index in `dbase O`,
`ref` and `r…` are line numbers, the other numbers are element or value
indices. -/
inductive Step where
  /-- `x` is the element of the nominal `a` (fresh `x`). -/
  | nom (x a : Nat)
  /-- `gci body → head` at `x`; `refs` cite `c x a` for the body. -/
  | gci (ci x : Nat) (refs : List Nat)
  /-- `a ⊑ ∃R.b` at `x` (cited `c x a`): fresh `y`. -/
  | ex (ci x ref y : Nat)
  /-- `a ⊑ ∃R.b` with `b` a nominal, `c x a` and `c y b` cited: `R(x, y)`. -/
  | exNom (ci x y ref refy : Nat)
  /-- `a ⊑ ∀R.b`, `c x a` and `R(x, y)` cited: `c y b`. -/
  | all (ci x y ref refr : Nat)
  /-- `R₁ ∘ … ∘ Rₖ ⊑ S` along the elements `xs`, `refs` the role facts. -/
  | chain (ci : Nat) (xs refs : List Nat)
  /-- `a ⊑ ≤k R.b` at `x`: `k + 1` successors `(y, R-fact, b-fact)`, two equal. -/
  | atMost (ci x ref : Nat) (ys : List (Nat × Nat × Nat))
  /-- `c x a`, `c y a` for a nominal `a`: `eq x y`. -/
  | nomEq (a x y ref1 ref2 : Nat)
  | eqSym (x y ref : Nat)
  /-- `eq x y` and a fact: the fact with `y` replaced by `x`. -/
  | eqRw (refEq ref : Nat)
  /-- `a ⊑ ∃u.(pos, neg)` at `x`: fresh value `w`. -/
  | dEx (ci x ref w : Nat)
  /-- `a ⊑ ∀u.(head)` at `x`, value `w`. -/
  | dAll (ci x w ref refd : Nat)
  /-- `a ⊑ ≤k u.(pos, neg)` at `x`: `k + 1` values `(w, d-fact, literal facts)`. -/
  | dAtMost (ci x ref : Nat) (ws : List (Nat × Nat × List Nat))
  /-- `u ⊑ v`, `d x u w` cited. -/
  | dSub (ci x w refd : Nat)
  | veqSym (w w' ref : Nat)
  | veqRw (refEq ref : Nat)
  /-- The literals of `w` cited by `refs` entail the literal `(j, b)`: the data
  oracle declares the literals with `(j, !b)` empty. -/
  | dLit (w j : Nat) (b : Bool) (refs : List Nat)
  /-- Excluded middle for the atom `j` at the value `w`. -/
  | litEM (w j : Nat)
deriving Repr, Inhabited

inductive Close where
  /-- the empty disjunction -/
  | empty (ref : Nat)
  | ne (x y r1 r2 : Nat)
  | vne (w w' r1 r2 : Nat)
  /-- literals on `w` whose conjunction is empty -/
  | lits (w : Nat) (refs : List Nat)
deriving Repr, Inhabited

/-- A refutation: steps, then a leaf, or a split on a disjunction (the left
branch adds its first fact, the right branch the rest). -/
inductive Proof where
  | close (ss : List Step) (c : Close)
  | split (ss : List Step) (ref : Nat) (l r : Proof)
deriving Repr, Inhabited

/-! ## The checker -/

structure St (n m p q : Nat) where
  lines : Array (Line n m p q)
  next : Nat

def St.atomAt (st : St n m p q) (i : Nat) : Option (Fact n m p q) :=
  match st.lines[i]? with
  | some (.atom f) => some f
  | _ => none

def St.has (st : St n m p q) (i : Nat) (f : Fact n m p q) : Bool :=
  decide (st.atomAt i = some f)

/-- The path of a chain: start and end. -/
def pathOK (st : St n m p q) : List (RoleT (Fin m)) → List Nat → List Nat → Option (Nat × Nat)
  | [], [x], [] => some (x, x)
  | R :: Rs, x :: xs, i :: is =>
    match pathOK st Rs xs is with
    | some (y, z) => if st.has i (rtF R x y) then some (x, z) else none
    | none => none
  | _, _, _ => none

/-- The literal facts of a value for `pos` and `neg`. -/
def rngOK (st : St n m p q) (w : Nat) (pos neg : List (Fin q)) (refs : List Nat) : Bool :=
  pos.all (fun j => refs.any fun i => st.has i (.lit w j true)) &&
    neg.all (fun j => refs.any fun i => st.has i (.lit w j false))

/-- The literals of the value `w` cited by `refs`. -/
def litsOf (st : St n m p q) (w : Nat) : List Nat → Option (List (Fin q × Bool))
  | [] => some []
  | i :: is =>
    match st.atomAt i, litsOf st w is with
    | some (.lit w' j b), some L => if w' = w then some ((j, b) :: L) else none
    | _, _ => none

variable (B : Array (SRIQD.Clause (Fin n) (Fin m) (Fin p) (Fin q))) (N : List (Fin n))
  (emp : List (Fin q × Bool) → Bool)

/-- The lines a step adds and the new bound of the indices. -/
def stepOut (st : St n m p q) : Step → Option (List (Line n m p q) × Nat)
  | .nom x a =>
    if h : a < n then
      if N.contains ⟨a, h⟩ && st.next ≤ x then some ([.atom (.c x ⟨a, h⟩)], x + 1) else none
    else none
  | .gci ci x refs =>
    match B[ci]? with
    | some (.obj (.gci body head)) =>
      if body.all (fun a => refs.any fun i => st.has i (.c x a)) then
        some ([mkLine (head.map fun h => .c x h)], st.next)
      else none
    | _ => none
  | .ex ci x ref y =>
    match B[ci]? with
    | some (.obj (.exRight a R b)) =>
      if st.has ref (.c x a) && st.next ≤ y then
        some ([.atom (rtF R x y), .atom (.c y b)], y + 1)
      else none
    | _ => none
  | .exNom ci x y ref refy =>
    match B[ci]? with
    | some (.obj (.exRight a R b)) =>
      if st.has ref (.c x a) && st.has refy (.c y b) && N.contains b then
        some ([.atom (rtF R x y)], st.next)
      else none
    | _ => none
  | .all ci x y ref refr =>
    match B[ci]? with
    | some (.obj (.allRight a R b)) =>
      if st.has ref (.c x a) && st.has refr (rtF R x y) then
        some ([.atom (.c y b)], st.next)
      else none
    | _ => none
  | .chain ci xs refs =>
    match B[ci]? with
    | some (.obj (.chain body S)) =>
      match pathOK st body xs refs with
      | some (x, z) => some ([.atom (rtF S x z)], st.next)
      | none => none
    | _ => none
  | .atMost ci x ref ys =>
    match B[ci]? with
    | some (.obj (.atMost a k R b)) =>
      if st.has ref (.c x a) && ys.length == k + 1 &&
          ys.all (fun t => st.has t.2.1 (rtF R x t.1) && st.has t.2.2 (.c t.1 b)) then
        some ([mkLine ((pairsOf (ys.map (·.1))).map fun pr => .eq pr.1 pr.2)], st.next)
      else none
    | _ => none
  | .nomEq a x y ref1 ref2 =>
    if h : a < n then
      if N.contains ⟨a, h⟩ && st.has ref1 (.c x ⟨a, h⟩) && st.has ref2 (.c y ⟨a, h⟩) then
        some ([.atom (.eq x y)], st.next)
      else none
    else none
  | .eqSym x y ref =>
    if st.has ref (.eq x y) then some ([.atom (.eq y x)], st.next) else none
  | .eqRw refEq ref =>
    match st.atomAt refEq, st.atomAt ref with
    | some (.eq x y), some f => some ([.atom (f.substO y x)], st.next)
    | _, _ => none
  | .dEx ci x ref w =>
    match B[ci]? with
    | some (.dEx a u pos neg) =>
      if st.has ref (.c x a) && st.next ≤ w then
        some (.atom (.d x u w) :: (pos.map fun j => .atom (.lit w j true)) ++
          (neg.map fun j => .atom (.lit w j false)), w + 1)
      else none
    | _ => none
  | .dAll ci x w ref refd =>
    match B[ci]? with
    | some (.dAll a u head) =>
      if st.has ref (.c x a) && st.has refd (.d x u w) then
        some ([mkLine (head.map fun l => .lit w l.1 l.2)], st.next)
      else none
    | _ => none
  | .dAtMost ci x ref ws =>
    match B[ci]? with
    | some (.dAtMost a k u pos neg) =>
      if st.has ref (.c x a) && ws.length == k + 1 &&
          ws.all (fun t => st.has t.2.1 (.d x u t.1) && rngOK st t.1 pos neg t.2.2) then
        some ([mkLine ((pairsOf (ws.map (·.1))).map fun pr => .veq pr.1 pr.2)], st.next)
      else none
    | _ => none
  | .dSub ci x w refd =>
    match B[ci]? with
    | some (.dSub u v) =>
      if st.has refd (.d x u w) then some ([.atom (.d x v w)], st.next) else none
    | _ => none
  | .veqSym w w' ref =>
    if st.has ref (.veq w w') then some ([.atom (.veq w' w)], st.next) else none
  | .veqRw refEq ref =>
    match st.atomAt refEq, st.atomAt ref with
    | some (.veq x y), some f => some ([.atom (f.substV y x)], st.next)
    | _, _ => none
  | .dLit w j b refs =>
    if h : j < q then
      match litsOf st w refs with
      | some L => if emp (L ++ [(⟨j, h⟩, !b)]) then some ([.atom (.lit w ⟨j, h⟩ b)], st.next) else none
      | none => none
    else none
  | .litEM w j =>
    if h : j < q then some ([.disj [.lit w ⟨j, h⟩ true, .lit w ⟨j, h⟩ false]], st.next) else none

def applyStep (st : St n m p q) (s : Step) : Option (St n m p q) :=
  match stepOut B N emp st s with
  | some (ls, nx) =>
    if st.next ≤ nx && ls.all (fun l => l.ids.all (· < nx)) then
      some ⟨st.lines ++ ls.toArray, nx⟩
    else none
  | none => none

def runSteps : St n m p q → List Step → Option (St n m p q)
  | st, [] => some st
  | st, s :: ss =>
    match applyStep B N emp st s with
    | some st' => runSteps st' ss
    | none => none

def closeOK (st : St n m p q) : Close → Bool
  | .empty ref => decide (st.lines[ref]? = some (.disj []))
  | .ne x y r1 r2 => st.has r1 (.eq x y) && st.has r2 (.ne x y)
  | .vne w w' r1 r2 => st.has r1 (.veq w w') && st.has r2 (.vne w w')
  | .lits w refs =>
    match litsOf st w refs with
    | some L => emp L
    | none => false

def check : St n m p q → Proof → Bool
  | st, .close ss c =>
    match runSteps B N emp st ss with
    | some st' => closeOK emp st' c
    | none => false
  | st, .split ss ref l r =>
    match runSteps B N emp st ss with
    | some st' =>
      match st'.lines[ref]? with
      | some (.disj (f :: rest)) =>
        check ⟨st'.lines.push (.atom f), st'.next⟩ l &&
          check ⟨st'.lines.push (.disj rest), st'.next⟩ r
      | _ => false
    | none => false

end ContextCalculus.SRIQN.Refute

namespace ContextCalculus.SRIQN.Refute

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory litSem rngSem)

variable {n m p q : Nat}

/-- **The refutation checker** on a data ontology with nominals. -/
def refute (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (emp : List (Fin q × Bool) → Bool)
    (pf : Proof) : Bool :=
  check (dbase O).toArray (dnoms O) emp ⟨#[], 0⟩ pf

/-! ## Soundness -/

section Sound

variable {D V : Type} {atom : Fin q → V → Prop} {I : DInterp D V (Fin n) (Fin m) (Fin p)}

/-- The lines hold at `e`, `ev`, and their indices are below `next`. -/
def Good (atom : Fin q → V → Prop) (I : DInterp D V (Fin n) (Fin m) (Fin p))
    (st : St n m p q) (e : Nat → D) (ev : Nat → V) : Prop :=
  ∀ l ∈ st.lines, l.holds atom I e ev ∧ ∀ i ∈ l.ids, i < st.next

theorem atomAt_some {st : St n m p q} {i : Nat} {f : Fact n m p q} (h : st.atomAt i = some f) :
    st.lines[i]? = some (.atom f) := by
  unfold St.atomAt at h
  split at h
  · next l hl => cases h; exact hl
  · cases h

theorem has_good {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev)
    {i : Nat} {f : Fact n m p q} (h : st.has i f = true) :
    f.holds atom I e ev ∧ ∀ j ∈ f.ids, j < st.next := by
  unfold St.has at h
  rw [decide_eq_true_eq] at h
  exact hg _ (Array.mem_of_getElem? (atomAt_some h))

theorem has_holds {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev)
    {i : Nat} {f : Fact n m p q} (h : st.has i f = true) : f.holds atom I e ev :=
  (has_good hg h).1

theorem atomAt_good {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev)
    {i : Nat} {f : Fact n m p q} (h : st.atomAt i = some f) : f.holds atom I e ev :=
  (hg _ (Array.mem_of_getElem? (atomAt_some h))).1

theorem pathOK_sound {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev) :
    ∀ {body : List (RoleT (Fin m))} {xs is : List Nat} {x z : Nat},
      pathOK st body xs is = some (x, z) → I.toInterp.path body (e x) (e z)
  | [], [x'], [], x, z, h => by
    simp only [pathOK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | R :: Rs, x' :: xs, i :: is, x, z, h => by
    simp only [pathOK] at h
    split at h
    · next y z' hp =>
      split_ifs at h with hh
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨e y, (holds_rtF).1 (has_holds hg hh), pathOK_sound hg hp⟩
    · cases h
  | [], [], _, _, _, h => by simp [pathOK] at h
  | [], _ :: _ :: _, _, _, _, h => by simp [pathOK] at h
  | [], [_], _ :: _, _, _, h => by simp [pathOK] at h
  | _ :: _, [], _, _, _, h => by simp [pathOK] at h
  | _ :: _, _ :: _, [], _, _, h => by simp [pathOK] at h

theorem litsOf_sound {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev)
    {w : Nat} : ∀ {is : List Nat} {L : List (Fin q × Bool)}, litsOf st w is = some L →
      ∀ l ∈ L, litSem atom l (ev w)
  | [], L, h => by
    simp only [litsOf, Option.some.injEq] at h
    subst h; simp
  | i :: is, L, h => by
    simp only [litsOf] at h
    split at h
    · next w' j b L' hi hL =>
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h hw
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact atomAt_good hg hi
      · exact litsOf_sound hg hL l hl
    · cases h

theorem rngOK_sound {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev)
    {w : Nat} {pos neg : List (Fin q)} {refs : List Nat} (h : rngOK st w pos neg refs = true) :
    rngSem atom pos neg (ev w) := by
  simp only [rngOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨i, -, hi⟩ := h.1 j hj
    have := has_holds hg hi
    simpa [Fact.holds] using this
  · obtain ⟨i, -, hi⟩ := h.2 j hj
    have := has_holds hg hi
    simpa [Fact.holds] using this

variable {B : Array (SRIQD.Clause (Fin n) (Fin m) (Fin p) (Fin q))} {N : List (Fin n)}
  {emp : List (Fin q × Bool) → Bool}

/-- What a model gives: every clause of `B` holds, every name of `N` is a
nominal, and what the data oracle declares empty is empty. -/
structure ModelOf (atom : Fin q → V → Prop) (I : DInterp D V (Fin n) (Fin m) (Fin p))
    (B : Array (SRIQD.Clause (Fin n) (Fin m) (Fin p) (Fin q))) (N : List (Fin n))
    (emp : List (Fin q × Bool) → Bool) : Prop where
  cl : ∀ (ci : Nat) cl, B[ci]? = some cl → SRIQD.satClause atom I cl
  nom : ∀ a ∈ N, NomAt I.toInterp a
  emp : ∀ L, emp L = true → ∀ v, ¬ ∀ l ∈ L, litSem atom l v

theorem upd_agree {α : Type} {f : Nat → α} {N y : Nat} {v : α} (hy : N ≤ y) :
    ∀ j < N, (fun i => if i = y then v else f i) j = f j := by
  intro j hj
  have : j ≠ y := by omega
  simp [this]

/-- **One step.** -/
theorem stepOut_sound (hM : ModelOf atom I B N emp) {st : St n m p q} {e : Nat → D} {ev : Nat → V}
    (hg : Good atom I st e ev) {s : Step} {ls : List (Line n m p q)} {nx : Nat}
    (h : stepOut B N emp st s = some (ls, nx)) :
    ∃ (e' : Nat → D) (ev' : Nat → V), (∀ j < st.next, e' j = e j ∧ ev' j = ev j) ∧
      ∀ l ∈ ls, l.holds atom I e' ev' := by
  have refl : ∀ j < st.next, e j = e j ∧ ev j = ev j := fun _ _ => ⟨rfl, rfl⟩
  cases s with
  | nom x a =>
    simp only [stepOut] at h
    split_ifs at h with ha hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hc
    obtain ⟨z, hz⟩ := hM.nom _ hc.1
    refine ⟨fun i => if i = x then z else e i, ev,
      fun j hj => ⟨upd_agree hc.2 j hj, rfl⟩, ?_⟩
    simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
    exact (hz z).2 rfl
  | gci ci x refs =>
    simp only [stepOut] at h
    split at h
    · next body head hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, holds_mkLine, List.mem_map]
      simp only [List.all_eq_true, List.any_eq_true] at hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQ.satClause] at hs
      obtain ⟨b, hb, hcb⟩ := hs (e x) fun a ha => by
        obtain ⟨i, -, hi⟩ := hc a ha
        exact has_holds hg hi
      exact ⟨_, ⟨b, hb, rfl⟩, hcb⟩
    · cases h
  | ex ci x ref y =>
    simp only [stepOut] at h
    split at h
    · next a R b hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQ.satClause] at hs
      obtain ⟨z, hz1, hz2⟩ := hs (e x) (has_holds hg hc.1)
      have hx : x < st.next := by
        have := (has_good hg hc.1).2 x (by simp [Fact.ids])
        exact this
      refine ⟨fun i => if i = y then z else e i, ev,
        fun j hj => ⟨upd_agree hc.2 j hj, rfl⟩, ?_⟩
      have hxy : x ≠ y := by omega
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · show (rtF R x y : Fact n m p q).holds atom I (fun i => if i = y then z else e i) ev
        rw [holds_rtF]
        simp only [if_neg hxy]
        exact hz1
      · show I.c b (if y = y then z else e y)
        rw [if_pos rfl]
        exact hz2
    · cases h
  | exNom ci x y ref refy =>
    simp only [stepOut] at h
    split at h
    · next a R b hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQ.satClause] at hs
      obtain ⟨z, hz1, hz2⟩ := hs (e x) (has_holds hg hc.1.1)
      obtain ⟨z0, hz0⟩ := hM.nom _ (by simpa using hc.2)
      have hy : I.c b (e y) := has_holds hg hc.1.2
      have : z = e y := by rw [(hz0 z).1 hz2, (hz0 (e y)).1 hy]
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, Line.holds, holds_rtF]
      rw [← this]; exact hz1
    · cases h
  | all ci x y ref refr =>
    simp only [stepOut] at h
    split at h
    · next a R b hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQ.satClause] at hs
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
      exact hs (e x) (has_holds hg hc.1) (e y) ((holds_rtF).1 (has_holds hg hc.2))
    · cases h
  | chain ci xs refs =>
    simp only [stepOut] at h
    split at h
    · next body S hB =>
      split at h
      · next x z hp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hs := hM.cl _ _ hB
        simp only [SRIQD.satClause, SRIQ.satClause] at hs
        refine ⟨e, ev, refl, ?_⟩
        simp only [List.mem_singleton, forall_eq, Line.holds, holds_rtF]
        exact hs _ _ (pathOK_sound hg hp)
      · cases h
    · cases h
  | atMost ci x ref ys =>
    simp only [stepOut] at h
    split at h
    · next a k R b hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      obtain ⟨⟨hx, hlen⟩, hys⟩ := hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQ.satClause] at hs
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, holds_mkLine, List.mem_map]
      rcases nodup_or_pair e (ys.map (·.1)) with hnd | ⟨pr, hpr, hpe⟩
      · exfalso
        have := hs (e x) (has_holds hg hx) ((ys.map (·.1)).map e) hnd (by
          intro z hz
          simp only [List.map_map, List.mem_map, Function.comp_apply] at hz
          obtain ⟨t, ht, rfl⟩ := hz
          have := hys t ht
          exact ⟨(holds_rtF).1 (has_holds hg this.1), has_holds hg this.2⟩)
        simp only [List.length_map, hlen] at this
        omega
      · exact ⟨_, ⟨pr, hpr, rfl⟩, hpe⟩
    · cases h
  | nomEq a x y ref1 ref2 =>
    simp only [stepOut] at h
    split_ifs at h with ha hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
    obtain ⟨z, hz⟩ := hM.nom _ (by simpa using hc.1.1)
    refine ⟨e, ev, refl, ?_⟩
    simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
    rw [(hz _).1 (has_holds hg hc.1.2), (hz _).1 (has_holds hg hc.2)]
  | eqSym x y ref =>
    simp only [stepOut] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨e, ev, refl, ?_⟩
    simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
    exact (has_holds hg hc : e x = e y).symm
  | eqRw refEq ref =>
    simp only [stepOut] at h
    split at h
    · next x y f h1 h2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, Line.holds]
      exact (holds_substO (atomAt_good hg h1)).2 (atomAt_good hg h2)
    · cases h
  | dEx ci x ref w =>
    simp only [stepOut] at h
    split at h
    · next a u pos neg hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQD.dLocal] at hs
      obtain ⟨v, hv1, hv2, hv3⟩ := hs (e x) (has_holds hg hc.1)
      refine ⟨e, fun i => if i = w then v else ev i,
        fun j hj => ⟨rfl, upd_agree hc.2 j hj⟩, ?_⟩
      intro l hl
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hl
      rcases hl with (rfl | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
      · simp only [Line.holds, Fact.holds]; exact hv1
      · simp only [Line.holds, Fact.holds]; simpa using hv2 j hj
      · simp only [Line.holds, Fact.holds]; simpa using hv3 j hj
    · cases h
  | dAll ci x w ref refd =>
    simp only [stepOut] at h
    split at h
    · next a u head hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQD.dLocal] at hs
      obtain ⟨l, hl, hls⟩ := hs (e x) (has_holds hg hc.1) (ev w) (has_holds hg hc.2)
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, holds_mkLine, List.mem_map]
      exact ⟨_, ⟨l, hl, rfl⟩, hls⟩
    · cases h
  | dAtMost ci x ref ws =>
    simp only [stepOut] at h
    split at h
    · next a k u pos neg hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      obtain ⟨⟨hx, hlen⟩, hws⟩ := hc
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQD.dLocal] at hs
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, holds_mkLine, List.mem_map]
      rcases nodup_or_pair ev (ws.map (·.1)) with hnd | ⟨pr, hpr, hpe⟩
      · exfalso
        have := hs (e x) (has_holds hg hx) ((ws.map (·.1)).map ev) hnd (by
          intro z hz
          simp only [List.map_map, List.mem_map, Function.comp_apply] at hz
          obtain ⟨t, ht, rfl⟩ := hz
          have := hws t ht
          exact ⟨has_holds hg this.1, rngOK_sound hg this.2⟩)
        simp only [List.length_map, hlen] at this
        omega
      · exact ⟨_, ⟨pr, hpr, rfl⟩, hpe⟩
    · cases h
  | dSub ci x w refd =>
    simp only [stepOut] at h
    split at h
    · next u v hB =>
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs := hM.cl _ _ hB
      simp only [SRIQD.satClause, SRIQD.dLocal] at hs
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
      exact hs (e x) (ev w) (has_holds hg hc)
    · cases h
  | veqSym w w' ref =>
    simp only [stepOut] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨e, ev, refl, ?_⟩
    simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
    exact (has_holds hg hc : ev w = ev w').symm
  | veqRw refEq ref =>
    simp only [stepOut] at h
    split at h
    · next x y f h1 h2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, Line.holds]
      exact (holds_substV (atomAt_good hg h1)).2 (atomAt_good hg h2)
    · cases h
  | dLit w j b refs =>
    simp only [stepOut] at h
    split_ifs at h with hj
    split at h
    · next L hL =>
      split_ifs at h with he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨e, ev, refl, ?_⟩
      simp only [List.mem_singleton, forall_eq, Line.holds, Fact.holds]
      by_contra hn
      refine hM.emp _ he (ev w) fun l hl => ?_
      rcases List.mem_append.1 hl with hl | hl
      · exact litsOf_sound hg hL l hl
      · rw [List.mem_singleton] at hl
        subst hl
        cases b <;> simp_all [litSem]
    · cases h
  | litEM w j =>
    simp only [stepOut] at h
    split_ifs at h with hj
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨e, ev, refl, ?_⟩
    simp only [forall_eq, Line.holds, Fact.holds, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    by_cases ha : atom ⟨j, hj⟩ (ev w) <;> simp [ha]

theorem applyStep_sound (hM : ModelOf atom I B N emp) {st st' : St n m p q} {e : Nat → D}
    {ev : Nat → V} (hg : Good atom I st e ev) {s : Step} (h : applyStep B N emp st s = some st') :
    ∃ (e' : Nat → D) (ev' : Nat → V), Good atom I st' e' ev' := by
  unfold applyStep at h
  split at h
  · next ls nx hs =>
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨hle, hids⟩ := hc
    obtain ⟨e', ev', hag, hnew⟩ := stepOut_sound hM hg hs
    refine ⟨e', ev', fun l hl => ?_⟩
    rcases Array.mem_append.1 hl with hl | hl
    · obtain ⟨hh, hi⟩ := hg l hl
      refine ⟨(Line.holds_congr fun i hi' => ?_).1 hh, fun i hi' => lt_of_lt_of_le (hi i hi') hle⟩
      exact ⟨(hag i (hi i hi')).1.symm, (hag i (hi i hi')).2.symm⟩
    · have hl' : l ∈ ls := by simpa using hl
      exact ⟨hnew l hl', fun i hi' => by simpa using hids l hl' i hi'⟩
  · cases h

theorem runSteps_sound (hM : ModelOf atom I B N emp) :
    ∀ {st st' : St n m p q} {e : Nat → D} {ev : Nat → V} {ss : List Step},
      Good atom I st e ev → runSteps B N emp st ss = some st' →
        ∃ (e' : Nat → D) (ev' : Nat → V), Good atom I st' e' ev'
  | st, st', e, ev, [], hg, h => by
    simp only [runSteps, Option.some.injEq] at h
    subst h; exact ⟨e, ev, hg⟩
  | st, st', e, ev, s :: ss, hg, h => by
    simp only [runSteps] at h
    split at h
    · next st1 h1 =>
      obtain ⟨e1, ev1, hg1⟩ := applyStep_sound hM hg h1
      exact runSteps_sound hM hg1 h
    · cases h

theorem closeOK_sound (hemp : ∀ L, emp L = true → ∀ v, ¬ ∀ l ∈ L, litSem atom l v)
    {st : St n m p q} {e : Nat → D} {ev : Nat → V} (hg : Good atom I st e ev) {c : Close}
    (h : closeOK emp st c = true) : False := by
  cases c with
  | empty ref =>
    simp only [closeOK, decide_eq_true_eq] at h
    obtain ⟨f, hf, -⟩ := (hg _ (Array.mem_of_getElem? h)).1
    cases hf
  | ne x y r1 r2 =>
    simp only [closeOK, Bool.and_eq_true] at h
    exact (has_holds hg h.2 : e x ≠ e y) (has_holds hg h.1)
  | vne w w' r1 r2 =>
    simp only [closeOK, Bool.and_eq_true] at h
    exact (has_holds hg h.2 : ev w ≠ ev w') (has_holds hg h.1)
  | lits w refs =>
    simp only [closeOK] at h
    split at h
    · next L hL => exact hemp L h (ev w) (litsOf_sound hg hL)
    · cases h

theorem check_sound (hM : ModelOf atom I B N emp) :
    ∀ (pf : Proof) {st : St n m p q} {e : Nat → D} {ev : Nat → V},
      Good atom I st e ev → check B N emp st pf = true → False
  | .close ss c, st, e, ev, hg, h => by
    simp only [check] at h
    split at h
    · next st' hr =>
      obtain ⟨e', ev', hg'⟩ := runSteps_sound hM hg hr
      exact closeOK_sound hM.emp hg' h
    · cases h
  | .split ss ref l r, st, e, ev, hg, h => by
    simp only [check] at h
    split at h
    · next st' hr =>
      obtain ⟨e', ev', hg'⟩ := runSteps_sound hM hg hr
      split at h
      · next f rest hf =>
        rw [Bool.and_eq_true] at h
        obtain ⟨⟨g, hgm, hgh⟩, hids⟩ := hg' _ (Array.mem_of_getElem? hf)
        have hfi : ∀ i ∈ f.ids, i < st'.next := fun i hi =>
          hids i (List.mem_flatMap.2 ⟨f, List.mem_cons_self .., hi⟩)
        rcases List.mem_cons.1 hgm with rfl | hrest
        · refine check_sound hM l (st := ⟨st'.lines.push (.atom g), st'.next⟩) (e := e') (ev := ev') ?_ h.1
          intro l' hl'
          rcases Array.mem_push.1 hl' with hl' | rfl
          · exact hg' l' hl'
          · exact ⟨hgh, hfi⟩
        · refine check_sound hM r (st := ⟨st'.lines.push (.disj rest), st'.next⟩) (e := e') (ev := ev') ?_ h.2
          intro l' hl'
          rcases Array.mem_push.1 hl' with hl' | rfl
          · exact hg' l' hl'
          · refine ⟨⟨g, hrest, hgh⟩, fun i hi => hids i ?_⟩
            obtain ⟨f', hf', hi'⟩ := List.mem_flatMap.1 hi
            exact List.mem_flatMap.2 ⟨f', List.mem_cons_of_mem _ hf', hi'⟩
      · cases h
    · cases h

end Sound

/-- **Soundness of the refutation checker.** If the data oracle `emp` only
declares empty what is empty in every admissible pair of `Θ`, then a
refutation the checker accepts shows that `O` has no model. -/
theorem refute_sound {Θ : DataTheory (Fin q)} {emp : List (Fin q × Bool) → Bool}
    (hne : ∀ (V : Type) (atom : Fin q → V → Prop), Θ V atom → Nonempty V)
    (hemp : ∀ (V : Type) (atom : Fin q → V → Prop), Θ V atom →
      ∀ L, emp L = true → ∀ v, ¬ ∀ l ∈ L, litSem atom l v)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} {pf : Proof}
    (h : refute O emp pf = true) : ¬ ConsistentDN Θ O := by
  rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
  have hM : ModelOf atom I (dbase O).toArray (dnoms O) emp :=
    ⟨fun ci cl hc => hI cl (List.mem_of_getElem? (by simpa using hc)), hn, hemp V atom hΘ⟩
  obtain ⟨d0⟩ := hD
  obtain ⟨v0⟩ := hne V atom hΘ
  exact check_sound hM pf (st := ⟨#[], 0⟩) (e := fun _ => d0)
    (ev := fun _ => v0) (fun l hl => by simp at hl) h

end ContextCalculus.SRIQN.Refute

#print axioms ContextCalculus.SRIQN.Refute.refute_sound
