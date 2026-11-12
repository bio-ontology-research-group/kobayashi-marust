import ContextCalculus.OWLFrontend.ELTranslate
import ContextCalculus.CBALCEncoding

/-!
# OWL ALC into the `Ctx` normal clauses

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7, ALC route. `translateALC O requested`
normalises an OWL ALC ontology (`OWL.Ontology.isALC`) into the clause shapes
`gci`, `exRight`, `exLeft`, `allRight` of `Ctx` that
`ALCReference.alcBit` decides exactly.

Layout of the concept indices (as in the EL route, whose prepass this file
reuses): the requested IRIs (duplicates removed) take `0 .. n-1` in order;
then the other class IRIs the ontology mentions, in first-occurrence order;
then `top` (clause `gci [] [top]`) and `bottom` (clause `gci [bottom] []`);
then the definers. Role indices: the object-property IRIs in
first-occurrence order.

Structural transformation with polarity, one fresh definer per occurrence of
a complex subexpression; no NNF pass. A negative occurrence `E` (left of
`⊑`) gets a definer `X` with clauses for `E ⊑ X`, a positive one clauses for
`X ⊑ E`:

| occurrence | clauses |
|---|---|
| negative `and [c1..cn]` | `gci [X1⁻ .. Xn⁻] [X]` |
| positive `and [c1..cn]` | `gci [X] [Xi⁺]` for each `i` |
| negative `or [c1..cn]` | `gci [Xi⁻] [X]` for each `i` |
| positive `or [c1..cn]` | `gci [X] [X1⁺ .. Xn⁺]` |
| negative `not c` | `gci [] [X, Y⁺]` |
| positive `not c` | `gci [X, Z⁻] []` |
| negative `some r c` | `exLeft r Xc⁻ X` |
| positive `some r c` | `exRight X r Xc⁺` |
| negative `all r c` | `gci [] [X, W]`, `exRight W r N`, `gci [N, Zc⁻] []` |
| positive `all r c` | `allRight X r Xc⁺` |

For the negative universal, `W` stands for `some r (not c)` and `N` for
`not c`. Class IRIs, `owl:Thing`, `owl:Nothing`, `and []` (top) and `or []`
(bottom) use their index directly.

Axioms: `SubClassOf(C D)` is `gci [X_C⁻] [X_D⁺]`; `EquivalentClasses` gives
`gci [N] [P]` for every negative member index `N` and positive member index
`P` with `N ≠ P`; `DisjointClasses` gives `gci [Xi⁻, Xj⁻] []` for `i < j`;
`ObjectPropertyDomain(r C)` is `exLeft r top X_C⁺`;
`ObjectPropertyRange(r C)` is `allRight top r X_C⁺`. Declarations give
nothing; role axioms are outside ALC and never reach the translation.

The state is the EL state (maps, meaning tables, `top`, `bottom`; its own
clause list stays empty) with a list of `Ctx` clauses over `Nat`. The
`Fin`-typed ontology is built once at the end; every index is in range
(`ALCTranslateCorrect`), so the conversion drops nothing.

Compiled code recurses only over the depth of one class expression; loops
over axioms, members and requested names are tail recursive or `foldl`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

/-- The result of the ALC translation: the requested IRIs (duplicates
removed, `named[i]` has concept index `i`) and the normal-form ontology over
`Fin conceptCount` concepts and `Fin roleCount` roles. -/
structure ALCTranslation where
  named : List OWL.IRI
  conceptCount : Nat
  roleCount : Nat
  hnamed : named.length ≤ conceptCount
  ontology : Ctx.Ontology (Fin conceptCount) (Fin roleCount)

namespace ALC

abbrev AC := Ctx.Clause Nat Nat

/-- Translation state: the EL state `b` (maps, meaning tables, `top`,
`bottom`) and the emitted clauses, newest first. -/
structure St where
  b : EL.St
  out : List AC := []

def internC (a : IRI) (s : St) : Nat × St :=
  let r := EL.internC a s.b
  (r.1, { s with b := r.2 })

def internR (r : IRI) (s : St) : Nat × St :=
  let q := EL.internR r s.b
  (q.1, { s with b := q.2 })

def freshC (e : ClassExpr) (s : St) : Nat × St :=
  let r := EL.freshC e s.b
  (r.1, { s with b := r.2 })

def emit (c : AC) (s : St) : St := { s with out := c :: s.out }

/-- `f k` for every member index `k`. -/
def emitEach (f : Nat → AC) : List (ClassExpr × Nat) → St → St
  | [], s => s
  | q :: qs, s => emitEach f qs (emit (f q.2) s)

mutual

/-- Structural transformation of one occurrence. `pos = false` is a negative
occurrence (the result `X` satisfies `E ⊑ X`), `pos = true` a positive one
(`X ⊑ E`). -/
def transExpr : ClassExpr → Bool → St → Nat × St
  | .cls a, _, s => internC a s
  | .thing, _, s => (s.b.top, s)
  | .nothing, _, s => (s.b.bottom, s)
  | .and [], _, s => (s.b.top, s)
  | .or [], _, s => (s.b.bottom, s)
  | .and cs@(_ :: _), false, s =>
      let ys := transList cs false s []
      let x := freshC (.and cs) ys.2
      (x.1, emit (.gci (ys.1.map Prod.snd) [x.1]) x.2)
  | .and cs@(_ :: _), true, s =>
      let ys := transList cs true s []
      let x := freshC (.and cs) ys.2
      (x.1, emitEach (fun y => .gci [x.1] [y]) ys.1 x.2)
  | .or cs@(_ :: _), false, s =>
      let ys := transList cs false s []
      let x := freshC (.or cs) ys.2
      (x.1, emitEach (fun y => .gci [y] [x.1]) ys.1 x.2)
  | .or cs@(_ :: _), true, s =>
      let ys := transList cs true s []
      let x := freshC (.or cs) ys.2
      (x.1, emit (.gci [x.1] (ys.1.map Prod.snd)) x.2)
  | .not c, false, s =>
      let y := transExpr c true s
      let x := freshC (.not c) y.2
      (x.1, emit (.gci [] [x.1, y.1]) x.2)
  | .not c, true, s =>
      let z := transExpr c false s
      let x := freshC (.not c) z.2
      (x.1, emit (.gci [x.1, z.1] []) x.2)
  | .some r c, false, s =>
      let a := internR (EL.propIRI r) s
      let y := transExpr c false a.2
      let x := freshC (.some r c) y.2
      (x.1, emit (.exLeft a.1 y.1 x.1) x.2)
  | .some r c, true, s =>
      let a := internR (EL.propIRI r) s
      let y := transExpr c true a.2
      let x := freshC (.some r c) y.2
      (x.1, emit (.exRight x.1 a.1 y.1) x.2)
  | .all r c, false, s =>
      let a := internR (EL.propIRI r) s
      let z := transExpr c false a.2
      let x := freshC (.all r c) z.2
      let w := freshC (.some r (.not c)) x.2
      let n := freshC (.not c) w.2
      (x.1, emit (.gci [n.1, z.1] []) (emit (.exRight w.1 a.1 n.1)
        (emit (.gci [] [x.1, w.1]) n.2)))
  | .all r c, true, s =>
      let a := internR (EL.propIRI r) s
      let y := transExpr c true a.2
      let x := freshC (.all r c) y.2
      (x.1, emit (.allRight x.1 a.1 y.1) x.2)

/-- Translate a list of occurrences of one polarity, keeping each next to its
index, in order. -/
def transList : List ClassExpr → Bool → St → List (ClassExpr × Nat) →
    List (ClassExpr × Nat) × St
  | [], _, s, acc => (acc.reverse, s)
  | c :: cs, p, s, acc =>
      let y := transExpr c p s
      transList cs p y.2 ((c, y.1) :: acc)

end

/-- `gci [n] [p]` for every negative member index `n` and positive member
index `p` with `n ≠ p`. -/
def emitEquiv (negs poss : List (ClassExpr × Nat)) (out : List AC) : List AC :=
  negs.foldl (fun o n =>
    poss.foldl (fun o p => if n.2 = p.2 then o else .gci [n.2] [p.2] :: o) o) out

/-- `gci [n, m] []` for every pair of members in list order. -/
def emitDisjoint : List (ClassExpr × Nat) → List AC → List AC
  | [], o => o
  | n :: rest, o => emitDisjoint rest (rest.foldl (fun o m => .gci [n.2, m.2] [] :: o) o)

/-- Translate one axiom. Axioms outside OWL ALC produce nothing. -/
def transAxiom (s : St) : Axiom → St
  | .subClassOf c d =>
      let n := transExpr c false s
      let p := transExpr d true n.2
      emit (.gci [n.1] [p.1]) p.2
  | .equivalentClasses cs =>
      let n := transList cs false s []
      let p := transList cs true n.2 []
      { p.2 with out := emitEquiv n.1 p.1 p.2.out }
  | .disjointClasses cs =>
      let n := transList cs false s []
      { n.2 with out := emitDisjoint n.1 n.2.out }
  | .domain r c =>
      let a := internR (EL.propIRI r) s
      let p := transExpr c true a.2
      emit (.exLeft a.1 p.2.b.top p.1) p.2
  | .range r c =>
      let a := internR (EL.propIRI r) s
      let p := transExpr c true a.2
      emit (.allRight p.2.b.top a.1 p.1) p.2
  | .subObjectPropertyOf _ _ | .equivalentObjectProperties _
  | .inverseObjectProperties _ _ | .transitive _ | .symmetric _ => s
  | .declareClass _ | .declareObjectProperty _ => s

/-- The start state after the prepass: `top` and `bottom` with their two
clauses (newest first). -/
def start (b : EL.St) : St :=
  let t := EL.setTopBottom b
  { b := t, out := [.gci [t.bottom] [], .gci [] [t.top]] }

/-- The full pipeline on an ontology, without the fragment test. -/
def run (O : Ontology) (requested : List IRI) : St × List IRI :=
  let r := EL.internRequested requested {} []
  let s := O.axioms.foldl EL.scanAxiom r.1
  (O.axioms.foldl transAxiom (start s), r.2)

/-! ## From `Nat` indices to `Fin` indices -/

/-- Convert a list of indices, `none` when one is out of range. -/
def finList (n : Nat) : List Nat → List (Fin n) → Option (List (Fin n))
  | [], acc => some acc.reverse
  | k :: ks, acc => if h : k < n then finList n ks (⟨k, h⟩ :: acc) else none

/-- Convert one clause, `none` when an index is out of range. -/
def toFin (n m : Nat) : AC → Option (Ctx.Clause (Fin n) (Fin m))
  | .gci body head =>
      match finList n body [], finList n head [] with
      | some b, some h => some (.gci b h)
      | _, _ => none
  | .exRight a r c =>
      if ha : a < n then if hr : r < m then if hc : c < n then
        some (.exRight ⟨a, ha⟩ ⟨r, hr⟩ ⟨c, hc⟩) else none else none else none
  | .exLeft r d c =>
      if hr : r < m then if hd : d < n then if hc : c < n then
        some (.exLeft ⟨r, hr⟩ ⟨d, hd⟩ ⟨c, hc⟩) else none else none else none
  | .allRight a r c =>
      if ha : a < n then if hr : r < m then if hc : c < n then
        some (.allRight ⟨a, ha⟩ ⟨r, hr⟩ ⟨c, hc⟩) else none else none else none

end ALC

/-- Normalise an OWL ALC ontology into `Ctx` normal clauses; `none` outside
OWL ALC. The inner test never fails (`translateALC_isSome`). -/
def translateALC (O : OWL.Ontology) (requested : List OWL.IRI) : Option ALCTranslation :=
  if O.isALC then
    let r := ALC.run O requested
    let n := r.1.b.cdefs.size
    let m := r.1.b.rdefs.size
    if h : r.2.length ≤ n then
      some { named := r.2, conceptCount := n, roleCount := m, hnamed := h,
             ontology := r.1.out.reverse.filterMap (ALC.toFin n m) }
    else none
  else none

end ContextCalculus.OWLFrontend
