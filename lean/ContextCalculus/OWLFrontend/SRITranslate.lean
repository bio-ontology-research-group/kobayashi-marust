import ContextCalculus.OWLFrontend.ALCTranslate
import ContextCalculus.OWL.FragmentSRI
import ContextCalculus.SRI.NormalForm

/-!
# OWL SRI into the `SRI` normal clauses

`docs/V1.6.3-HT-PLAN.md`. `translateSRI O requested` normalises an ontology
of the SRI part of the frontend fragment (`OWL.Ontology.isSRI`) into the
clauses `gci`, `exRight`, `allRight`, `chain` of `SRI.Clause`. It extends the
v1.6.2 ALC translation (`ALCTranslate`) to inverse properties and to the
object-property axioms, and keeps its index layout and its state.

Layout of the concept indices (as in the ALC route): the requested IRIs
(duplicates removed) take `0 .. n-1` in order; then the other class IRIs the
ontology mentions, in first-occurrence order; then `top` (clause
`gci [] [top]`) and `bottom` (clause `gci [bottom] []`); then the definers.
Role indices: the object-property IRIs in first-occurrence order, an
inverse `ObjectInverseOf(r)` sharing the index of `r`.

The role term of an object-property expression is `.pos k` for a property
IRI with index `k` and `.inv k` for its inverse. Below `R` is the role term
of `r` and `R⁻` its flip.

Structural transformation with polarity, one fresh definer per occurrence of
a complex subexpression, as in ALC. The rows that differ from ALC:

| occurrence | clauses |
|---|---|
| negative `some r c` | `allRight Xc⁻ R⁻ X` (`∃R.c ⊑ X` as `c ⊑ ∀R⁻.X`) |
| positive `some r c` | `exRight X R Xc⁺` |
| negative `all r c` | `gci [] [X, W]`, `exRight W R N`, `gci [N, Zc⁻] []` |
| positive `all r c` | `allRight X R Xc⁺` |

Axioms: the class axioms as in ALC; `ObjectPropertyDomain(r C)` is
`allRight top R⁻ X_C⁺`; `ObjectPropertyRange(r C)` is `allRight top R X_C⁺`;
`SubObjectPropertyOf(ObjectPropertyChain(r1 .. rn) s)` is
`chain [R1 .. Rn] S`; `EquivalentObjectProperties` gives `chain [R] S` for
every ordered pair of member role terms with `R ≠ S`;
`InverseObjectProperties(r s)` gives `chain [R] S⁻` and `chain [S] R⁻`;
`TransitiveObjectProperty(r)` is `chain [R, R] R`;
`SymmetricObjectProperty(r)` is `chain [R] R⁻`. Declarations give nothing;
the prepass has already interned their IRIs.

The `Fin`-typed ontology is built once at the end; every index is in range
(`SRITranslateCorrect`), so the conversion drops nothing.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

/-- The result of the SRI translation: the requested IRIs (duplicates
removed, `named[i]` has concept index `i`) and the normal-form ontology over
`Fin conceptCount` concepts and `Fin roleCount` roles. -/
structure SRITranslation where
  named : List OWL.IRI
  conceptCount : Nat
  roleCount : Nat
  hnamed : named.length ≤ conceptCount
  ontology : SRI.Ontology (Fin conceptCount) (Fin roleCount)

namespace SRIT

abbrev SC := SRI.Clause Nat Nat
abbrev RT := SRI.RoleT Nat

/-- Translation state: the EL state `b` (maps, meaning tables, `top`,
`bottom`) and the emitted clauses, newest first. -/
structure St where
  b : EL.St
  out : List SC := []

def internC (a : IRI) (s : St) : Nat × St :=
  let r := EL.internC a s.b
  (r.1, { s with b := r.2 })

def internR (r : IRI) (s : St) : Nat × St :=
  let q := EL.internR r s.b
  (q.1, { s with b := q.2 })

def freshC (e : ClassExpr) (s : St) : Nat × St :=
  let r := EL.freshC e s.b
  (r.1, { s with b := r.2 })

def emit (c : SC) (s : St) : St := { s with out := c :: s.out }

/-- The role term of an object-property expression whose IRI has index `k`. -/
def mkRT : ObjProp → Nat → RT
  | .named _, k => .pos k
  | .inv _, k => .inv k

/-- The role term of `r`, interning its IRI. -/
def roleT (r : ObjProp) (s : St) : RT × St :=
  let a := internR (EL.propIRI r) s
  (mkRT r a.1, a.2)

/-- The role terms of a list of object-property expressions, in order. -/
def roleTs : List ObjProp → St → List RT → List RT × St
  | [], s, acc => (acc.reverse, s)
  | r :: rs, s, acc =>
      let a := roleT r s
      roleTs rs a.2 (a.1 :: acc)

/-- `f k` for every member index `k`. -/
def emitEach (f : Nat → SC) : List (ClassExpr × Nat) → St → St
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
      let a := roleT r s
      let y := transExpr c false a.2
      let x := freshC (.some r c) y.2
      (x.1, emit (.allRight y.1 a.1.flip x.1) x.2)
  | .some r c, true, s =>
      let a := roleT r s
      let y := transExpr c true a.2
      let x := freshC (.some r c) y.2
      (x.1, emit (.exRight x.1 a.1 y.1) x.2)
  | .all r c, false, s =>
      let a := roleT r s
      let z := transExpr c false a.2
      let x := freshC (.all r c) z.2
      let w := freshC (.some r (.not c)) x.2
      let n := freshC (.not c) w.2
      (x.1, emit (.gci [n.1, z.1] []) (emit (.exRight w.1 a.1 n.1)
        (emit (.gci [] [x.1, w.1]) n.2)))
  | .all r c, true, s =>
      let a := roleT r s
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
def emitEquiv (negs poss : List (ClassExpr × Nat)) (out : List SC) : List SC :=
  negs.foldl (fun o n =>
    poss.foldl (fun o p => if n.2 = p.2 then o else .gci [n.2] [p.2] :: o) o) out

/-- `gci [n, m] []` for every pair of members in list order. -/
def emitDisjoint : List (ClassExpr × Nat) → List SC → List SC
  | [], o => o
  | n :: rest, o => emitDisjoint rest (rest.foldl (fun o m => .gci [n.2, m.2] [] :: o) o)

/-- `chain [R] S` for every ordered pair of role terms with `R ≠ S`. -/
def emitRoleEquiv (rs : List RT) (out : List SC) : List SC :=
  rs.foldl (fun o R => rs.foldl (fun o S => if R = S then o else .chain [R] S :: o) o) out

/-- Translate one axiom. -/
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
      let a := roleT r s
      let p := transExpr c true a.2
      emit (.allRight p.2.b.top a.1.flip p.1) p.2
  | .range r c =>
      let a := roleT r s
      let p := transExpr c true a.2
      emit (.allRight p.2.b.top a.1 p.1) p.2
  | .subObjectPropertyOf rs r =>
      let l := roleTs rs s []
      let a := roleT r l.2
      emit (.chain l.1 a.1) a.2
  | .equivalentObjectProperties rs =>
      let l := roleTs rs s []
      { l.2 with out := emitRoleEquiv l.1 l.2.out }
  | .inverseObjectProperties r r' =>
      let a := roleT r s
      let b := roleT r' a.2
      emit (.chain [b.1] a.1.flip) (emit (.chain [a.1] b.1.flip) b.2)
  | .transitive r =>
      let a := roleT r s
      emit (.chain [a.1, a.1] a.1) a.2
  | .symmetric r =>
      let a := roleT r s
      emit (.chain [a.1] a.1.flip) a.2
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

/-- Convert a role term, `none` when its index is out of range. -/
def finRT (m : Nat) : RT → Option (SRI.RoleT (Fin m))
  | .pos r => if h : r < m then some (.pos ⟨r, h⟩) else none
  | .inv r => if h : r < m then some (.inv ⟨r, h⟩) else none

/-- Convert a list of role terms, `none` when one is out of range. -/
def finRTs (m : Nat) : List RT → List (SRI.RoleT (Fin m)) → Option (List (SRI.RoleT (Fin m)))
  | [], acc => some acc.reverse
  | R :: Rs, acc =>
      match finRT m R with
      | some R' => finRTs m Rs (R' :: acc)
      | none => none

/-- Convert one clause, `none` when an index is out of range. -/
def toFin (n m : Nat) : SC → Option (SRI.Clause (Fin n) (Fin m))
  | .gci body head =>
      match ALC.finList n body [], ALC.finList n head [] with
      | some b, some h => some (.gci b h)
      | _, _ => none
  | .exRight a R c =>
      if ha : a < n then if hc : c < n then
        (finRT m R).map fun R' => .exRight ⟨a, ha⟩ R' ⟨c, hc⟩
      else none else none
  | .allRight a R c =>
      if ha : a < n then if hc : c < n then
        (finRT m R).map fun R' => .allRight ⟨a, ha⟩ R' ⟨c, hc⟩
      else none else none
  | .chain body S =>
      match finRTs m body [], finRT m S with
      | some b, some S' => some (.chain b S')
      | _, _ => none

end SRIT

/-- Normalise an OWL SRI ontology into `SRI` normal clauses; `none` outside
the SRI fragment. The inner test never fails (`translateSRI_isSome`). -/
def translateSRI (O : OWL.Ontology) (requested : List OWL.IRI) : Option SRITranslation :=
  if O.isSRI then
    let r := SRIT.run O requested
    let n := r.1.b.cdefs.size
    let m := r.1.b.rdefs.size
    if h : r.2.length ≤ n then
      some { named := r.2, conceptCount := n, roleCount := m, hnamed := h,
             ontology := r.1.out.reverse.filterMap (SRIT.toFin n m) }
    else none
  else none

end ContextCalculus.OWLFrontend
