import ContextCalculus.OWLFrontend.SRITranslate
import ContextCalculus.OWL.FragmentSHIQ
import ContextCalculus.SRIQ.NormalForm

/-!
# OWL SHIQ into the `SRIQ` normal clauses (v1.7.0 stage C1)

`docs/V1.7.0-C1-SHIQ-DESIGN.md`, section 6. `translateSRIQ O requested`
normalises an ontology of the SHIQ part of the frontend fragment
(`OWL.Ontology.isSHIQ`) into `SRIQ.Clause`. It is the SRI translation
(`SRITranslate`) with number restrictions and functionality: the same index
layout, the same state, the same rows for every constructor of the SRI part,
and these new rows (`R` the role term of `r`):

| occurrence | clauses |
|---|---|
| `min 0 r c`, either polarity | none, the index of `top` (`≥ 0` is `Thing`) |
| positive `min (k+1) r c` | `atLeast X (k+1) R Xc⁺` |
| negative `min (k+1) r c` | `gci [] [X, W]`, `atMost W k R Zc⁻` |
| positive `max k r c` | `atMost X k R Zc⁻` |
| negative `max k r c` | `gci [] [X, W]`, `atLeast W (k+1) R Xc⁺` |
| positive `exact k r c` | `atLeast X k R Xc⁺`, `atMost X k R Zc⁻` |
| negative `exact 0 r c` | `gci [] [X, W]`, `atLeast W 1 R Xc⁺` |
| negative `exact (k+1) r c` | `gci [] [X, W₁, W₂]`, `atMost W₁ k R Zc⁻`, `atLeast W₂ (k+2) R Xc⁺` |

A negative occurrence with result `X` satisfies `E ⊑ X`: the definer `W`
stands for the complement of `E` (`¬ ≥ (k+1) R.c` is `≤ k R.c`,
`¬ ≤ k R.c` is `≥ (k+1) R.c`), and `gci [] [X, W]` says every element is
in `X` or in `W`. `Xc⁺` is the positive translation of the filler
(`Xc⁺ ⊑ c`), `Zc⁻` the negative one (`c ⊑ Zc⁻`).

Axioms: those of the SRI translation, and
`FunctionalObjectProperty(r)` is `atMost top 1 R top`,
`InverseFunctionalObjectProperty(r)` is `atMost top 1 R⁻ top`.

The SRI translation cannot be reused by composition: its structural
transformation maps every number restriction, at any depth, to `top`, so the
counting clauses of a nested restriction such as `some r (min 2 s c)` cannot
be added afterwards. This file copies its transformation and adds the rows
above.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

/-- The result of the SHIQ translation: the requested IRIs (duplicates
removed, `named[i]` has concept index `i`) and the normal-form ontology over
`Fin conceptCount` concepts and `Fin roleCount` roles. -/
structure SRIQTranslation where
  named : List OWL.IRI
  conceptCount : Nat
  roleCount : Nat
  hnamed : named.length ≤ conceptCount
  ontology : SRIQ.Ontology (Fin conceptCount) (Fin roleCount)

namespace SRIQT

abbrev QC := SRIQ.Clause Nat Nat
abbrev RT := SRI.RoleT Nat

open SRIT (mkRT)

/-- Translation state: the EL state `b` (maps, meaning tables, `top`,
`bottom`) and the emitted clauses, newest first. -/
structure St where
  b : EL.St
  out : List QC := []

def internC (a : IRI) (s : St) : Nat × St :=
  let r := EL.internC a s.b
  (r.1, { s with b := r.2 })

def internR (r : IRI) (s : St) : Nat × St :=
  let q := EL.internR r s.b
  (q.1, { s with b := q.2 })

def freshC (e : ClassExpr) (s : St) : Nat × St :=
  let r := EL.freshC e s.b
  (r.1, { s with b := r.2 })

def emit (c : QC) (s : St) : St := { s with out := c :: s.out }

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
def emitEach (f : Nat → QC) : List (ClassExpr × Nat) → St → St
  | [], s => s
  | q :: qs, s => emitEach f qs (emit (f q.2) s)

mutual

/-- Structural transformation of one occurrence. `pos = false` is a negative
occurrence (the result `X` satisfies `E ⊑ X`), `pos = true` a positive one
(`X ⊑ E`). Constructors outside the SHIQ part give `top` and no clause. -/
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
  | .min 0 _ _, _, s => (s.b.top, s)
  | .min (k + 1) r c, false, s =>
      let a := roleT r s
      let z := transExpr c false a.2
      let x := freshC (.min (k + 1) r c) z.2
      let w := freshC (.not (.min (k + 1) r c)) x.2
      (x.1, emit (.atMost w.1 k a.1 z.1) (emit (.gci [] [x.1, w.1]) w.2))
  | .min (k + 1) r c, true, s =>
      let a := roleT r s
      let y := transExpr c true a.2
      let x := freshC (.min (k + 1) r c) y.2
      (x.1, emit (.atLeast x.1 (k + 1) a.1 y.1) x.2)
  | .max k r c, false, s =>
      let a := roleT r s
      let y := transExpr c true a.2
      let x := freshC (.max k r c) y.2
      let w := freshC (.not (.max k r c)) x.2
      (x.1, emit (.atLeast w.1 (k + 1) a.1 y.1) (emit (.gci [] [x.1, w.1]) w.2))
  | .max k r c, true, s =>
      let a := roleT r s
      let z := transExpr c false a.2
      let x := freshC (.max k r c) z.2
      (x.1, emit (.atMost x.1 k a.1 z.1) x.2)
  | .exact 0 r c, false, s =>
      let a := roleT r s
      let y := transExpr c true a.2
      let x := freshC (.exact 0 r c) y.2
      let w := freshC (.not (.max 0 r c)) x.2
      (x.1, emit (.atLeast w.1 1 a.1 y.1) (emit (.gci [] [x.1, w.1]) w.2))
  | .exact (k + 1) r c, false, s =>
      let a := roleT r s
      let z := transExpr c false a.2
      let y := transExpr c true z.2
      let x := freshC (.exact (k + 1) r c) y.2
      let w₁ := freshC (.not (.min (k + 1) r c)) x.2
      let w₂ := freshC (.not (.max (k + 1) r c)) w₁.2
      (x.1, emit (.atLeast w₂.1 (k + 2) a.1 y.1) (emit (.atMost w₁.1 k a.1 z.1)
        (emit (.gci [] [x.1, w₁.1, w₂.1]) w₂.2)))
  | .exact k r c, true, s =>
      let a := roleT r s
      let y := transExpr c true a.2
      let z := transExpr c false y.2
      let x := freshC (.exact k r c) z.2
      (x.1, emit (.atMost x.1 k a.1 z.1) (emit (.atLeast x.1 k a.1 y.1) x.2))
  | .oneOf _, _, s | .hasValue .., _, s | .hasSelf _, _, s
  | .dataSome .., _, s | .dataAll .., _, s
  | .dataHasValue .., _, s | .dataMin .., _, s | .dataMax .., _, s
  | .dataExact .., _, s => (s.b.top, s)

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
def emitEquiv (negs poss : List (ClassExpr × Nat)) (out : List QC) : List QC :=
  negs.foldl (fun o n =>
    poss.foldl (fun o p => if n.2 = p.2 then o else .gci [n.2] [p.2] :: o) o) out

/-- `gci [n, m] []` for every pair of members in list order. -/
def emitDisjoint : List (ClassExpr × Nat) → List QC → List QC
  | [], o => o
  | n :: rest, o => emitDisjoint rest (rest.foldl (fun o m => .gci [n.2, m.2] [] :: o) o)

/-- `chain [R] S` for every ordered pair of role terms with `R ≠ S`. -/
def emitRoleEquiv (rs : List RT) (out : List QC) : List QC :=
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
  | .functional r =>
      let a := roleT r s
      emit (.atMost a.2.b.top 1 a.1 a.2.b.top) a.2
  | .inverseFunctional r =>
      let a := roleT r s
      emit (.atMost a.2.b.top 1 a.1.flip a.2.b.top) a.2
  | .declareClass _ | .declareObjectProperty _ => s
  | .disjointUnion .. | .disjointObjectProperties _
  | .reflexive _ | .irreflexive _ | .asymmetric _
  | .subDataPropertyOf .. | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataDomain .. | .dataRange .. | .functionalData _ | .datatypeDefinition ..
  | .hasKey .. | .sameIndividual _ | .differentIndividuals _ | .classAssertion ..
  | .objectPropertyAssertion .. | .negativeObjectPropertyAssertion ..
  | .dataPropertyAssertion .. | .negativeDataPropertyAssertion ..
  | .declareDataProperty _ | .declareNamedIndividual _ | .declareDatatype _
  | .declareAnnotationProperty _ => s

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

open SRIT (finRT finRTs)

/-- Convert one clause, `none` when an index is out of range. -/
def toFin (n m : Nat) : QC → Option (SRIQ.Clause (Fin n) (Fin m))
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
  | .atLeast a k R c =>
      if ha : a < n then if hc : c < n then
        (finRT m R).map fun R' => .atLeast ⟨a, ha⟩ k R' ⟨c, hc⟩
      else none else none
  | .atMost a k R c =>
      if ha : a < n then if hc : c < n then
        (finRT m R).map fun R' => .atMost ⟨a, ha⟩ k R' ⟨c, hc⟩
      else none else none
  | .chain body S =>
      match finRTs m body [], finRT m S with
      | some b, some S' => some (.chain b S')
      | _, _ => none

end SRIQT

/-- Normalise an OWL SHIQ ontology into `SRIQ` normal clauses; `none` outside
the SHIQ part. The inner test never fails (`translateSRIQ_isSome`). -/
def translateSRIQ (O : OWL.Ontology) (requested : List OWL.IRI) : Option SRIQTranslation :=
  if O.isSHIQ then
    let r := SRIQT.run O requested
    let n := r.1.b.cdefs.size
    let m := r.1.b.rdefs.size
    if h : r.2.length ≤ n then
      some { named := r.2, conceptCount := n, roleCount := m, hnamed := h,
             ontology := r.1.out.reverse.filterMap (SRIQT.toFin n m) }
    else none
  else none

end ContextCalculus.OWLFrontend
