import ContextCalculus.OWL.Fragment
import ContextCalculus.ELCompletion
import Std.Data.HashMap

/-!
# OWL EL into the ELC normal forms NF1 to NF7

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7, EL route. `translateEL O requested`
normalises an OWL EL ontology (`OWL.Ontology.isEL`) into the clause shapes of
`ELCompletion` that `ELReference.referenceBit` decides exactly.

Layout of the concept indices: the requested IRIs (duplicates removed) take
`0 .. n-1` in order; then the other class IRIs the ontology mentions, in
first-occurrence order; then `top` and `bottom`; then the definers of the
structural transformation. Role indices: the object-property IRIs in
first-occurrence order, then the fresh roles that split chains longer than
two.

Structural transformation with polarity (Plaisted-Greenbaum), one fresh
definer per occurrence of a complex subexpression:

- negative occurrence `E` (left of `⊑`): a definer `X` with clauses for
  `E ⊑ X`; positive occurrence (right of `⊑`): clauses for `X ⊑ E`;
- `owl:Thing` is `top`, `owl:Nothing` is `bottom`, a class IRI is its index;
- negative `and [c1, .., cn]` is a binary `nf2` chain through fresh definers
  (`and []` is `top`); positive `and` gives `nf1 X Xi` per conjunct;
- negative `some r c` is `nf4 r Xc X`, positive `some r c` is `nf3 X r Xc`.

Axioms: `SubClassOf(C D)` is `nf1 X_C X_D`; `EquivalentClasses` gives `nf1`
both ways for every pair of members (pairs with equal indices are skipped);
`DisjointClasses` gives `nf2 X_Ci X_Cj bottom` for every pair `i < j`;
`ObjectPropertyDomain(r C)` is `nf4 r top X_C`; a role chain of length 1 is
`nf6`, of length 2 `nf7`, longer chains split through fresh roles; an empty
chain (outside OWL EL) is `reflexive`; `TransitiveObjectProperty(r)` is
`nf7 r r r`; `EquivalentObjectProperties` gives `nf6` both ways for every
pair. Declarations produce nothing.

The state records, for every concept index, the class expression it stands
for (`cdefs`), and for every role index the reversed chain of property IRIs
whose composition it stands for (`rdefs`). The correctness proof
(`ELTranslateCorrect`) reads both; the reasoner does not.

Compiled code recurses only over the depth of one class expression and the
length of one role chain; loops over axioms, members and requested names
are tail recursive or `foldl`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

/-- The result of the EL translation: the requested IRIs (duplicates removed,
`named[i]` has concept index `i`), the indices of `top` and `bottom`, and the
normal-form ontology. -/
structure ELTranslation where
  named : List OWL.IRI
  top : Nat
  bottom : Nat
  ontology : ELCompletion.Ontology Nat Nat

namespace EL

abbrev NF := ELCompletion.Clause Nat Nat

/-- Translation state. -/
structure St where
  cmap : Std.HashMap IRI Nat := {}
  /-- `cdefs[k]` is the class expression that concept index `k` stands for. -/
  cdefs : Array ClassExpr := #[]
  rmap : Std.HashMap IRI Nat := {}
  /-- `rdefs[k]` is the reversed list of property IRIs whose composition role
  index `k` stands for. -/
  rdefs : Array (List IRI) := #[]
  /-- Emitted clauses, newest first. -/
  out : List NF := []
  top : Nat := 0
  bottom : Nat := 0

/-- The index of the class IRI `a`, allocated on first use. -/
def internC (a : IRI) (s : St) : Nat × St :=
  match s.cmap[a]? with
  | some k => (k, s)
  | none => (s.cdefs.size,
      { s with cmap := s.cmap.insert a s.cdefs.size, cdefs := s.cdefs.push (.cls a) })

/-- The index of the object-property IRI `r`, allocated on first use. -/
def internR (r : IRI) (s : St) : Nat × St :=
  match s.rmap[r]? with
  | some k => (k, s)
  | none => (s.rdefs.size,
      { s with rmap := s.rmap.insert r s.rdefs.size, rdefs := s.rdefs.push [r] })

/-- A fresh definer standing for `e`. -/
def freshC (e : ClassExpr) (s : St) : Nat × St :=
  (s.cdefs.size, { s with cdefs := s.cdefs.push e })

/-- A fresh role standing for the composition of `rev.reverse`. -/
def freshR (rev : List IRI) (s : St) : Nat × St :=
  (s.rdefs.size, { s with rdefs := s.rdefs.push rev })

def emit (c : NF) (s : St) : St := { s with out := c :: s.out }

/-- The property IRI of an object-property expression (inverses are outside
OWL EL and never reach the translation). -/
def propIRI : ObjProp → IRI
  | .named r => r
  | .inv r => r

mutual

/-- Structural transformation of one occurrence. `pos = false` is a negative
occurrence (the result `X` satisfies `E ⊑ X`), `pos = true` a positive one
(`X ⊑ E`). Constructors outside OWL EL give `top` and no clause. -/
def transExpr : ClassExpr → Bool → St → Nat × St
  | .cls a, _, s => internC a s
  | .thing, _, s => (s.top, s)
  | .nothing, _, s => (s.bottom, s)
  | .and cs, false, s => transNegAnd cs none s
  | .and cs, true, s =>
      let x := freshC (.and cs) s
      (x.1, transPosAnd cs x.1 x.2)
  | .some r c, false, s =>
      let a := internR (propIRI r) s
      let y := transExpr c false a.2
      let x := freshC (.some r c) y.2
      (x.1, emit (.nf4 a.1 y.1 x.1) x.2)
  | .some r c, true, s =>
      let a := internR (propIRI r) s
      let y := transExpr c true a.2
      let x := freshC (.some r c) y.2
      (x.1, emit (.nf3 x.1 a.1 y.1) x.2)
  | .or _, _, s => (s.top, s)
  | .not _, _, s => (s.top, s)
  | .all _ _, _, s => (s.top, s)

/-- Negative conjunction: a left-nested `nf2` chain. The accumulator holds
the index and the expression of the conjunction of the conjuncts so far. -/
def transNegAnd : List ClassExpr → Option (Nat × ClassExpr) → St → Nat × St
  | [], none, s => (s.top, s)
  | [], some (a, _), s => (a, s)
  | c :: cs, none, s =>
      let y := transExpr c false s
      transNegAnd cs (some (y.1, c)) y.2
  | c :: cs, some (a, e), s =>
      let y := transExpr c false s
      let x := freshC (.and [e, c]) y.2
      transNegAnd cs (some (x.1, .and [e, c])) (emit (.nf2 a y.1 x.1) x.2)

/-- Positive conjunction: `nf1 x Xi` for every conjunct. -/
def transPosAnd : List ClassExpr → Nat → St → St
  | [], _, s => s
  | c :: cs, x, s =>
      let y := transExpr c true s
      transPosAnd cs x (emit (.nf1 x y.1) y.2)

end

/-- Translate the members of an n-ary class axiom, keeping each member next
to its index. -/
def transMembers (pos : Bool) :
    List ClassExpr → St → List (ClassExpr × Nat) → List (ClassExpr × Nat) × St
  | [], s, acc => (acc.reverse, s)
  | c :: cs, s, acc =>
      let y := transExpr c pos s
      transMembers pos cs y.2 ((c, y.1) :: acc)

/-- `nf1 n p` for every negative member index `n` and positive member index
`p` with `n ≠ p`. -/
def emitEquiv (negs poss : List (ClassExpr × Nat)) (out : List NF) : List NF :=
  negs.foldl (fun o n =>
    poss.foldl (fun o p => if n.2 = p.2 then o else .nf1 n.2 p.2 :: o) o) out

/-- `nf2 n m bottom` for every pair of members in list order. -/
def emitDisjoint (bottom : Nat) : List (ClassExpr × Nat) → List NF → List NF
  | [], o => o
  | n :: rest, o => emitDisjoint bottom rest (rest.foldl (fun o m => .nf2 n.2 m.2 bottom :: o) o)

/-- Intern a list of object properties, each next to its index, newest
first. -/
def internRoles : List ObjProp → St → List (ObjProp × Nat) → List (ObjProp × Nat) × St
  | [], s, acc => (acc, s)
  | r :: rs, s, acc =>
      let a := internR (propIRI r) s
      internRoles rs a.2 ((r, a.1) :: acc)

/-- `nf6 a b` for every pair of role indices with `a ≠ b`. -/
def emitRoleEquiv (roles : List (ObjProp × Nat)) (out : List NF) : List NF :=
  roles.foldl (fun o a =>
    roles.foldl (fun o b => if a.2 = b.2 then o else .nf6 a.2 b.2 :: o) o) out

/-- Split a role chain. `acc` stands for the composition of `pre.reverse`;
the clauses make `acc ∘ rest ⊑ sup`. -/
def transChain (sup : Nat) : Nat → List IRI → List IRI → St → St
  | acc, _, [], s => emit (.nf6 acc sup) s
  | acc, _, [r], s =>
      let a := internR r s
      emit (.nf7 acc a.1 sup) a.2
  | acc, pre, r :: rest@(_ :: _), s =>
      let a := internR r s
      let u := freshR (r :: pre) a.2
      transChain sup u.1 (r :: pre) rest (emit (.nf7 acc a.1 u.1) u.2)

/-- Translate one axiom. Axioms outside OWL EL produce nothing. -/
def transAxiom (s : St) : Axiom → St
  | .subClassOf c d =>
      let n := transExpr c false s
      let p := transExpr d true n.2
      emit (.nf1 n.1 p.1) p.2
  | .equivalentClasses cs =>
      let n := transMembers false cs s []
      let p := transMembers true cs n.2 []
      { p.2 with out := emitEquiv n.1 p.1 p.2.out }
  | .disjointClasses cs =>
      let n := transMembers false cs s []
      { n.2 with out := emitDisjoint n.2.bottom n.1 n.2.out }
  | .domain r c =>
      let a := internR (propIRI r) s
      let p := transExpr c true a.2
      emit (.nf4 a.1 p.2.top p.1) p.2
  | .subObjectPropertyOf rs r =>
      let a := internR (propIRI r) s
      match rs with
      | [] => emit (.reflexive a.1) a.2
      | r1 :: rest =>
          let b := internR (propIRI r1) a.2
          transChain a.1 b.1 [propIRI r1] (rest.map propIRI) b.2
  | .equivalentObjectProperties rs =>
      let a := internRoles rs s []
      { a.2 with out := emitRoleEquiv a.1 a.2.out }
  | .transitive r =>
      let a := internR (propIRI r) s
      emit (.nf7 a.1 a.1 a.1) a.2
  | .range _ _ | .inverseObjectProperties _ _ | .symmetric _ => s
  | .declareClass _ | .declareObjectProperty _ => s

/-! ## Index layout prepass -/

mutual

/-- Intern the class and property IRIs of `E` in first-occurrence order. -/
def scanExpr : ClassExpr → St → St
  | .cls a, s => (internC a s).2
  | .thing, s => s
  | .nothing, s => s
  | .and cs, s => scanList cs s
  | .or cs, s => scanList cs s
  | .not c, s => scanExpr c s
  | .some r c, s => scanExpr c (internR (propIRI r) s).2
  | .all r c, s => scanExpr c (internR (propIRI r) s).2

def scanList : List ClassExpr → St → St
  | [], s => s
  | c :: cs, s => scanList cs (scanExpr c s)

end

def scanRoles (rs : List ObjProp) (s : St) : St :=
  rs.foldl (fun s r => (internR (propIRI r) s).2) s

def scanAxiom (s : St) : Axiom → St
  | .subClassOf c d => scanExpr d (scanExpr c s)
  | .equivalentClasses cs | .disjointClasses cs => scanList cs s
  | .domain r c | .range r c => scanExpr c (internR (propIRI r) s).2
  | .subObjectPropertyOf rs r => (internR (propIRI r) (scanRoles rs s)).2
  | .equivalentObjectProperties rs => scanRoles rs s
  | .inverseObjectProperties r r' => scanRoles [r, r'] s
  | .transitive r | .symmetric r => (internR (propIRI r) s).2
  | .declareClass a => (internC a s).2
  | .declareObjectProperty r => (internR r s).2

/-- Intern the requested IRIs in order; the second component lists the IRIs
that received a new index, in order (the requested list without
duplicates). -/
def internRequested : List IRI → St → List IRI → St × List IRI
  | [], s, acc => (s, acc.reverse)
  | a :: as, s, acc =>
      if s.cmap.contains a then internRequested as s acc
      else internRequested as (internC a s).2 (a :: acc)

/-- Allocate `top` and `bottom` after the names; no clause yet. -/
def setTopBottom (s : St) : St :=
  { s with
    out := []
    top := s.cdefs.size
    bottom := s.cdefs.size + 1
    cdefs := (s.cdefs.push .thing).push .nothing }

/-- The full pipeline on an ontology, without the fragment test. -/
def run (O : Ontology) (requested : List IRI) : St × List IRI :=
  let r := internRequested requested {} []
  let s := O.axioms.foldl scanAxiom r.1
  (O.axioms.foldl transAxiom (setTopBottom s), r.2)

end EL

/-- Normalise an OWL EL ontology into NF1 to NF7; `none` outside OWL EL. -/
def translateEL (O : OWL.Ontology) (requested : List OWL.IRI) : Option ELTranslation :=
  if O.isEL then
    let r := EL.run O requested
    some { named := r.2, top := r.1.top, bottom := r.1.bottom, ontology := r.1.out.reverse }
  else none

end ContextCalculus.OWLFrontend
