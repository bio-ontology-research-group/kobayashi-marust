import ContextCalculus.OWLFrontend.SRIQTranslate
import ContextCalculus.OWL.FragmentSHIQKB
import ContextCalculus.OWL.Names
import ContextCalculus.SRIQ.ABox

/-!
# OWL SHIQ knowledge bases into `SRIQ` clauses and assertions (stage C1b)

`docs/V1.7.0-C1B-ABOX-DESIGN.md`. `translateSRIQKB O requested extra`
normalises an ontology of the SHIQ knowledge-base part
(`OWL.Ontology.isSHIQKB`) into a `SRIQ` ontology over `Fin conceptCount`
concepts and `Fin roleCount` roles, and an ABox over the individuals
`inds = O.individualNames ++ extra` (individual `a` has index
`inds.idxOf a`).

The TBox part goes through the SHIQ translation (`SRIQT.run`, the pipeline
of `translateSRIQ`) applied to the ontology `kbTBox O base`: the axioms of
`O` that are not assertions, and one axiom per assertion that interns the
names the assertion needs.

* `ClassAssertion(C a)` at position `j` of `O.axioms`: the assertion is
  `X(a)` with `X = assertName base j C`. For a class IRI `C = A`, `X = A`
  and the extra axiom is `SubClassOf(A A)` (it interns `A`). For a complex
  `C`, `X` is the fresh definition name `defName base j` and the extra
  axiom is `SubClassOf(X C)`: the SHIQ translation of `C` does the work,
  and a model of `O` extends to `X` by `X = C`.
* `ObjectPropertyAssertion(r a b)` and its negative: the extra axiom is
  `SubObjectPropertyOf(r r)` (it interns the property IRI of `r`).
* `SameIndividual` gives `same a b` for every ordered pair of members,
  `DifferentIndividuals` gives `diff a b` for every pair in list order.

Fresh names. `defBase O requested` is a prefix longer than every class IRI
of `O` and every requested IRI (`#` padding to the maximal length), and
`defName base j` appends `j` more `#`. So the definition names have
pairwise different lengths, and none is a class IRI of `O` or a requested
IRI. The definition name of position `j` is the only name that depends on
`j`; the positions come from `O.axioms.zipIdx`.

The translation fails (`none`) when a lookup of an index fails; on the
fragment it never does (`translateSRIQKB_isSome`).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

/-- The result of the knowledge-base translation: the requested IRIs
(`named[i]` has concept index `i`), the individuals (individual `a` has
index `inds.idxOf a`), and the TBox and ABox in normal form. -/
structure SRIQKBTranslation where
  named : List OWL.IRI
  inds : List OWL.IRI
  conceptCount : Nat
  roleCount : Nat
  hnamed : named.length ≤ conceptCount
  ontology : SRIQ.Ontology (Fin conceptCount) (Fin roleCount)
  abox : SRIQ.ABox (Fin conceptCount) (Fin roleCount) (Fin inds.length)

namespace SRIQKB

/-- The maximal length of a list of IRIs (`0` for the empty list). -/
def maxLen (l : List IRI) : Nat := l.foldl (fun k s => max k s.length) 0

/-- The prefix of the definition names: longer than every class IRI an
axiom of `O` mentions and than every requested IRI. -/
def defBase (O : Ontology) (requested : List IRI) : String :=
  "urn:km:owl-kb:def:".pushn '#' (maxLen (O.axioms.flatMap Axiom.classNames ++ requested))

/-- The definition name of the class assertion at position `j`. -/
def defName (base : String) (j : Nat) : IRI := base.pushn '#' j

/-- The class name of the class assertion `C(a)` at position `j`: `C`
itself for a class IRI, the definition name otherwise. -/
def assertName (base : String) (j : Nat) : ClassExpr → IRI
  | .cls a => a
  | _ => defName base j

/-- The TBox axioms an assertion adds. -/
def defAxioms (base : String) : Axiom × Nat → List Axiom
  | (.classAssertion c _, j) => [.subClassOf (.cls (assertName base j c)) c]
  | (.objectPropertyAssertion r _ _, _) => [.subObjectPropertyOf [r] r]
  | (.negativeObjectPropertyAssertion r _ _, _) => [.subObjectPropertyOf [r] r]
  | _ => []

/-- The TBox fed to the SHIQ translation: the axioms that are not
assertions, then the axioms the assertions add. -/
def kbTBox (O : Ontology) (base : String) : Ontology :=
  ⟨O.axioms.filter (fun ax => !ax.isAssertion) ++ O.axioms.zipIdx.flatMap (defAxioms base)⟩

/-- The index of a named individual. -/
def indIx (inds : List IRI) : Individual → Option (Fin inds.length)
  | .named a => if h : inds.idxOf a < inds.length then some ⟨_, h⟩ else none
  | .anon _ => none

/-- The concept index of a class IRI in the final state. -/
def clsIx (F : SRIQT.St) (n : Nat) (a : IRI) : Option (Fin n) :=
  F.b.cmap[a]?.bind fun x => if h : x < n then some ⟨x, h⟩ else none

/-- The role term of a basic property in the final state. -/
def roleIx (F : SRIQT.St) (m : Nat) (r : ObjProp) : Option (SRI.RoleT (Fin m)) :=
  F.b.rmap[EL.propIRI r]?.bind fun k => SRIT.finRT m (SRIT.mkRT r k)

/-- `f x` for every `x`, concatenated; `none` if one is `none`. -/
def collect {α β : Type} (f : α → Option (List β)) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, collect f xs with
    | some l, some l' => some (l ++ l')
    | _, _ => none

/-- Every ordered pair of members. -/
def allPairs {α : Type} (as : List α) : List (α × α) :=
  as.flatMap fun a => as.map fun b => (a, b)

/-- Every pair of members in list order. -/
def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ pairsOf l

abbrev KA (n m k : Nat) := SRIQ.Assertion (Fin n) (Fin m) (Fin k)

/-- The assertion `mk i i'` on a pair of individuals. -/
def pairAssert {n m : Nat} (inds : List IRI)
    (mk : Fin inds.length → Fin inds.length → KA n m inds.length) (p : Individual × Individual) :
    Option (List (KA n m inds.length)) :=
  match indIx inds p.1, indIx inds p.2 with
  | some i, some i' => some [mk i i']
  | _, _ => none

/-- The assertions of one axiom at position `j`. -/
def assertsOf (F : SRIQT.St) (base : String) (inds : List IRI) (n m : Nat) :
    Axiom × Nat → Option (List (KA n m inds.length))
  | (.classAssertion c a, j) =>
    match indIx inds a, clsIx F n (assertName base j c) with
    | some i, some x => some [.cls i x]
    | _, _ => none
  | (.objectPropertyAssertion r a b, _) =>
    match indIx inds a, roleIx F m r, indIx inds b with
    | some i, some R, some i' => some [.role i R i']
    | _, _, _ => none
  | (.negativeObjectPropertyAssertion r a b, _) =>
    match indIx inds a, roleIx F m r, indIx inds b with
    | some i, some R, some i' => some [.nrole i R i']
    | _, _, _ => none
  | (.sameIndividual as, _) => collect (pairAssert inds .same) (allPairs as)
  | (.differentIndividuals as, _) => collect (pairAssert inds .diff) (pairsOf as)
  | _ => some []

end SRIQKB

open SRIQKB in
/-- Normalise an OWL SHIQ knowledge base; `none` outside the SHIQ
knowledge-base part. `extra` lists individuals to index beyond those of
`O` (for a query about an individual `O` does not mention). -/
def translateSRIQKB (O : OWL.Ontology) (requested : List OWL.IRI) (extra : List OWL.IRI := []) :
    Option SRIQKBTranslation :=
  if O.isSHIQKB then
    let base := defBase O requested
    let r := SRIQT.run (kbTBox O base) requested
    let inds := O.individualNames ++ extra
    if h : r.2.length ≤ r.1.b.cdefs.size then
      (collect (assertsOf r.1 base inds r.1.b.cdefs.size r.1.b.rdefs.size) O.axioms.zipIdx).map
        fun A =>
          { named := r.2, inds := inds, conceptCount := r.1.b.cdefs.size,
            roleCount := r.1.b.rdefs.size, hnamed := h,
            ontology := r.1.out.reverse.filterMap (SRIQT.toFin r.1.b.cdefs.size r.1.b.rdefs.size),
            abox := A }
    else none
  else none

end ContextCalculus.OWLFrontend
