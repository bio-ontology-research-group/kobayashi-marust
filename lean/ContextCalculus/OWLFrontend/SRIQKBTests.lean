import ContextCalculus.OWLFrontend.SRIQKBReference

/-!
# Tests for the SHIQ knowledge-base route

The translation of assertions (`translateSRIQKB`), the hint parser, and the
answers of `owlSHIQKBReference`, `owlTypeRow` and `owlSameRow` on small
knowledge bases. The procedures underneath enumerate every record and every
realisation, so each input keeps at most six concept indices and three
individuals. Times with the interpreter of `#guard` (ws, 2026-11-14): under
0.4 s for each check on two or three concept indices, about 6 s for each of
the three checks on `Oab` (six concept indices with the complement name),
about 9 s for the equality that is not entailed (an exhaustive search over
three individuals); the whole file takes about 40 s. The compiled
`km-owl-reference --procedure sriq-kb` runs the inputs of
`testdata/sriq-kb/` in 0.3 s to 2 s each.

Layout as in `SRIQTranslateTests`: requested names first, then the other
class IRIs (including the class names of class assertions), `top` and
`bottom`, then the definers. Individuals follow `O.individualNames`.
-/

namespace ContextCalculus.OWLFrontend.SRIQKBTests

open ContextCalculus.OWL

def unfinRT {m : Nat} : SRI.RoleT (Fin m) → SRI.RoleT Nat
  | .pos r => .pos r.val
  | .inv r => .inv r.val

def unfin {n m : Nat} : SRIQ.Clause (Fin n) (Fin m) → SRIQ.Clause Nat Nat
  | .gci b h => .gci (b.map Fin.val) (h.map Fin.val)
  | .exRight a R c => .exRight a.val (unfinRT R) c.val
  | .allRight a R c => .allRight a.val (unfinRT R) c.val
  | .atLeast a k R c => .atLeast a.val k (unfinRT R) c.val
  | .atMost a k R c => .atMost a.val k (unfinRT R) c.val
  | .chain body S => .chain (body.map unfinRT) (unfinRT S)

def unfinA {n m k : Nat} : SRIQ.Assertion (Fin n) (Fin m) (Fin k) → SRIQ.Assertion Nat Nat Nat
  | .cls a X => .cls a.val X.val
  | .role a R b => .role a.val (unfinRT R) b.val
  | .nrole a R b => .nrole a.val (unfinRT R) b.val
  | .same a b => .same a.val b.val
  | .diff a b => .diff a.val b.val

/-- The individuals, clauses and assertions of the translation. -/
def kb (O : Ontology) (requested : List IRI) :
    Option (List IRI × List (SRIQ.Clause Nat Nat) × List (SRIQ.Assertion Nat Nat Nat)) :=
  (translateSRIQKB O requested).map fun T => (T.inds, T.ontology.map unfin, T.abox.map unfinA)

/-- The rows of the route as `(sub, unsat, sups)`. -/
def rowsOf (O : Ontology) (requested : List IRI) (hint : Option RawHint) :
    Option (List (Nat × Bool × List Nat)) :=
  (owlSHIQKBReference O requested hint).map fun a => a.rows.map fun r => (r.sub, r.unsat, r.sups)

/-- The hint check alone (`checkRealisation` on the encoding). -/
def hintAccepted (O : Ontology) (requested : List IRI) (h : RawHint) : Option Bool :=
  (translateSRIQKB O requested).map fun T =>
    (kbHint T (some h)).any (SRIQ.Proc.checkRealisation (SRIQ.Proc.encTransQ T.ontology).2
      (SRIQ.Proc.encABox T.ontology T.abox))

/-- The hint check of `owlTypeRow` alone. -/
def typeHintAccepted (O : Ontology) (C a : IRI) (h : RawHint) : Option Bool :=
  (translateSRIQKB O [C] [a]).bind fun T =>
    if hC : 0 < T.named.length then
      if ha : T.inds.idxOf a < T.inds.length then
        let O' := SRIQ.Proc.complO T.ontology ⟨0, Nat.lt_of_lt_of_le hC T.hnamed⟩
        let A' := SRIQ.Proc.complA T.abox ⟨_, ha⟩
        some ((h.toHint _ _ _).any (SRIQ.Proc.checkRealisation (SRIQ.Proc.encTransQ O').2
          (SRIQ.Proc.encABox O' A')))
      else none
    else none

/-- A hint from its text; the empty hint when the text does not parse. -/
def hint (text : String) : RawHint := (RawHint.parseHint text).toOption.getD {}

def r : ObjProp := .named "r"
def si : ObjProp := .inv "s"
def A : ClassExpr := .cls "A"
def B : ClassExpr := .cls "B"
def a : Individual := .named "a"
def b : Individual := .named "b"
def c : Individual := .named "c"

/-! ## The translation of assertions -/

/- `(∀r.B)(a)`, `r(a,b)`, `¬s⁻(b,a)`, `a = b`, `a, b, c` pairwise
different, `B(c)`; requested `B`. `B = 0`, the definition name `X = 1` of
the first assertion, `top = 2`, `bottom = 3`, the `∀` definer `4`. Roles
`r = 0`, `s = 1`; individuals `a, b, c = 0, 1, 2`. `X ⊑ ∀r.B` gives
`gci [1] [4]` and `allRight 4 r 0`; the role assertions intern their
roles with `chain [R] R`; `B(c)` interns `B` with `gci [0] [0]`. -/
#guard kb ⟨[.classAssertion (.all r B) a, .objectPropertyAssertion r a b,
    .negativeObjectPropertyAssertion si b a, .sameIndividual [a, b],
    .differentIndividuals [a, b, c], .classAssertion B c]⟩ ["B"] ==
  some (["a", "b", "c"],
    [.gci [] [2], .gci [3] [], .allRight 4 (.pos 0) 0, .gci [1] [4], .chain [.pos 0] (.pos 0),
      .chain [.inv 1] (.inv 1), .gci [0] [0]],
    [.cls 0 1, .role 0 (.pos 0) 1, .nrole 1 (.inv 1) 0, .same 0 0, .same 0 1, .same 1 0,
      .same 1 1, .diff 0 1, .diff 0 2, .diff 1 2, .cls 2 0])

/- Anonymous individuals are declined. -/
#guard (kb ⟨[.classAssertion A (.anon "x")]⟩ []).isNone
/- Data assertions are outside the fragment. -/
#guard (kb ⟨[.dataPropertyAssertion (.named "p") a ⟨"1", "xsd:int", none⟩]⟩ []).isNone
/- A negative assertion on a transitive role: the translation succeeds, the
route declines (`negSimpleB` fails). -/
#guard (kb ⟨[.transitive r, .negativeObjectPropertyAssertion r a b]⟩ []).isSome
#guard (owlSHIQKBReference ⟨[.transitive r, .negativeObjectPropertyAssertion r a b]⟩ [] none).isNone

/-! ## The hint format -/

#guard reprStr (RawHint.parseHint "blocks 2\nblk 0 1 1 # a comment\nty 0 2\nlab 0 1 +0 -1\n\nkid 1 +0 / 2 3\n") ==
  reprStr (Except.ok (ε := String)
    ({ nb := 2, blk := [0, 1, 1], ty := [(0, [2])], lab := [(0, 1, [.pos 0, .inv 1])],
       kids := [(1, [.pos 0], [2, 3])] } : RawHint))
#guard reprStr (RawHint.parseHint "blocks 2\nfoo 1") ==
  reprStr (Except.error (α := RawHint) "unknown directive: foo")
#guard reprStr (RawHint.parseHint "lab 0 1 r") ==
  reprStr (Except.error (α := RawHint) "not a role (+k or -k): r")

/-! ## Consistency (requested `A`, not in the ontology: `A = 0`, `top = 1`,
`bottom = 2`; role `r = 0`) -/

/-- `r` functional, `r(a,a)`, `r(a,b)`, `a ≠ b`: inconsistent. -/
def Oinc : Ontology :=
  ⟨[.functional r, .objectPropertyAssertion r a a, .objectPropertyAssertion r a b,
    .differentIndividuals [a, b]]⟩

-- Every requested IRI is below every requested IRI.
#guard rowsOf Oinc ["A"] none == some [(0, true, [])]

/-- `r` functional, `r(a,b)`, `r(a,c)`: consistent, with `b` and `c` in one
block. -/
def Omerge : Ontology :=
  ⟨[.functional r, .objectPropertyAssertion r a b, .objectPropertyAssertion r a c]⟩

def Hmerge : RawHint := hint "blocks 2\nblk 0 1 1\nty 0 1\nty 1 1\nlab 0 1 +0\n"

#guard hintAccepted Omerge ["A"] Hmerge == some true
#guard rowsOf Omerge ["A"] (some Hmerge) == some [(0, false, [0])]
-- Without the merge the hint fails: `a` has two `r`-successors.
#guard hintAccepted Omerge ["A"] (hint "blocks 3\nblk 0 1 2\nty 0 1\nty 1 1\nty 2 1\nlab 0 1 +0\nlab 0 2 +0\n") ==
  some false

/-- `r` functional, `r(a,a)`, `r(a,b)`: consistent, with `a` and `b` in one
block. -/
def Otwo : Ontology :=
  ⟨[.functional r, .objectPropertyAssertion r a a, .objectPropertyAssertion r a b]⟩

/-- `a` and `b` in two blocks: two `r`-successors of `a`. -/
def Htwo : RawHint := hint "blocks 2\nblk 0 1\nty 0 1\nty 1 1\nlab 0 0 +0\nlab 0 1 +0\n"

-- The bad hint fails its check, and the search finds the merged block.
#guard hintAccepted Otwo ["A"] Htwo == some false
#guard rowsOf Otwo ["A"] (some Htwo) == some [(0, false, [0])]
-- A hint that does not fit the translation counts as no hint.
#guard rowsOf Otwo ["A"] (some (hint "blocks 1\nblk 0\nty 0 7\n")) == some [(0, false, [0])]

/-! ## Realization -/

/-- `A ⊑ ∀r.B`, `A(a)`, `r(a,b)`. For `owlTypeRow` with `C = B`: `B = 0`,
`A = 1`, `top = 2`, `bottom = 3`, the `∀` definer `4`, the complement of
`B` is `5`; individuals `a = 0`, `b = 1`. -/
def Oab : Ontology :=
  ⟨[.subClassOf A (.all r B), .classAssertion A a, .objectPropertyAssertion r a b]⟩

-- `B(b)` follows through the role assertion and the universal restriction.
#guard owlTypeRow Oab "B" "b" none == some true

/-- A countermodel for `B(a)`: `a` in `A`, the definer and the complement
of `B`; `b` in `B`. -/
def Hab : RawHint := hint "blocks 2\nblk 0 1\nty 0 1 2 4 5\nty 1 0 2\nlab 0 1 +0\n"

#guard typeHintAccepted Oab "B" "a" Hab == some true
#guard owlTypeRow Oab "B" "a" (some Hab) == some false
-- `B(c)` for an individual the ontology does not mention: not entailed.
#guard owlTypeRow ⟨[.objectPropertyAssertion r a b]⟩ "B" "c" none == some false

-- Functionality forces `a = b` in `Otwo` and `b = c` in `Omerge`; nothing
-- forces `a = b` in `Omerge`.
#guard owlSameRow Otwo "a" "b" none == some true
#guard owlSameRow Omerge "b" "c" none == some true
#guard owlSameRow Omerge "a" "b" none == some false

end ContextCalculus.OWLFrontend.SRIQKBTests
