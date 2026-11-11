import ContextCalculus.ALCCommonSourceRecognizer

/-!
# Unit tests for `ALCCommonSourceRecognizer`

Executable checks (`#eval` and `by decide`) for `recognizeALC`, covering:
- disjunctive GCIs forcing a subsumption (`A ⊑ B ⊔ C`, `B ⊑ D`, `C ⊑ D`),
- existential plus universal restrictions with per-clause variable renaming and
  permuted body literals (`A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `B ⊓ C ⊑ BC`, `∃r.BC ⊑ D`),
- an unsatisfiable concept via an empty-head GCI (`B ⊑ ⊥`, `A ⊑ ∃r.B`),
- fail-closed rejections on equalities, constants, nested function terms,
  unmatched or mismatched Skolem halves, duplicate Skolem functions, and role
  clauses outside the ALC table.
-/

namespace ContextCalculus.ALCCommonSourceRecognizerTests

open ContextCalculus.CheckerTerm
open ContextCalculus.ALCReference
open ContextCalculus.ALCCommonSourceRecognizer

private def C (iri : Nat) (t : FTerm) : FLit := .P (.concept iri t)
private def R (iri : Nat) (s t : FTerm) : FLit := .P (.role iri s t)
private def x : FTerm := .var 0
private def y : FTerm := .var (-1)

/-- Helper that runs `recognizeALC` and checks `alcBit` on `(sub, sup)`. -/
def recognizedBit (named : List Nat) (source : List FCL)
    (sub sup : Nat) : Option Bool := do
  let r ← recognizeALC named source
  let i ← r.conceptIndex sub
  let j ← r.conceptIndex sup
  some (alcBit r.ontology i j)

/-- 1. Disjunctive GCI (`A = 10, B = 20, C = 30, D = 40`, plus unused requested
concept `50`): `A ⊑ B ⊔ C`, `B ⊑ D`, `C ⊑ D` entails `A ⊑ D`. -/
def disjunctiveSource : List FCL :=
  [ ⟨[C 10 x], [C 20 x, C 30 x]⟩
  , ⟨[C 20 x], [C 40 x]⟩
  , ⟨[C 30 (.var 5)], [C 40 (.var 5)]⟩ ]

#eval recognizeALC [10, 20, 30, 40, 50] disjunctiveSource
#eval recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 10 40
#eval recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 10 20
#eval recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 10 50

example : (recognizeALC [10, 20, 30, 40, 50] disjunctiveSource).isSome = true := by decide
example : recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 10 40 = some true := by decide
example : recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 10 20 = some false := by decide
example : recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 10 50 = some false := by decide
example : recognizedBit [10, 20, 30, 40, 50] disjunctiveSource 50 50 = some true := by decide

/-- 2. Existential plus universal (`A = 0, B = 1, C = 2, BC = 3, D = 4`,
role `r = 0`, Skolem function `7`, permuted body order and renamed variables):
`A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `B ⊓ C ⊑ BC`, `∃r.BC ⊑ D` entails `A ⊑ D`. -/
def exAllSource : List FCL :=
  [ ⟨[C 0 x], [R 0 x (.app 7 x)]⟩
  , ⟨[C 0 x], [C 1 (.app 7 x)]⟩
  , ⟨[R 0 (.var 2) (.var (-3)), C 0 (.var 2)], [C 2 (.var (-3))]⟩
  , ⟨[C 2 x, C 1 x], [C 3 x]⟩
  , ⟨[R 0 x y, C 3 y], [C 4 x]⟩ ]

#eval recognizeALC [0, 1, 2, 3, 4] exAllSource
#eval recognizedBit [0, 1, 2, 3, 4] exAllSource 0 4
#eval recognizedBit [0, 1, 2, 3, 4] exAllSource 4 0

example : (recognizeALC [0, 1, 2, 3, 4] exAllSource).isSome = true := by decide
example : recognizedBit [0, 1, 2, 3, 4] exAllSource 0 4 = some true := by decide
example : recognizedBit [0, 1, 2, 3, 4] exAllSource 4 0 = some false := by decide

/-- 3. Unsatisfiable concept via empty-head GCI (`B = 1` has `B ⊑ ⊥`, `A = 0`
has `A ⊑ ∃r.B`, `C = 2` is unconstrained). -/
def unsatSource : List FCL :=
  [ ⟨[C 1 x], []⟩
  , ⟨[C 0 x], [R 0 x (.app 3 x)]⟩
  , ⟨[C 0 x], [C 1 (.app 3 x)]⟩ ]

#eval recognizeALC [0, 1, 2] unsatSource
#eval recognizedBit [0, 1, 2] unsatSource 1 2
#eval recognizedBit [0, 1, 2] unsatSource 0 2
#eval recognizedBit [0, 1, 2] unsatSource 2 0

example : (recognizeALC [0, 1, 2] unsatSource).isSome = true := by decide
example : recognizedBit [0, 1, 2] unsatSource 1 2 = some true := by decide
example : recognizedBit [0, 1, 2] unsatSource 0 2 = some true := by decide
example : recognizedBit [0, 1, 2] unsatSource 2 0 = some false := by decide

/-- 4. Rejections: equalities, constants, nested function terms, unmatched or
mismatched Skolem pairs, duplicate Skolem functions, and role axioms outside
the ALC table. -/
def rejectEq : List FCL :=
  [ ⟨[C 0 x], [.eq x y]⟩ ]

def rejectConst : List FCL :=
  [ ⟨[], [C 0 (.const 0)]⟩ ]

def rejectNestedApp : List FCL :=
  [ ⟨[C 0 x], [R 0 x (.app 0 x)]⟩
  , ⟨[C 0 x], [C 1 (.app 0 (.app 0 x))]⟩ ]

def rejectUnmatchedHalf : List FCL :=
  [ ⟨[C 0 x], [R 0 x (.app 0 x)]⟩ ]

def rejectMismatchedSubject : List FCL :=
  [ ⟨[C 0 x], [R 0 x (.app 0 x)]⟩
  , ⟨[C 1 x], [C 2 (.app 0 x)]⟩ ]

def rejectDuplicateFn : List FCL :=
  [ ⟨[C 0 x], [R 0 x (.app 0 x)]⟩
  , ⟨[C 0 x], [C 1 (.app 0 x)]⟩
  , ⟨[C 0 x], [R 0 x (.app 0 x)]⟩
  , ⟨[C 0 x], [C 2 (.app 0 x)]⟩ ]

def rejectRoleInclusion : List FCL :=
  [ ⟨[R 0 x y], [R 1 x y]⟩ ]

def rejectCollapsedVars : List FCL :=
  [ ⟨[C 0 x, R 0 x x], [C 1 x]⟩ ]

#eval recognizeALC [0, 1] rejectEq
#eval recognizeALC [0] rejectConst
#eval recognizeALC [0, 1] rejectNestedApp
#eval recognizeALC [0] rejectUnmatchedHalf
#eval recognizeALC [0, 1, 2] rejectMismatchedSubject
#eval recognizeALC [0, 1, 2] rejectDuplicateFn
#eval recognizeALC [0] rejectRoleInclusion
#eval recognizeALC [0, 1] rejectCollapsedVars

example : recognizeALC [0, 1] rejectEq = none := by decide
example : recognizeALC [0] rejectConst = none := by decide
example : recognizeALC [0, 1] rejectNestedApp = none := by decide
example : recognizeALC [0] rejectUnmatchedHalf = none := by decide
example : recognizeALC [0, 1, 2] rejectMismatchedSubject = none := by decide
example : recognizeALC [0, 1, 2] rejectDuplicateFn = none := by decide
example : recognizeALC [0] rejectRoleInclusion = none := by decide
example : recognizeALC [0, 1] rejectCollapsedVars = none := by decide

end ContextCalculus.ALCCommonSourceRecognizerTests
