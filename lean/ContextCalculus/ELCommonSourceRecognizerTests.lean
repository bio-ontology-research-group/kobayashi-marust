import ContextCalculus.ELCommonSourceRecognizer
import ContextCalculus.KMConcreteWorkerAdapters

/-!
# Unit tests for `ELCommonSourceRecognizer`

Covers every accepted clause shape alone, `nf3` pairs in both orders,
n-ary conjunctions and disjointnesses, explicit total concepts, fresh
distinguished names when no total concept clause is present, and fail-closed
rejections (equality literal, unpaired `nf3` half, reused function symbol,
individual constant).
-/

namespace ContextCalculus.ELCommonSourceRecognizerTests

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.ELCommonSourceRecognizer
open ContextCalculus.KMConcreteWorkerAdapters

abbrev cLit (a : Nat) (t : FTerm) : FLit := .P (.concept a t)
abbrev rLit (r : Nat) (s t : FTerm) : FLit := .P (.role r s t)

abbrev vx : FTerm := .var 0
abbrev vy : FTerm := .var (-1)
abbrev vz : FTerm := .var (-2)

/-! ## Each accepted shape alone -/

-- nf1: A(x) → B(x)
#eval recognizeEL [1, 2] [⟨[cLit 1 vx], [cLit 2 vx]⟩]

example :
    recognizeEL [1, 2] [⟨[cLit 1 vx], [cLit 2 vx]⟩] =
      some { top := 3, bottom := 4, ontology := [.nf1 1 2] } := by
  decide

-- nf2: A(x) ∧ B(x) → C(x)
#eval recognizeEL [1, 2, 3] [⟨[cLit 1 vx, cLit 2 vx], [cLit 3 vx]⟩]

example :
    recognizeEL [1, 2, 3] [⟨[cLit 1 vx, cLit 2 vx], [cLit 3 vx]⟩] =
      some { top := 4, bottom := 5, ontology := [.nf2 1 2 3] } := by
  decide

-- nf2 with empty head (binary disjointness A ⊓ B ⊑ ⊥): A(x) ∧ B(x) → ⊥
#eval recognizeEL [1, 2] [⟨[cLit 1 vx, cLit 2 vx], []⟩]

example :
    recognizeEL [1, 2] [⟨[cLit 1 vx, cLit 2 vx], []⟩] =
      some { top := 3, bottom := 4, ontology := [.nf2 1 2 4] } := by
  decide

-- nf3 pair (role half first, filler half second)
def nf3RoleClause : FCL := ⟨[cLit 1 vx], [rLit 2 vx (.app 10 vx)]⟩
def nf3FillerClause : FCL := ⟨[cLit 1 vx], [cLit 3 (.app 10 vx)]⟩

#eval recognizeEL [1, 3] [nf3RoleClause, nf3FillerClause]

example :
    recognizeEL [1, 3] [nf3RoleClause, nf3FillerClause] =
      some { top := 4, bottom := 5, ontology := [.nf3 1 2 3] } := by
  rfl

-- nf3 pair in reversed order (filler half first, role half second)
#eval recognizeEL [1, 3] [nf3FillerClause, nf3RoleClause]

example :
    recognizeEL [1, 3] [nf3FillerClause, nf3RoleClause] =
      some { top := 4, bottom := 5, ontology := [.nf3 1 2 3] } := by
  decide

-- nf4 (role-first body): R(x,y) ∧ B(y) → C(x)
#eval recognizeEL [2, 3] [⟨[rLit 1 (.var 0) (.var 1), cLit 2 (.var 1)], [cLit 3 (.var 0)]⟩]

example :
    recognizeEL [2, 3]
      [⟨[rLit 1 (.var 0) (.var 1), cLit 2 (.var 1)], [cLit 3 (.var 0)]⟩] =
      some { top := 4, bottom := 5, ontology := [.nf4 1 2 3] } := by
  decide

-- nf4 (concept-first body, CB wire order with y = -1, x = 0): B(y) ∧ R(x,y) → C(x)
#eval recognizeEL [2, 3] [⟨[cLit 2 vy, rLit 1 vx vy], [cLit 3 vx]⟩]

example :
    recognizeEL [2, 3] [⟨[cLit 2 vy, rLit 1 vx vy], [cLit 3 vx]⟩] =
      some { top := 4, bottom := 5, ontology := [.nf4 1 2 3] } := by
  decide

-- nf4 with implicit top filler (ObjectPropertyDomain: R(x,y) → C(x))
#eval recognizeEL [3] [⟨[rLit 1 vx vy], [cLit 3 vx]⟩]

example :
    recognizeEL [3] [⟨[rLit 1 vx vy], [cLit 3 vx]⟩] =
      some { top := 4, bottom := 5, ontology := [.nf4 1 4 3] } := by
  decide

-- nf5: A(x) → ⊥
#eval recognizeEL [1, 2] [⟨[cLit 2 vx], []⟩]

example :
    recognizeEL [1, 2] [⟨[cLit 2 vx], []⟩] =
      some { top := 3, bottom := 2, ontology := [.nf5 2] } := by
  rfl

-- nf6: R(x,y) → S(x,y)
#eval recognizeEL [1, 2] [⟨[rLit 1 vx vy], [rLit 2 vx vy]⟩]

example :
    recognizeEL [1, 2] [⟨[rLit 1 vx vy], [rLit 2 vx vy]⟩] =
      some { top := 3, bottom := 4, ontology := [.nf6 1 2] } := by
  decide

-- nf7 (first-second body order): R(x,y) ∧ S(y,z) → T(x,z)
#eval recognizeEL [1, 2]
  [⟨[rLit 1 (.var 0) (.var 1), rLit 2 (.var 1) (.var 2)], [rLit 3 (.var 0) (.var 2)]⟩]

example :
    recognizeEL [1, 2]
      [⟨[rLit 1 (.var 0) (.var 1), rLit 2 (.var 1) (.var 2)],
        [rLit 3 (.var 0) (.var 2)]⟩] =
      some { top := 3, bottom := 4, ontology := [.nf7 1 2 3] } := by
  decide

-- nf7 (second-first body order with CB-centered variables y = -1, x = 0, z1 = -2)
#eval recognizeEL [1, 2] [⟨[rLit 2 vx vz, rLit 1 vy vx], [rLit 3 vy vz]⟩]

example :
    recognizeEL [1, 2] [⟨[rLit 2 vx vz, rLit 1 vy vx], [rLit 3 vy vz]⟩] =
      some { top := 3, bottom := 4, ontology := [.nf7 1 2 3] } := by
  decide

-- reflexive: ⊤ → R(x,x)
#eval recognizeEL [1, 2] [⟨[], [rLit 1 vx vx]⟩]

example :
    recognizeEL [1, 2] [⟨[], [rLit 1 vx vx]⟩] =
      some { top := 3, bottom := 4, ontology := [.reflexive 1] } := by
  decide

-- top candidate alone: ⊤ → A(x)
#eval recognizeEL [1, 2] [⟨[], [cLit 7 vx]⟩]

example :
    recognizeEL [1, 2] [⟨[], [cLit 7 vx]⟩] =
      some { top := 7, bottom := 9, ontology := [] } := by
  rfl

/-! ## Explicit total concept vs fresh distinguished names -/

-- Explicit total concept: first `top` candidate becomes `top`, further ones become `nf1 top a`
#eval recognizeEL [1, 2]
  [⟨[], [cLit 10 vx]⟩, ⟨[], [cLit 11 vx]⟩, ⟨[cLit 1 vx], [cLit 2 vx]⟩]

example :
    recognizeEL [1, 2]
      [⟨[], [cLit 10 vx]⟩, ⟨[], [cLit 11 vx]⟩, ⟨[cLit 1 vx], [cLit 2 vx]⟩] =
      some { top := 10, bottom := 13, ontology := [.nf1 10 11, .nf1 1 2] } := by
  decide

-- Without an explicit total concept: `top` and `bottom` are fresh above `source` and `named`
#eval recognizeEL [1, 20] [⟨[cLit 1 vx], [cLit 2 vx]⟩]

example :
    recognizeEL [1, 20] [⟨[cLit 1 vx], [cLit 2 vx]⟩] =
      some { top := 21, bottom := 22, ontology := [.nf1 1 2] } := by
  decide

/-! ## Fail-closed rejections -/

-- Rejection 1: equality literal
#eval recognizeEL [1] [⟨[cLit 1 vx], [.eq vx vy]⟩]

example :
    recognizeEL [1] [⟨[cLit 1 vx], [.eq vx vy]⟩] = none := by
  rfl

-- Rejection 2a: unpaired nf3 role half
#eval recognizeEL [1, 3] [nf3RoleClause]

example :
    recognizeEL [1, 3] [nf3RoleClause] = none := by
  decide

-- Rejection 2b: unpaired nf3 filler half
#eval recognizeEL [1, 3] [nf3FillerClause]

example :
    recognizeEL [1, 3] [nf3FillerClause] = none := by
  decide

-- Rejection 3: function symbol used twice
#eval recognizeEL [1, 3, 4, 6]
  [nf3RoleClause, nf3FillerClause,
   ⟨[cLit 4 vx], [rLit 5 vx (.app 10 vx)]⟩,
   ⟨[cLit 4 vx], [cLit 6 (.app 10 vx)]⟩]

example :
    recognizeEL [1, 3, 4, 6]
      [nf3RoleClause, nf3FillerClause,
       ⟨[cLit 4 vx], [rLit 5 vx (.app 10 vx)]⟩,
       ⟨[cLit 4 vx], [cLit 6 (.app 10 vx)]⟩] = none := by
  decide

-- Rejection 4: individual constant
#eval recognizeEL [1, 2] [⟨[cLit 1 (.const 0)], [cLit 2 (.const 0)]⟩]

example :
    recognizeEL [1, 2] [⟨[cLit 1 (.const 0)], [cLit 2 (.const 0)]⟩] = none := by
  rfl

/-! ## N-ary conjunctions and disjointnesses -/

-- 1. Three-atom body: A1(x) ∧ A2(x) ∧ A3(x) → D(x)
-- max concept = 4, freshBase = 5, top = 5, bottom = 6, firstAux = 7
#eval recognizeEL [1, 2, 3, 4]
  [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx], [cLit 4 vx]⟩]

example :
    recognizeEL [1, 2, 3, 4]
      [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx], [cLit 4 vx]⟩] =
      some { top := 5, bottom := 6, ontology := [.nf2 1 2 7, .nf2 7 3 4] } := by
  decide

-- 2. Five-atom body: A1(x) ∧ A2(x) ∧ A3(x) ∧ A4(x) ∧ A5(x) → D(x)
-- max concept = 6, freshBase = 7, top = 7, bottom = 8, firstAux = 9..11
#eval recognizeEL [1, 2, 3, 4, 5, 6]
  [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx, cLit 4 vx, cLit 5 vx], [cLit 6 vx]⟩]

example :
    recognizeEL [1, 2, 3, 4, 5, 6]
      [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx, cLit 4 vx, cLit 5 vx], [cLit 6 vx]⟩] =
      some {
        top := 7
        bottom := 8
        ontology := [.nf2 1 2 9, .nf2 9 3 10, .nf2 10 4 11, .nf2 11 5 6]
      } := by
  decide

-- 3. N-ary disjointness: A1(x) ∧ A2(x) ∧ A3(x) → ⊥
-- max concept = 3, freshBase = 4, top = 4, bottom = 5, firstAux = 6
#eval recognizeEL [1, 2, 3]
  [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx], []⟩]

example :
    recognizeEL [1, 2, 3]
      [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx], []⟩] =
      some { top := 4, bottom := 5, ontology := [.nf2 1 2 6, .nf2 6 3 5] } := by
  decide

-- 4. Two n-ary clauses in one source: distinct fresh auxiliary names across clauses
-- max concept = 6, freshBase = 7, top = 7, bottom = 8, firstAux = 9 (first clause uses 9, second uses 10..11)
#eval recognizeEL [1, 2, 3, 4, 5, 6]
  [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx], [cLit 4 vx]⟩,
   ⟨[cLit 2 vx, cLit 3 vx, cLit 4 vx, cLit 5 vx], [cLit 6 vx]⟩]

example :
    recognizeEL [1, 2, 3, 4, 5, 6]
      [⟨[cLit 1 vx, cLit 2 vx, cLit 3 vx], [cLit 4 vx]⟩,
       ⟨[cLit 2 vx, cLit 3 vx, cLit 4 vx, cLit 5 vx], [cLit 6 vx]⟩] =
      some {
        top := 7
        bottom := 8
        ontology := [.nf2 1 2 9, .nf2 9 3 4, .nf2 2 3 10, .nf2 10 4 11, .nf2 11 5 6]
      } := by
  decide

-- 5. Repeated concept inside one body: A1(x) ∧ A1(x) ∧ A2(x) → D(x)
-- max concept = 3, freshBase = 4, top = 4, bottom = 5, firstAux = 6
#eval recognizeEL [1, 2, 3]
  [⟨[cLit 1 vx, cLit 1 vx, cLit 2 vx], [cLit 3 vx]⟩]

example :
    recognizeEL [1, 2, 3]
      [⟨[cLit 1 vx, cLit 1 vx, cLit 2 vx], [cLit 3 vx]⟩] =
      some { top := 4, bottom := 5, ontology := [.nf2 1 1 6, .nf2 6 2 3] } := by
  decide

-- 6. Semantic check: requested entailment through an n-ary clause is reported
-- by `referenceBit` via `KMConcreteWorkerAdapters.referenceAnswer`
-- Source: 1 ⊑ 2, 1 ⊑ 3, 1 ⊑ 4, and 2 ⊓ 3 ⊓ 4 ⊑ 5; entails 1 ⊑ 5 (and not 5 ⊑ 1).
def naryEntailmentSource : List FCL :=
  [⟨[cLit 1 vx], [cLit 2 vx]⟩,
   ⟨[cLit 1 vx], [cLit 3 vx]⟩,
   ⟨[cLit 1 vx], [cLit 4 vx]⟩,
   ⟨[cLit 2 vx, cLit 3 vx, cLit 4 vx], [cLit 5 vx]⟩]

#eval (recognizeEL [1, 5] naryEntailmentSource).map (fun rec => referenceAnswer rec [1, 5])

example :
    ((recognizeEL [1, 5] naryEntailmentSource).map (fun rec => referenceAnswer rec [1, 5])) =
      some {
        named := [1, 5]
        cells := [
          { sub := 1, sup := 1, answer := true },
          { sub := 1, sup := 5, answer := true },
          { sub := 5, sup := 1, answer := false },
          { sub := 5, sup := 5, answer := true }
        ]
      } := by
  decide

end ContextCalculus.ELCommonSourceRecognizerTests
