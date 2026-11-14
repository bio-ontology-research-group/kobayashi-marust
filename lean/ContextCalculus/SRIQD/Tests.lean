import ContextCalculus.SRIQD.ABoxProcedure
import ContextCalculus.SRIQD.Transitivity
import ContextCalculus.SRIQD.TestTheory
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the procedures with data (stage C4, step 5)

All tests use the test theory of `SRIQD/TestTheory.lean`, whose oracle
`card spec` satisfies `OracleSpec` (`oracleSpec_test`), so by
`satQD_iff`, `entailsQD_iff`, `entailsQDS_iff` and `consistentKBD_iff`
each `#guard` states a fact about the semantics. Roles are `Fin 1`;
data properties `Fin 1` (`u = 0`) unless stated. `satQD O card a` is
`false` iff `a` is unsatisfiable.
-/

namespace ContextCalculus.SRIQD.Tests

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQD ContextCalculus.SRIQD.TestTheory

/-! ## A functional data property with two different literals -/

/-- Atoms: `"1"` (`0`), `"2"` (`1`), `xsd:integer` (`2`). -/
def spec1 : Fin 3 → ASpec := ![.intR (some 1) (some 1), .intR (some 2) (some 2), .int]

/-- `⊤ ⊑ T` (`T = 0`) and `T ⊑ ≤1 u.⊤`: `u` is functional. -/
def O1 : Ontology (Fin 1) (Fin 1) (Fin 1) (Fin 3) := [.obj (.gci [] [0]), .dAtMost 0 1 0 [] []]

/-- `u(a, "1")` and `u(a, "2")`. -/
def A1 : ABox (Fin 1) (Fin 1) (Fin 1) (Fin 3) (Fin 1) := [.dPos 0 0 0, .dPos 0 0 1]

/-- One individual `a = 0`. -/
abbrev AB := ABox (Fin 1) (Fin 1) (Fin 1) (Fin 3) (Fin 1)

#guard !Proc.consistentKBD O1 (card spec1) A1 none
-- The same literal twice is consistent, and so is one literal.
#guard Proc.consistentKBD O1 (card spec1) ([.dPos 0 0 0, .dPos 0 0 0] : AB) none
#guard Proc.consistentKBD O1 (card spec1) ([.dPos 0 0 0] : AB) none
-- Without functionality the two literals are consistent.
#guard Proc.consistentKBD [.obj (.gci [] [0])] (card spec1) A1 none
-- A literal and its negative assertion clash; another negative one does not.
#guard !Proc.consistentKBD O1 (card spec1) ([.dPos 0 0 0, .dNeg 0 0 0] : AB) none
#guard Proc.consistentKBD O1 (card spec1) ([.dPos 0 0 0, .dNeg 0 0 1] : AB) none
-- `u(a, "1")` with `T ⊑ ∀u.integer` is consistent.
#guard Proc.consistentKBD (O1 ++ [.dAll 0 0 [(2, true)]]) (card spec1) ([.dPos 0 0 0] : AB) none

/-- A hint for `u(a, "1")`: one block of type `{T, N_a}` (`N_a = 1`, the
fresh name of `a`). -/
def H1 : SRIQ.Proc.Hint 2 1 1 where
  nb := 1
  blk := fun _ => 0
  ty := fun _ => {0, 1}
  lab := fun _ _ => ∅
  kids := fun _ => []

#guard SRIQ.Proc.checkRealisation (Proc.reduceQ (Proc.encO O1 ([.dPos 0 0 0] : AB)) (card spec1))
  (Proc.encA ([.dPos 0 0 0] : AB)) H1
#guard Proc.consistentKBD O1 (card spec1) ([.dPos 0 0 0] : AB) (some H1)
-- The hint does not make an inconsistent knowledge base consistent.
#guard !Proc.consistentKBD O1 (card spec1) A1 (some H1)

/-! ## Counting booleans -/

/-- Atom: `xsd:boolean` (`0`). -/
def spec2 : Fin 1 → ASpec := ![.bool]

/-- `A ⊑ ≥k u.boolean` (`A = 0`, `T = 1`). -/
def O2 (k : Nat) : Ontology (Fin 2) (Fin 1) (Fin 1) (Fin 1) :=
  [.obj (.gci [] [1]), .dAtLeast 0 k 0 [0] []]

#guard !Proc.satQD (O2 3) (card spec2) 0
#guard Proc.satQD (O2 2) (card spec2) 0

/-! ## `∃u.int[≥5] ⊓ ∀u.int[≤3]` -/

/-- Atoms: `int[≥5]` (`0`), `int[≤3]` (`1`). -/
def spec3 : Fin 2 → ASpec := ![.intR (some 5) none, .intR none (some 3)]

/-- `A ⊑ ∃u.int[≥5]`, `A ⊑ ∀u.int[≤3]` (`A = 0`, `T = 1`). -/
def O3 : Ontology (Fin 2) (Fin 1) (Fin 1) (Fin 2) :=
  [.obj (.gci [] [1]), .dEx 0 0 [0] [], .dAll 0 0 [(1, true)]]

#guard !Proc.satQD O3 (card spec3) 0
#guard Proc.satQD (O3.take 2) (card spec3) 0

/-! ## `≥2` and `≥3` of `int[≥1, ≤2]` -/

/-- Atom: `int[≥1, ≤2]` (`0`). -/
def spec4 : Fin 1 → ASpec := ![.intR (some 1) (some 2)]

/-- `A ⊑ ≥k u.int[≥1, ≤2]`. -/
def O4 (k : Nat) : Ontology (Fin 2) (Fin 1) (Fin 1) (Fin 1) :=
  [.obj (.gci [] [1]), .dAtLeast 0 k 0 [0] []]

#guard Proc.satQD (O4 2) (card spec4) 0
#guard !Proc.satQD (O4 3) (card spec4) 0

/-- The same range as a conjunction of three atoms: `integer` (`0`),
`int[≥1]` (`1`), `int[≤2]` (`2`). -/
def spec4' : Fin 3 → ASpec := ![.int, .intR (some 1) none, .intR none (some 2)]

def O4' (k : Nat) : Ontology (Fin 2) (Fin 1) (Fin 1) (Fin 3) :=
  [.obj (.gci [] [1]), .dAtLeast 0 k 0 [0, 1, 2] []]

#guard Proc.satQD (O4' 2) (card spec4') 0
#guard !Proc.satQD (O4' 3) (card spec4') 0

/-! ## A universal restriction with a disjunctive head -/

/-- Atoms: `int[≤3]` (`0`), `int[≥5]` (`1`), `"4"` (`2`), `"5"` (`3`). -/
def spec6 : Fin 4 → ASpec :=
  ![.intR none (some 3), .intR (some 5) none, .intR (some 4) (some 4), .intR (some 5) (some 5)]

/-- `A ⊑ ∀u.(int[≤3] ⊔ int[≥5])` and `A ⊑ ∃u.L` for a literal atom `L`. -/
def O6 (L : Fin 4) : Ontology (Fin 2) (Fin 1) (Fin 1) (Fin 4) :=
  [.obj (.gci [] [1]), .dAll 0 0 [(0, true), (1, true)], .dEx 0 0 [L] []]

#guard !Proc.satQD (O6 2) (card spec6) 0
#guard Proc.satQD (O6 3) (card spec6) 0
-- A negative literal in the head: `A ⊑ ∀u.¬"4"` with `A ⊑ ∃u."4"`.
#guard !Proc.satQD ([.obj (.gci [] [1]), .dAll 0 0 [(2, false)], .dEx 0 0 [2] []] :
  Ontology (Fin 2) (Fin 1) (Fin 1) (Fin 4)) (card spec6) 0

/-! ## A sub data property carrying a universal restriction -/

/-- Data properties `u = 0`, `w = 1`; `u ⊑ w`, `A ⊑ ∀w.int[≤3]`,
`A ⊑ ∃u.int[≥5]`. -/
def O7 : Ontology (Fin 2) (Fin 1) (Fin 2) (Fin 2) :=
  [.obj (.gci [] [1]), .dSub 0 1, .dAll 0 1 [(1, true)], .dEx 0 0 [0] []]

#guard !Proc.satQD O7 (card spec3) 0
-- Without `u ⊑ w`, `A` is satisfiable.
#guard Proc.satQD (O7.eraseIdx 1) (card spec3) 0

/-! ## A subsumption that holds by finiteness -/

/-- `A ⊑ ≥2 u.D`, `⊤ ⊑ B ⊔ NB`, `NB ⊑ ∀u.¬L` (`A = 0`, `B = 1`, `NB = 2`,
`T = 3`; atoms `D = 0`, `L = 1`). Two distinct values in `D` include `L`
when `D` has two values, so `A ⊑ B`. -/
def O8 : Ontology (Fin 4) (Fin 1) (Fin 1) (Fin 2) :=
  [.obj (.gci [] [3]), .obj (.gci [] [1, 2]), .dAtLeast 0 2 0 [0] [], .dAll 2 0 [(1, false)]]

/-- `D = boolean`, `L = "true"`. -/
def spec8 : Fin 2 → ASpec := ![.bool, .boolV true]

/-- `D = integer`, `L = "0"`. -/
def spec8i : Fin 2 → ASpec := ![.int, .intR (some 0) (some 0)]

/-- `D = int[≥1, ≤2]`, `L = "1"`. -/
def spec8r : Fin 2 → ASpec := ![.intR (some 1) (some 2), .intR (some 1) (some 1)]

#guard Proc.entailsQD O8 (card spec8) 0 1
#guard !Proc.entailsQD O8 (card spec8i) 0 1
#guard Proc.entailsQD O8 (card spec8r) 0 1
#guard Proc.classifyQD O8 (card spec8) [0] == [(0, [0, 1, 3])]
#guard Proc.classifyQD O8 (card spec8i) [0] == [(0, [0, 3])]

/-! ## Transitivity with data -/

/-- `A ⊑ ∃R.B`, `B ⊑ ∃R.C`, `A ⊑ ∀R.D`, `D ⊑ ∀u.int[≤3]`, `C ⊑ ∃u.int[≥5]`
(`A = 0`, `B = 1`, `C = 2`, `D = 3`), and with `tr` the role `R` is
transitive. Then `C` lies below `A` along `R`, gets `D`, and clashes, so
`A` is unsatisfiable and `A ⊑ C`. The two checks take about a minute. -/
def O9 (tr : Bool) : Ontology (Fin 4) (Fin 1) (Fin 1) (Fin 2) :=
  [.obj (.exRight 0 (.pos 0) 1), .obj (.exRight 1 (.pos 0) 2), .obj (.allRight 0 (.pos 0) 3),
    .dAll 3 0 [(1, true)], .dEx 2 0 [0] []] ++
    (if tr then [.obj (.chain [.pos 0, .pos 0] (.pos 0))] else [])

#guard Proc.entailsQDS (O9 true) (card spec3) 0 2
#guard !Proc.entailsQDS (O9 false) (card spec3) 0 2

end ContextCalculus.SRIQD.Tests
