import ContextCalculus.SRIQ.ABoxProcedure
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the ABox procedure

Roles are `Fin 1` (`R = 0`) unless stated. Each ontology has a top name
`T = 0` with `⊤ ⊑ T`. `Proc.consistentKB O A none` runs the exhaustive
search; with `some h` it first checks the hint `h`, and
`Proc.checkRealisation O A h` checks the hint alone.

The searches on three individuals take about 15 s each (the
inconsistent cases try every block map, type and label); the whole file
takes about a minute.
-/

namespace ContextCalculus.SRIQ.ABoxTests

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ

/-! ## Two individuals forced equal by a functional role -/

/-- Functional `R` (`T ⊑ ≤1 R.T`) and `B ⊓ C ⊑ ⊥` (`B = 1`, `C = 2`). -/
def O1 : Ontology (Fin 3) (Fin 1) :=
  [.gci [] [0], .atMost 0 1 (.pos 0) 0, .gci [1, 2] []]

/-- Functional `R` without the disjointness. -/
def O1' : Ontology (Fin 3) (Fin 1) :=
  [.gci [] [0], .atMost 0 1 (.pos 0) 0]

/-- `R(a,b)`, `R(a,c)`, `B(b)`, `C(c)` (`a = 0`, `b = 1`, `c = 2`). -/
def A1 : ABox (Fin 3) (Fin 1) (Fin 3) :=
  [.role 0 (.pos 0) 1, .role 0 (.pos 0) 2, .cls 1 1, .cls 2 2]

-- `b` and `c` are forced equal, and the merged block clashes.
#guard !Proc.consistentKB O1 A1 none

/-- `a` alone, `b` and `c` merged into one block. -/
def H1 : Proc.Hint 3 1 3 where
  nb := 2
  blk := ![0, 1, 1]
  ty := ![{0}, {0, 1, 2}]
  lab := ![![∅, {.pos 0}], ![{.inv 0}, ∅]]
  kids := fun _ => []

/-- `b` and `c` in different blocks: two `R`-successors of `a`. -/
def H1bad : Proc.Hint 3 1 3 where
  nb := 3
  blk := ![0, 1, 2]
  ty := ![{0}, {0, 1}, {0, 2}]
  lab := ![![∅, {.pos 0}, {.pos 0}], ![{.inv 0}, ∅, ∅], ![{.inv 0}, ∅, ∅]]
  kids := fun _ => []

/-- All three individuals in one block with an `R`-loop. -/
def H1one : Proc.Hint 3 1 3 where
  nb := 1
  blk := fun _ => 0
  ty := fun _ => {0, 1, 2}
  lab := fun _ _ => {.pos 0, .inv 0}
  kids := fun _ => []

-- Without the disjointness the knowledge base is consistent.
#guard Proc.checkRealisation O1' A1 H1
#guard Proc.checkRealisation O1' A1 H1one
#guard !Proc.checkRealisation O1' A1 H1bad
#guard Proc.consistentKB O1' A1 (some H1bad)
-- With the disjointness the merged block fails its check.
#guard !Proc.checkRealisation O1 A1 H1
#guard !Proc.consistentKB O1 A1 (some H1)

/-! ## `diff` against a forced merge -/

/-- Functional `R` over the top name alone. -/
def O2 : Ontology (Fin 1) (Fin 1) :=
  [.gci [] [0], .atMost 0 1 (.pos 0) 0]

/-- `R(a,b)`, `R(a,c)`, `b ≠ c` under functional `R`. -/
def A2 : ABox (Fin 1) (Fin 1) (Fin 3) :=
  [.role 0 (.pos 0) 1, .role 0 (.pos 0) 2, .diff 1 2]

#guard !Proc.consistentKB O2 A2 none
-- Without `b ≠ c` it is consistent.
#guard Proc.consistentKB O2 (A2.take 2) none
-- `a ≠ b` is consistent: `b` and `c` share a block apart from `a`.
#guard Proc.consistentKB O2 (A2.take 2 ++ [.diff 0 1]) none

/-! ## A negative role assertion against an entailed edge -/

/-- `R ⊑ S` (`R = 0`, `S = 1`). -/
def O3 : Ontology (Fin 1) (Fin 2) :=
  [.gci [] [0], .chain [.pos 0] (.pos 1)]

/-- `R(a,b)` and `¬S(a,b)`. -/
def A3 : ABox (Fin 1) (Fin 2) (Fin 2) :=
  [.role 0 (.pos 0) 1, .nrole 0 (.pos 1) 1]

#guard !Proc.consistentKB O3 A3 none
-- Through the inverse: `R⁻(b,a)` and `¬S(a,b)`.
#guard !Proc.consistentKB O3
  ([.role 1 (.inv 0) 0, .nrole 0 (.pos 1) 1] : ABox (Fin 1) (Fin 2) (Fin 2)) none
-- `¬R(a,b)` with `S(a,b)` is consistent.
#guard Proc.consistentKB O3
  ([.role 0 (.pos 1) 1, .nrole 0 (.pos 0) 1] : ABox (Fin 1) (Fin 2) (Fin 2)) none

/-! ## An at-most counts a named neighbour and a tree child together -/

/-- `A ⊑ ∃R.B`, `A ⊑ ≤1 R.T`, `B ⊓ C ⊑ ⊥` (`A = 1`, `B = 2`, `C = 3`). -/
def O4 : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [0], .exRight 1 (.pos 0) 2, .atMost 1 1 (.pos 0) 0, .gci [2, 3] []]

/-- `A(a)`, `R(a,b)`, `C(b)`: the named `b` uses the only `R`-place of
`a`, and the `B`-successor cannot be `b`. -/
def A4 : ABox (Fin 4) (Fin 1) (Fin 2) :=
  [.cls 0 1, .role 0 (.pos 0) 1, .cls 1 3]

#guard !Proc.consistentKB O4 A4 none

/-- With `≤2` in place of `≤1`, `a` has `b` and a tree child in `B`. -/
def O4' : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [0], .exRight 1 (.pos 0) 2, .atMost 1 2 (.pos 0) 0, .gci [2, 3] []]

def H4 : Proc.Hint 4 1 2 where
  nb := 2
  blk := ![0, 1]
  ty := ![{0, 1}, {0, 3}]
  lab := ![![∅, {.pos 0}], ![{.inv 0}, ∅]]
  kids := ![[({.pos 0}, {0, 2})], []]

#guard Proc.checkRealisation O4' A4 H4
#guard Proc.consistentKB O4' A4 none
-- The same hint fails under `≤1`: the named neighbour and the child are two.
#guard !Proc.checkRealisation O4 A4 H4

/-! ## An individual that needs an infinite tree -/

/-- `Z ⊑ A`, `A ⊑ ∃R.A`, `T ⊑ ≤1 R⁻.T`, `Z ⊑ ∀R⁻.E`, `E ⊑ ⊥`
(`Z = 1`, `A = 2`, `E = 3`). `Z(a)` has no `R`-predecessor, so `a` has
no loop and its `R`-chain is an infinite tree. -/
def O5 : Ontology (Fin 4) (Fin 1) :=
  [.gci [] [0], .gci [1] [2], .exRight 2 (.pos 0) 2, .atMost 0 1 (.inv 0) 0,
    .allRight 1 (.inv 0) 3, .gci [3] []]

def A5 : ABox (Fin 4) (Fin 1) (Fin 1) := [.cls 0 1]

def H5 : Proc.Hint 4 1 1 where
  nb := 1
  blk := fun _ => 0
  ty := fun _ => {0, 1, 2}
  lab := fun _ _ => ∅
  kids := fun _ => [({.pos 0}, {0, 2})]

/-- The loop is not a realisation here. -/
def H5loop : Proc.Hint 4 1 1 where
  nb := 1
  blk := fun _ => 0
  ty := fun _ => {0, 1, 2}
  lab := fun _ _ => {.pos 0, .inv 0}
  kids := fun _ => []

#guard Proc.checkRealisation O5 A5 H5
#guard !Proc.checkRealisation O5 A5 H5loop
#guard Proc.consistentKB O5 A5 none
-- `R(a,a)` makes it inconsistent.
#guard !Proc.consistentKB O5 (A5 ++ [.role 0 (.pos 0) 0]) none

/-! ## An inconsistent knowledge base in `classifyKB` -/

-- Every requested name gets every name as a subsumer.
#guard Proc.classifyKB O1 A1 none [1, 2] == [(1, [0, 1, 2]), (2, [0, 1, 2])]
-- Consistent: the rows of `classifyQ`.
#guard Proc.classifyKB O1' A1 (some H1) [1, 2] == Proc.classifyQ O1' [1, 2]
#guard Proc.classifyKB O1' A1 (some H1) [1, 2] == [(1, [0, 1]), (2, [0, 2])]

end ContextCalculus.SRIQ.ABoxTests
