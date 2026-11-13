import ContextCalculus.SRI.Fast
import ContextCalculus.SRI.Transitivity

/-!
# Tests for the fast procedure

The cases of `ProcedureTests.lean` and `TransitivityTests.lean`, run with
`fastEntails`; each `#guard` checks the expected answer, and the small
cases also check agreement with `entails` of `Procedure.lean`. Then
`classify` on the disjunction example and on a chain with 401 names.
-/

namespace ContextCalculus.SRI.FastTests

open ContextCalculus.SRI Proc

/-! ## The cases of `ProcedureTests.lean` -/

/-- `A ⊑ ∃r.B` and `B ⊑ ∀r⁻.C`. -/
def O1 : Ontology (Fin 3) (Fin 1) :=
  [.exRight 0 (.pos 0) 1, .allRight 1 (.inv 0) 2]

#guard fastEntails O1 [0] 0 2
#guard !fastEntails O1 [0] 0 1
#guard fastEntails O1 [0] 0 2 == entails O1 [0] 0 2
#guard fastEntails O1 [0] 0 1 == entails O1 [0] 0 1

/-- `r ⊑ s`, `A ⊑ ∃r.B` and `B ⊑ ∀s⁻.C`. -/
def O2 : Ontology (Fin 3) (Fin 2) :=
  [.chain [.pos 0] (.pos 1), .exRight 0 (.pos 0) 1, .allRight 1 (.inv 1) 2]

#guard fastEntails O2 [0] 0 2
#guard fastEntails O2 [0] 0 2 == entails O2 [0] 0 2

def O2' : Ontology (Fin 3) (Fin 2) := [.exRight 0 (.pos 0) 1, .allRight 1 (.inv 1) 2]

#guard !fastEntails O2' [0] 0 2
#guard fastEntails O2' [0] 0 2 == entails O2' [0] 0 2

/-- `A ⊑ ∃r.B` alone. -/
def O3 : Ontology (Fin 3) (Fin 1) :=
  [.exRight 0 (.pos 0) 1]

#guard !fastEntails O3 [0] 0 2
#guard fastEntails O3 [0] 0 0
#guard fastEntails O3 [0] 0 2 == entails O3 [0] 0 2

/-- `A ⊑ B ⊔ C`, `B ⊑ D` and `C ⊑ D`. -/
def O4 : Ontology (Fin 4) (Fin 1) :=
  [.gci [0] [1, 2], .gci [1] [3], .gci [2] [3]]

#guard fastEntails O4 [0] 0 3
#guard !fastEntails O4 [0] 0 1
#guard !fastEntails O4 [0] 0 2
#guard [1, 2, 3].all fun b => fastEntails O4 [0] 0 b == entails O4 [0] 0 b

/-- `A ⊑ ∃r.B`, `B ⊑ ⊥`: `A` is unsatisfiable. -/
def O5 : Ontology (Fin 3) (Fin 1) := [.exRight 0 (.pos 0) 1, .gci [1] []]

#guard fastEntails O5 [0] 0 2
#guard fastEntails O5 [0] 0 2 == entails O5 [0] 0 2

/-! ## The cases of `TransitivityTests.lean` -/

abbrev old {n m : Nat} (O : Ontology (Fin n) (Fin m)) (i : Fin n) :
    Fin (n + (encTrans O).1) :=
  Fin.castAdd _ i

/-- Ask `a ⊑ b` of the encoding with the fast procedure. -/
def ask {n m : Nat} (O : Ontology (Fin n) (Fin m)) (a b : Fin n) : Bool :=
  fastEntails (encTrans O).2 [old O a] (old O a) (old O b)

def base1 : Ontology (Fin 4) (Fin 1) :=
  [.allRight 0 (.pos 0) 1, .exRight 0 (.pos 0) 2, .exRight 2 (.pos 0) 3, .gci [3, 1] []]

def T1 : Ontology (Fin 4) (Fin 1) := .chain [.pos 0, .pos 0] (.pos 0) :: base1

#guard ask T1 0 2
#guard !ask base1 0 2
#guard !ask T1 2 1

def base2 : Ontology (Fin 4) (Fin 1) :=
  [.exRight 0 (.pos 0) 1, .exRight 1 (.pos 0) 2, .allRight 2 (.inv 0) 3]

def T2 : Ontology (Fin 4) (Fin 1) := .chain [.pos 0, .pos 0] (.pos 0) :: base2

#guard ask T2 0 3
#guard !ask base2 0 3
#guard ask T2 1 3
#guard ask base2 1 3

def base3 : Ontology (Fin 4) (Fin 2) :=
  [.chain [.pos 0] (.pos 1), .allRight 0 (.pos 1) 1, .exRight 0 (.pos 0) 2,
   .exRight 2 (.pos 0) 3]

def T3 : Ontology (Fin 4) (Fin 2) := .chain [.pos 0, .pos 0] (.pos 0) :: base3

#guard ask (T3 ++ [.gci [3, 1] []]) 0 2
#guard !ask (base3 ++ [.gci [3, 1] []]) 0 2
#guard ask (.chain [.pos 1, .pos 1] (.pos 1) :: base3 ++ [.gci [3, 1] []]) 0 2

/-! ## Classification -/

-- Every name of `O4` with its subsumers, from one run.
#guard classify O4 [0, 1, 2, 3] == [(0, [0, 3]), (1, [1, 3]), (2, [2, 3]), (3, [3])]

-- An unsatisfiable name has every name as a subsumer.
#guard classify O5 [0, 1, 2] == [(0, [0, 1, 2]), (1, [0, 1, 2]), (2, [2])]

/-- A chain with `2k + 1` names: `Aᵢ ⊑ ∃r.Aᵢ₊₁`, `Aᵢ₊₁ ⊑ ∀s⁻.Bᵢ`,
`Bᵢ ⊑ Z` and `r ⊑ s`, with `Aᵢ = i`, `Bᵢ = k + i` (so `B₀ = Aₖ`) and
`Z = 2k`. Each `Aᵢ` with `i < k` has the subsumers `Aᵢ`, `Bᵢ`, `Z`. -/
def chainO (k : Nat) : Ontology (Fin (2 * k + 1)) (Fin 2) :=
  let nm : Nat → Fin (2 * k + 1) := fun i => ⟨i % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
  ((List.range k).flatMap fun i =>
    [.exRight (nm i) (.pos 0) (nm (i + 1)), .allRight (nm (i + 1)) (.inv 1) (nm (k + i)),
     .gci [nm (k + i)] [nm (2 * k)]]) ++ [.chain [.pos 0] (.pos 1)]

-- 401 names: `5k + 1` subsumer pairs in all.
#guard ((classify (chainO 200) (List.finRange 401)).map (·.2.length)).sum == 1001
#guard fastEntails (chainO 200) [37] 37 237 && !fastEntails (chainO 200) [37] 37 38

end ContextCalculus.SRI.FastTests
