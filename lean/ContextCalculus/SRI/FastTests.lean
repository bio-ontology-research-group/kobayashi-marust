import ContextCalculus.SRI.Fast
import ContextCalculus.SRI.Transitivity

/-!
# Tests for the fast procedure

The cases of `ProcedureTests.lean` and `TransitivityTests.lean`, run with
`fastEntails`; each `#guard` checks the expected answer, and the small
cases also check agreement with `entails` of `Procedure.lean`. Then
`classify` and `classifyF` on the disjunction example, an unsatisfiable
name, and a chain with 401 names.
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

-- `classifyF` gives the same subsumers, and `none` for an unsatisfiable name.
#guard classifyF O4 [0, 1, 2, 3] ==
  [(0, some [0, 3]), (1, some [1, 3]), (2, some [2, 3]), (3, some [3])]
#guard classifyF O5 [0, 1, 2] == [(0, none), (1, none), (2, some [2])]

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
#guard ((classifyF (chainO 200) (List.finRange 401)).map fun p => (p.2.getD []).length).sum ==
  1001

/-! ## The sorted type operations against `Finset` -/

/-- Every type over five names, stored in decreasing order (so `toL`
takes the slow path on each). -/
def tys5 : List (Ty 5) :=
  (List.finRange 5).sublists.map fun l => l.reverse.toFinset

#guard tys5.length == 32
-- union, subset and insertion
#guard tys5.all fun s => tys5.all fun t => decide (uni s t = s ∪ t)
#guard tys5.all fun s => tys5.all fun t => sub s t == decide (s ⊆ t)
#guard tys5.all fun s => (List.finRange 5).all fun a => decide (ins a s = insert a s)
-- the results of the operations, used again, give the same answers
#guard tys5.all fun s => tys5.all fun t =>
  sub (uni s t) (uni t s) && sub s (uni s t) && toL (uni s t) == (s ∪ t).sort (· ≤ ·)
-- `toL` sorts, and `ofL` builds the type of a list
#guard tys5.all fun s => toL s == s.sort (· ≤ ·) && sortedB (toL s)
#guard ([[], [3, 1, 4, 1, 5, 9, 2, 6], [0, 0, 0], [9, 8, 7, 6, 5, 4, 3, 2, 1, 0]] :
    List (List (Fin 10))).all fun L => decide (ofL L = L.toFinset) && sortedB (toL (ofL L))
-- membership in the hash set of `branchesF` agrees with the type
#guard tys5.all fun s => (List.finRange 5).all fun a =>
  (Cur.ofTy s).h.contains a == decide (a ∈ s) &&
    ((Cur.ofTy s).addAll [a, 0]).h.contains 0 &&
    decide (((Cur.ofTy s).addAll [a, 0]).ty = s ∪ {a, 0})
-- `branchesF` gives the branches of `O4` and `O5`
#guard tys5.all fun s =>
  let s4 : Ty 4 :=
    ((toL s).filterMap fun a => if h : a.val < 4 then some (⟨a.val, h⟩ : Fin 4) else none).toFinset
  (branches O4 s4).all (· ∈ branchesF O4 (mkIx O4) s4) &&
    (branchesF O4 (mkIx O4) s4).all fun t => decide (s4 ⊆ t)
#guard (branchesF O5 (mkIx O5) {1}).isEmpty && (branches O5 {1}).isEmpty

end ContextCalculus.SRI.FastTests
