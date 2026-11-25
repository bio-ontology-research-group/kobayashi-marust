import ContextCalculus.SRIQD.ABoxProcedure

/-!
# The forbidden types without data clauses (stage C3c, check speed)

`badQ` lists every type without a data star by enumerating all `2ⁿ` types,
so every decision of the C2a routes was exponential in the number of names
even with a hint. Without data clauses every type has the empty data star,
so the list is empty; `badQF` returns it at once in that case and is
registered with `@[csimp]` (`badQ_eq_F`).
-/

namespace ContextCalculus.SRIQD.Proc

variable {n m p q : Nat}

/-- An object clause. -/
def isObjB : Clause (Fin n) (Fin m) (Fin p) (Fin q) → Bool
  | .obj _ => true
  | _ => false

theorem dataSat_of_obj {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    (h : O.all isObjB = true) (card : Finset (Fin q) → Option Nat) (t : Finset (Fin n)) :
    DataSat O card t := by
  rw [List.all_eq_true] at h
  refine ⟨[], ⟨fun e he => by simp at he, fun τ k _ => by simp [tcnt], ?_, ?_, ?_, ?_⟩⟩
  · intro a u head hcl; exact absurd (h _ hcl) (by simp [isObjB])
  · intro a u pos neg hcl; exact absurd (h _ hcl) (by simp [isObjB])
  · intro a k u pos neg hcl; exact absurd (h _ hcl) (by simp [isObjB])
  · intro a k u pos neg hcl; exact absurd (h _ hcl) (by simp [isObjB])

def badQF (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat) :
    List (Finset (Fin n)) :=
  if O.all isObjB then [] else (allTypes n).filter fun t => !dataSatB O card t

@[csimp] theorem badQ_eq_F : @badQ = @badQF := by
  funext n m p q O card
  unfold badQ badQF
  split_ifs with h
  · rw [List.filter_eq_nil_iff]
    intro t _
    simp [(dataSatB_iff t).2 (dataSat_of_obj h card t)]
  · rfl

end ContextCalculus.SRIQD.Proc

#print axioms ContextCalculus.SRIQD.Proc.badQ_eq_F
