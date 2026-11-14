import ContextCalculus.SRIQD.KBB
import ContextCalculus.SRIQD.CellPartsProc

/-!
# Consistency over the parts of a cell theory (stage C4)

A knowledge base is consistent in a cell theory iff it is consistent in
some part (`consistentParts_iff`); each part has a bounded oracle, so
`consistentKBDS` decides it for every hint.
-/

namespace ContextCalculus.SRIQD

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {q s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}
variable {n m p k : Nat}

/-- Some part accepts the knowledge base. -/
def consistentParts (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hint : Option (SRIQ.Proc.Hint (n + (Proc.encTransQD O).1 + k) m k)) : Bool :=
  (partsOf size s (cells.filter sp)).any fun x =>
    Proc.consistentKBDS O (partCard cells size sp E (toPart s x)) A hint

/-- **Consistency over the parts**, for every hint. -/
theorem consistentParts_iff (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {A : ABox (Fin n) (Fin m) (Fin p) (Fin q) (Fin k)}
    (hS : Proc.IsSHIQDKB O A)
    (hB : dbnd (Proc.encO (Proc.encTransQD O).2 (Proc.encABoxD O A)) ≤ B)
    (hint : Option (SRIQ.Proc.Hint (n + (Proc.encTransQD O).1 + k) m k)) :
    consistentParts O A cells size sp E hint = true ↔ ConsistentKB (cellTheory key E) O A := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  unfold consistentParts
  rw [List.any_eq_true]
  constructor
  · rintro ⟨xa, hxa, h⟩
    obtain ⟨D, V, hD, atom, hΘ, I, ind, hI, hA⟩ := (Proc.consistentKBDS_iffB
      (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hint).1 h
    exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, I, ind, hI, hA⟩
  · rintro ⟨D, V, hD, atom, hΘ, I, ind, hI, hA⟩
    obtain ⟨fr, hval, hpart⟩ := part_of_cellTheory hc hfin hΘ
    let sc := cells.filter sp
    let xa : List (K × List Nat) := sc.map fun c => (c, (allG s).map (countsOf key fr c))
    have hxa : xa ∈ partsOf size s sc := by
      refine mem_partsOf.2 ⟨by simp [xa, Function.comp_def], fun pr hpr => ?_⟩
      obtain ⟨c, hcs, rfl⟩ := List.mem_map.1 hpr
      obtain ⟨hcc, hs⟩ := List.mem_filter.1 hcs
      refine mem_comps.2 ⟨by simp, ?_⟩
      have := hval c hcc hs
      simp [this]
    have hagree : ∀ c ∈ cells, sp c = true → ∀ g, toPart s xa c g = countsOf key fr c g := by
      intro c hcc hs g
      unfold toPart
      rw [lookup_map sc _ (List.mem_filter.2 ⟨hcc, hs⟩), Option.getD_some, getD_idxOf_map]
    have hpart' : partTheory key cells sp E (toPart s xa) V atom := by
      obtain ⟨e, fr', hin, hat⟩ := hpart
      refine ⟨e, fr', fun c hcc hs g => ?_, hat⟩
      rw [hin c hcc hs g, hagree c hcc hs g]
    refine ⟨xa, hxa, (Proc.consistentKBDS_iffB
      (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hint).2
      ⟨D, V, hD, atom, hpart', I, ind, hI, hA⟩⟩

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.consistentParts_iff
