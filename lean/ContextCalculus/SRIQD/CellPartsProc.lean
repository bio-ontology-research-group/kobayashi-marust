import ContextCalculus.SRIQD.CellParts

/-!
# The parts, enumerated, and the procedure over them (stage C4)

`partsOf cs` lists, for the small cells `cs`, every choice of counts per
reading that adds up to the cell size (`comps`). `entailsSub_cell_iff_parts`:
for `dbnd O ≤ B` and `B · 2^s ≤ L`, a subsumption holds in the cell theory
iff `entailsQD` accepts it with the oracle of every listed part.

The number of parts is the product, over the small cells, of the number of
ways to split the cell size `k` into `2^s` counts, `C(k + 2^s - 1, 2^s - 1)`.
-/

namespace ContextCalculus.SRIQD

set_option linter.unusedSectionVars false

/-- The lists of `m` naturals that add up to `k`. -/
def comps : Nat → Nat → List (List Nat)
  | k, 0 => if k = 0 then [[]] else []
  | k, m + 1 => (List.range (k + 1)).flatMap fun i => (comps (k - i) m).map (i :: ·)

theorem mem_comps : ∀ {k m : Nat} {l : List Nat}, l ∈ comps k m ↔ l.length = m ∧ l.sum = k
  | k, 0, l => by
    unfold comps
    split_ifs with hk
    · subst hk
      simp only [List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro h; rw [List.eq_nil_of_length_eq_zero h]; simp; omega
  | k, m + 1, l => by
    unfold comps
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨i, hi, l', hl', rfl⟩
      obtain ⟨h1, h2⟩ := mem_comps.1 hl'
      refine ⟨by simp [h1], ?_⟩
      simp only [List.sum_cons, h2]
      omega
    · rintro ⟨hl, hs⟩
      cases l with
      | nil => simp at hl
      | cons i l' =>
        simp only [List.length_cons, List.sum_cons] at hl hs
        exact ⟨i, by omega, l', mem_comps.2 ⟨by omega, by omega⟩, rfl⟩

variable {Val K : Type} [DecidableEq K] {q s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

/-- Every choice of counts for the cells `cs`. -/
def partsOf (size : K → Option Nat) (s : Nat) : List K → List (List (K × List Nat))
  | [] => [[]]
  | c :: cs => (partsOf size s cs).flatMap fun a =>
      (comps ((size c).getD 0) (allG s).length).map fun ns => (c, ns) :: a

/-- The counts of an enumerated part. -/
def toPart (s : Nat) (a : List (K × List Nat)) (c : K) (g : Fin s → Bool) : Nat :=
  ((a.lookup c).getD []).getD ((allG s).idxOf g) 0

theorem mem_partsOf : ∀ {cs : List K} {a : List (K × List Nat)}, a ∈ partsOf size s cs ↔
    a.map Prod.fst = cs ∧ ∀ p ∈ a, p.2 ∈ comps ((size p.1).getD 0) (allG s).length
  | [], a => by
    simp only [partsOf, List.mem_singleton, List.map_eq_nil_iff]
    constructor
    · rintro rfl; simp
    · rintro ⟨rfl, -⟩; rfl
  | c :: cs, a => by
    simp only [partsOf, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a', ha', ns, hns, rfl⟩
      obtain ⟨h1, h2⟩ := mem_partsOf.1 ha'
      refine ⟨by simp [h1], fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hns
      · exact h2 p hp
    · rintro ⟨h1, h2⟩
      cases a with
      | nil => simp at h1
      | cons p a' =>
        simp only [List.map_cons, List.cons.injEq] at h1
        refine ⟨a', mem_partsOf.2 ⟨h1.2, fun p' hp' => h2 p' (List.mem_cons_of_mem _ hp')⟩,
          p.2, ?_, ?_⟩
        · have := h2 p List.mem_cons_self; rw [h1.1] at this; exact this
        · rw [← h1.1]

theorem lookup_mem : ∀ {a : List (K × List Nat)} {c : K} {x : List Nat},
    a.lookup c = some x → (c, x) ∈ a
  | [], _, _, h => by simp [List.lookup] at h
  | (c', y) :: a, c, x, h => by
    unfold List.lookup at h
    split at h
    · rename_i hc
      have : c = c' := by simpa using hc
      cases h; subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_isSome {a : List (K × List Nat)} {c : K} (h : c ∈ a.map Prod.fst) :
    ∃ x, a.lookup c = some x := by
  induction a with
  | nil => simp at h
  | cons p a ih =>
    obtain ⟨c', y⟩ := p
    unfold List.lookup
    split
    · exact ⟨_, rfl⟩
    · rename_i hc
      rcases List.mem_cons.1 h with h | h
      · simp only at h; subst h; simp at hc
      · exact ih h

theorem lookup_map (cs : List K) (f : K → List Nat) {c : K} (hc : c ∈ cs) :
    (cs.map fun c => (c, f c)).lookup c = some (f c) := by
  induction cs with
  | nil => simp at hc
  | cons c' cs ih =>
    simp only [List.map_cons]
    unfold List.lookup
    split
    · rename_i h
      have : c = c' := by simpa using h
      subst this; rfl
    · rename_i h
      rcases List.mem_cons.1 hc with rfl | hc
      · simp at h
      · exact ih hc

theorem getD_idxOf_map (f : (Fin s → Bool) → Nat) (g : Fin s → Bool) :
    ((allG s).map f).getD ((allG s).idxOf g) 0 = f g := by
  have hlt := List.idxOf_lt_length_of_mem (mem_allG g)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some,
    List.getElem_map, List.getElem_idxOf]

theorem map_getD_idxOf {ns : List Nat} (hl : ns.length = (allG s).length) :
    (allG s).map (fun g => ns.getD ((allG s).idxOf g) 0) = ns := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  rw [List.getElem_map, (allG_nodup s).idxOf_getElem, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- Every listed part is valid. -/
theorem validPart_of_mem {L : Nat} {a : List (K × List Nat)}
    (ha : a ∈ partsOf size s (cells.filter fun c => small size L c)) :
    ValidPart cells size L (toPart s a) := by
  intro c hc hs
  obtain ⟨h1, h2⟩ := mem_partsOf.1 ha
  have hca : c ∈ a.map Prod.fst := by rw [h1]; exact List.mem_filter.2 ⟨hc, hs⟩
  obtain ⟨x, hx⟩ := lookup_isSome hca
  have hxc := mem_comps.1 (h2 _ (lookup_mem hx))
  obtain ⟨k, hk, -⟩ := small_size hs
  simp only [hk, Option.getD_some] at hxc
  rw [hk]
  congr 1
  have : (allG s).map (toPart s a c) = x := by
    unfold toPart
    rw [hx, Option.getD_some]
    exact map_getD_idxOf hxc.1
  rw [this, hxc.2]

/-! ## The procedure -/

variable {n m p : Nat}

/-- Every subsumer accepted by every part. -/
def entailsParts (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (L : Nat) (E : Fin q → K → (Fin s → Bool) → Bool) (a b : Fin n) :
    Bool :=
  (partsOf size s (cells.filter fun c => small size L c)).all fun x =>
    Proc.entailsQD O (partCard cells size L E (toPart s x)) a b

/-- **Exactness over the parts.** -/
theorem entailsParts_iff (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hB : dbnd O ≤ B) (hA : IsALCHIQ O) (a b : Fin n) :
    entailsParts O cells size L E a b = true ↔ EntailsSub (cellTheory key E) O a b := by
  classical
  unfold entailsParts
  rw [List.all_eq_true]
  constructor
  · intro h D V _ atom hΘ I hI x hx
    obtain ⟨fr, hval, hpart⟩ := part_of_cellTheory (L := L) hc hΘ
    let sc := cells.filter fun c => small size L c
    let xa : List (K × List Nat) := sc.map fun c => (c, (allG s).map (countsOf key fr c))
    have hxa : xa ∈ partsOf size s sc := by
      refine mem_partsOf.2 ⟨by simp [xa, Function.comp_def], fun pr hpr => ?_⟩
      obtain ⟨c, hcs, rfl⟩ := List.mem_map.1 hpr
      obtain ⟨hcc, hs⟩ := List.mem_filter.1 hcs
      refine mem_comps.2 ⟨by simp, ?_⟩
      have := hval c hcc hs
      simp [this]
    have hagree : ∀ c ∈ cells, small size L c = true → ∀ g,
        toPart s xa c g = countsOf key fr c g := by
      intro c hcc hs g
      unfold toPart
      rw [lookup_map sc _ (List.mem_filter.2 ⟨hcc, hs⟩), Option.getD_some, getD_idxOf_map]
    have hpart' : partTheory key cells size L E (toPart s xa) V atom := by
      obtain ⟨e, fr', hin, hat⟩ := hpart
      refine ⟨e, fr', fun c hcc hs g => ?_, hat⟩
      rw [hin c hcc hs g, hagree c hcc hs g]
    have hent := (Proc.entailsQD_iffB (oracleSpecB_part hc hL (validPart_of_mem hxa)) hB hA a b).1
      (h xa hxa)
    exact hent D V atom hpart' I hI x hx
  · intro h xa hxa
    refine (Proc.entailsQD_iffB (oracleSpecB_part hc hL (validPart_of_mem hxa)) hB hA a b).2 ?_
    intro D V _ atom hΘ I hI x hx
    exact h D V atom (cellTheory_of_part hΘ) I hI x hx

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.entailsParts_iff
