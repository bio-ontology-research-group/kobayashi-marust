import ContextCalculus.SRIQN.Procedure
import ContextCalculus.SRIQN.CheckFast

/-!
# Rows by reduction to consistency (stage C2, design section 5)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. With nominals every row reduces to
consistency.

* `entailsSubN_iff`: `a ⊑ b` iff the ontology with a fresh nominal `X`
  (the new name `Fin.last n`), `X ⊑ a` and `X ⊓ b ⊑ ⊥` is inconsistent.
* `entailsSubN_nom_iff`: for a nominal name `a`, `a ⊑ b` iff the ontology
  with `a ⊓ b ⊑ ⊥` is inconsistent. Type rows (`N_i ⊑ C`) and same rows
  (`N_i ⊑ N_j`) are of this form, and so is the different row with
  `b` the complement of `N_j`.

Both reductions stay inside C2a and ALCHOIQ (`isC2a_subExt`,
`isC2a_append_bot`, `isALCHOIQ_subExt`, `isALCHOIQ_append_gci`): they add
a gci with an empty head, or a nominal `X` and the gcis `X ⊑ a`,
`X ⊓ b ⊑ ⊥`; a new nominal name and new positive occurrences implied by a
nominal only shrink the set of subjects that `IsC2a` constrains. So the procedure rows (`subRowN`, `nomRowN`) are
exact on C2a for every hint.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (lowerL upperL mem_lowerL mem_upperL)

variable {D CName Role : Type}

theorem models_append {I : Interp D CName Role} {O O' : Ontology CName Role} :
    models I (O ++ O') ↔ models I O ∧ models I O' := by
  simp only [models, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- **Rows on nominal names.** For a nominal name `a`, `a ⊑ b` iff adding
`a ⊓ b ⊑ ⊥` makes the ontology inconsistent. -/
theorem entailsSubN_nom_iff (O : Ontology CName Role) {a : CName} (ha : a ∈ noms O) (b : CName) :
    EntailsSubN O a b ↔ ¬ ConsistentN (O ++ [.base (.gci [a, b] [])]) := by
  constructor
  · rintro h ⟨D, hD, J, hJ⟩
    obtain ⟨hO, hg⟩ := models_append.1 hJ
    obtain ⟨x, hx⟩ := (models_iff.1 hO).2 a ha
    have hax : J.c a x := (hx x).2 rfl
    have hbx := h D J hO x hax
    obtain ⟨c, hc, -⟩ := hg _ List.mem_cons_self x (by simp [hax, hbx])
    simp at hc
  · intro hn D _ I hI x hx
    by_contra hb
    obtain ⟨y, hy⟩ := (models_iff.1 hI).2 a ha
    refine hn ⟨D, inferInstance, I, models_append.2 ⟨hI, ?_⟩⟩
    intro cl hcl
    simp only [List.mem_singleton] at hcl
    subst hcl
    intro z hz
    have hza : I.c a z := hz a (by simp)
    have hzb : I.c b z := hz b (by simp)
    rw [hy] at hza
    rw [(hy x).1 hx, ← hza] at hb
    exact absurd hzb hb

/-! ## Subsumption with a fresh nominal -/

section Fin

variable {n m : Nat}

/-- The clauses on the old names `Fin.castSucc` of `Fin (n + 1)`. -/
def liftO (O : Ontology (Fin n) (Fin m)) : Ontology (Fin (n + 1)) (Fin m) :=
  O.map (mapN Fin.castSucc)

/-- The ontology of the subsumption row: a fresh nominal `X = Fin.last n`
in `a` and not in `b`. -/
def subExt (O : Ontology (Fin n) (Fin m)) (a b : Fin n) : Ontology (Fin (n + 1)) (Fin m) :=
  liftO O ++ [.nom (Fin.last n), .base (.gci [Fin.last n] [a.castSucc]),
    .base (.gci [Fin.last n, b.castSucc] [])]

/-- `I` with the new name interpreted as `{x}`. -/
def extI (I : Interp D (Fin n) (Fin m)) (x : D) : Interp D (Fin (n + 1)) (Fin m) :=
  ⟨fun i y => if h : i.val < n then I.c ⟨i.val, h⟩ y else y = x, I.r⟩

theorem pull_extI (I : Interp D (Fin n) (Fin m)) (x : D) : pull (extI I x) Fin.castSucc = I := by
  cases I with
  | mk c r =>
    simp only [pull, extI, Interp.mk.injEq, and_true]
    funext a y
    simp

/-- **Subsumption rows.** `a ⊑ b` iff the ontology with a fresh nominal in
`a` and not in `b` is inconsistent. -/
theorem entailsSubN_iff (O : Ontology (Fin n) (Fin m)) (a b : Fin n) :
    EntailsSubN O a b ↔ ¬ ConsistentN (subExt O a b) := by
  constructor
  · rintro h ⟨D, hD, J, hJ⟩
    obtain ⟨hO, hx⟩ := models_append.1 hJ
    have hO' : models (pull J Fin.castSucc) O := (models_mapN J _ O).1 hO
    obtain ⟨x, hxX⟩ : NomAt J (Fin.last n) := hx _ List.mem_cons_self
    have hX : J.c (Fin.last n) x := (hxX x).2 rfl
    have h2 : satClause J (.base (.gci [Fin.last n] [a.castSucc])) := hx _ (by simp)
    have h3 : satClause J (.base (.gci [Fin.last n, b.castSucc] [])) := hx _ (by simp)
    obtain ⟨c, hc, hcx⟩ := h2 x (by simpa using hX)
    simp only [List.mem_singleton] at hc
    subst hc
    have hb := h D (pull J Fin.castSucc) hO' x hcx
    obtain ⟨c, hc, -⟩ := h3 x (by simp only [List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]; exact ⟨hX, hb⟩)
    simp at hc
  · intro hn D _ I hI x hx
    by_contra hb
    refine hn ⟨D, inferInstance, extI I x, models_append.2 ⟨?_, ?_⟩⟩
    · rw [liftO, models_mapN, pull_extI]
      exact hI
    · intro cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact ⟨x, fun y => by simp [extI]⟩
      · intro y hy
        have : y = x := by simpa [extI] using hy
        subst this
        exact ⟨_, List.mem_cons_self, by simpa [extI] using hx⟩
      · intro y hy
        have h1 : y = x := by simpa [extI] using hy (Fin.last n) (by simp)
        have h2 := hy b.castSucc (by simp)
        subst h1
        simp [extI] at h2
        exact absurd h2 hb

end Fin

/-! ## The reductions stay inside C2a -/

section Preserve

theorem roleLe_congr {C1 C2 : Type} {B : SRIQ.Ontology C1 Role} {B' : SRIQ.Ontology C2 Role}
    (h : ∀ body S, SRIQ.Clause.chain body S ∈ B ↔ SRIQ.Clause.chain body S ∈ B')
    (R S : RoleT Role) : SRIQ.RoleLe B R S ↔ SRIQ.RoleLe B' R S := by
  have hs : SRI.RoleStep (SRIQ.sriPart B) = SRI.RoleStep (SRIQ.sriPart B') := by
    funext R S
    simp only [SRI.RoleStep, SRIQ.mem_sriPart, SRIQ.ofSRI, h]
  unfold SRIQ.RoleLe SRI.RoleLe
  rw [hs]

theorem lowerL_append_gci (B : SRIQ.Ontology CName Role) (body head : List CName) :
    lowerL (B ++ [.gci body head]) = lowerL B := by
  simp [lowerL, List.filterMap_append]

theorem upperL_append_gci (B : SRIQ.Ontology CName Role) (body head : List CName) :
    upperL (B ++ [.gci body head]) = upperL B := by
  simp [upperL, List.filterMap_append]

theorem chain_mem_append_gci {B : SRIQ.Ontology CName Role} {body head : List CName}
    {rs : List (RoleT Role)} {S : RoleT Role} :
    SRIQ.Clause.chain rs S ∈ B ++ [.gci body head] ↔ SRIQ.Clause.chain rs S ∈ B := by
  simp

theorem basePart_gci (O : Ontology CName Role) (body head : List CName) :
    basePart (O ++ [.base (.gci body head)]) = basePart O ++ [.gci body head] := by
  simp [basePart, List.filterMap_append]

theorem noms_gci (O : Ontology CName Role) (body head : List CName) :
    noms (O ++ [.base (.gci body head)]) = noms O := by
  simp [noms, List.filterMap_append]

theorem nomOnly_append_bot {O : Ontology CName Role} {body : List CName} {X : CName}
    (h : NomOnly O X) : NomOnly (O ++ [.base (.gci body [])]) X := by
  refine ⟨by rw [noms_gci]; exact h.1, fun cl hcl => ?_⟩
  rw [noms_gci]
  rw [basePart_gci, List.mem_append, List.mem_singleton] at hcl
  rcases hcl with hcl | rfl
  · exact h.2 cl hcl
  · intro hX
    simp at hX

/-- Adding a gci with an empty head keeps C2a. -/
theorem isC2a_append_bot {O : Ontology CName Role} (h : IsC2a O) (body : List CName) :
    IsC2a (O ++ [.base (.gci body [])]) := by
  intro q hq hqn hqo q' hq' hle
  rw [basePart_gci, lowerL_append_gci] at hq
  rw [basePart_gci, upperL_append_gci] at hq'
  rw [noms_gci] at hqn
  rw [basePart_gci, roleLe_congr (fun _ _ => chain_mem_append_gci)] at hle
  exact h q hq hqn (fun ho => hqo (nomOnly_append_bot ho)) q' hq' hle

theorem isALCHOIQ_append_gci {O : Ontology CName Role} (h : IsALCHOIQ O) (body head : List CName) :
    IsALCHOIQ (O ++ [.base (.gci body head)]) := by
  intro rs S hcl
  rw [basePart_gci, chain_mem_append_gci] at hcl
  exact h rs S hcl

variable {n m : Nat}

theorem basePart_subExt (O : Ontology (Fin n) (Fin m)) (a b : Fin n) :
    basePart (subExt O a b) = (basePart O).map (mapC Fin.castSucc) ++
      [.gci [Fin.last n] [a.castSucc], .gci [Fin.last n, b.castSucc] []] := by
  simp only [subExt, liftO, basePart, List.filterMap_append, List.filterMap_map]
  congr 1
  · rw [List.map_filterMap]
    congr 1
    funext cl
    cases cl <;> rfl

theorem noms_subExt (O : Ontology (Fin n) (Fin m)) (a b : Fin n) :
    noms (subExt O a b) = (noms O).map Fin.castSucc ++ [Fin.last n] := by
  simp only [subExt, liftO, noms, List.filterMap_append, List.filterMap_map]
  congr 1
  · rw [List.map_filterMap]
    congr 1
    funext cl
    cases cl <;> rfl

theorem chain_mem_subExt {O : Ontology (Fin n) (Fin m)} {a b : Fin n} {rs : List (RoleT (Fin m))}
    {S : RoleT (Fin m)} :
    SRIQ.Clause.chain rs S ∈ basePart (subExt O a b) ↔ SRIQ.Clause.chain rs S ∈ basePart O := by
  rw [basePart_subExt]
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, reduceCtorEq,
    or_false]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp only [mapC, reduceCtorEq, SRIQ.Clause.chain.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem lowerL_subExt (O : Ontology (Fin n) (Fin m)) (a b : Fin n) :
    lowerL (basePart (subExt O a b)) =
      (lowerL (basePart O)).map fun q => (q.1.castSucc, q.2.1, q.2.2.1, q.2.2.2.castSucc) := by
  rw [basePart_subExt]
  simp only [lowerL, List.filterMap_append, List.filterMap_map]
  rw [List.filterMap_cons, List.filterMap_cons]
  simp only [List.filterMap_nil, List.append_nil, List.map_filterMap]
  congr 1
  funext cl
  cases cl <;> rfl

theorem upperL_subExt (O : Ontology (Fin n) (Fin m)) (a b : Fin n) :
    upperL (basePart (subExt O a b)) =
      (upperL (basePart O)).map fun q => (q.1.castSucc, q.2.1, q.2.2.1, q.2.2.2.castSucc) := by
  rw [basePart_subExt]
  simp only [upperL, List.filterMap_append, List.filterMap_map]
  rw [List.filterMap_cons, List.filterMap_cons]
  simp only [List.filterMap_nil, List.append_nil, List.map_filterMap]
  congr 1
  funext cl
  cases cl <;> rfl

theorem posOK_mapC {N : List (Fin n)} {X : Fin n} {cl : SRIQ.Clause (Fin n) (Fin m)}
    (h : PosOK N X cl) : PosOK (N.map Fin.castSucc ++ [Fin.last n]) X.castSucc
      (mapC Fin.castSucc cl) := by
  cases cl with
  | gci body head =>
    intro hX
    simp only [List.mem_map] at hX
    obtain ⟨X', hX', he⟩ := hX
    obtain rfl := Fin.castSucc_injective _ he
    obtain ⟨a, ha, rfl, rfl⟩ := h hX'
    exact ⟨a.castSucc, List.mem_append_left _ (List.mem_map_of_mem ha), rfl, rfl⟩
  | exRight _ _ b => exact fun he => h (Fin.castSucc_injective _ he)
  | allRight _ _ b => exact fun he => h (Fin.castSucc_injective _ he)
  | atLeast _ _ _ b => exact fun he => h (Fin.castSucc_injective _ he)
  | atMost _ _ _ _ => trivial
  | chain _ _ => trivial

theorem nomOnly_subExt {O : Ontology (Fin n) (Fin m)} {a b X : Fin n} (h : NomOnly O X) :
    NomOnly (subExt O a b) X.castSucc := by
  refine ⟨?_, fun cl hcl => ?_⟩
  · rw [noms_subExt]
    simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists, not_and]
    exact ⟨fun c hc he => h.1 (Fin.castSucc_injective _ he ▸ hc),
      Fin.castSucc_ne_last X⟩
  · rw [noms_subExt]
    rw [basePart_subExt, List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · obtain ⟨cl0, hcl0, rfl⟩ := List.mem_map.1 hcl
      exact posOK_mapC (h.2 cl0 hcl0)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · intro hX
        simp only [List.mem_singleton] at hX
        exact ⟨Fin.last n, List.mem_append_right _ (List.mem_singleton_self _), rfl, by rw [hX]⟩
      · intro hX
        simp at hX

/-- The subsumption row keeps C2a: the fresh nominal is a nominal name. -/
theorem isC2a_subExt {O : Ontology (Fin n) (Fin m)} (h : IsC2a O) (a b : Fin n) :
    IsC2a (subExt O a b) := by
  intro q hq hqn hqo q' hq' hle
  rw [lowerL_subExt] at hq
  rw [upperL_subExt] at hq'
  rw [noms_subExt] at hqn
  rw [roleLe_congr (B' := basePart O) (fun _ _ => chain_mem_subExt)] at hle
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq
  obtain ⟨q1, hq1, rfl⟩ := List.mem_map.1 hq'
  exact h q0 hq0 (fun hn => hqn (List.mem_append_left _ (List.mem_map_of_mem hn)))
    (fun ho => hqo (nomOnly_subExt ho)) q1 hq1 hle

theorem isALCHOIQ_subExt {O : Ontology (Fin n) (Fin m)} (h : IsALCHOIQ O) (a b : Fin n) :
    IsALCHOIQ (subExt O a b) := by
  intro rs S hcl
  exact h rs S (chain_mem_subExt.1 hcl)

end Preserve

/-! ## Procedure rows -/

namespace Proc

open ContextCalculus.SRIQN.Proc

variable {n m : Nat}

/-- The subsumption row `a ⊑ b`, with an optional countermodel hint for
`subExt O a b`. -/
def subRowN (O : Ontology (Fin n) (Fin m)) (a b : Fin n) (hint : Option (HintN (n + 1) m)) :
    Bool :=
  !consistentN (basePart (subExt O a b)) (noms (subExt O a b)) hint

/-- The row `a ⊑ b` for a nominal name `a`, with an optional countermodel
hint for the ontology with `a ⊓ b ⊑ ⊥`. -/
def nomRowN (O : Ontology (Fin n) (Fin m)) (a b : Fin n) (hint : Option (HintN n m)) : Bool :=
  !consistentN (basePart (O ++ [.base (.gci [a, b] [])])) (noms (O ++ [.base (.gci [a, b] [])]))
    hint

theorem subRowN_iff {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (hC : IsC2a O) (a b : Fin n)
    (hint : Option (HintN (n + 1) m)) : subRowN O a b hint = true ↔ EntailsSubN O a b := by
  rw [subRowN, Bool.not_eq_true', entailsSubN_iff, ← consistentN_iff (isALCHOIQ_subExt hA a b)
    (isC2a_subExt hC a b) hint]
  simp

theorem nomRowN_iff {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (hC : IsC2a O) {a : Fin n}
    (ha : a ∈ noms O) (b : Fin n) (hint : Option (HintN n m)) :
    nomRowN O a b hint = true ↔ EntailsSubN O a b := by
  rw [nomRowN, Bool.not_eq_true', entailsSubN_nom_iff O ha, ← consistentN_iff
    (isALCHOIQ_append_gci hA _ _) (isC2a_append_bot hC _) hint]
  simp

end Proc

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.entailsSubN_iff
#print axioms ContextCalculus.SRIQN.entailsSubN_nom_iff
#print axioms ContextCalculus.SRIQN.isC2a_subExt
#print axioms ContextCalculus.SRIQN.Proc.subRowN_iff
#print axioms ContextCalculus.SRIQN.Proc.nomRowN_iff
