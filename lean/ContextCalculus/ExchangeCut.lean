import ContextCalculus.CompletenessExchange

/-!
# Hypotheses, merge hypotheses and the exchange cut

`CompletenessExchange.lean` and `ExchangeEquality.lean` treat the ground
context as a clause set that is closed under ordered resolution on its own,
and they ask it to deliver every interface clause.  KM's ground context is
not such a set: it fires an ontology clause only on atoms it holds in a head,
and it reasons under an atom that only a receiver holds only after the
receiver pushed it as a hypothesis `A → A` (r-Succ).  The clauses it then
derives carry the hypotheses in their bodies, as labels.  This file states
that exchange at the propositional level and proves it complete, with the
conditions under which a receiver may skip a push.

Setting (docs/PER-CONTEXT-ORDERING.md section 12):

* `P` is the ground theory: every ground instance of an ontology clause and
  every ground fact (the nuclei).
* `SG` is the ground context.  It holds the hypothesis clause `h → h` of
  every hypothesis the receiver pushed (`Hu h`), and it is closed under
  *labelled ordered hyperresolution* (`ClosedHyper`): for a nucleus of `P`
  and, for each body atom `b` of the nucleus, a clause of `SG` whose head has
  `b` strictly on top, `SG` holds the hyperresolvent up to strengthening.
  Body atoms of `SG` clauses are labels; they are never resolved inside `SG`.
  This is KM's Hyper rule in the ground context.
* `SQ` is the receiver (a query or ordinary context), closed under ordered
  resolution (`ClosedR`).  Both use the same rank `rk`: KM's literal order is
  the same function in every context.
* The guard delivers every clause of `SG` whose atoms are interface atoms and
  whose body atoms are hypotheses of the receiver (`hdeliver`).
* *Demand*: every interface atom that is the strict maximum of a receiver
  clause `c` is a hypothesis of the receiver, or `c` is `Covered`: the ground
  context holds a clause `e` whose head atoms are head atoms of `c` and
  whose body atoms are hypotheses of the receiver that every model of the
  receiver makes true whenever `c` produces its maximum (a body atom of `c`,
  or the head atom of a receiver clause whose other atoms are those of `c`).

Main results (all `sorry`-free):

* `labelledModel_sat_nuclei`: the candidate model `labelledModel rk SG J`,
  built from the clauses of `SG` whose labels lie in `J`, satisfies the
  ground theory `P` (the propositional skeleton of the paper's ground
  fragment built under the hypotheses `Γ_o`).
* `cut_exchange_complete`: refutational completeness of the receiver against
  `P`, under the demand condition with covers.
* `cut_unit_readout_complete`: the positive unit readout in the same
  setting.
* `pushed_exchange_complete`: the special case without covers, the exchange
  of the paper's calculus in which every demanded atom is pushed.  For a
  query context whose element may be the individual `o`, the paper's proof
  uses the ground atoms `Γ_o` of the query model as hypotheses; the clause
  `⊤ → Δ'' ∨ K(o)` that Join case 3 encodes (core `⊤ → K(x)`, bridge
  `⊤ → Δ'' ∨ x ≈ o`) has `K(o)` as its demanded atom, and only the merge
  hypothesis `K(o) → K(o)` meets the demand.
* `no_merge_hypothesis_counterexample`: without it the exchange is
  incomplete.  Ground theory `{K(o) → D(o)}`, receiver `{⊤ → K(o)}`, empty
  ground context: both are closed, the guard has nothing to deliver, the
  union entails `D(o)`, and the receiver derives neither `⊥` nor `→ D(o)`
  (the skeleton of seed r1600, docs/NOMINALS-CB.md section 10).
* `horn_unit_readout`: if every body-free clause of the closed ground
  context is a unit, every atom the ground theory entails is such a unit
  (the readout condition of the nominal-label cache).
* `exists_common_rank`: a strict partial order and an interface that is
  downward closed among the ground context's atoms admit one injective rank
  that extends the order and keeps every ground-context atom below an
  interface atom in the interface.

Scope.  Equalities are opaque atoms; congruence (the Eq rule, Join case 3 as
the clause above, rewriting `o` to `x`) and locality of the receiver's atoms
are argued in docs/PER-CONTEXT-ORDERING.md, not mechanised.  Which receiver
clauses KM covers by pushes, by covers, and by the argued simulation of the
ground context (pushes blocked by the r-Succ side condition (*), Join case 3
for non-core atoms) is listed there.
-/

namespace ContextCalculus.ExchangeCut

open ContextCalculus.PropRes
open ContextCalculus.Exchange

set_option linter.unusedSectionVars false

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Labelled ordered hyperresolution -/

/-- `a` is the strictly rank-maximal head atom of `e`; body atoms (labels)
are not compared. -/
def HeadMax (rk : Atom → ℕ) (e : PClause Atom) (a : Atom) : Prop :=
  a ∈ e.pos ∧ ∀ b ∈ e.pos, b ≠ a → rk b < rk a

/-- The hyperresolvent of the nucleus `n` with the electron `E b` for every
body atom `b` of `n`: the labels of the electrons, their remaining head
atoms, and the head of the nucleus. -/
def hyperRes (n : PClause Atom) (E : Atom → PClause Atom) : PClause Atom :=
  ⟨n.neg.biUnion (fun b => (E b).neg), n.neg.biUnion (fun b => (E b).pos.erase b) ∪ n.pos⟩

/-- Closure of the ground context `SG` under labelled ordered
hyperresolution with the nuclei `P` (KM's Hyper in the ground context). -/
def ClosedHyper (rk : Atom → ℕ) (P SG : Finset (PClause Atom)) : Prop :=
  ∀ n ∈ P, ∀ E : Atom → PClause Atom,
    (∀ b ∈ n.neg, E b ∈ SG ∧ HeadMax rk (E b) b) →
    Tautological (hyperRes n E) ∨ ∃ r ∈ SG, Strengthens r (hyperRes n E)

/-- The hypothesis clause `h → h` (r-Succ, merge hypotheses). -/
def hyp (h : Atom) : PClause Atom := ⟨{h}, {h}⟩

/-- Closure on maximal head atoms of a strict relation implies closure under
every rank that extends it (the transfer used for KM's partial order). -/
def ClosedHyperMaximal (lt : Atom → Atom → Prop) (P SG : Finset (PClause Atom)) : Prop :=
  ∀ n ∈ P, ∀ E : Atom → PClause Atom,
    (∀ b ∈ n.neg, E b ∈ SG ∧ b ∈ (E b).pos ∧ ∀ c ∈ (E b).pos, ¬ lt b c) →
    Tautological (hyperRes n E) ∨ ∃ r ∈ SG, Strengthens r (hyperRes n E)

theorem closedHyper_of_maximal {lt : Atom → Atom → Prop} {rk : Atom → ℕ}
    (hext : Extends lt rk) {P SG : Finset (PClause Atom)}
    (h : ClosedHyperMaximal lt P SG) : ClosedHyper rk P SG := by
  intro n hn E hE
  refine h n hn E (fun b hb => ⟨(hE b hb).1, (hE b hb).2.1, ?_⟩)
  intro c hc hlt
  have h1 := hext b c hlt
  by_cases hcb : c = b
  · subst hcb; exact lt_irrefl _ h1
  · exact absurd ((hE b hb).2.2 c hc hcb) (not_lt.mpr h1.le)

/-! ## The ground model under a set of true labels -/

section Model

variable (rk : Atom → ℕ) (SG : Finset (PClause Atom)) (J : Atom → Prop)

open Classical in
/-- Candidate model of the ground context under the true labels `J`: an atom
is true when it is a true label or the strict head maximum of a clause whose
labels are true and whose other head atoms are false. -/
noncomputable def labelledModel : Atom → Prop :=
  (InvImage.wf rk wellFounded_lt).fix fun a ih =>
    J a ∨ ∃ e ∈ SG, ∃ hm : HeadMax rk e a, (∀ h ∈ e.neg, J h) ∧
      (∀ b (hb : b ∈ e.pos) (hba : b ≠ a), ¬ ih b (hm.2 b hb hba))

theorem labelledModel_def (a : Atom) :
    labelledModel rk SG J a ↔
      J a ∨ ∃ e ∈ SG, HeadMax rk e a ∧ (∀ h ∈ e.neg, J h) ∧
        ∀ b ∈ e.pos, b ≠ a → ¬ labelledModel rk SG J b := by
  classical
  unfold labelledModel
  rw [(InvImage.wf rk wellFounded_lt).fix_eq]
  constructor
  · rintro (h | ⟨e, he, hm, hneg, hpos⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, hm, hneg, fun b hb hba => hpos b hb hba⟩
  · rintro (h | ⟨e, he, hm, hneg, hpos⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, hm, hneg, fun b hb hba => hpos b hb hba⟩

theorem labelledModel_of_label {a : Atom} (h : J a) : labelledModel rk SG J a :=
  (labelledModel_def rk SG J a).mpr (Or.inl h)

/-- Every clause of `SG` whose labels are true holds in the candidate model,
provided no such clause has an empty head. -/
theorem labelledModel_sat_labelled (hinj : Function.Injective rk)
    (hnobot : ∀ e ∈ SG, (∀ h ∈ e.neg, J h) → e.pos.Nonempty) :
    ∀ e ∈ SG, (∀ h ∈ e.neg, J h) → ∃ b ∈ e.pos, labelledModel rk SG J b := by
  intro e he hJ
  by_contra hnone
  push Not at hnone
  obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image e.pos rk (hnobot e he hJ)
  have hhm : HeadMax rk e m :=
    ⟨hm, fun b hb hbm => lt_of_le_of_ne (hmmax b hb) (fun h => hbm (hinj h))⟩
  exact hnone m hm ((labelledModel_def rk SG J m).mpr
    (Or.inr ⟨e, he, hhm, hJ, fun b hb _ => hnone b hb⟩))

/-- **The candidate model satisfies the ground theory.**  If `SG` is closed
under labelled ordered hyperresolution with the nuclei `P`, holds the
hypothesis clause of every true label, and has no clause with true labels
and an empty head, then `labelledModel rk SG J` is a model of `P`. -/
theorem labelledModel_sat_nuclei (hinj : Function.Injective rk)
    {P : Finset (PClause Atom)} (hcl : ClosedHyper rk P SG)
    (hhyp : ∀ h, J h → hyp h ∈ SG)
    (hnobot : ∀ e ∈ SG, (∀ h ∈ e.neg, J h) → e.pos.Nonempty) :
    ∀ n ∈ P, n.sat (labelledModel rk SG J) := by
  classical
  intro n hn hneg
  by_contra hpos
  push Not at hpos
  -- an electron for every body atom of the nucleus
  have hex : ∀ b ∈ n.neg, ∃ e : PClause Atom, e ∈ SG ∧ HeadMax rk e b ∧
      (∀ h ∈ e.neg, J h) ∧ ∀ x ∈ e.pos, x ≠ b → ¬ labelledModel rk SG J x := by
    intro b hb
    rcases (labelledModel_def rk SG J b).mp (hneg b hb) with hJb | ⟨e, he, hm, hl, hp⟩
    · refine ⟨hyp b, hhyp b hJb, ⟨by simp [hyp], ?_⟩, ?_, ?_⟩
      · intro x hx hxb; simp [hyp] at hx; exact absurd hx hxb
      · intro h hh; simp [hyp] at hh; exact hh ▸ hJb
      · intro x hx hxb; simp [hyp] at hx; exact absurd hx hxb
    · exact ⟨e, he, hm, hl, hp⟩
  haveI : Inhabited (PClause Atom) := ⟨PClause.bot⟩
  choose! E hE using hex
  have hresNeg : ∀ x ∈ (hyperRes n E).neg, J x := by
    intro x hx
    simp only [hyperRes, Finset.mem_biUnion] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    exact (hE b hb).2.2.1 x hxb
  have hresPos : ∀ x ∈ (hyperRes n E).pos, ¬ labelledModel rk SG J x := by
    intro x hx
    simp only [hyperRes, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with ⟨b, hb, hxb⟩ | hx
    · exact (hE b hb).2.2.2 x (Finset.mem_of_mem_erase hxb) (Finset.ne_of_mem_erase hxb)
    · exact hpos x hx
  rcases hcl n hn E (fun b hb => ⟨(hE b hb).1, (hE b hb).2.1⟩) with htaut | ⟨r, hr, hstr⟩
  · obtain ⟨x, hxn, hxp⟩ := htaut
    exact hresPos x hxp (labelledModel_of_label rk SG J (hresNeg x hxn))
  · obtain ⟨x, hx, hMx⟩ := labelledModel_sat_labelled rk SG J hinj hnobot r hr
      (fun h hh => hresNeg h (hstr.1 hh))
    exact hresPos x (hstr.2 hx) hMx

end Model

/-! ## The exchange with covers -/

/-- The receiver clause `c` with strict maximum `a` is *covered*: the ground
context holds `e` with every head atom a head atom of `c` and every label a
hypothesis of the receiver that is a body atom of `c` or the head atom of a
receiver clause `v` whose body atoms are body atoms of `c` and whose other
head atoms are head atoms of `c` other than `a` (KM: Join case 3 read as the
clause `⊤ → Δ'' ∨ K(o)`). -/
def Covered (SG SQ : Finset (PClause Atom)) (Hu : Atom → Prop)
    (c : PClause Atom) (a : Atom) : Prop :=
  ∃ e ∈ SG, e.pos ⊆ c.pos ∧ ∀ h ∈ e.neg, Hu h ∧
    (h ∈ c.neg ∨ ∃ v ∈ SQ, v.neg ⊆ c.neg ∧ ∀ b ∈ v.pos, b = h ∨ (b ∈ c.pos ∧ b ≠ a))

theorem covered_mono {SG SQ SQ' : Finset (PClause Atom)} {Hu : Atom → Prop}
    {c : PClause Atom} {a : Atom} (hsub : SQ ⊆ SQ') (h : Covered SG SQ Hu c a) :
    Covered SG SQ' Hu c a := by
  obtain ⟨e, he, hpos, hneg⟩ := h
  refine ⟨e, he, hpos, fun h hh => ⟨(hneg h hh).1, ?_⟩⟩
  rcases (hneg h hh).2 with h1 | ⟨v, hv, hvn, hvp⟩
  · exact Or.inl h1
  · exact Or.inr ⟨v, hsub hv, hvn, hvp⟩

/-- The exchange conditions with hypotheses.  `rk` is the common rank,
`V` the receiver's interface, `Hu` the hypotheses it pushed. -/
structure CutCond (rk : Atom → ℕ) (V Hu : Atom → Prop)
    (P SG SQ : Finset (PClause Atom)) : Prop where
  hyp_mem : ∀ h, Hu h → hyp h ∈ SG
  hyp_iface : ∀ h, Hu h → V h
  lower : ∀ a b, V a → rk b < rk a → Occurs SG b → V b
  deliver : ∀ e ∈ SG, (∀ a ∈ lits e, V a) → (∀ h ∈ e.neg, Hu h) →
    ∃ d ∈ SQ, Strengthens d e
  demand : ∀ c ∈ SQ, ∀ a, StrictMaxR rk c a → V a → Hu a ∨ Covered SG SQ Hu c a
  local_ : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ V a → ¬ Occurs P a

/-- The receiver's candidate model (empty interface). -/
noncomputable abbrev recvModel (rk : Atom → ℕ) (SQ : Finset (PClause Atom)) : Atom → Prop :=
  ItrueOver rk SQ (fun _ => False) (fun _ => False)

theorem recvModel_def (rk : Atom → ℕ) (SQ : Finset (PClause Atom)) (a : Atom) :
    recvModel rk SQ a ↔ ∃ c ∈ SQ, StrictMaxR rk c a ∧
      (∀ b ∈ c.neg, recvModel rk SQ b) ∧ (∀ b ∈ c.pos, b ≠ a → ¬ recvModel rk SQ b) := by
  unfold recvModel
  rw [ItrueOver_def]
  simp

theorem recvModel_sat (rk : Atom → ℕ) (hinj : Function.Injective rk)
    {SQ : Finset (PClause Atom)} (hcl : ClosedR rk SQ) (hbot : PClause.bot ∉ SQ) :
    ∀ c ∈ SQ, c.sat (recvModel rk SQ) := by
  refine based_model_correct rk SQ (fun _ => False) (fun _ => False) hinj hcl
    (fun _ _ h _ => h) ?_
  intro c hc hall
  have hempty : lits c = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    exact hall a ha
  exact absurd ((lits_eq_empty_bot c hempty) ▸ hc) hbot

/-- **Extension across the exchange.**  Under `CutCond`, the receiver's
candidate model extends to a model of the ground theory `P` and the
receiver that agrees with it on the receiver's atoms. -/
theorem cut_extend (rk : Atom → ℕ) (hinj : Function.Injective rk)
    {V Hu : Atom → Prop} {P SG SQ : Finset (PClause Atom)}
    (hclG : ClosedHyper rk P SG) (hclQ : ClosedR rk SQ)
    (hbot : PClause.bot ∉ SQ) (hx : CutCond rk V Hu P SG SQ) :
    ∃ K : Atom → Prop, (∀ c ∈ P ∪ SQ, c.sat K) ∧
      (∀ c ∈ SQ, ∀ a ∈ lits c, K a ↔ recvModel rk SQ a) := by
  classical
  set Ju := recvModel rk SQ with hJu
  have hJuQ := recvModel_sat rk hinj hclQ hbot
  let J : Atom → Prop := fun h => Hu h ∧ Ju h
  let M := labelledModel rk SG J
  -- no ground clause with true labels has an empty head
  have hnobot : ∀ e ∈ SG, (∀ h ∈ e.neg, J h) → e.pos.Nonempty := by
    intro e he hJ
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ a ∈ lits e, V a := by
      intro a ha
      rcases mem_lits.mp ha with h | h
      · exact hx.hyp_iface a (hJ a h).1
      · rw [hne] at h; simp at h
    obtain ⟨d, hd, hstr⟩ := hx.deliver e he hall (fun h hh => (hJ h hh).1)
    obtain ⟨b, hb, _⟩ := hJuQ d hd (fun h hh => (hJ h (hstr.1 hh)).2)
    have := hstr.2 hb
    rw [hne] at this; simp at this
  -- agreement on the interface, by strong induction on the rank
  have agree : ∀ n : ℕ, ∀ a : Atom, rk a = n → V a → (M a ↔ Ju a) := by
    intro n0
    induction n0 using Nat.strong_induction_on with
    | _ n ih =>
    intro a hrk hVa
    subst hrk
    constructor
    · intro hMa
      rcases (labelledModel_def rk SG J a).mp hMa with hJa | ⟨e, he, hm, hl, hp⟩
      · exact hJa.2
      · have hall : ∀ x ∈ lits e, V x := by
          intro x hx'
          rcases mem_lits.mp hx' with h | h
          · exact hx.hyp_iface x (hl x h).1
          · by_cases hxa : x = a
            · exact hxa ▸ hVa
            · exact hx.lower a x hVa (hm.2 x h hxa) ⟨e, he, hx'⟩
        obtain ⟨d, hd, hstr⟩ := hx.deliver e he hall (fun h hh => (hl h hh).1)
        obtain ⟨x, hxd, hJx⟩ := hJuQ d hd (fun h hh => (hl h (hstr.1 hh)).2)
        have hxe := hstr.2 hxd
        by_cases hxa : x = a
        · exact hxa ▸ hJx
        · have hlt := hm.2 x hxe hxa
          have hVx := hall x (mem_lits.mpr (Or.inr hxe))
          exact absurd ((ih (rk x) hlt x rfl hVx).mpr hJx) (hp x hxe hxa)
    · intro hJa
      obtain ⟨c, hc, hmax, hcneg, hcpos⟩ := (recvModel_def rk SQ a).mp hJa
      rcases hx.demand c hc a hmax hVa with hHa | ⟨e, he, hepos, heneg⟩
      · exact labelledModel_of_label rk SG J ⟨hHa, hJa⟩
      · have hlab : ∀ h ∈ e.neg, J h := by
          intro h hh
          refine ⟨(heneg h hh).1, ?_⟩
          rcases (heneg h hh).2 with hcn | ⟨v, hv, hvn, hvp⟩
          · exact hcneg h hcn
          · obtain ⟨b, hb, hJb⟩ := hJuQ v hv (fun y hy => hcneg y (hvn hy))
            rcases hvp b hb with rfl | ⟨hbc, hba⟩
            · exact hJb
            · exact absurd hJb (hcpos b hbc hba)
        obtain ⟨x, hxe, hMx⟩ := labelledModel_sat_labelled rk SG J hinj hnobot e he hlab
        by_cases hxa : x = a
        · exact hxa ▸ hMx
        · have hxc := hepos hxe
          have hlt := hmax.2.2 x (mem_lits.mpr (Or.inr hxc)) hxa
          have hVx := hx.lower a x hVa hlt ⟨e, he, mem_lits.mpr (Or.inr hxe)⟩
          exact absurd ((ih (rk x) hlt x rfl hVx).mp hMx) (hcpos x hxc hxa)
  have hMP := labelledModel_sat_nuclei rk SG J hinj hclG
    (fun h hJ => hx.hyp_mem h hJ.1) hnobot
  let K : Atom → Prop := fun a => if Occurs P a then M a else Ju a
  have hKP : ∀ c ∈ P, ∀ a ∈ lits c, K a ↔ M a := by
    intro c hc a ha
    have : Occurs P a := ⟨c, hc, ha⟩
    simp only [K, this, if_true]
  have hKQ : ∀ c ∈ SQ, ∀ a ∈ lits c, K a ↔ Ju a := by
    intro c hc a ha
    by_cases hocc : Occurs P a
    · have hVa : V a := by
        by_contra hnot
        exact hx.local_ c hc a ha hnot hocc
      simp only [K, hocc, if_true]
      exact agree (rk a) a rfl hVa
    · simp only [K, hocc, if_false]
  refine ⟨K, ?_, hKQ⟩
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · intro hneg
    obtain ⟨b, hb, hMb⟩ := hMP c hc (fun a ha =>
      (hKP c hc a (mem_lits.mpr (Or.inl ha))).mp (hneg a ha))
    exact ⟨b, hb, (hKP c hc b (mem_lits.mpr (Or.inr hb))).mpr hMb⟩
  · intro hneg
    obtain ⟨b, hb, hJb⟩ := hJuQ c hc (fun a ha =>
      (hKQ c hc a (mem_lits.mpr (Or.inl ha))).mp (hneg a ha))
    exact ⟨b, hb, (hKQ c hc b (mem_lits.mpr (Or.inr hb))).mpr hJb⟩

/-- **Refutational completeness of the exchange with hypotheses and covers.**
If the ground theory and the receiver are jointly unsatisfiable, the receiver
derives `⊥`. -/
theorem cut_exchange_complete (rk : Atom → ℕ) (hinj : Function.Injective rk)
    {V Hu : Atom → Prop} {P SG SQ : Finset (PClause Atom)}
    (hclG : ClosedHyper rk P SG) (hclQ : ClosedR rk SQ)
    (hx : CutCond rk V Hu P SG SQ) (hunsat : Unsat (P ∪ SQ)) :
    PClause.bot ∈ SQ := by
  by_contra hbot
  obtain ⟨K, hK, _⟩ := cut_extend rk hinj hclG hclQ hbot hx
  exact hunsat ⟨K, hK⟩

/-- **Positive unit readout with hypotheses and covers.**  If `P ∪ SQ`
entails an atom `b` that is rank-least among the receiver's atoms and is an
interface atom or outside the ground theory, the receiver holds `⊥` or a
clause that strengthens `→ b`. -/
theorem cut_unit_readout_complete (rk : Atom → ℕ) (hinj : Function.Injective rk)
    {V Hu : Atom → Prop} {P SG SQ : Finset (PClause Atom)}
    (hclG : ClosedHyper rk P SG) (hclQ : ClosedR rk SQ)
    (hx : CutCond rk V Hu P SG SQ) (b : Atom)
    (hleast : ∀ c ∈ SQ, ∀ a ∈ lits c, a ≠ b → rk b < rk a)
    (hbloc : V b ∨ ¬ Occurs P b)
    (hent : ∀ I : Atom → Prop, (∀ c ∈ P ∪ SQ, c.sat I) → I b) :
    PClause.bot ∈ SQ ∨ ∃ d ∈ SQ, Strengthens d (unit b) := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨hbot, hnounit⟩ := hnot
  let SQ' : Finset (PClause Atom) := insert (negUnit b) SQ
  have hsub : SQ ⊆ SQ' := Finset.subset_insert _ _
  have hmaxIsUnit : ∀ d ∈ SQ, StrictMaxR rk d b → Strengthens d (unit b) := by
    intro d hd hmax
    refine ⟨?_, ?_⟩
    · intro a ha
      exfalso
      by_cases hab : a = b
      · exact hmax.2.1 (hab ▸ ha)
      · have h1 := hmax.2.2 a (mem_lits.mpr (Or.inl ha)) hab
        have h2 := hleast d hd a (mem_lits.mpr (Or.inl ha)) hab
        omega
    · intro a ha
      by_cases hab : a = b
      · simp [unit, hab]
      · exfalso
        have h1 := hmax.2.2 a (mem_lits.mpr (Or.inr ha)) hab
        have h2 := hleast d hd a (mem_lits.mpr (Or.inr ha)) hab
        omega
  have hclQ' : ClosedR rk SQ' := by
    intro d hd c hc a hmax hneg hub
    rcases Finset.mem_insert.mp hd with hdEq | hdQ
    · subst hdEq; exact absurd hmax.1 (by simp [negUnit])
    rcases Finset.mem_insert.mp hc with hcEq | hcQ
    · subst hcEq
      have hab : a = b := by simpa [negUnit] using hneg
      subst hab
      exact absurd (hmaxIsUnit d hdQ hmax) (hnounit d hdQ)
    · rcases hclQ d hdQ c hcQ a hmax hneg hub with h | ⟨r, hr, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, hs⟩
  have hbot' : PClause.bot ∉ SQ' := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · have : (PClause.bot : PClause Atom).neg = (negUnit b).neg := by rw [h]
      simp [PClause.bot, negUnit] at this
    · exact hbot h
  have hx' : CutCond rk V Hu P SG SQ' := by
    refine ⟨hx.hyp_mem, hx.hyp_iface, hx.lower, ?_, ?_, ?_⟩
    · intro e he hall hneg
      obtain ⟨d, hd, hs⟩ := hx.deliver e he hall hneg
      exact ⟨d, hsub hd, hs⟩
    · intro c hc a hmax hVa
      rcases Finset.mem_insert.mp hc with rfl | hcQ
      · exact absurd hmax.1 (by simp [negUnit])
      · rcases hx.demand c hcQ a hmax hVa with h | h
        · exact Or.inl h
        · exact Or.inr (covered_mono hsub h)
    · intro c hc a ha hnV
      rcases Finset.mem_insert.mp hc with rfl | hcQ
      · have hab : a = b := by simpa [lits, negUnit] using ha
        subst hab
        rcases hbloc with h | h
        · exact absurd h hnV
        · exact h
      · exact hx.local_ c hcQ a ha hnV
  obtain ⟨K, hK, _⟩ := cut_extend rk hinj hclG hclQ' hbot' hx'
  have hKb : K b := hent K (fun c hc => by
    rcases Finset.mem_union.mp hc with h | h
    · exact hK c (Finset.mem_union_left _ h)
    · exact hK c (Finset.mem_union_right _ (hsub h)))
  obtain ⟨x, hx'', _⟩ := hK (negUnit b) (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
    (by intro a ha; simp [negUnit] at ha; exact ha ▸ hKb)
  simp [negUnit] at hx''

/-- **The paper's exchange: every demanded atom pushed.**  The special case
of `cut_exchange_complete` without covers.  For a query context blocked by
the r-Succ side condition (*), the demanded atoms of the Join case 3 clauses
`⊤ → Δ'' ∨ K(o)` are the merge hypotheses `K(o)`. -/
theorem pushed_exchange_complete (rk : Atom → ℕ) (hinj : Function.Injective rk)
    {V Hu : Atom → Prop} {P SG SQ : Finset (PClause Atom)}
    (hclG : ClosedHyper rk P SG) (hclQ : ClosedR rk SQ)
    (hyp_mem : ∀ h, Hu h → hyp h ∈ SG) (hyp_iface : ∀ h, Hu h → V h)
    (lower : ∀ a b, V a → rk b < rk a → Occurs SG b → V b)
    (deliver : ∀ e ∈ SG, (∀ a ∈ lits e, V a) → (∀ h ∈ e.neg, Hu h) →
      ∃ d ∈ SQ, Strengthens d e)
    (pushed : ∀ c ∈ SQ, ∀ a, StrictMaxR rk c a → V a → Hu a)
    (local_ : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ V a → ¬ Occurs P a)
    (hunsat : Unsat (P ∪ SQ)) :
    PClause.bot ∈ SQ :=
  cut_exchange_complete rk hinj hclG hclQ
    ⟨hyp_mem, hyp_iface, lower, deliver,
      fun c hc a hmax hVa => Or.inl (pushed c hc a hmax hVa), local_⟩ hunsat

/-- A receiver clause that the ground context holds verbatim (up to
strengthening, with the receiver's hypotheses as labels) is covered for
every atom: the cut of `Engine::rsucc_covered` for delivered clauses. -/
theorem covered_of_strengthened {SG SQ : Finset (PClause Atom)} {Hu : Atom → Prop}
    {c e : PClause Atom} (a : Atom) (he : e ∈ SG) (hstr : Strengthens e c)
    (hHu : ∀ h ∈ e.neg, Hu h) : Covered SG SQ Hu c a :=
  ⟨e, he, hstr.2, fun h hh => ⟨hHu h hh, Or.inl (hstr.1 hh)⟩⟩

/-! ## One rank for both contexts -/

/-- A strict partial order and an interface that is downward closed among the
ground context's atoms (R2: no ground-context atom outside the interface lies
below an interface atom) admit one injective rank that extends the order and
keeps every ground-context atom below an interface atom in the interface. -/
theorem exists_common_rank [Fintype Atom]
    (lt : Atom → Atom → Prop) [DecidableRel lt]
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (V G : Atom → Prop) [DecidablePred V]
    (hdown : ∀ a b, lt a b → V b → G a → V a) :
    ∃ rk : Atom → ℕ, Function.Injective rk ∧ Extends lt rk ∧
      ∀ a b, V a → rk b < rk a → G b → V b := by
  classical
  let V' : Atom → Prop := fun z => V z ∨ ∃ a, V a ∧ lt z a
  have hdown' : ∀ a b, lt a b → V' b → V' a := by
    intro a b hab hb
    rcases hb with hb | ⟨c, hc, hbc⟩
    · exact Or.inr ⟨b, hb, hab⟩
    · exact Or.inr ⟨c, hc, htrans a b c hab hbc⟩
  obtain ⟨rk, hinj, hext, hlow⟩ :=
    exists_rank_extending_lower lt hirrefl htrans V' hdown'
  refine ⟨rk, hinj, hext, ?_⟩
  intro a b hVa hlt hGb
  rcases hlow a b (Or.inl hVa) hlt with h | ⟨c, hc, hbc⟩
  · exact h
  · exact hdown b c hbc hc hGb

/-! ## Without the merge hypothesis the exchange is incomplete -/

/-- Atom `0` is `K(o)` (the query core at the individual `o`), atom `1` is
`D(o)`. -/
def mhRank : Fin 2 → ℕ := fun a => (a : ℕ)

/-- Ground theory: the instance `K(o) → D(o)`. -/
def mhP : Finset (PClause (Fin 2)) := {⟨{0}, {1}⟩}

/-- Receiver: the Join case 3 clause `⊤ → K(o)` of a query context whose
core is `K(x)` and whose bridge is `⊤ → x ≈ o`. -/
def mhSQ : Finset (PClause (Fin 2)) := {⟨∅, {0}⟩}

theorem no_merge_hypothesis_counterexample :
    ClosedHyper mhRank mhP ∅ ∧ ClosedR mhRank mhSQ ∧
      (∀ I : Fin 2 → Prop, (∀ c ∈ mhP ∪ mhSQ, c.sat I) → I 1) ∧
      PClause.bot ∉ mhSQ ∧ (¬ ∃ d ∈ mhSQ, Strengthens d (unit 1)) ∧
      StrictMaxR mhRank ⟨∅, {0}⟩ 0 ∧ ¬ Covered ∅ mhSQ (fun _ => False) ⟨∅, {0}⟩ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn E hE
    simp only [mhP, Finset.mem_singleton] at hn
    subst hn
    exact absurd (hE 0 (by simp)).1 (by simp)
  · intro d hd c hc a _ hneg _
    simp only [mhSQ, Finset.mem_singleton] at hc
    subst hc
    simp at hneg
  · intro I hI
    have h0 : I 0 := by
      obtain ⟨x, hx, hIx⟩ := hI ⟨∅, {0}⟩ (by simp [mhP, mhSQ]) (by simp)
      simp at hx; exact hx ▸ hIx
    obtain ⟨x, hx, hIx⟩ := hI ⟨{0}, {1}⟩ (by simp [mhP, mhSQ])
      (by intro a ha; simp at ha; exact ha ▸ h0)
    simp at hx; exact hx ▸ hIx
  · simp [mhSQ, PClause.bot]
  · rintro ⟨d, hd, hstr⟩
    simp only [mhSQ, Finset.mem_singleton] at hd
    subst hd
    have := hstr.2 (by simp : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)))
    simp [unit] at this
  · refine ⟨by simp, by simp, ?_⟩
    intro b hb hne
    simp [lits] at hb
    exact absurd hb hne
  · rintro ⟨e, he, _⟩
    simp at he

/-! ## Horn readout of the nominal-label cache -/

/-- **Horn readout.**  If the ground context is closed under labelled ordered
hyperresolution with the ground theory `P` and every body-free clause it
holds is a unit `→ a` (so it does not hold `⊥`), then every atom that `P` entails
is the head of such a unit.  This is the condition under which the
nominal-label cache (`complete_nominal_enumeration_queries`,
docs/NOMINALS-CB.md section 10.2) reads the types of an individual off the
unit clauses: the body-free units are then the least model of the ground
theory. -/
theorem horn_unit_readout (rk : Atom → ℕ) (hinj : Function.Injective rk)
    {P SG : Finset (PClause Atom)} (hcl : ClosedHyper rk P SG)
    (hunits : ∀ e ∈ SG, e.neg = ∅ → ∃ a, e.pos = {a})
    (b : Atom) (hent : ∀ I : Atom → Prop, (∀ c ∈ P, c.sat I) → I b) :
    unit b ∈ SG := by
  classical
  let J : Atom → Prop := fun _ => False
  have hnobot : ∀ e ∈ SG, (∀ h ∈ e.neg, J h) → e.pos.Nonempty := by
    intro e he hJ
    have hneg : e.neg = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro h hh
      exact hJ h hh
    obtain ⟨a, ha⟩ := hunits e he hneg
    rw [ha]; exact Finset.singleton_nonempty a
  have hM := labelledModel_sat_nuclei rk SG J hinj hcl (fun _ h => h.elim) hnobot
  have hMb := hent _ hM
  rcases (labelledModel_def rk SG J b).mp hMb with h | ⟨e, he, hm, hl, _⟩
  · exact h.elim
  · have hneg : e.neg = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro h hh
      exact hl h hh
    obtain ⟨a, ha⟩ := hunits e he hneg
    have hab : b = a := by
      have := hm.1
      rw [ha] at this
      simpa using this
    have : e = unit b := by
      cases e
      simp only [unit] at *
      simp_all
    exact this ▸ he

end ContextCalculus.ExchangeCut
