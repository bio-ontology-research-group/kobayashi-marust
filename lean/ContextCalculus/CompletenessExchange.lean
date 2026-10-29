import ContextCalculus.CompletenessProp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ground completeness of clause exchange between differently ordered contexts

`CompletenessOrdered.lean` proves that ordered ground resolution under ONE
total order is refutationally complete.  The CB engine runs one saturation per
context, and contexts may use different literal orders (arXiv:1805.01396,
Definition 5: the context structure maps each context `v` to its own order
`≻_v`).  A context that consumes clauses of another context sees only the
clauses that the exchange rules deliver to it.  This file proves, on the
ground (propositional) core, when such an exchange is complete although the
two contexts use unrelated orders.

Setting (docs/PER-CONTEXT-ORDERING.md):

* a *server* context `G` (KM: the nominal ground context) saturated under its
  own rank `rkG`;
* a *consumer* context `Q` (KM: an ordinary or query context) saturated under
  an unrelated rank `rkQ`;
* an *interface* `V` of atoms: `G` delivers to `Q` every clause it holds whose
  atoms all lie in `V` (KM: the announced-individual guard of r-Pred), and
  every atom that the two clause sets share lies in `V`.

Main results (all `sorry`-free):

* `based_model_correct` (projection lemma): if `V` is a lower set of `rkG`,
  every assignment of `V` that satisfies the `V`-clauses of a `rkG`-closed set
  extends to a model of the whole set.  Ordered resolution with the interface
  at the bottom of the order computes the projection onto the interface.
* `exchange_refutation_complete`: under the delivery and locality conditions
  above and `V` a lower set of `rkG`, if `G ∪ Q` is unsatisfiable then `Q`
  derives `⊥` under its own order `rkQ`, whatever `rkQ` is.
* `exchange_unit_readout_complete`: the positive unit readout.  If `G ∪ Q`
  entails an atom `b` that is `rkQ`-least among the atoms of `Q`, then `Q`
  holds `⊥` or a clause that strengthens the unit `→ b`.
* `closedR_of_closedAll` and `closedR_of_closedMaximal`: closure under
  unrestricted resolution (the incomparable regime) implies closure under
  every rank, and closure under resolution on the maximal literals of a strict
  partial order (the Sequoia regime) implies closure under every rank that
  extends the partial order.
* `unordered_server_complete_for_every_interface`: an unordered server serves
  EVERY interface, so a consumer with any order is complete against it.
* `ordered_server_interface_not_lower_counterexample`: the lower-set condition
  cannot be dropped.  A two-atom server whose interface atom lies above its
  private atom saturates without delivering anything, and the consumer stays
  `⊥`-free although the union is unsatisfiable.  This is the propositional
  skeleton of the seed-297 and `p1` counterexamples.

Scope: ground propositional clauses, resolution modulo strengthening and
tautology deletion (the closure contract of `CompletenessOrderedSubsumption`).
Equality, Skolem terms, and the lifting to the first-order context calculus
are not covered here; they are the same open obligations as for the
single-order case (lean/README.md, "What is NOT claimed").
-/

namespace ContextCalculus.Exchange

open ContextCalculus.PropRes

set_option linter.unusedSectionVars false

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Clause vocabulary (order-free copies of the `OrdRes` helpers) -/

/-- All atoms of a clause. -/
def lits (c : PClause Atom) : Finset Atom := c.neg ∪ c.pos

theorem mem_lits {c : PClause Atom} {a : Atom} : a ∈ lits c ↔ a ∈ c.neg ∨ a ∈ c.pos := by
  simp [lits, Finset.mem_union]

theorem lits_eq_empty_bot (q : PClause Atom) (hq : lits q = ∅) : q = PClause.bot := by
  have hn : q.neg = ∅ :=
    Finset.subset_empty.mp (by rw [← hq]; intro y hy; exact mem_lits.mpr (Or.inl hy))
  have hp : q.pos = ∅ :=
    Finset.subset_empty.mp (by rw [← hq]; intro y hy; exact mem_lits.mpr (Or.inr hy))
  cases q; simp_all [PClause.bot]

/-- `stronger` subsumes `weaker` (production redundancy). -/
def Strengthens (stronger weaker : PClause Atom) : Prop :=
  stronger.neg ⊆ weaker.neg ∧ stronger.pos ⊆ weaker.pos

/-- One atom with both polarities. -/
def Tautological (clause : PClause Atom) : Prop :=
  ∃ atom, atom ∈ clause.neg ∧ atom ∈ clause.pos

theorem sat_of_strengthens (I : Atom → Prop) {stronger weaker : PClause Atom}
    (hstrengthens : Strengthens stronger weaker) (hstronger : stronger.sat I) :
    weaker.sat I := by
  intro hnegative
  obtain ⟨atom, hatom, htrue⟩ := hstronger (fun a ha => hnegative a (hstrengthens.1 ha))
  exact ⟨atom, hstrengthens.2 hatom, htrue⟩

/-! ## Rank-ordered resolution -/

/-- `a` is the strictly maximal positive literal of `c` under the rank `rk`. -/
def StrictMaxR (rk : Atom → ℕ) (c : PClause Atom) (a : Atom) : Prop :=
  a ∈ c.pos ∧ a ∉ c.neg ∧ ∀ b ∈ lits c, b ≠ a → rk b < rk a

/-- Closure under `rk`-ordered resolution modulo strengthening and tautology
deletion (the production closure contract, here for an explicit rank). -/
def ClosedR (rk : Atom → ℕ) (S : Finset (PClause Atom)) : Prop :=
  ∀ d ∈ S, ∀ c ∈ S, ∀ a : Atom,
    StrictMaxR rk d a → a ∈ c.neg → (∀ b ∈ lits c, rk b ≤ rk a) →
    Tautological (PropRes.resolvent d c a) ∨
      ∃ retained ∈ S, Strengthens retained (PropRes.resolvent d c a)

/-- Closure under UNRESTRICTED resolution modulo strengthening and tautology
deletion: the incomparable regime, which resolves on every literal. -/
def ClosedAll (S : Finset (PClause Atom)) : Prop :=
  ∀ d ∈ S, ∀ c ∈ S, ∀ a : Atom, a ∈ d.pos → a ∈ c.neg →
    Tautological (PropRes.resolvent d c a) ∨
      ∃ retained ∈ S, Strengthens retained (PropRes.resolvent d c a)

/-- `a` is maximal in the literal set of `c` for a strict relation `lt`. -/
def MaximalIn (lt : Atom → Atom → Prop) (c : PClause Atom) (a : Atom) : Prop :=
  a ∈ lits c ∧ ∀ b ∈ lits c, ¬ lt a b

/-- Closure under resolution on maximal literals of a strict partial order
`lt` (Hyper firing on every maximal literal; the Sequoia regime when `lt`
orders internal concepts above named ones and leaves named ones incomparable).
-/
def ClosedMaximal (lt : Atom → Atom → Prop) (S : Finset (PClause Atom)) : Prop :=
  ∀ d ∈ S, ∀ c ∈ S, ∀ a : Atom,
    a ∈ d.pos → a ∉ d.neg → MaximalIn lt d a → a ∈ c.neg → MaximalIn lt c a →
    Tautological (PropRes.resolvent d c a) ∨
      ∃ retained ∈ S, Strengthens retained (PropRes.resolvent d c a)

theorem closedR_of_closedAll (rk : Atom → ℕ) {S : Finset (PClause Atom)}
    (h : ClosedAll S) : ClosedR rk S := by
  intro d hd c hc a hmax hneg _
  exact h d hd c hc a hmax.1 hneg

/-- A rank `rk` extends the strict relation `lt`. -/
def Extends (lt : Atom → Atom → Prop) (rk : Atom → ℕ) : Prop :=
  ∀ a b, lt a b → rk a < rk b

theorem closedR_of_closedMaximal {lt : Atom → Atom → Prop} {rk : Atom → ℕ}
    (hext : Extends lt rk) {S : Finset (PClause Atom)}
    (h : ClosedMaximal lt S) : ClosedR rk S := by
  intro d hd c hc a hmax hneg hub
  refine h d hd c hc a hmax.1 hmax.2.1 ⟨mem_lits.mpr (Or.inr hmax.1), ?_⟩ hneg
    ⟨mem_lits.mpr (Or.inl hneg), ?_⟩
  · intro b hb hlt
    have h1 := hext a b hlt
    by_cases hba : b = a
    · subst hba; exact lt_irrefl _ h1
    · exact absurd (hmax.2.2 b hb hba) (not_lt.mpr h1.le)
  · intro b hb hlt
    exact absurd (hub b hb) (not_le.mpr (hext a b hlt))

/-! ## The candidate model over a fixed interface assignment -/

section Based

variable (rk : Atom → ℕ) (S : Finset (PClause Atom)) (V : Atom → Prop)
  (J : Atom → Prop)

open Classical in
/-- Bachmair–Ganzinger candidate model built ON TOP of an assignment `J` of
the interface `V`: interface atoms take their `J` value, every other atom is
true iff some clause produces it. -/
noncomputable def ItrueOver : Atom → Prop :=
  (InvImage.wf rk wellFounded_lt).fix fun a ih =>
    if V a then J a else
    ∃ c ∈ S, ∃ hsm : StrictMaxR rk c a,
      (∀ b (hb : b ∈ c.neg), ih b (hsm.2.2 b (mem_lits.2 (Or.inl hb))
          (by rintro rfl; exact hsm.2.1 hb))) ∧
      (∀ b (hb : b ∈ c.pos) (hba : b ≠ a),
          ¬ ih b (hsm.2.2 b (mem_lits.2 (Or.inr hb)) hba))

theorem ItrueOver_def (a : Atom) :
    ItrueOver rk S V J a ↔
      (V a ∧ J a) ∨ (¬ V a ∧ ∃ c ∈ S, StrictMaxR rk c a ∧
        (∀ b ∈ c.neg, ItrueOver rk S V J b) ∧
        (∀ b ∈ c.pos, b ≠ a → ¬ ItrueOver rk S V J b)) := by
  classical
  unfold ItrueOver
  rw [(InvImage.wf rk wellFounded_lt).fix_eq]
  by_cases hV : V a
  · simp only [hV, if_true, true_and, not_true_eq_false, false_and, or_false]
  · simp only [hV, if_false, false_and, false_or, not_false_eq_true, true_and]
    constructor
    · rintro ⟨c, hc, hsm, hneg, hpos⟩
      exact ⟨c, hc, hsm, fun b hb => hneg b hb, fun b hb hba => hpos b hb hba⟩
    · rintro ⟨c, hc, hsm, hneg, hpos⟩
      exact ⟨c, hc, hsm, fun b hb => hneg b hb, fun b hb hba => hpos b hb hba⟩

theorem ItrueOver_of_V {a : Atom} (ha : V a) :
    ItrueOver rk S V J a ↔ J a := by
  rw [ItrueOver_def]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd ha h
  · intro h; exact Or.inl ⟨ha, h⟩

/-- `V` is a lower set of the rank: every atom below an interface atom is an
interface atom. -/
def LowerSet (V : Atom → Prop) : Prop := ∀ a b, V a → rk b < rk a → V b

/-- **Projection lemma.**  Let `S` be closed under `rk`-ordered resolution and
let the interface `V` be a lower set of `rk`.  Every assignment `J` that
satisfies the clauses of `S` lying entirely inside `V` extends (agreeing on
`V`) to a model of all of `S`. -/
theorem based_model_correct (hinj : Function.Injective rk)
    (hclosed : ClosedR rk S) (hV : LowerSet rk V)
    (hJ : ∀ c ∈ S, (∀ a ∈ lits c, V a) → c.sat J) :
    ∀ c ∈ S, c.sat (ItrueOver rk S V J) := by
  have hbot : PClause.bot ∉ S := by
    intro h
    have := hJ _ h (by intro a ha; simp [lits, PClause.bot] at ha)
    exact PClause.not_sat_bot J this
  have key : ∀ n : ℕ, ∀ a : Atom, rk a = n → ∀ c ∈ S,
      (∀ b ∈ lits c, rk b ≤ rk a) → a ∈ lits c →
      c.sat (ItrueOver rk S V J) := by
    intro n0
    induction n0 using Nat.strong_induction_on with
    | _ n ih =>
    intro a hrk c hc hub hmem hnegative
    subst hrk
    by_contra hfalse
    push Not at hfalse
    by_cases hVa : V a
    · -- the whole clause lies in the interface
      have hall : ∀ b ∈ lits c, V b := by
        intro b hb
        rcases lt_or_eq_of_le (hub b hb) with hlt | heq
        · exact hV a b hVa hlt
        · rw [hinj heq]; exact hVa
      have hsatJ := hJ c hc hall
      have hnegJ : ∀ b ∈ c.neg, J b := fun b hb =>
        (ItrueOver_of_V rk S V J (hall b (mem_lits.mpr (Or.inl hb)))).mp
          (hnegative b hb)
      obtain ⟨b, hb, hJb⟩ := hsatJ hnegJ
      exact hfalse b hb
        ((ItrueOver_of_V rk S V J (hall b (mem_lits.mpr (Or.inr hb)))).mpr hJb)
    · by_cases hapos : a ∈ c.pos
      · by_cases haneg : a ∈ c.neg
        · exact (hfalse a hapos) (hnegative a haneg)
        · have hmax : StrictMaxR rk c a :=
            ⟨hapos, haneg, fun b hb hne =>
              lt_of_le_of_ne (hub b hb) (fun h => hne (hinj h))⟩
          have htrue : ItrueOver rk S V J a := (ItrueOver_def rk S V J a).mpr
            (Or.inr ⟨hVa, c, hc, hmax, hnegative, fun b hb _ => hfalse b hb⟩)
          exact (hfalse a hapos) htrue
      · have haneg : a ∈ c.neg := by
          rcases mem_lits.mp hmem with h | h
          · exact h
          · exact absurd h hapos
        have htrue := hnegative a haneg
        rcases (ItrueOver_def rk S V J a).mp htrue with ⟨hV', _⟩ | ⟨_, producer,
            hproducer, hproducerMax, hproducerNeg, hproducerPos⟩
        · exact hVa hV'
        let resolvent := PropRes.resolvent producer c a
        have hresNeg : ∀ atom ∈ resolvent.neg, ItrueOver rk S V J atom := by
          intro atom hatom
          change atom ∈ producer.neg ∪ c.neg.erase a at hatom
          rcases Finset.mem_union.mp hatom with h | h
          · exact hproducerNeg atom h
          · exact hnegative atom (Finset.mem_of_mem_erase h)
        have hresPos : ∀ atom ∈ resolvent.pos, ¬ ItrueOver rk S V J atom := by
          intro atom hatom
          change atom ∈ producer.pos.erase a ∪ c.pos at hatom
          rcases Finset.mem_union.mp hatom with h | h
          · exact hproducerPos atom (Finset.mem_of_mem_erase h)
              (Finset.ne_of_mem_erase h)
          · exact hfalse atom h
        rcases hclosed producer hproducer c hc a hproducerMax haneg hub with
          htaut | ⟨retained, hretained, hstrengthens⟩
        · obtain ⟨atom, hn, hp⟩ := htaut
          exact (hresPos atom hp) (hresNeg atom hn)
        · have hretNeg : ∀ atom ∈ retained.neg, ItrueOver rk S V J atom :=
            fun atom h => hresNeg atom (hstrengthens.1 h)
          have hretPos : ∀ atom ∈ retained.pos, ¬ ItrueOver rk S V J atom :=
            fun atom h => hresPos atom (hstrengthens.2 h)
          by_cases hretBot : retained = PClause.bot
          · exact hbot (hretBot ▸ hretained)
          · have hne : (lits retained).Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              intro hempty
              exact hretBot (lits_eq_empty_bot retained hempty)
            have hresLt : ∀ b ∈ lits resolvent, rk b < rk a := by
              intro b hb
              rcases mem_lits.mp hb with h | h
              · change b ∈ producer.neg ∪ c.neg.erase a at h
                rcases Finset.mem_union.mp h with h | h
                · exact hproducerMax.2.2 b (mem_lits.mpr (Or.inl h))
                    (fun hba => hproducerMax.2.1 (hba ▸ h))
                · exact lt_of_le_of_ne
                    (hub b (mem_lits.mpr (Or.inl (Finset.mem_of_mem_erase h))))
                    (fun hr => Finset.ne_of_mem_erase h (hinj hr))
              · change b ∈ producer.pos.erase a ∪ c.pos at h
                rcases Finset.mem_union.mp h with h | h
                · exact hproducerMax.2.2 b
                    (mem_lits.mpr (Or.inr (Finset.mem_of_mem_erase h)))
                    (Finset.ne_of_mem_erase h)
                · exact lt_of_le_of_ne (hub b (mem_lits.mpr (Or.inr h)))
                    (fun hr => hapos ((hinj hr) ▸ h))
            have hretLt : ∀ b ∈ lits retained, rk b < rk a := by
              intro b hb
              apply hresLt b
              rcases mem_lits.mp hb with h | h
              · exact mem_lits.mpr (Or.inl (hstrengthens.1 h))
              · exact mem_lits.mpr (Or.inr (hstrengthens.2 h))
            -- the rank-maximal atom of the retained clause
            obtain ⟨m, hm, hmmax⟩ :=
              Finset.exists_max_image (lits retained) rk hne
            have hsat := ih (rk m) (hretLt m hm) m rfl retained hretained
              hmmax hm hretNeg
            obtain ⟨atom, hatom, htrue⟩ := hsat
            exact (hretPos atom hatom) htrue
  intro c hc
  have hne : (lits c).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hbot ((lits_eq_empty_bot c hempty) ▸ hc)
  obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image (lits c) rk hne
  exact key (rk m) m rfl c hc hmmax hm

end Based

/-- Single-context special case: a `rk`-closed set without `⊥` has a model
(empty interface).  This is `OrdResModulo.ordered_model_exists_of_closedModuloTautology`
for an explicit rank. -/
theorem rank_model_exists (rk : Atom → ℕ) (hinj : Function.Injective rk)
    (S : Finset (PClause Atom)) (hclosed : ClosedR rk S)
    (hbot : PClause.bot ∉ S) :
    ∃ I : Atom → Prop, ∀ c ∈ S, c.sat I := by
  refine ⟨ItrueOver rk S (fun _ => False) (fun _ => False),
    based_model_correct rk S (fun _ => False) (fun _ => False) hinj hclosed
      (fun _ _ h _ => h) ?_⟩
  intro c hc hall
  have hempty : lits c = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    exact hall a ha
  exact absurd ((lits_eq_empty_bot c hempty) ▸ hc) hbot

/-! ## Two contexts, two orders -/

/-- Atoms occurring in a clause set. -/
def Occurs (S : Finset (PClause Atom)) (a : Atom) : Prop := ∃ c ∈ S, a ∈ lits c

/-- The exchange conditions between a server `SG` and a consumer `SQ` over
the interface `V`: `G` delivers every interface clause (up to strengthening),
and every atom the two sets share is an interface atom. -/
structure ExchangeCond (V : Atom → Prop) (SG SQ : Finset (PClause Atom)) : Prop where
  deliver : ∀ c ∈ SG, (∀ a ∈ lits c, V a) → ∃ d ∈ SQ, Strengthens d c
  local_ : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ V a → ¬ Occurs SG a

/-- Glue a model of the consumer to a model of the server. -/
theorem glue_models {V : Atom → Prop} {SG SQ : Finset (PClause Atom)}
    (hx : ExchangeCond V SG SQ) (J I : Atom → Prop)
    (hJ : ∀ c ∈ SQ, c.sat J) (hI : ∀ c ∈ SG, c.sat I)
    (hagree : ∀ a, V a → (I a ↔ J a)) :
    ∃ K : Atom → Prop, (∀ c ∈ SG ∪ SQ, c.sat K) ∧
      (∀ c ∈ SQ, ∀ a ∈ lits c, K a ↔ J a) := by
  classical
  let K : Atom → Prop := fun a => if Occurs SG a then I a else J a
  have hKG : ∀ c ∈ SG, ∀ a ∈ lits c, K a ↔ I a := by
    intro c hc a ha
    have : Occurs SG a := ⟨c, hc, ha⟩
    simp only [K, this, if_true]
  have hKQ : ∀ c ∈ SQ, ∀ a ∈ lits c, K a ↔ J a := by
    intro c hc a ha
    by_cases hocc : Occurs SG a
    · have hVa : V a := by
        by_contra hnot
        exact hx.local_ c hc a ha hnot hocc
      simp only [K, hocc, if_true]
      exact hagree a hVa
    · simp only [K, hocc, if_false]
  refine ⟨K, ?_, hKQ⟩
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · intro hneg
    obtain ⟨b, hb, hIb⟩ := hI c hc (fun a ha =>
      (hKG c hc a (mem_lits.mpr (Or.inl ha))).mp (hneg a ha))
    exact ⟨b, hb, (hKG c hc b (mem_lits.mpr (Or.inr hb))).mpr hIb⟩
  · intro hneg
    obtain ⟨b, hb, hJb⟩ := hJ c hc (fun a ha =>
      (hKQ c hc a (mem_lits.mpr (Or.inl ha))).mp (hneg a ha))
    exact ⟨b, hb, (hKQ c hc b (mem_lits.mpr (Or.inr hb))).mpr hJb⟩

/-- Every consumer model extends across the exchange to a model of
`SG ∪ SQ` that agrees with it on the consumer's atoms. -/
theorem extend_consumer_model (rkG : Atom → ℕ) (hinjG : Function.Injective rkG)
    {V : Atom → Prop} (hV : LowerSet rkG V)
    {SG SQ : Finset (PClause Atom)} (hclG : ClosedR rkG SG)
    (hx : ExchangeCond V SG SQ) (J : Atom → Prop) (hJ : ∀ c ∈ SQ, c.sat J) :
    ∃ K : Atom → Prop, (∀ c ∈ SG ∪ SQ, c.sat K) ∧
      (∀ c ∈ SQ, ∀ a ∈ lits c, K a ↔ J a) := by
  have hJG : ∀ c ∈ SG, (∀ a ∈ lits c, V a) → c.sat J := by
    intro c hc hall
    obtain ⟨d, hd, hstr⟩ := hx.deliver c hc hall
    exact sat_of_strengthens J hstr (hJ d hd)
  have hI := based_model_correct rkG SG V J hinjG hclG hV hJG
  exact glue_models hx J (ItrueOver rkG SG V J) hJ hI
    (fun a ha => ItrueOver_of_V rkG SG V J ha)

/-- **Refutational completeness across a two-order exchange.**  The server
`G` is closed under its order `rkG`, with the interface `V` a lower set of
`rkG`; the consumer `Q` is closed under an UNRELATED order `rkQ`; `G`
delivers its interface clauses to `Q` and the two share only interface atoms.
If `SG ∪ SQ` is unsatisfiable, the consumer derives `⊥`.  The theorem places
no condition on which clauses `Q` sent to `G` before saturation: they are
members of `SG` like any other. -/
theorem exchange_refutation_complete
    (rkG rkQ : Atom → ℕ) (hinjG : Function.Injective rkG)
    (hinjQ : Function.Injective rkQ)
    {V : Atom → Prop} (hV : LowerSet rkG V)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedR rkG SG) (hclQ : ClosedR rkQ SQ)
    (hx : ExchangeCond V SG SQ) (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ := by
  by_contra hbot
  obtain ⟨J, hJ⟩ := rank_model_exists rkQ hinjQ SQ hclQ hbot
  obtain ⟨K, hK, _⟩ := extend_consumer_model rkG hinjG hV hclG hx J hJ
  exact hunsat ⟨K, hK⟩

/-- The unit clause `→ b`. -/
def unit (b : Atom) : PClause Atom := ⟨∅, {b}⟩

/-- The negated unit `b → ⊥`. -/
def negUnit (b : Atom) : PClause Atom := ⟨{b}, ∅⟩

/-- **Positive unit readout across a two-order exchange.**  Under the
hypotheses of `exchange_refutation_complete`, let `b` be `rkQ`-least among the
atoms of `Q` (KM: a named concept in a query context, below every internal
concept; Theorem 2, condition C2 of arXiv:1805.01396), and let `b` be an
interface atom or private to `Q`.  If `SG ∪ SQ` entails `b`, then `Q` holds
`⊥` or a clause that strengthens `→ b`. -/
theorem exchange_unit_readout_complete
    (rkG rkQ : Atom → ℕ) (hinjG : Function.Injective rkG)
    (hinjQ : Function.Injective rkQ)
    {V : Atom → Prop} (hV : LowerSet rkG V)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedR rkG SG) (hclQ : ClosedR rkQ SQ)
    (hx : ExchangeCond V SG SQ) (b : Atom)
    (hleast : ∀ c ∈ SQ, ∀ a ∈ lits c, a ≠ b → rkQ b < rkQ a)
    (hbloc : V b ∨ ¬ Occurs SG b)
    (hent : ∀ I : Atom → Prop, (∀ c ∈ SG ∪ SQ, c.sat I) → I b) :
    PClause.bot ∈ SQ ∨ ∃ d ∈ SQ, Strengthens d (unit b) := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨hbot, hnounit⟩ := hnot
  let SQ' : Finset (PClause Atom) := insert (negUnit b) SQ
  have hlitsNeg : lits (negUnit b) = {b} := by simp [lits, negUnit]
  -- any clause of SQ' with `b` strictly maximal positive is the unit `→ b`
  have hmaxIsUnit : ∀ d ∈ SQ, StrictMaxR rkQ d b → Strengthens d (unit b) := by
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
  have hclQ' : ClosedR rkQ SQ' := by
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
  obtain ⟨J, hJ⟩ := rank_model_exists rkQ hinjQ SQ' hclQ' hbot'
  have hJb : ¬ J b := by
    intro hb
    obtain ⟨x, hx', _⟩ := hJ (negUnit b) (Finset.mem_insert_self _ _)
      (by intro a ha; simp [negUnit] at ha; exact ha ▸ hb)
    simp [negUnit] at hx'
  have hJQ : ∀ c ∈ SQ, c.sat J := fun c hc => hJ c (Finset.mem_insert_of_mem hc)
  -- extend across the exchange; `b` keeps its consumer value
  have hJG : ∀ c ∈ SG, (∀ a ∈ lits c, V a) → c.sat J := by
    intro c hc hall
    obtain ⟨d, hd, hstr⟩ := hx.deliver c hc hall
    exact sat_of_strengthens J hstr (hJQ d hd)
  let I := ItrueOver rkG SG V J
  have hI := based_model_correct rkG SG V J hinjG hclG hV hJG
  let K : Atom → Prop := fun a => if Occurs SG a then I a else J a
  obtain ⟨K', hK', _⟩ := glue_models hx J I hJQ hI
    (fun a ha => ItrueOver_of_V rkG SG V J ha)
  -- recompute the glued model explicitly to read off `b`
  have hKmodel : ∀ c ∈ SG ∪ SQ, c.sat K := by
    have hKG : ∀ c ∈ SG, ∀ a ∈ lits c, K a ↔ I a := by
      intro c hc a ha
      have : Occurs SG a := ⟨c, hc, ha⟩
      simp only [K, this, if_true]
    have hKQ : ∀ c ∈ SQ, ∀ a ∈ lits c, K a ↔ J a := by
      intro c hc a ha
      by_cases hocc : Occurs SG a
      · have hVa : V a := by
          by_contra hnotV
          exact hx.local_ c hc a ha hnotV hocc
        simp only [K, hocc, if_true]
        exact ItrueOver_of_V rkG SG V J hVa
      · simp only [K, hocc, if_false]
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · intro hneg
      obtain ⟨x, hx', hIx⟩ := hI c hc (fun a ha =>
        (hKG c hc a (mem_lits.mpr (Or.inl ha))).mp (hneg a ha))
      exact ⟨x, hx', (hKG c hc x (mem_lits.mpr (Or.inr hx'))).mpr hIx⟩
    · intro hneg
      obtain ⟨x, hx', hJx⟩ := hJQ c hc (fun a ha =>
        (hKQ c hc a (mem_lits.mpr (Or.inl ha))).mp (hneg a ha))
      exact ⟨x, hx', (hKQ c hc x (mem_lits.mpr (Or.inr hx'))).mpr hJx⟩
  have hKb : K b ↔ J b := by
    rcases hbloc with hVb | hnocc
    · by_cases hocc : Occurs SG b
      · simp only [K, hocc, if_true]
        exact ItrueOver_of_V rkG SG V J hVb
      · simp only [K, hocc, if_false]
    · simp only [K, hnocc, if_false]
  exact hJb (hKb.mp (hent K hKmodel))

/-! ## The two regimes on the server side -/

/-- On a finite atom type every interface `V` is a lower set of some injective
rank: put `V` first. -/
theorem exists_rank_lower (V : Atom → Prop) [Fintype Atom] [DecidablePred V] :
    ∃ rk : Atom → ℕ, Function.Injective rk ∧ LowerSet rk V := by
  let e := Fintype.equivFin Atom
  let n := Fintype.card Atom
  refine ⟨fun a => if V a then (e a : ℕ) else n + (e a : ℕ), ?_, ?_⟩
  · intro a b h
    have hlt : ∀ x : Atom, (e x : ℕ) < n := fun x => (e x).isLt
    by_cases ha : V a <;> by_cases hb : V b <;> simp only [ha, hb, if_true, if_false] at h
    · exact e.injective (Fin.ext h)
    · have := hlt a; omega
    · have := hlt b; omega
    · exact e.injective (Fin.ext (by omega))
  · intro a b ha hlt
    by_contra hb
    have hlt' : ∀ x : Atom, (e x : ℕ) < n := fun x => (e x).isLt
    simp only [ha, hb, if_true, if_false] at hlt
    have := hlt' a
    omega

/-- **An unordered server serves every interface.**  If the server is closed
under unrestricted resolution (the incomparable regime), a consumer closed
under ANY order is refutationally complete across ANY exchange interface. -/
theorem unordered_server_complete_for_every_interface [Fintype Atom]
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ)
    (V : Atom → Prop) [DecidablePred V]
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedAll SG) (hclQ : ClosedR rkQ SQ)
    (hx : ExchangeCond V SG SQ) (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ := by
  obtain ⟨rkG, hinjG, hV⟩ := exists_rank_lower V
  exact exchange_refutation_complete rkG rkQ hinjG hinjQ hV
    (closedR_of_closedAll rkG hclG) hclQ hx hunsat

/-- **A partially ordered server serves an interface when some linear
extension puts the interface at the bottom.**  This covers a server that uses
the Sequoia order on non-interface atoms and leaves interface atoms below or
incomparable: closure on maximal literals implies closure under every linear
extension. -/
theorem maximal_server_complete
    (lt : Atom → Atom → Prop) (rkG rkQ : Atom → ℕ)
    (hinjG : Function.Injective rkG) (hinjQ : Function.Injective rkQ)
    (hext : Extends lt rkG)
    {V : Atom → Prop} (hV : LowerSet rkG V)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal lt SG) (hclQ : ClosedR rkQ SQ)
    (hx : ExchangeCond V SG SQ) (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ :=
  exchange_refutation_complete rkG rkQ hinjG hinjQ hV
    (closedR_of_closedMaximal hext hclG) hclQ hx hunsat

/-- On a finite atom type, a strict partial order `lt` and a set `V` that is
downward closed for `lt` admit an injective rank that extends `lt` and has `V`
as a lower set: put `V` first and order inside each block by the size of the
strict down-set, breaking ties by an enumeration of the atoms. -/
theorem exists_rank_extending_lower [Fintype Atom]
    (lt : Atom → Atom → Prop) [DecidableRel lt]
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (V : Atom → Prop) [DecidablePred V] (hdown : ∀ a b, lt a b → V b → V a) :
    ∃ rk : Atom → ℕ, Function.Injective rk ∧ Extends lt rk ∧ LowerSet rk V := by
  classical
  let e := Fintype.equivFin Atom
  let n := Fintype.card Atom
  let h : Atom → ℕ := fun a => (Finset.univ.filter (fun c => lt c a)).card
  have hle : ∀ a, h a ≤ n := fun a => by
    simpa [h, n] using Finset.card_filter_le (Finset.univ : Finset Atom) (fun c => lt c a)
  have hlt : ∀ a b, lt a b → h a < h b := by
    intro a b hab
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact htrans c a b hc hab
    · intro hsub
      have : a ∈ Finset.univ.filter (fun c => lt c a) :=
        hsub (by simp [hab])
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hirrefl a this
  have he : ∀ a, (e a : ℕ) < n := fun a => (e a).isLt
  let M := (n + 1) * (n + 1)
  let inner : Atom → ℕ := fun a => h a * n + (e a : ℕ)
  have hinner : ∀ a, inner a < M := by
    intro a
    have h1 := hle a
    have h2 := he a
    have : h a * n ≤ n * n := Nat.mul_le_mul_right n h1
    simp only [inner, M]
    nlinarith
  let rk : Atom → ℕ := fun a => (if V a then 0 else M) + inner a
  refine ⟨rk, ?_, ?_, ?_⟩
  · intro a b hab
    have hinj_inner : inner a = inner b → a = b := by
      intro hi
      simp only [inner] at hi
      have hmod : (e a : ℕ) = (e b : ℕ) := by
        have := congrArg (· % n) hi
        simp only at this
        rwa [Nat.mul_add_mod_of_lt (he a), Nat.mul_add_mod_of_lt (he b)] at this
      exact e.injective (Fin.ext hmod)
    have ha := hinner a
    have hb := hinner b
    by_cases hVa : V a <;> by_cases hVb : V b <;>
      simp only [rk, hVa, hVb, if_true, if_false, zero_add] at hab
    · exact hinj_inner hab
    · omega
    · omega
    · exact hinj_inner (by omega)
  · intro a b hab
    have hh := hlt a b hab
    have hea := he a
    have heb := he b
    have hinner_lt : inner a < inner b := by
      simp only [inner]
      have : (h a + 1) * n ≤ h b * n := Nat.mul_le_mul_right n hh
      nlinarith
    by_cases hVb : V b
    · have hVa := hdown a b hab hVb
      simp only [rk, hVa, hVb, if_true, zero_add]
      exact hinner_lt
    · by_cases hVa : V a
      · simp only [rk, hVa, hVb, if_true, if_false, zero_add]
        have := hinner a
        omega
      · simp only [rk, hVa, hVb, if_false]
        omega
  · intro a b hVa hrk
    by_contra hVb
    simp only [rk, hVa, hVb, if_true, if_false, zero_add] at hrk
    have := hinner a
    omega

/-- **Exchange completeness for a server ordered by a strict partial order
whose interface is downward closed** (the form R2 of the context regime
establishes in KM's ground context): no linear extension has to be supplied. -/
theorem downward_server_complete [Fintype Atom]
    (lt : Atom → Atom → Prop) [DecidableRel lt]
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ)
    (V : Atom → Prop) [DecidablePred V] (hdown : ∀ a b, lt a b → V b → V a)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal lt SG) (hclQ : ClosedR rkQ SQ)
    (hx : ExchangeCond V SG SQ) (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ := by
  obtain ⟨rkG, hinjG, hext, hV⟩ :=
    exists_rank_extending_lower lt hirrefl htrans V hdown
  exact maximal_server_complete lt rkG rkQ hinjG hinjQ hext hV hclG hclQ hx hunsat

/-! ## The lower-set condition cannot be dropped -/

/-- Two atoms: `0` is the interface atom (KM: `B(b)`, about an individual the
consumer announced), `1` is private to the server (KM: `Q_0(a)`, about an
individual the consumer never announced).  The server ranks the interface atom
ABOVE the private one. -/
def cxRankG : Fin 2 → ℕ := fun a => if a = 0 then 1 else 0

/-- Server clauses `→ B(b) ∨ Q_0(a)` and `Q_0(a) → ⊥`. -/
def cxSG : Finset (PClause (Fin 2)) := {⟨∅, {0, 1}⟩, ⟨{1}, ∅⟩}

/-- Consumer clause `B(b) → ⊥` (the refutation hypothesis of a readout). -/
def cxSQ : Finset (PClause (Fin 2)) := {⟨{0}, ∅⟩}

/-- **Counterexample.**  The server is closed under its order, the consumer
under any order, the exchange conditions hold (the server holds no clause
inside the interface, so it delivers nothing), the union is unsatisfiable,
and yet the consumer holds no `⊥`. -/
theorem ordered_server_interface_not_lower_counterexample :
    Function.Injective cxRankG ∧
    ClosedR cxRankG cxSG ∧
    ClosedR (fun a : Fin 2 => (a : ℕ)) cxSQ ∧
    ExchangeCond (fun a : Fin 2 => a = 0) cxSG cxSQ ∧
    Unsat (cxSG ∪ cxSQ) ∧
    PClause.bot ∉ cxSQ ∧
    ¬ LowerSet cxRankG (fun a : Fin 2 => a = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [cxRankG]
  · intro d hd c hc a hmax hneg _
    simp only [cxSG, Finset.mem_insert, Finset.mem_singleton] at hd hc
    exfalso
    rcases hd with rfl | rfl
    · -- producer `→ 0 ∨ 1`: the consumer must hold `a` negatively
      rcases hc with rfl | rfl
      · simp at hneg
      · -- consumer `1 → ⊥`; atom `1` is not strictly maximal in the producer
        have ha : a = 1 := by simpa using hneg
        subst ha
        have := hmax.2.2 0 (by simp [lits]) (by decide)
        simp [cxRankG] at this
    · exact absurd hmax.1 (by simp)
  · intro d hd c hc a hmax hneg _
    simp only [cxSQ, Finset.mem_singleton] at hd
    subst hd
    exact absurd hmax.1 (by simp)
  · refine ⟨?_, ?_⟩
    · intro c hc hall
      simp only [cxSG, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact absurd (hall 1 (by simp [lits])) (by decide)
      · exact absurd (hall 1 (by simp [lits])) (by decide)
    · intro c hc a ha hnotV
      simp only [cxSQ, Finset.mem_singleton] at hc
      subst hc
      have : a = 0 := by simpa [lits] using ha
      exact absurd this hnotV
  · rintro ⟨I, hI⟩
    have h1 := hI ⟨∅, {0, 1}⟩ (by simp [cxSG])
    have h2 := hI ⟨{1}, ∅⟩ (by simp [cxSG])
    have h3 := hI ⟨{0}, ∅⟩ (by simp [cxSQ])
    obtain ⟨x, hx, hIx⟩ := h1 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · obtain ⟨y, hy, _⟩ := h3 (by simpa using hIx)
      simp at hy
    · obtain ⟨y, hy, _⟩ := h2 (by simpa using hIx)
      simp at hy
  · intro h
    simp only [cxSQ, Finset.mem_singleton] at h
    have : (PClause.bot : PClause (Fin 2)).neg = ({0} : Finset (Fin 2)) := by
      rw [h]
    simp [PClause.bot] at this
  · intro h
    have := h 0 1 rfl (by simp [cxRankG])
    exact absurd this (by decide)

#print axioms closedR_of_closedAll
#print axioms closedR_of_closedMaximal
#print axioms based_model_correct
#print axioms rank_model_exists
#print axioms extend_consumer_model
#print axioms exchange_refutation_complete
#print axioms exchange_unit_readout_complete
#print axioms unordered_server_complete_for_every_interface
#print axioms maximal_server_complete
#print axioms exists_rank_extending_lower
#print axioms downward_server_complete
#print axioms ordered_server_interface_not_lower_counterexample

end ContextCalculus.Exchange
