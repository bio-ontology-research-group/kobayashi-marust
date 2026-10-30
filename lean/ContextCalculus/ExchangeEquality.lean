import ContextCalculus.CompletenessExchange

/-!
# The announced-individual interface with ground (in)equalities

`CompletenessExchange.lean` proves exchange completeness for an abstract
interface `V` that is a lower set (or downward closed) in the server's order,
under the delivery condition `ExchangeCond.deliver`: the server hands every
clause inside `V` to the consumer.  This file instantiates `V` with the
interface that KM's nominal ground context serves under the context regime
(docs/PER-CONTEXT-ORDERING.md, sections 5 and 8), with ground equalities
treated as propositional atoms:

* every ground atom carries the finite set of individuals it mentions;
* a context that announced the individuals `I` has as interface the ground
  atoms whose individuals all lie in `I`, and the ground equality atoms
  `o ≈ o'` with `o ∈ I` or `o' ∈ I` (rule R3; an inequality `o ≉ o'` in a
  head is the negative literal of the same atom);
* the server's order is a strict partial order filtered by rule R2: a ground
  atom lies below another ground atom only if its individuals are among the
  other's, a ground equality lies below a ground atom only if they share an
  individual, and nothing lies below a ground equality;
* the guard delivers a clause when each of its atoms lies in the interface
  (`InIface`, `engine::in_announced_interface`).

Main results (all `sorry`-free):

* `filt_irrefl`, `filt_trans`: the R2 filter of a strict partial order is a
  strict partial order.
* `iface_downward`: for EVERY announced set `I`, the interface is downward
  closed in the filtered order.  Without the two equality clauses of R2 this
  fails: a private equality below an interface atom is the skeleton of
  `ordered_server_interface_not_lower_counterexample`.
* `exchangeCond_of_guard`: a server that delivers every clause passing the
  guard meets `ExchangeCond.deliver`.  The unit-only R3 of v1.5.4 does not:
  `→ E(b) ∨ b ≈ c` lies inside the interface of a context that announced
  `b` and was not delivered.  `inIface_of_all_announced`: the guard extends
  the v1.5.4 guard.
* `announced_exchange_complete`: refutational completeness of the exchange
  between the ground context (closed on maximal literals of the filtered
  order) and any consumer (closed under any rank), for every announced set.
* `announced_unit_readout_complete`: the positive unit readout in the same
  setting.

Scope.  Equalities are opaque atoms here: the theorem covers the
propositional skeleton of the exchange.  Congruence (the Eq rule, rewriting of
`o` to `x` in the consumer, Join case 3) and the locality of the consumer's
atoms (`ExchangeCond.local_`) are argued in docs/PER-CONTEXT-ORDERING.md
section 8, not mechanised.
-/

namespace ContextCalculus.ExchangeEquality

open ContextCalculus.PropRes
open ContextCalculus.Exchange

set_option linter.unusedSectionVars false

variable {Atom Ind : Type*} [DecidableEq Atom] [DecidableEq Ind]

/-- Ground signature: the individuals of each atom, and which atoms are
ground (in)equalities between individuals. -/
structure GroundSig (Atom Ind : Type*) where
  inds : Atom → Finset Ind
  isEq : Atom → Prop

/-- The interface of a context that announced `I` (R3 for equality atoms). -/
def Iface (σ : GroundSig Atom Ind) (I : Finset Ind) (a : Atom) : Prop :=
  (σ.isEq a ∧ (σ.inds a ∩ I).Nonempty) ∨ (¬ σ.isEq a ∧ σ.inds a ⊆ I)

/-- R2: the comparisons the context regime keeps between ground atoms. -/
def Compatible (σ : GroundSig Atom Ind) (a b : Atom) : Prop :=
  ¬ σ.isEq b ∧ ((σ.isEq a ∧ (σ.inds a ∩ σ.inds b).Nonempty) ∨
    (¬ σ.isEq a ∧ σ.inds a ⊆ σ.inds b))

/-- The server order after R2. -/
def filt (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop) (a b : Atom) : Prop :=
  lt a b ∧ Compatible σ a b

theorem filt_irrefl (σ : GroundSig Atom Ind) {lt : Atom → Atom → Prop}
    (hirrefl : ∀ a, ¬ lt a a) : ∀ a, ¬ filt σ lt a a :=
  fun a h => hirrefl a h.1

theorem compatible_trans (σ : GroundSig Atom Ind) {a b c : Atom}
    (hab : Compatible σ a b) (hbc : Compatible σ b c) : Compatible σ a c := by
  refine ⟨hbc.1, ?_⟩
  have hbsub : σ.inds b ⊆ σ.inds c := by
    rcases hbc.2 with h | h
    · exact absurd h.1 hab.1
    · exact h.2
  rcases hab.2 with h | h
  · left
    refine ⟨h.1, ?_⟩
    obtain ⟨o, ho⟩ := h.2
    rw [Finset.mem_inter] at ho
    exact ⟨o, Finset.mem_inter.mpr ⟨ho.1, hbsub ho.2⟩⟩
  · exact Or.inr ⟨h.1, h.2.trans hbsub⟩

theorem filt_trans (σ : GroundSig Atom Ind) {lt : Atom → Atom → Prop}
    (htrans : ∀ a b c, lt a b → lt b c → lt a c) :
    ∀ a b c, filt σ lt a b → filt σ lt b c → filt σ lt a c :=
  fun a b c hab hbc => ⟨htrans a b c hab.1 hbc.1, compatible_trans σ hab.2 hbc.2⟩

/-- **The announced interface is downward closed for every announced set.** -/
theorem iface_downward (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (I : Finset Ind) : ∀ a b, filt σ lt a b → Iface σ I b → Iface σ I a := by
  intro a b hab hb
  have hbI : σ.inds b ⊆ I := by
    rcases hb with h | h
    · exact absurd h.1 hab.2.1
    · exact h.2
  rcases hab.2.2 with h | h
  · left
    refine ⟨h.1, ?_⟩
    obtain ⟨o, ho⟩ := h.2
    rw [Finset.mem_inter] at ho
    exact ⟨o, Finset.mem_inter.mpr ⟨ho.1, hbI ho.2⟩⟩
  · exact Or.inr ⟨h.1, h.2.trans hbI⟩

/-- The guard of the context regime (`engine::in_announced_interface`): a
clause passes when each of its atoms lies in the announced interface, so an
equality atom needs one announced side and every other atom needs all its
individuals announced.  The unit-only R3 of v1.5.4 passed only clauses whose
individuals were all announced, plus the units `→ o ≈ o'`; it did not pass
`→ E(b) ∨ b ≈ c` for a context that announced `b`, which lies inside the
interface. -/
def InIface (σ : GroundSig Atom Ind) (I : Finset Ind) (c : PClause Atom) : Prop :=
  ∀ a ∈ lits c, Iface σ I a

/-- A clause whose individuals are all announced passes the guard (the guard
extends the v1.5.4 guard). -/
theorem inIface_of_all_announced (σ : GroundSig Atom Ind) (I : Finset Ind)
    (c : PClause Atom) (hall : ∀ a ∈ lits c, σ.inds a ⊆ I)
    (hne : ∀ a ∈ lits c, σ.isEq a → (σ.inds a).Nonempty) : InIface σ I c := by
  intro a ha
  by_cases he : σ.isEq a
  · left
    obtain ⟨o, ho⟩ := hne a ha he
    exact ⟨he, ⟨o, Finset.mem_inter.mpr ⟨ho, hall a ha ho⟩⟩⟩
  · exact Or.inr ⟨he, hall a ha⟩

/-- A server that delivers every clause passing the guard, with a consumer that
holds non-interface atoms only privately, meets the exchange conditions. -/
theorem exchangeCond_of_guard (σ : GroundSig Atom Ind) (I : Finset Ind)
    {SG SQ : Finset (PClause Atom)}
    (hdeliver : ∀ c ∈ SG, InIface σ I c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ Iface σ I a → ¬ Occurs SG a) :
    ExchangeCond (Iface σ I) SG SQ :=
  ⟨fun c hc hall => hdeliver c hc hall, hlocal⟩

/-- **Exchange completeness for the announced interface with equality atoms.**
The ground context is closed on maximal literals of the R2-filtered order of a
strict partial order; the consumer is closed under any rank; the ground
context delivers every clause the guard admits.  Then an unsatisfiable union
gives `⊥` in the consumer, whatever individuals it announced. -/
theorem announced_exchange_complete [Fintype Atom]
    (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ) (I : Finset Ind)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal (filt σ lt) SG) (hclQ : ClosedR rkQ SQ)
    (hdeliver : ∀ c ∈ SG, InIface σ I c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ Iface σ I a → ¬ Occurs SG a)
    (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ := by
  classical
  exact downward_server_complete (filt σ lt) (filt_irrefl σ hirrefl) (filt_trans σ htrans)
    rkQ hinjQ (Iface σ I) (iface_downward σ lt I) hclG hclQ
    (exchangeCond_of_guard σ I hdeliver hlocal) hunsat

/-- **Positive unit readout** for the announced interface: if the union
entails an atom `b` that is `rkQ`-least among the consumer's atoms and is an
interface atom or private to the consumer, the consumer holds `⊥` or a clause
that strengthens `→ b`. -/
theorem announced_unit_readout_complete [Fintype Atom]
    (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ) (I : Finset Ind)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal (filt σ lt) SG) (hclQ : ClosedR rkQ SQ)
    (hdeliver : ∀ c ∈ SG, InIface σ I c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ Iface σ I a → ¬ Occurs SG a)
    (b : Atom) (hleast : ∀ c ∈ SQ, ∀ a ∈ lits c, a ≠ b → rkQ b < rkQ a)
    (hbV : Iface σ I b ∨ ¬ Occurs SG b)
    (hent : ∀ J : Atom → Prop, (∀ c ∈ SG ∪ SQ, c.sat J) → J b) :
    PClause.bot ∈ SQ ∨ ∃ d ∈ SQ, Strengthens d (unit b) := by
  classical
  obtain ⟨rkG, hinjG, hext, hV⟩ :=
    exists_rank_extending_lower (filt σ lt) (filt_irrefl σ hirrefl) (filt_trans σ htrans)
      (Iface σ I) (iface_downward σ lt I)
  exact exchange_unit_readout_complete rkG rkQ hinjG hinjQ hV
    (closedR_of_closedMaximal hext hclG) hclQ
    (exchangeCond_of_guard σ I hdeliver hlocal) b hleast hbV hent

#print axioms filt_trans
#print axioms iface_downward
#print axioms inIface_of_all_announced
#print axioms exchangeCond_of_guard
#print axioms announced_exchange_complete
#print axioms announced_unit_readout_complete

end ContextCalculus.ExchangeEquality
