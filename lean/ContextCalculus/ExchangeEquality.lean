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

/-! ## R2 with a rank on individuals (docs/PER-CONTEXT-ORDERING.md section 11)

The filter above is the largest one that keeps the interface downward closed
for EVERY announced set `I`: a ground equality may not lie below an equality
over another pair, since some context may announce a side of the upper one
only.  KM can instead enlarge the interface on the equality side.  Fix a rank
`rk` on individuals (KM uses the term id) and give a context that announced
`I` the bound `m = max rk I`.  Its interface holds the ground atoms with all
individuals in `I` (as before) and the ground equality atoms with a side of
rank at most `m` (a superset of the equality atoms with an announced side).
The filter may then keep:

* an equality below another equality when its least rank is at most the
  other's least rank,
* an equality below a ground atom when it has a side of rank at most the
  rank of some individual of the atom (implied by KM's term-major order),
* a ground atom below a ground atom when its individuals are among the other's,

and nothing else (no ground atom below an equality).  The theorems below
show that this filter is again a strict partial order, that every such
interface is downward closed, and that the old filter and the old guard are
special cases, so the exchange theorems apply unchanged. -/

section Ranked

variable (rk : Ind → ℕ)

/-- The interface of a context that announced `I`, with rank bound `m`. -/
def IfaceR (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ) (a : Atom) : Prop :=
  (σ.isEq a ∧ ∃ o ∈ σ.inds a, rk o ≤ m) ∨ (¬ σ.isEq a ∧ σ.inds a ⊆ I)

/-- R2 with ranks: the comparisons kept between ground atoms. -/
def CompatibleR (σ : GroundSig Atom Ind) (a b : Atom) : Prop :=
  (σ.isEq b ∧ σ.isEq a ∧ ∃ o ∈ σ.inds a, ∀ o' ∈ σ.inds b, rk o ≤ rk o') ∨
  (¬ σ.isEq b ∧ ((σ.isEq a ∧ ∃ o ∈ σ.inds a, ∃ o' ∈ σ.inds b, rk o ≤ rk o') ∨
    (¬ σ.isEq a ∧ σ.inds a ⊆ σ.inds b)))

/-- The server order after the ranked R2. -/
def filtR (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop) (a b : Atom) : Prop :=
  lt a b ∧ CompatibleR rk σ a b

theorem filtR_irrefl (σ : GroundSig Atom Ind) {lt : Atom → Atom → Prop}
    (hirrefl : ∀ a, ¬ lt a a) : ∀ a, ¬ filtR rk σ lt a a :=
  fun a h => hirrefl a h.1

theorem compatibleR_trans (σ : GroundSig Atom Ind) {a b c : Atom}
    (hab : CompatibleR rk σ a b) (hbc : CompatibleR rk σ b c) : CompatibleR rk σ a c := by
  rcases hbc with ⟨hcE, hbE, o1, ho1, hle1⟩ | ⟨hcE, hbc⟩
  · -- `b` and `c` are equalities, so `a` is one as well
    rcases hab with ⟨_, haE, o, ho, hle⟩ | ⟨hbN, _⟩
    · exact Or.inl ⟨hcE, haE, o, ho, fun o' ho' => (hle o1 ho1).trans (hle1 o' ho')⟩
    · exact absurd hbE hbN
  · rcases hbc with ⟨hbE, o1, ho1, o2, ho2, hle12⟩ | ⟨hbN, hbsub⟩
    · -- `b` is an equality below the atom `c`
      rcases hab with ⟨_, haE, o, ho, hle⟩ | ⟨hbN, _⟩
      · exact Or.inr ⟨hcE, Or.inl ⟨haE, o, ho, o2, ho2, (hle o1 ho1).trans hle12⟩⟩
      · exact absurd hbE hbN
    · -- `b` and `c` are ground atoms
      rcases hab with ⟨hbE, _⟩ | ⟨_, hab⟩
      · exact absurd hbE hbN
      · rcases hab with ⟨haE, o, ho, o', ho', hle⟩ | ⟨haN, hasub⟩
        · exact Or.inr ⟨hcE, Or.inl ⟨haE, o, ho, o', hbsub ho', hle⟩⟩
        · exact Or.inr ⟨hcE, Or.inr ⟨haN, hasub.trans hbsub⟩⟩

theorem filtR_trans (σ : GroundSig Atom Ind) {lt : Atom → Atom → Prop}
    (htrans : ∀ a b c, lt a b → lt b c → lt a c) :
    ∀ a b c, filtR rk σ lt a b → filtR rk σ lt b c → filtR rk σ lt a c :=
  fun a b c hab hbc => ⟨htrans a b c hab.1 hbc.1, compatibleR_trans rk σ hab.2 hbc.2⟩

/-- **Every ranked interface is downward closed**, provided the bound covers
the announced individuals. -/
theorem ifaceR_downward (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (I : Finset Ind) (m : ℕ) (hm : ∀ o ∈ I, rk o ≤ m) :
    ∀ a b, filtR rk σ lt a b → IfaceR rk σ I m b → IfaceR rk σ I m a := by
  intro a b hab hb
  rcases hab.2 with ⟨hbE, haE, o, ho, hle⟩ | ⟨hbN, hcomp⟩
  · rcases hb with ⟨_, o', ho', hm'⟩ | ⟨hbN, _⟩
    · exact Or.inl ⟨haE, o, ho, (hle o' ho').trans hm'⟩
    · exact absurd hbE hbN
  · have hbI : σ.inds b ⊆ I := by
      rcases hb with ⟨hbE, _⟩ | ⟨_, h⟩
      · exact absurd hbE hbN
      · exact h
    rcases hcomp with ⟨haE, o, ho, o', ho', hle⟩ | ⟨haN, hsub⟩
    · exact Or.inl ⟨haE, o, ho, hle.trans (hm o' (hbI ho'))⟩
    · exact Or.inr ⟨haN, hsub.trans hbI⟩

/-- The ranked filter keeps every comparison of the R2 filter above. -/
theorem compatibleR_of_compatible (σ : GroundSig Atom Ind) {a b : Atom}
    (h : Compatible σ a b) : CompatibleR rk σ a b := by
  rcases h with ⟨hbN, h⟩
  rcases h with ⟨haE, o, ho⟩ | ⟨haN, hsub⟩
  · rw [Finset.mem_inter] at ho
    exact Or.inr ⟨hbN, Or.inl ⟨haE, o, ho.1, o, ho.2, le_rfl⟩⟩
  · exact Or.inr ⟨hbN, Or.inr ⟨haN, hsub⟩⟩

/-- The ranked interface contains the interface of the announced individuals. -/
theorem ifaceR_of_iface (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ)
    (hm : ∀ o ∈ I, rk o ≤ m) {a : Atom} (h : Iface σ I a) : IfaceR rk σ I m a := by
  rcases h with ⟨haE, o, ho⟩ | ⟨haN, hsub⟩
  · rw [Finset.mem_inter] at ho
    exact Or.inl ⟨haE, o, ho.1, hm o ho.2⟩
  · exact Or.inr ⟨haN, hsub⟩

/-- The ranked guard: each atom of the clause lies in the ranked interface. -/
def InIfaceR (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ) (c : PClause Atom) : Prop :=
  ∀ a ∈ lits c, IfaceR rk σ I m a

/-- The ranked guard passes every clause the announced-individual guard passes. -/
theorem inIfaceR_of_inIface (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ)
    (hm : ∀ o ∈ I, rk o ≤ m) {c : PClause Atom} (h : InIface σ I c) : InIfaceR rk σ I m c :=
  fun a ha => ifaceR_of_iface rk σ I m hm (h a ha)

/-- **Exchange completeness for the ranked interface.** -/
theorem ranked_exchange_complete [Fintype Atom]
    (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ) (I : Finset Ind) (m : ℕ)
    (hm : ∀ o ∈ I, rk o ≤ m)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal (filtR rk σ lt) SG) (hclQ : ClosedR rkQ SQ)
    (hdeliver : ∀ c ∈ SG, InIfaceR rk σ I m c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ IfaceR rk σ I m a → ¬ Occurs SG a)
    (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ := by
  classical
  exact downward_server_complete (filtR rk σ lt) (filtR_irrefl rk σ hirrefl)
    (filtR_trans rk σ htrans) rkQ hinjQ (IfaceR rk σ I m) (ifaceR_downward rk σ lt I m hm)
    hclG hclQ ⟨fun c hc hall => hdeliver c hc hall, hlocal⟩ hunsat

/-- **Positive unit readout** for the ranked interface. -/
theorem ranked_unit_readout_complete [Fintype Atom]
    (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ) (I : Finset Ind) (m : ℕ)
    (hm : ∀ o ∈ I, rk o ≤ m)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal (filtR rk σ lt) SG) (hclQ : ClosedR rkQ SQ)
    (hdeliver : ∀ c ∈ SG, InIfaceR rk σ I m c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ IfaceR rk σ I m a → ¬ Occurs SG a)
    (b : Atom) (hleast : ∀ c ∈ SQ, ∀ a ∈ lits c, a ≠ b → rkQ b < rkQ a)
    (hbV : IfaceR rk σ I m b ∨ ¬ Occurs SG b)
    (hent : ∀ J : Atom → Prop, (∀ c ∈ SG ∪ SQ, c.sat J) → J b) :
    PClause.bot ∈ SQ ∨ ∃ d ∈ SQ, Strengthens d (unit b) := by
  classical
  obtain ⟨rkG, hinjG, hext, hV⟩ :=
    exists_rank_extending_lower (filtR rk σ lt) (filtR_irrefl rk σ hirrefl)
      (filtR_trans rk σ htrans) (IfaceR rk σ I m) (ifaceR_downward rk σ lt I m hm)
  exact exchange_unit_readout_complete rkG rkQ hinjG hinjQ hV
    (closedR_of_closedMaximal hext hclG) hclQ
    ⟨fun c hc hall => hdeliver c hc hall, hlocal⟩ b hleast hbV hent

end Ranked

/-! ## R2 with the larger rank (the variant KM implements)

The ranked filter above lets an equality lie below another one when its
least rank is at most the other's least rank, and its guard admits an
equality whose least rank is within the receiver's bound.  KM implements the
dual reading, which delivers fewer equalities: an equality is an interface
atom of a context that announced `I` (bound `m`) when a side is announced or
all its sides have rank at most `m`; it lies below another equality over the
same individuals, or over others when each of its ranks is at most each rank
of the other; it lies below a ground atom when it shares an individual with
it, or when each of its ranks is at most the rank of one individual of the
atom (KM's term-major order with the term id as the rank implies this).  The
same results hold. -/

section MaxRanked

variable (rk : Ind → ℕ)

/-- The interface of a context that announced `I`, with rank bound `m`. -/
def IfaceM (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ) (a : Atom) : Prop :=
  (σ.isEq a ∧ ((σ.inds a ∩ I).Nonempty ∨ ∀ o ∈ σ.inds a, rk o ≤ m)) ∨
    (¬ σ.isEq a ∧ σ.inds a ⊆ I)

/-- R2 with the larger rank: the comparisons kept between ground atoms. -/
def CompatibleM (σ : GroundSig Atom Ind) (a b : Atom) : Prop :=
  (σ.isEq b ∧ σ.isEq a ∧ (σ.inds a = σ.inds b ∨
      ((σ.inds b).Nonempty ∧ ∀ o ∈ σ.inds a, ∀ o' ∈ σ.inds b, rk o ≤ rk o'))) ∨
  (¬ σ.isEq b ∧ ((σ.isEq a ∧ ((σ.inds a ∩ σ.inds b).Nonempty ∨
      ∃ o' ∈ σ.inds b, ∀ o ∈ σ.inds a, rk o ≤ rk o')) ∨
    (¬ σ.isEq a ∧ σ.inds a ⊆ σ.inds b)))

/-- The server order after the larger-rank R2. -/
def filtM (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop) (a b : Atom) : Prop :=
  lt a b ∧ CompatibleM rk σ a b

theorem filtM_irrefl (σ : GroundSig Atom Ind) {lt : Atom → Atom → Prop}
    (hirrefl : ∀ a, ¬ lt a a) : ∀ a, ¬ filtM rk σ lt a a :=
  fun a h => hirrefl a h.1

theorem compatibleM_trans (σ : GroundSig Atom Ind) {a b c : Atom}
    (hab : CompatibleM rk σ a b) (hbc : CompatibleM rk σ b c) : CompatibleM rk σ a c := by
  rcases hbc with ⟨hcE, hbE, hbc⟩ | ⟨hcN, hbc⟩
  · -- `b` and `c` are equalities, so `a` is one as well
    rcases hab with ⟨_, haE, hab⟩ | ⟨hbN, _⟩
    · refine Or.inl ⟨hcE, haE, ?_⟩
      rcases hab with hab | ⟨hbne, hab⟩ <;> rcases hbc with hbc | ⟨hcne, hbc⟩
      · exact Or.inl (hab.trans hbc)
      · exact Or.inr ⟨hcne, fun o ho o' ho' => hbc o (hab ▸ ho) o' ho'⟩
      · exact Or.inr ⟨hbc ▸ hbne, fun o ho o' ho' => hab o ho o' (hbc ▸ ho')⟩
      · refine Or.inr ⟨hcne, fun o ho o'' ho'' => ?_⟩
        obtain ⟨o', ho'⟩ := hbne
        exact (hab o ho o' ho').trans (hbc o' ho' o'' ho'')
    · exact absurd hbE hbN
  · rcases hbc with ⟨hbE, hbc⟩ | ⟨hbN, hbsub⟩
    · -- `b` is an equality below the atom `c`
      rcases hab with ⟨_, haE, hab⟩ | ⟨hbN, _⟩
      · refine Or.inr ⟨hcN, Or.inl ⟨haE, ?_⟩⟩
        rcases hab with hab | ⟨hbne, hab⟩
        · exact hab ▸ hbc
        · rcases hbc with ⟨o1, ho1⟩ | ⟨o2, ho2, hbc⟩
          · rw [Finset.mem_inter] at ho1
            exact Or.inr ⟨o1, ho1.2, fun o ho => hab o ho o1 ho1.1⟩
          · obtain ⟨o', ho'⟩ := hbne
            exact Or.inr ⟨o2, ho2, fun o ho => (hab o ho o' ho').trans (hbc o' ho')⟩
      · exact absurd hbE hbN
    · -- `b` and `c` are ground atoms
      rcases hab with ⟨hbE, _⟩ | ⟨_, hab⟩
      · exact absurd hbE hbN
      · rcases hab with ⟨haE, hab⟩ | ⟨haN, hasub⟩
        · refine Or.inr ⟨hcN, Or.inl ⟨haE, ?_⟩⟩
          rcases hab with ⟨o, ho⟩ | ⟨o', ho', hle⟩
          · rw [Finset.mem_inter] at ho
            exact Or.inl ⟨o, Finset.mem_inter.mpr ⟨ho.1, hbsub ho.2⟩⟩
          · exact Or.inr ⟨o', hbsub ho', hle⟩
        · exact Or.inr ⟨hcN, Or.inr ⟨haN, hasub.trans hbsub⟩⟩

theorem filtM_trans (σ : GroundSig Atom Ind) {lt : Atom → Atom → Prop}
    (htrans : ∀ a b c, lt a b → lt b c → lt a c) :
    ∀ a b c, filtM rk σ lt a b → filtM rk σ lt b c → filtM rk σ lt a c :=
  fun a b c hab hbc => ⟨htrans a b c hab.1 hbc.1, compatibleM_trans rk σ hab.2 hbc.2⟩

/-- **Every larger-rank interface is downward closed**, provided the bound
covers the announced individuals. -/
theorem ifaceM_downward (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (I : Finset Ind) (m : ℕ) (hm : ∀ o ∈ I, rk o ≤ m) :
    ∀ a b, filtM rk σ lt a b → IfaceM rk σ I m b → IfaceM rk σ I m a := by
  intro a b hab hb
  rcases hab.2 with ⟨hbE, haE, hcomp⟩ | ⟨hbN, hcomp⟩
  · rcases hb with ⟨_, hb⟩ | ⟨hbN, _⟩
    · refine Or.inl ⟨haE, ?_⟩
      rcases hcomp with heq | ⟨_, hle⟩
      · exact heq ▸ hb
      · rcases hb with ⟨o', ho'⟩ | hall
        · rw [Finset.mem_inter] at ho'
          exact Or.inr fun o ho => (hle o ho o' ho'.1).trans (hm o' ho'.2)
        · obtain ⟨o', ho'⟩ := ‹(σ.inds b).Nonempty›
          exact Or.inr fun o ho => (hle o ho o' ho').trans (hall o' ho')
    · exact absurd hbE hbN
  · have hbI : σ.inds b ⊆ I := by
      rcases hb with ⟨hbE, _⟩ | ⟨_, h⟩
      · exact absurd hbE hbN
      · exact h
    rcases hcomp with ⟨haE, hcomp⟩ | ⟨haN, hsub⟩
    · refine Or.inl ⟨haE, ?_⟩
      rcases hcomp with ⟨o, ho⟩ | ⟨o', ho', hle⟩
      · rw [Finset.mem_inter] at ho
        exact Or.inl ⟨o, Finset.mem_inter.mpr ⟨ho.1, hbI ho.2⟩⟩
      · exact Or.inr fun o ho => (hle o ho).trans (hm o' (hbI ho'))
    · exact Or.inr ⟨haN, hsub.trans hbI⟩

/-- The larger-rank filter keeps every comparison of the R2 filter of
7c238e52 (`Compatible`). -/
theorem compatibleM_of_compatible (σ : GroundSig Atom Ind) {a b : Atom}
    (h : Compatible σ a b) : CompatibleM rk σ a b := by
  rcases h with ⟨hbN, h⟩
  rcases h with ⟨haE, hne⟩ | ⟨haN, hsub⟩
  · exact Or.inr ⟨hbN, Or.inl ⟨haE, Or.inl hne⟩⟩
  · exact Or.inr ⟨hbN, Or.inr ⟨haN, hsub⟩⟩

/-- The larger-rank interface contains the interface of the announced
individuals. -/
theorem ifaceM_of_iface (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ)
    {a : Atom} (h : Iface σ I a) : IfaceM rk σ I m a := by
  rcases h with ⟨haE, hne⟩ | ⟨haN, hsub⟩
  · exact Or.inl ⟨haE, Or.inl hne⟩
  · exact Or.inr ⟨haN, hsub⟩

/-- The larger-rank guard. -/
def InIfaceM (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ) (c : PClause Atom) : Prop :=
  ∀ a ∈ lits c, IfaceM rk σ I m a

theorem inIfaceM_of_inIface (σ : GroundSig Atom Ind) (I : Finset Ind) (m : ℕ)
    {c : PClause Atom} (h : InIface σ I c) : InIfaceM rk σ I m c :=
  fun a ha => ifaceM_of_iface rk σ I m (h a ha)

/-- **Exchange completeness for the larger-rank interface.** -/
theorem maxranked_exchange_complete [Fintype Atom]
    (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ) (I : Finset Ind) (m : ℕ)
    (hm : ∀ o ∈ I, rk o ≤ m)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal (filtM rk σ lt) SG) (hclQ : ClosedR rkQ SQ)
    (hdeliver : ∀ c ∈ SG, InIfaceM rk σ I m c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ IfaceM rk σ I m a → ¬ Occurs SG a)
    (hunsat : Unsat (SG ∪ SQ)) :
    PClause.bot ∈ SQ := by
  classical
  exact downward_server_complete (filtM rk σ lt) (filtM_irrefl rk σ hirrefl)
    (filtM_trans rk σ htrans) rkQ hinjQ (IfaceM rk σ I m) (ifaceM_downward rk σ lt I m hm)
    hclG hclQ ⟨fun c hc hall => hdeliver c hc hall, hlocal⟩ hunsat

/-- **Positive unit readout** for the larger-rank interface. -/
theorem maxranked_unit_readout_complete [Fintype Atom]
    (σ : GroundSig Atom Ind) (lt : Atom → Atom → Prop)
    (hirrefl : ∀ a, ¬ lt a a) (htrans : ∀ a b c, lt a b → lt b c → lt a c)
    (rkQ : Atom → ℕ) (hinjQ : Function.Injective rkQ) (I : Finset Ind) (m : ℕ)
    (hm : ∀ o ∈ I, rk o ≤ m)
    {SG SQ : Finset (PClause Atom)}
    (hclG : ClosedMaximal (filtM rk σ lt) SG) (hclQ : ClosedR rkQ SQ)
    (hdeliver : ∀ c ∈ SG, InIfaceM rk σ I m c → ∃ d ∈ SQ, Strengthens d c)
    (hlocal : ∀ c ∈ SQ, ∀ a ∈ lits c, ¬ IfaceM rk σ I m a → ¬ Occurs SG a)
    (b : Atom) (hleast : ∀ c ∈ SQ, ∀ a ∈ lits c, a ≠ b → rkQ b < rkQ a)
    (hbV : IfaceM rk σ I m b ∨ ¬ Occurs SG b)
    (hent : ∀ J : Atom → Prop, (∀ c ∈ SG ∪ SQ, c.sat J) → J b) :
    PClause.bot ∈ SQ ∨ ∃ d ∈ SQ, Strengthens d (unit b) := by
  classical
  obtain ⟨rkG, hinjG, hext, hV⟩ :=
    exists_rank_extending_lower (filtM rk σ lt) (filtM_irrefl rk σ hirrefl)
      (filtM_trans rk σ htrans) (IfaceM rk σ I m) (ifaceM_downward rk σ lt I m hm)
  exact exchange_unit_readout_complete rkG rkQ hinjG hinjQ hV
    (closedR_of_closedMaximal hext hclG) hclQ
    ⟨fun c hc hall => hdeliver c hc hall, hlocal⟩ b hleast hbV hent

end MaxRanked

#print axioms filt_trans
#print axioms iface_downward
#print axioms inIface_of_all_announced
#print axioms exchangeCond_of_guard
#print axioms announced_exchange_complete
#print axioms announced_unit_readout_complete

#print axioms filtR_trans
#print axioms ifaceR_downward
#print axioms compatibleR_of_compatible
#print axioms inIfaceR_of_inIface
#print axioms ranked_exchange_complete
#print axioms ranked_unit_readout_complete

#print axioms filtM_trans
#print axioms ifaceM_downward
#print axioms compatibleM_of_compatible
#print axioms inIfaceM_of_inIface
#print axioms maxranked_exchange_complete
#print axioms maxranked_unit_readout_complete

end ContextCalculus.ExchangeEquality
