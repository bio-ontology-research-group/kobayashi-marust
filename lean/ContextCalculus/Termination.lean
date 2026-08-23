/-
  ContextCalculus/Termination.lean
  ================================
  **Blocking termination.**

  `CompletenessEq.herbrand_complete_ground` takes its term universe `T` as a
  `Fintype`. This file constructs one finite no-repeat-core universe and proves
  its combinatorial depth bound. It does not prove that the Rust engine's
  blocking relation preserves models, that production contexts are branches in
  this universe, or that the production saturation terminates.

  The engine attaches to each context a **core** (a finite set of concept names,
  the concepts the central element must satisfy).  The Succ rule spawns a
  successor context with a new core; **blocking** refuses to expand a context
  whose core has already appeared on the branch from the root.  So every branch
  the tableau builds is a list of *distinct* cores.

  Cores live in `Finset CN`, which is finite when the concept-name vocabulary
  `CN` is.  Hence:

    * `branch_depth_bound`  — every branch has length `≤ |𝒫(CN)| = 2^|CN|`;
    * `no_infinite_branch`  — there is no infinite branch (an infinite branch
                              would repeat a core, contradicting blocking);
    * `reachable_finite`    — the set of all branches the tableau builds is
                              finite (bounded depth + finite cores);
    * `blockedUniverse` / its `Fintype` instance — the blocked Herbrand universe
                              is a finite type, exactly what `CompletenessEq`
                              needs.

  This is the finite-depth component of a König-style blocking argument. A
  production termination and completeness theorem still needs checked
  refinement hypotheses connecting contexts, successors, reuse, and blocking
  to this abstract universe.
-/
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace ContextCalculus.Termination

/-- A blocking-respecting branch is a list of cores with **no repeats** — the
    blocking invariant the engine maintains along each root-to-leaf path. -/
def BlockedBranch {L : Type} (br : List L) : Prop := br.Nodup

variable {L : Type} [Fintype L]

/-- **Depth bound.**  A blocking-respecting branch is no longer than the number
    of possible cores. -/
theorem branch_depth_bound {br : List L} (h : BlockedBranch br) :
    br.length ≤ Fintype.card L :=
  List.Nodup.length_le_card h

/-- **No infinite branch.**  An infinite branch would inject `ℕ` into the finite
    set of cores, which is impossible — so blocking cuts every branch. -/
theorem no_infinite_branch (f : ℕ → L) : ¬ Function.Injective f :=
  not_injective_infinite_finite f

/-- **The completion is finite.**  The set of all blocking-respecting branches is
    finite: each is a duplicate-free (hence length-bounded) list over the finite
    core type. -/
theorem reachable_finite : {br : List L | BlockedBranch br}.Finite := by
  apply Set.Finite.subset (List.finite_length_le L (Fintype.card L))
  intro br hbr
  exact branch_depth_bound hbr

end ContextCalculus.Termination

/-! ### Instantiation for the context calculus

  The cores of the context calculus are `Finset CN`.  With a finite concept-name
  vocabulary, the depth bound is `2^|CN|` and the blocked universe is a finite
  type — discharging the `Fintype` hypothesis of `CompletenessEq`. -/

namespace ContextCalculus.Termination

variable (CN : Type) [Fintype CN] [DecidableEq CN]

/-- The blocked Herbrand universe: branches of distinct cores over `CN`. -/
def blockedUniverse : Type := {br : List (Finset CN) // BlockedBranch br}

/-- **The abstract blocked universe is finite.** This supplies a possible
    `Fintype` term universe; a separate refinement theorem must show that it
    represents the production engine's terms and blocking. -/
noncomputable instance : Fintype (blockedUniverse CN) :=
  (reachable_finite (L := Finset CN)).fintype

/-- Every duplicate-free abstract core branch has length at most
    `2 ^ |CN|`. This theorem alone does not establish production termination. -/
theorem context_branch_bound {br : List (Finset CN)} (h : BlockedBranch br) :
    br.length ≤ 2 ^ Fintype.card CN := by
  have := branch_depth_bound (L := Finset CN) h
  simpa [Fintype.card_finset] using this

end ContextCalculus.Termination
