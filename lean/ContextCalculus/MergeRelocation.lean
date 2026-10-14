/-!
# Merge link relocation and merged-root read-off

Facts the bridge completion relies on when a node `x` is merged into a node
`y` (a nominal or at-most merge), in any interpretation that realizes the
merge (`value (merge x) = value x` for every node):

* every relocated role link holds: an `R`-link `s → t` becomes
  `merge s → merge t`, including the self link when both endpoints merge
  into the same node (merge phase 5: ancestor, nominal, self-link and
  merge-target arms);
* a concept read from the label of the merge representative holds for the
  merged-away root (the read-off of a merged subject root);
* a deterministic chain of merges composes.

Clearing the current-node pointer after a backtrack only changes which
pending concepts are scheduled, not what a rule derives, so it needs no
semantic lemma: it is a completeness repair of the schedule.
-/

namespace ContextCalculus.MergeRelocation

variable {Node Domain : Type}

/-- A merge map is realized by `value` when every node and its merge target
denote the same element. -/
def Realizes (merge : Node → Node) (value : Node → Domain) : Prop :=
  ∀ x, value (merge x) = value x

theorem relocated_link_holds (merge : Node → Node) (value : Node → Domain)
    (hreal : Realizes merge value) (R : Domain → Domain → Prop) (s t : Node)
    (hst : R (value s) (value t)) :
    R (value (merge s)) (value (merge t)) := by
  rw [hreal s, hreal t]; exact hst

theorem relocated_self_link_holds (merge : Node → Node) (value : Node → Domain)
    (hreal : Realizes merge value) (R : Domain → Domain → Prop) (s t : Node)
    (hst : R (value s) (value t)) (hsame : merge s = merge t) :
    R (value (merge s)) (value (merge s)) := by
  have h := relocated_link_holds merge value hreal R s t hst
  rw [← hsame] at h; exact h

theorem representative_label_holds (merge : Node → Node) (value : Node → Domain)
    (hreal : Realizes merge value) (C : Domain → Prop) (root : Node)
    (hlabel : C (value (merge root))) :
    C (value root) := by
  rw [← hreal root]; exact hlabel

theorem realizes_comp (first second : Node → Node) (value : Node → Domain)
    (h1 : Realizes first value) (h2 : Realizes second value) :
    Realizes (second ∘ first) value := by
  intro x; simp only [Function.comp]; rw [h2, h1]

end ContextCalculus.MergeRelocation
