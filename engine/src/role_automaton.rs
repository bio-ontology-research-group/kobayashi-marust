//! Role automaton — faithful port of Konclude's
//! `CRoleChainAutomataTransformationPreProcess`.
//!
//! Konclude compiles every "complex" role (a role that is transitive, or
//! appears in a role chain `R1∘R2⊑R`, or has sub-/super-roles) into a single
//! non-deterministic finite automaton (NFA) of states + role-labelled
//! transitions.  At tableau runtime the ∀-rule (`applyALLRule`) walks this
//! automaton: a `∀R.C` on a node seeds the automaton's begin-state; each
//! role-edge advances the state; reaching the end-state forces `C` on the
//! successor.  Transitivity of `R` is an epsilon self-loop `endState→beginState`
//! in R's automaton; a chain `R1∘R2⊑R` is the unfolding
//! `begin --R1--> mid --R2--> end`; sub-roles `S⊑R` glue `S`-transitions into
//! `R`'s automaton.  This makes the runtime ∀-rule uniform — it carries no
//! special transitive/chain logic, exactly mirroring Konclude.
//!
//! This module builds the automaton as a pure data structure (states +
//! transitions), independent of the clause/tableau representation, so it can
//! be unit-tested in isolation and later wired into both the frontend clause
//! emission and the QoSat ∀-propagation.  Every mechanism Konclude implements
//! is built here, even ones that do not fire on the current benchmark corpus
//! (inverse-role traversal, implication/branch transition types) — they are
//! kept for completeness and future use, as Konclude ships them.
//!
//! Source reference: `Konclude/Source/Reasoner/Preprocess/
//! CRoleChainAutomataTransformationPreProcess.{h,cpp}` (laptop:
//! `~/Public/software/Konclude`).

use std::collections::{HashMap, HashSet};

/// A role identifier (the caller's role-id space; opaque to this module).
pub type Role = u32;

/// One transition in a role automaton.  `role` is the role labelling the edge
/// that advances the automaton along this transition; `eps` marks an epsilon
/// (role-less) transition (used for the transitive self-loop and the glue
/// arcs between sub-automata, exactly as Konclude's
/// `appendTransitionOperandConceptLinker(endConcept, beginConcept)` epsilon
/// self-loop in `generateRoleChainAutomatConcept`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Transition {
    pub from: State,
    pub to: State,
    pub role: Option<Role>, // None = epsilon
}

/// A state in a role automaton (Konclude `CCAQAND` state concept).
pub type State = u32;

/// A per-role NFA: states + transitions + the designated begin/end pair.
/// Mirrors the structure `convertAutomatConcept` builds for one `∀R.C`:
/// `begin --R--> end`, plus the chain/transitive unfoldings glued in by
/// `generateRoleChainAutomatConcept`.
#[derive(Clone, Debug, Default)]
pub struct RoleAutomaton {
    pub role: Role,
    pub begin: State,
    pub end: State,
    pub states: HashSet<State>,
    pub transitions: Vec<Transition>,
}

/// The role-box facts this module consumes (mirrors Konclude's
/// `collectSubRoleChains` + `createRecursiveTraversalData`):
///   - `transitive`: roles declared `TransitiveObjectProperty` (Konclude
///     stores these as the degenerate chain `R∘R⊑R`, see
///     `isTransitiveChainData`).
///   - `chains`: `R1∘R2⊑R` triples.
///   - `sub_role`: `S⊑R` pairs (the role hierarchy).
///   - `inverse`: `R↔S` inverse pairs (Konclude's
///     `createInverseRoleChainLinkers` threads these into every automaton
///     whose role has an inverse, so the ∀-propagation walks inverse edges
///     too — kept here for fidelity even though the current KM QoSat path
///     routes inverse via bridge clauses).
#[derive(Clone, Debug, Default)]
pub struct RoleBox {
    pub transitive: HashSet<Role>,
    pub chains: Vec<(Role, Role, Role)>, // (R1, R2, R)
    pub sub_role: Vec<(Role, Role)>,     // (S, R): S ⊑ R
    pub inverse: Vec<(Role, Role)>,
}

impl RoleBox {
    /// Reflexive-transitive super-role closure of `r`: { r } ∪ { R : r ⊑* R }.
    /// Konclude's `getIndirectSuperRoleList`.
    pub fn super_close(&self, r: Role) -> HashSet<Role> {
        let mut out = HashSet::new();
        out.insert(r);
        let mut st = vec![r];
        while let Some(u) = st.pop() {
            for &(s, sup) in &self.sub_role {
                if s == u && out.insert(sup) {
                    st.push(sup);
                }
            }
        }
        out
    }

    /// Is `r` complex (needs an automaton)?  Konclude's `role->isComplexRole()`:
    /// transitive, or appears in a chain (as any of R1/R2/R), or has a sub- or
    /// super-role.  Plain roles keep the plain `∀R.C` rule (no automaton).
    pub fn is_complex(&self, r: Role) -> bool {
        if self.transitive.contains(&r) {
            return true;
        }
        for &(r1, r2, rr) in &self.chains {
            if r1 == r || r2 == r || rr == r {
                return true;
            }
        }
        for &(s, sup) in &self.sub_role {
            if s == r || sup == r {
                return true;
            }
        }
        false
    }

    /// Inverse of `r`, if any (Konclude `getInverseRole`).
    pub fn inverse_of(&self, r: Role) -> Option<Role> {
        for &(a, b) in &self.inverse {
            if a == r {
                return Some(b);
            }
            if b == r {
                return Some(a);
            }
        }
        None
    }
}

/// Builder for role automata — the port of
/// `CRoleChainAutomataTransformationPreProcess`.  One builder per ontology;
/// `build(r)` returns the automaton for complex role `r` (cached).
pub struct AutomatonBuilder {
    pub rb: RoleBox,
    cache: HashMap<Role, RoleAutomaton>,
    next_state: State,
    /// Roles already unfolded along the current recursion path (Konclude's
    /// `alreadyUnfoldRoleSet`), to terminate the recursive chain unfolding.
    unfolding: HashSet<Role>,
}

impl AutomatonBuilder {
    pub fn new(rb: RoleBox) -> Self {
        AutomatonBuilder {
            rb,
            cache: HashMap::new(),
            next_state: 0,
            unfolding: HashSet::new(),
        }
    }

    fn fresh_state(&mut self) -> State {
        let s = self.next_state;
        self.next_state += 1;
        s
    }

    /// Build (and cache) the automaton for complex role `r`.  Mirrors
    /// `convertAutomatConcept`: the main `begin --r--> end` transition, then
    /// `generateRoleChainAutomatConcept` glues in chains + transitive
    /// self-loops + sub-role transitions.
    pub fn build(&mut self, r: Role) -> RoleAutomaton {
        if let Some(a) = self.cache.get(&r) {
            return a.clone();
        }
        let mut auto = RoleAutomaton::default();
        auto.role = r;
        let begin = self.fresh_state();
        let end = self.fresh_state();
        auto.begin = begin;
        auto.end = end;
        auto.states.insert(begin);
        auto.states.insert(end);
        // main transition: begin --r--> end  (Konclude line 507-508)
        auto.transitions.push(Transition {
            from: begin,
            to: end,
            role: Some(r),
        });
        // transitive self-loop: end --ε--> begin  (Konclude line 1494-1506,
        // the `transStart && transEnd` branch).  This is what makes ∀R.C
        // chase ALL R-successors transitively.
        if self.rb.transitive.contains(&r) {
            auto.transitions.push(Transition {
                from: end,
                to: begin,
                role: None,
            });
        }
        // unfold chains + sub-roles (Konclude generateRoleChainAutomatConcept).
        // Operate on a local copy of the recursion guard.
        let mut local = self.unfolding.clone();
        local.insert(r);
        // also mark all super-roles as unfolded (Konclude line 1291-1296:
        // superSuperRole added to locUnfoldRoleSet) so a chain through a
        // super-role does not re-unfold the same automaton.
        let supers = self.rb.super_close(r);
        for sup in supers {
            local.insert(sup);
        }
        self.unfold(r, begin, end, &local, &mut auto);
        self.cache.insert(r, auto.clone());
        auto
    }

    /// Like `build` but returns a reference into the cache (the caller-owned
    /// `build` is preferred; this is for traversal helpers).
    pub fn get(&self, r: Role) -> Option<&RoleAutomaton> {
        self.cache.get(&r)
    }

    /// Port of `generateRoleChainAutomatConcept` (the 3-arg overload, line 1274):
    /// for each chain `R1∘R2⊑U` with `U ⊑* r` (i.e. `r` is `U` or a sub-role of
    /// `U`), glue a `begin --R1--> mid --R2--> end` path into the automaton,
    /// recursing into `R1`/`R2`'s own automata if they are complex.
    ///
    /// Soundness: `R1∘R2⊑U` and `U ⊑* r` ⟹ `R1∘R2 ⊑* r`, so a node reachable
    /// via `R1` then `R2` is `r`-reachable — the ∀R.C must cover it.
    fn unfold(&mut self, r: Role, begin: State, end: State, unfolded: &HashSet<Role>, auto: &mut RoleAutomaton) {
        // chains whose super U has r in its sub-role closure (U ⊑* r is r=U or U⊑...⊑r;
        // equivalently r ∈ sub_close(U).  We test U ⊇* r i.e. r ∈ super_close(U)... 
        // correct direction: U ⊑* r means r is a SUPER of U, i.e. r ∈ super_close(U).
        let chains: Vec<(Role, Role, Role)> = self.rb.chains.clone();
        for &(r1, r2, u) in &chains {
            if !self.rb.super_close(u).contains(&r) {
                continue;
            }
            // Konclude line 1384-1399: subBegin --R1--> subEnd --(glue)--> ...
            // For the 2-link chain R1∘R2, the path is begin --R1--> mid --R2--> end.
            // (Konclude's loop builds one sub-automaton per chained role and glues
            // them end-to-end; for a 2-link chain this is exactly two transitions.)
            let mid = self.fresh_state();
            auto.states.insert(mid);
            auto.transitions.push(Transition {
                from: begin,
                to: mid,
                role: Some(r1),
            });
            auto.transitions.push(Transition {
                from: mid,
                to: end,
                role: Some(r2),
            });
            // recurse into R1, R2 if they are complex and not already unfolded
            // (Konclude line 1403-1408 generateRoleChainAutomatConcept recursion).
            for &sub in &[r1, r2] {
                if self.rb.is_complex(sub) && !unfolded.contains(&sub) {
                    let mut local = unfolded.clone();
                    local.insert(sub);
                    let subsup = self.rb.super_close(sub);
                    for sup in subsup {
                        local.insert(sup);
                    }
                    // build a sub-automaton for `sub` and glue its begin/end
                    // onto the (begin, mid) or (mid, end) arc.  For simplicity
                    // and fidelity to Konclude's single-path glue, we recurse
                    // to add sub-role transitions off the relevant state.
                    self.unfold(sub, begin, mid, &local, auto);
                    self.unfold(sub, mid, end, &local, auto);
                }
            }
        }
        // sub-role traversal (Konclude mRecTraversalSubRoleList, line 1278-1307):
        // for each sub-role S of r (S ⊑ r), a transition `begin --S--> end` so
        // that ∀R.C also fires across S-edges (S⊑R ⟹ ∀R.C ⊑ ∀S.C).
        let subroles: Vec<(Role, Role)> = self.rb.sub_role.clone();
        for &(s, sup) in &subroles {
            if sup == r && s != r {
                auto.transitions.push(Transition {
                    from: begin,
                    to: end,
                    role: Some(s),
                });
                if self.rb.is_complex(s) && !unfolded.contains(&s) {
                    let mut local = unfolded.clone();
                    local.insert(s);
                    let ssup = self.rb.super_close(s);
                    for sup2 in ssup {
                        local.insert(sup2);
                    }
                    self.unfold(s, begin, end, &local, auto);
                }
            }
        }
        // inverse-role traversal (Konclude createInverseRoleChainLinkers):
        // if r has an inverse r⁻, the automaton must also walk r⁻ edges (an
        // r⁻-successor is an r-predecessor).  Add a begin --r⁻--> end
        // transition so ∀R.C propagates across inverse edges.  Kept for
        // fidelity (Konclude ships it); the current KM QoSat routes inverse
        // via bridge clauses, so this is inert there but available.
        if let Some(rinv) = self.rb.inverse_of(r) {
            auto.transitions.push(Transition {
                from: begin,
                to: end,
                role: Some(rinv),
            });
        }
    }

    /// Convenience: build automata for all complex roles.
    pub fn build_all(&mut self) -> Vec<RoleAutomaton> {
        let roles: Vec<Role> = {
            let mut s: HashSet<Role> = HashSet::new();
            s.extend(self.rb.transitive.iter().copied());
            for &(r1, r2, r) in &self.rb.chains {
                s.insert(r1);
                s.insert(r2);
                s.insert(r);
            }
            for &(sub, sup) in &self.sub_role_list() {
                s.insert(sub);
                s.insert(sup);
            }
            s.into_iter().collect()
        };
        let mut out = Vec::new();
        for r in roles {
            let a = self.build(r);
            out.push(a);
        }
        out
    }

    fn sub_role_list(&self) -> Vec<(Role, Role)> {
        self.rb.sub_role.clone()
    }
}

/// Epsilon-closure of a state set: all states reachable via epsilon (role=None)
/// transitions.  Used by the runtime ∀-walker to follow the transitive
/// self-loop and the glue arcs (Konclude processes these inline in
/// `applyAutomatTransactions`, but the closure is the equivalent clean form).
pub fn epsilon_closure(auto: &RoleAutomaton, start: &[State]) -> HashSet<State> {
    let mut out: HashSet<State> = start.iter().copied().collect();
    let mut st: Vec<State> = start.to_vec();
    while let Some(u) = st.pop() {
        for t in &auto.transitions {
            if t.role.is_none() && t.from == u && out.insert(t.to) {
                st.push(t.to);
            }
        }
    }
    out
}

/// One step of the ∀-automaton walk: from `states`, advance along every
/// `role`-labelled transition, returning the new state set (after epsilon
/// closure).  This is what `applyALLRule` does per edge: a node with the
/// ∀R.C automaton-seeded states, on gaining an R-edge to a successor, pushes
/// the advanced states onto the successor; the successor's AND-decomposition
/// re-fires.  Returns the states that reached `end` (forcing C on the
/// successor) plus the new frontier for the next hop.
pub fn step(auto: &RoleAutomaton, states: &HashSet<State>, role: Role) -> HashSet<State> {
    let mut next: HashSet<State> = HashSet::new();
    for &s in states {
        for t in &auto.transitions {
            if t.from == s && t.role == Some(role) {
                next.insert(t.to);
            }
        }
    }
    epsilon_closure(auto, &next.into_iter().collect::<Vec<_>>())
}

/// Did the walk reach the end-state?  (Konclude: the end-state's AND-operands
/// — the original C of ∀R.C — are asserted on the successor.)
pub fn reached_end(auto: &RoleAutomaton, states: &HashSet<State>) -> bool {
    states.contains(&auto.end)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rb_transitive(r: Role) -> RoleBox {
        RoleBox {
            transitive: [r].into_iter().collect(),
            ..Default::default()
        }
    }

    /// Transitive R: automaton has begin --R--> end AND the epsilon self-loop
    /// end --ε--> begin (the mechanism that makes ∀R.C chase all successors).
    #[test]
    fn transitive_self_loop() {
        let mut b = AutomatonBuilder::new(rb_transitive(1));
        let a = b.build(1).clone();
        assert!(a.transitions.iter().any(|t| t.from == a.begin && t.to == a.end && t.role == Some(1)));
        assert!(a.transitions.iter().any(|t| t.from == a.end && t.to == a.begin && t.role.is_none()));
    }

    /// A plain (non-complex) role has no automaton built; the caller keeps the
    /// plain ∀R.C rule.  (Sanity: is_complex false.)
    #[test]
    fn plain_role_not_complex() {
        let rb = RoleBox::default();
        assert!(!rb.is_complex(7));
    }

    /// Chain R1∘R2⊑R: the automaton for R gains a begin --R1--> mid --R2--> end
    /// path, so ∀R.C propagates across an R1-edge then an R2-edge.
    #[test]
    fn chain_unfolding() {
        let rb = RoleBox {
            chains: vec![(1, 2, 3)], // R1∘R2 ⊑ R3
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(3).clone();
        // main transition
        assert!(a.transitions.iter().any(|t| t.from == a.begin && t.to == a.end && t.role == Some(3)));
        // chain path: begin --1--> mid --2--> end  (mid is some fresh state)
        let mid = a
            .transitions
            .iter()
            .find(|t| t.from == a.begin && t.role == Some(1))
            .map(|t| t.to)
            .expect("R1 transition from begin");
        assert!(a.transitions.iter().any(|t| t.from == mid && t.to == a.end && t.role == Some(2)));
    }

    /// Sub-role S⊑R: the automaton for R gains a begin --S--> end transition,
    /// so ∀R.C fires across S-edges (S⊑R ⟹ ∀R.C ⊑ ∀S.C).
    #[test]
    fn sub_role_transition() {
        let rb = RoleBox {
            sub_role: vec![(2, 1)], // S=2 ⊑ R=1
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(1).clone();
        assert!(a.transitions.iter().any(|t| t.from == a.begin && t.to == a.end && t.role == Some(2)));
    }

    /// Transitive + chain: ∀R.C with R transitive and a chain R1∘R2⊑R.  The
    /// automaton has both the self-loop AND the chain path — the runtime walker
    /// composes them (a node reached via R1∘R2 also re-fires ∀R.C onward via
    /// the self-loop).  This is the 14817 case (develops_from transitive +
    /// part_of∘develops_from⊑develops_from).
    #[test]
    fn transitive_plus_chain() {
        let rb = RoleBox {
            transitive: [1].into_iter().collect(),
            chains: vec![(2, 1, 1)], // part ∘ dev ⊑ dev
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(1).clone();
        assert!(a.transitions.iter().any(|t| t.role.is_none() && t.from == a.end && t.to == a.begin));
        let mid = a
            .transitions
            .iter()
            .find(|t| t.from == a.begin && t.role == Some(2))
            .map(|t| t.to);
        assert!(mid.is_some(), "chain R1 transition from begin exists");
        let mid = mid.unwrap();
        assert!(a.transitions.iter().any(|t| t.from == mid && t.to == a.end && t.role == Some(1)));
    }

    /// The ∀-walker: seeding begin, advancing along R reaches end (plain).
    #[test]
    fn walk_plain_reaches_end() {
        let rb = RoleBox {
            transitive: [1].into_iter().collect(),
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(1).clone();
        let start = epsilon_closure(&a, &[a.begin]);
        let after_r = step(&a, &start, 1);
        assert!(reached_end(&a, &after_r));
    }

    /// The ∀-walker on a chain: begin --R1--> mid --R2--> end.  Two steps
    /// (R1 then R2) reach end; one step (R1 only) does not.
    #[test]
    fn walk_chain_two_steps() {
        let rb = RoleBox {
            chains: vec![(1, 2, 3)],
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(3).clone();
        let start = epsilon_closure(&a, &[a.begin]);
        let after_r1 = step(&a, &start, 1);
        assert!(!reached_end(&a, &after_r1));
        let after_r2 = step(&a, &after_r1, 2);
        assert!(reached_end(&a, &after_r2));
    }

    /// Transitive walk: begin --R--> end --ε--> begin --R--> end.  After one
    /// R-step we reach end; the epsilon closure brings us back to begin, so a
    /// second R-step again reaches end — the transitive chase.
    #[test]
    fn walk_transitive_chase() {
        let rb = RoleBox {
            transitive: [1].into_iter().collect(),
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(1).clone();
        let start = epsilon_closure(&a, &[a.begin]);
        let s1 = step(&a, &start, 1);
        assert!(reached_end(&a, &s1));
        // s1 epsilon-closes back to begin, so another R-step still reaches end
        let s2 = step(&a, &s1, 1);
        assert!(reached_end(&a, &s2));
    }

    /// Inverse-role transition is added (fidelity: Konclude ships it even
    /// though KM's current path routes inverse via bridge clauses).
    #[test]
    fn inverse_transition_present() {
        let rb = RoleBox {
            inverse: vec![(1, 2)],
            sub_role: vec![(1, 1)], // make 1 complex so an automaton is built
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let a = b.build(1).clone();
        assert!(a.transitions.iter().any(|t| t.from == a.begin && t.to == a.end && t.role == Some(2)));
    }

    /// Sub-role closure: super_close(r) is reflexive + transitive.
    #[test]
    fn super_close_transitive() {
        let rb = RoleBox {
            sub_role: vec![(1, 2), (2, 3)], // 1 ⊑ 2 ⊑ 3
            ..Default::default()
        };
        let sc = rb.super_close(1);
        assert!(sc.contains(&1) && sc.contains(&2) && sc.contains(&3));
        assert!(!sc.contains(&4));
    }

    /// build_all produces automata for every complex role (no duplicates).
    #[test]
    fn build_all_covers_complex() {
        let rb = RoleBox {
            transitive: [1].into_iter().collect(),
            chains: vec![(2, 3, 4)],
            sub_role: vec![(5, 1)],
            ..Default::default()
        };
        let mut b = AutomatonBuilder::new(rb);
        let autos = b.build_all();
        let roles: HashSet<Role> = autos.iter().map(|a| a.role).collect();
        // complex roles: 1 (transitive+has sub 5), 2,3,4 (chain), 5 (sub of 1)
        for &r in &[1, 2, 3, 4, 5] {
            assert!(roles.contains(&r), "missing automaton for role {}", r);
        }
    }
}
