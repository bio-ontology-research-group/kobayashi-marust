//! Compact all-different evidence for counted successor sets.
//! This storage primitive does not fabricate pair-edge IDs: consumers receive
//! the dependency and must materialize the actual endpoints when reporting a
//! clash. Successor producers can opt into this representation; production
//! defaults still retain explicit pair edges during validation.

use std::collections::HashMap;
use std::sync::Arc;
use super::super::model::substrate::Cint64;
use super::TrackPointId;

#[derive(Clone)]
pub struct DistinctGroup {
    members: Arc<[Cint64]>,
    dependency: TrackPointId,
}

impl DistinctGroup {
    pub fn new(mut members: Vec<Cint64>, dependency: TrackPointId) -> Self {
        members.sort_unstable();
        members.dedup();
        Self { members: members.into(), dependency }
    }
    pub fn contains(&self, member: Cint64) -> bool {
        self.members.binary_search(&member).is_ok()
    }
    pub fn members(&self) -> &[Cint64] { &self.members }
}

/// A localized view of one member's partners. Each installed group shares its
/// member vector; pair-specific replacement/removal remains local to this view.
#[derive(Clone)]
pub struct DistinctGroupView {
    owner: Cint64,
    groups: Vec<DistinctGroup>,
    overrides: HashMap<Cint64, Option<TrackPointId>>,
}

impl DistinctGroupView {
    pub fn owner(&self) -> Cint64 { self.owner }
    pub fn new(owner: Cint64) -> Self {
        Self { owner, groups: Vec::new(), overrides: HashMap::new() }
    }
    /// Equivalent to inserting every owner/partner pair with this dependency.
    /// Installing a later group reinstates removed partners and supersedes
    /// older evidence for precisely the pairs present in that group.
    pub fn install(&mut self, group: DistinctGroup) -> bool {
        if !group.contains(self.owner) { return false; }
        self.overrides.retain(|partner, _| !group.contains(*partner));
        self.groups.push(group);
        true
    }
    pub fn replace_pair(&mut self, partner: Cint64, dependency: TrackPointId) {
        if partner != self.owner { self.overrides.insert(partner, Some(dependency)); }
    }
    pub fn remove_pair(&mut self, partner: Cint64) {
        self.overrides.insert(partner, None);
    }
    pub fn dependency(&self, partner: Cint64) -> Option<TrackPointId> {
        if partner == self.owner { return None; }
        if let Some(value) = self.overrides.get(&partner) { return *value; }
        self.groups.iter().rev().find(|group| group.contains(partner))
            .map(|group| group.dependency)
    }
    pub fn len(&self) -> usize {
        if self.groups.len() == 1 && self.overrides.is_empty() {
            return self.groups[0].members.len() - 1;
        }
        self.partners().len()
    }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    /// Enumerate once per partner with the newest active pair provenance.
    pub fn partners(&self) -> Vec<(Cint64, TrackPointId)> {
        let mut partners = HashMap::new();
        for group in &self.groups {
            for &partner in group.members() {
                if partner != self.owner { partners.insert(partner, group.dependency); }
            }
        }
        for (&partner, &dependency) in &self.overrides {
            if partner == self.owner { continue; }
            if let Some(dependency) = dependency { partners.insert(partner, dependency); }
            else { partners.remove(&partner); }
        }
        let mut result: Vec<_> = partners.into_iter().collect();
        result.sort_unstable_by_key(|(partner, _)| *partner);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::super::model::substrate::Id;

    #[test]
    fn group_storage_agrees_with_explicit_pairs_after_localization_and_replacement() {
        let first = Id::new(1);
        let second = Id::new(2);
        let third = Id::new(3);
        for owner in -4..=4 {
            let mut compact = DistinctGroupView::new(owner);
            let mut explicit = HashMap::new();
            for (members, dependency) in [
                (vec![-4, -2, 0, 2, 4], first),
                ((-4..=4).collect(), second),
            ] {
                let group = DistinctGroup::new(members, dependency);
                let accepted = group.contains(owner);
                assert_eq!(compact.install(group.clone()), accepted);
                if accepted {
                    for &partner in group.members() {
                        if partner != owner { explicit.insert(partner, dependency); }
                    }
                }
            }
            let parent = compact.clone();
            compact.remove_pair(-3);
            explicit.remove(&-3);
            compact.replace_pair(17, third);
            explicit.insert(17, third);
            let group = DistinctGroup::new(vec![owner, -3, 2, 2], first);
            compact.install(group.clone());
            for &partner in group.members() {
                if partner != owner { explicit.insert(partner, first); }
            }
            for partner in -5..=18 {
                assert_eq!(compact.dependency(partner), explicit.get(&partner).copied());
            }
            assert_eq!(compact.partners().into_iter().collect::<HashMap<_, _>>(), explicit);
            assert_eq!(compact.len(), explicit.len());
            if owner != -3 { assert_eq!(parent.dependency(-3), Some(second)); }
        }
    }

    #[test]
    fn all_member_views_share_one_group_vector_and_never_make_self_distinct() {
        let group = DistinctGroup::new((0..10_000).collect(), TrackPointId::NONE);
        let copy = group.clone();
        assert!(Arc::ptr_eq(&group.members, &copy.members));
        let mut view = DistinctGroupView::new(123);
        assert!(view.install(copy));
        assert_eq!(view.dependency(124), Some(TrackPointId::NONE));
        assert_eq!(view.dependency(123), None);
        assert_eq!(view.dependency(10_000), None);
        assert_eq!(view.partners().len(), 9_999);
        assert_eq!(view.len(), 9_999);
    }
}
