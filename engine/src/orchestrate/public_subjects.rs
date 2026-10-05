//! Query selection for exact source compilation; never alters the ontology.
use std::collections::{BTreeMap,BTreeSet};
fn iri(s:&str)->&str { s.strip_prefix('<').and_then(|s|s.strip_suffix('>')).unwrap_or(s) }
pub(crate) fn select(named:&[String],map:&BTreeMap<String,String>,private:&BTreeSet<String>)
    -> Result<Vec<String>,String> {
    let private:BTreeSet<_>=private.iter().map(|s|iri(s)).collect();
    let mut found=BTreeSet::new();let mut result=BTreeSet::new();
    for name in named {
        let full=map.get(name).map(|s|iri(s)).unwrap_or(name);
        if private.contains(full) { found.insert(full); } else { result.insert(name.clone()); }
    }
    if found!=private {return Err("private source classes missing from named frontend signature".into());}
    Ok(result.into_iter().collect())
}
/// `eligible` is the frontend's named signature, which also contains roles
/// and individuals. Intersect it with the converter's actual class subjects.
/// Do not require every registry symbol to be a class concept.
pub(crate) fn resolve(concepts:&[String],queries:&[usize],eligible:&[String])->Option<Vec<usize>> {
    let eligible:BTreeSet<_>=eligible.iter().map(String::as_str).collect();
    let candidates:Vec<_>=if queries.is_empty() {(0..concepts.len()).collect()} else {queries.to_vec()};
    let mut selected=BTreeSet::new();
    for id in candidates {
        let name=concepts.get(id)?;
        if eligible.contains(name.as_str()) {selected.insert(id);}
    }
    Some(selected.into_iter().collect())
}

#[cfg(test)] mod tests {
    use super::*;
    #[test] fn exact_iris_preserve_colliding_public_names() {
        let named=vec!["private".into(),"public".into(),"__ground_like_user_class".into()];
        let map=BTreeMap::from([("private".into(),"<urn:generated#same>".into()),
            ("public".into(),"urn:user#same".into())]);
        let private=BTreeSet::from(["urn:generated#same".into()]);
        assert_eq!(select(&named,&map,&private).unwrap(),vec!["__ground_like_user_class","public"]);
        assert!(select(&named,&map,&BTreeSet::from(["urn:missing".into()])).is_err());
    }
    #[test] fn query_selection_is_exact_and_keeps_input_unchanged() {
        let concepts=vec!["A".into(),"helper".into(),"B".into()];let queries=vec![0,1,2];
        assert_eq!(resolve(&concepts,&queries,&["B".into(),"A".into(),"B".into()]),Some(vec![0,2]));
        assert_eq!(resolve(&concepts,&queries,&[]),Some(vec![]));
        assert_eq!(resolve(&concepts,&queries,&["role_only".into(),"B".into()]),Some(vec![2]));
        assert_eq!(resolve(&concepts,&[99],&["B".into()]),None);
        assert_eq!(resolve(&concepts,&[0],&["B".into()]),Some(vec![]));
        assert_eq!(concepts,vec!["A","helper","B"]);assert_eq!(queries,vec![0,1,2]);
    }
}
