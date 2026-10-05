//! Guarded source quotient for independent, explicitly functional numeric roles.
//! This prototype is not connected to production admission.
use super::{datatypes::numeric_cells::{self,Kind,ProfilePartition},sexpr::{Node,Parser}};
use std::collections::{BTreeMap,BTreeSet};
type Prefixes=BTreeMap<String,String>;
fn canonical(s:&str,p:&Prefixes)->String {
    if let Some(t)=s.strip_prefix("^^") {return format!("^^{}",canonical(t,p));}
    if s.starts_with('<') || s.starts_with('"') {return s.into();}
    if let Some((prefix,local))=s.split_once(':') {
        if let Some(base)=p.get(prefix) {return format!("<{base}{local}>");}
    }
    s.into()
}
fn render(n:&Node<'_>,p:&Prefixes)->String {
    match n {Node::Atom(s)=>canonical(s,p),Node::List(h,a)=>format!("{h}({})",a.iter().map(|n|render(n,p)).collect::<Vec<_>>().join(" "))}
}
fn facet(n:&Node<'_>)->bool {match n {Node::List(h,a)=>*h=="DatatypeRestriction"||a.iter().any(facet),_=>false}}
fn role_range<'a>(h:&str,a:&'a[Node<'a>])->Option<(usize,Option<&'a Node<'a>>)> {
    match h {
        "DataSomeValuesFrom"|"DataAllValuesFrom"|"DataPropertyRange" if a.len()==2=>Some((0,a.get(1))),
        "DataMinCardinality"|"DataMaxCardinality"|"DataExactCardinality" if (2..=3).contains(&a.len())=>Some((1,a.get(2))),
        _=>None,
    }
}
fn discover(n:&Node<'_>,p:&Prefixes,out:&mut BTreeSet<String>) {
    if let Node::List(h,a)=n {
        if *h=="Annotation" {return;}
        let logical:Vec<_>=a.iter().filter(|n|n.head()!=Some("Annotation")).cloned().collect();
        if let Some((i,Some(r)))=role_range(h,&logical) {
            if facet(r) {if let Some(s)=logical[i].as_atom(){out.insert(canonical(s,p));}}
        }
        for n in a {discover(n,p,out)}
    }
}
#[derive(Default)]
struct Usage {functional:bool,ranges:BTreeSet<String>,global_ranges:BTreeSet<String>,literals:BTreeSet<String>}
fn inspect(n:&Node<'_>,p:&Prefixes,uses:&mut BTreeMap<String,Usage>)->Result<(),String> {
    let Node::List(h,args)=n else {
        if let Node::Atom(s)=n {if uses.contains_key(&canonical(s,p)) {return Err("numeric role in unverified source position".into());}}
        return Ok(());
    };
    if *h=="Annotation" {return Ok(());}
    if matches!(*h,"Import"|"DatatypeDefinition") {return Err("numeric quotient needs closed datatype/source definitions".into());}
    let a:Vec<_>=args.iter().filter(|n|n.head()!=Some("Annotation")).cloned().collect();
    let slot=match *h {"DataMinCardinality"|"DataMaxCardinality"|"DataExactCardinality"=>1,_=>0};
    let role=a.get(slot).and_then(Node::as_atom).map(|s|canonical(s,p));
    if let Some(role)=role.filter(|r|uses.contains_key(r)) {
        if role=="<http://www.w3.org/2002/07/owl#topDataProperty>" || role=="<http://www.w3.org/2002/07/owl#bottomDataProperty>" {return Err("cannot quotient built-in data properties".into());}
        if slot==1 && a[0].as_atom().and_then(|n|n.parse::<u64>().ok()).is_none() {return Err("invalid cardinality".into());}
        let u=uses.get_mut(&role).unwrap();
        if let Some((_,range))=role_range(h,&a) {
            if let Some(range)=range {
                let text=render(range,p);u.ranges.insert(text.clone());
                if *h=="DataPropertyRange" {u.global_ranges.insert(text);}
            }
            return Ok(());
        }
        match *h {
            "FunctionalDataProperty" if a.len()==1=>{u.functional=true;return Ok(());},
            "DataProperty" if a.len()==1=>return Ok(()),
            "DataPropertyDomain" if a.len()==2=>return inspect(&a[1],p,uses),
            "SubDataPropertyOf" if a.len()==2 && render(&a[1],p)=="<http://www.w3.org/2002/07/owl#topDataProperty>"=>return Ok(()),
            "DataHasValue"|"DataPropertyAssertion"|"NegativeDataPropertyAssertion"=>{
                let at=if *h=="DataHasValue" {1}else{2};
                let (literal,used)=super::parse::glue_literal(&a.iter().collect::<Vec<_>>(),at).ok_or("invalid literal position")?;
                if at+used!=a.len(){return Err("extra literal operands".into());}
                // Glue first, then expand only the datatype suffix.
                let literal=if let Some((lex,dt))=literal.rsplit_once("^^") {format!("{lex}^^{}",canonical(dt,p))}else{literal};
                u.literals.insert(literal);return Ok(());
            },
            _=>return Err(format!("numeric role coupled through {h}")),
        }
    }
    for n in args {inspect(n,p,uses)?;} Ok(())
}
struct Plan {partition:ProfilePartition,ranges:BTreeMap<String,usize>,allowed:Vec<usize>}
fn enumeration(values:impl Iterator<Item=String>)->String {format!("DataOneOf({})",values.collect::<Vec<_>>().join(" "))}
fn rewrite(n:&Node<'_>,p:&Prefixes,plans:&BTreeMap<String,Plan>)->Result<String,String> {
    let Node::List(h,args)=n else {return Ok(render(n,p));};
    if *h=="Annotation" {return Ok(render(n,p));}
    let a:Vec<_>=args.iter().filter(|n|n.head()!=Some("Annotation")).cloned().collect();
    if let Some((slot,Some(range)))=role_range(h,&a) {
        let role=render(&a[slot],p);
        if let Some(plan)=plans.get(&role) {
            let raw=&plan.partition.range_members[*plan.ranges.get(&render(range,p)).ok_or("uncollected range")?];
            // Range axioms constrain all edges conjunctively. Intersect every
            // local qualifier with that same effective range; outside values
            // remain represented when no global range excludes them.
            let members:Vec<_>=plan.allowed.iter().copied()
                .filter(|i| *h=="DataPropertyRange" || raw.contains(i)).collect();
            if members.is_empty() {
                return Ok(match *h {
                    "DataSomeValuesFrom"=>"<http://www.w3.org/2002/07/owl#Nothing>".into(),
                    "DataAllValuesFrom"=>format!("DataMaxCardinality(0 {role})"),
                    "DataPropertyRange"=>format!("SubClassOf(<http://www.w3.org/2002/07/owl#Thing> DataMaxCardinality(0 {role}))"),
                    "DataMinCardinality"|"DataExactCardinality"=>if a[0].as_atom().and_then(|n|n.parse::<u64>().ok())==Some(0) {"<http://www.w3.org/2002/07/owl#Thing>".into()}else{"<http://www.w3.org/2002/07/owl#Nothing>".into()},
                    "DataMaxCardinality"=>"<http://www.w3.org/2002/07/owl#Thing>".into(),
                    _=>return Err("unhandled empty range".into()),
                });
            }
            let replacement=enumeration(members.iter().map(|&i|plan.partition.values[i].clone()));
            let mut out=Vec::new();let mut logical=0;
            for arg in args {
                if arg.head()==Some("Annotation") {out.push(render(arg,p));continue;}
                out.push(if logical==slot+1 {replacement.clone()}else{rewrite(arg,p,plans)?});logical+=1;
            }
            return Ok(format!("{h}({})",out.join(" ")));
        }
    }
    let mut out=args.iter().map(|n|rewrite(n,p,plans)).collect::<Result<Vec<_>,_>>()?;
    if *h=="Ontology" {for (role,plan) in plans {
        out.push(if plan.allowed.is_empty() {
            format!("SubClassOf(<http://www.w3.org/2002/07/owl#Thing> DataMaxCardinality(0 {role}))")
        } else {format!("DataPropertyRange({role} {})",enumeration(plan.allowed.iter().map(|&i|plan.partition.values[i].clone())))});
    }}
    Ok(format!("{h}({})",out.join(" ")))
}
pub fn normalize(text:&str,limit:usize)->Result<Option<String>,String> {
    let mut parser=Parser::new(text);let mut nodes=Vec::new();
    while parser.peek().is_some(){nodes.push(parser.parse()?);}
    let mut prefixes=Prefixes::from([("owl".into(),"http://www.w3.org/2002/07/owl#".into()),("xsd".into(),"http://www.w3.org/2001/XMLSchema#".into()),("rdfs".into(),"http://www.w3.org/2000/01/rdf-schema#".into())]);
    for n in &nodes {if let Node::List("Prefix",a)=n {
        let spec=a.first().and_then(Node::as_atom).ok_or("bad prefix declaration")?;
        let (prefix,iri)=spec.split_once(":=<").ok_or("bad prefix declaration")?;
        prefixes.insert(prefix.into(),iri.strip_suffix('>').ok_or("bad prefix IRI")?.into());
    }}
    let ontologies=nodes.iter().filter(|n|n.head()==Some("Ontology")).collect::<Vec<_>>();
    if ontologies.len()!=1{return Err("expected one ontology".into());}
    let ontology=ontologies[0];let mut roles=BTreeSet::new();discover(ontology,&prefixes,&mut roles);
    if roles.is_empty(){return Ok(None);}
    let mut uses=roles.into_iter().map(|r|(r,Usage::default())).collect::<BTreeMap<_,_>>();
    inspect(ontology,&prefixes,&mut uses)?;
    let mut plans=BTreeMap::new();
    for (role,u) in uses {
        if !u.functional {return Err(format!("numeric role lacks explicit functionality: {role}"));}
        let ranges=u.ranges.into_iter().collect::<Vec<_>>();let literals=u.literals.into_iter().collect::<Vec<_>>();
        let partition=[Kind::Integer,Kind::Float].into_iter().find_map(|kind|numeric_cells::partition(kind,&ranges,&literals,limit)).ok_or("unsupported numeric profile")?;
        let indexed:BTreeMap<_,_>=ranges.into_iter().enumerate().map(|(i,r)|(r,i)).collect();
        let allowed=(0..partition.values.len()).filter(|i|u.global_ranges.iter()
            .all(|r|partition.range_members[indexed[r]].contains(i))).collect();
        plans.insert(role,Plan{partition,ranges:indexed,allowed});
    }
    Ok(Some(rewrite(ontology,&prefixes,&plans)?))
}
#[cfg(test)] mod tests {
    use super::*;
    fn source(extra:&str)->String {format!("Prefix(:=<urn:test:>) Ontology(FunctionalDataProperty(:p) SubClassOf(:A DataSomeValuesFrom(:p DatatypeRestriction(xsd:integer xsd:minExclusive \"3\"^^xsd:integer))) {extra})")}
    #[test] fn finite_cover_includes_outside_and_preserves_negative_constants() {
        let result=normalize(&source("NegativeDataPropertyAssertion(:p :a \"4\"^^xsd:integer) SubClassOf(:Out DataSomeValuesFrom(:p DataComplementOf(xsd:integer)))"),32).unwrap().unwrap();
        assert!(result.contains("#string>"));assert!(result.contains("NegativeDataPropertyAssertion(<urn:test:p> <urn:test:a> \"4\" ^^<http://www.w3.org/2001/XMLSchema#integer>)"));
        assert!(!result.contains("DatatypeRestriction"));assert!(result.contains("DataPropertyRange(<urn:test:p> DataOneOf("));
    }
    #[test] fn declared_ranges_are_intersected_and_empty_intersections_forbid_edges() {
        let result=normalize(&source("DataPropertyRange(:p xsd:integer) DataPropertyRange(:p DatatypeRestriction(xsd:integer xsd:maxInclusive \"3\"^^xsd:integer))"),32).unwrap().unwrap();
        assert!(result.contains("SubClassOf(<urn:test:A> <http://www.w3.org/2002/07/owl#Nothing>)"));
        assert!(!result.contains("#string>"));assert!(!result.contains("DataOneOf()"));
        let result=normalize(&source("DataPropertyRange(:p xsd:integer) DataPropertyRange(:p DataComplementOf(xsd:integer))"),32).unwrap().unwrap();
        assert!(result.contains("DataMaxCardinality(0 <urn:test:p>)"));
        assert!(!result.contains("DataOneOf()"));
    }
    #[test] fn decline_coupling_unknown_positions_and_rebound_datatypes() {
        for extra in ["SubDataPropertyOf(:p :q)","SubDataPropertyOf(:q :p)","DisjointDataProperties(:p :q)","HasKey(:A () (:p))","DLSafeRule(Body(DataPropertyAtom(:p Variable(:x) Variable(:v))) Head())","Import(<urn:missing>)"] {
            assert!(normalize(&source(extra),32).is_err(),"{extra}");
        }
        assert!(normalize(&source("").replace("FunctionalDataProperty(:p)",""),32).is_err());
        assert!(normalize(&source("DataMinCardinality(bad :p xsd:integer)"),32).is_err());
        assert!(normalize(&source("").replace(":p","owl:topDataProperty"),32).is_err());
        assert!(normalize(&format!("Prefix(xsd:=<urn:fake:>) {}",source("")),32).is_err());
    }
    #[test] fn empty_ranges_and_unqualified_cardinality_remain_well_formed() {
        let s=source("SubClassOf(:B DataAllValuesFrom(:p DataIntersectionOf(xsd:integer DataComplementOf(xsd:integer)))) SubClassOf(:C DataMaxCardinality(1 :p))");
        let result=normalize(&s,32).unwrap().unwrap();assert!(result.contains("DataMaxCardinality(0 <urn:test:p>)"));assert!(!result.contains("DataOneOf()"));assert!(result.contains("DataMaxCardinality(1 <urn:test:p>)"));
    }
}
