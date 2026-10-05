//! Finite membership-profile representatives for independent functional numeric
//! properties. This does NOT authorize rewriting a source property: functionality,
//! complete predicate/literal collection, and absence of coupling need separate
//! source evidence. Native datatype admission is unchanged.
use super::{builtin_datatype_key, builtin_facet_key, exact_swrl_integer, glued_atoms,
    named_dt, parse_literal, Node, Parser, Partition, Val};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Kind { Integer, Float }
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
enum Point { Integer(i128), Float(u32) }
#[derive(Clone,Debug)]
enum Predicate { Bounds(Vec<(&'static str,Point)>), Values(Vec<Point>),
    Not(Box<Predicate>), And(Vec<Predicate>), Or(Vec<Predicate>) }

fn point(kind:Kind,literal:&str)->Option<Point> {
    match (kind,parse_literal(literal)?.0) {
        (Kind::Integer,Val::Num(_))=>exact_swrl_integer(literal).map(Point::Integer),
        (Kind::Float,Val::Float32(bits))=>Some(Point::Float(bits)),
        _=>None,
    }
}
fn named(kind:Kind,name:&str)->Option<Predicate> {
    if kind==Kind::Float {
        return (builtin_datatype_key(name)==Some("float")).then(||Predicate::Bounds(vec![]));
    }
    let d=named_dt(name)?;
    if d.part!=Partition::Numeric || !d.integral {return None;}
    let mut bounds=Vec::new();
    if let Some(n)=d.min {bounds.push(("minInclusive",Point::Integer(n)));}
    if let Some(n)=d.max {bounds.push(("maxInclusive",Point::Integer(n)));}
    Some(Predicate::Bounds(bounds))
}
fn predicate(kind:Kind,node:&Node<'_>)->Option<Predicate> {
    match node {
        Node::Atom(name)=>named(kind,name),
        Node::List("DataComplementOf",args) if args.len()==1=>
            Some(Predicate::Not(Box::new(predicate(kind,&args[0])?))),
        Node::List("DataIntersectionOf",args)=>Some(Predicate::And(args.iter()
            .map(|n|predicate(kind,n)).collect::<Option<_>>()?)),
        Node::List("DataUnionOf",args)=>Some(Predicate::Or(args.iter()
            .map(|n|predicate(kind,n)).collect::<Option<_>>()?)),
        Node::List("DataOneOf",args)=>Some(Predicate::Values(glued_atoms(args)?.iter()
            .map(|s|point(kind,s)).collect::<Option<_>>()?)),
        Node::List("DatatypeRestriction",args)=> {
            let tokens=glued_atoms(args)?;
            if tokens.len()<3 || tokens.len()%2!=1 {return None;}
            let Predicate::Bounds(mut bounds)=named(kind,&tokens[0])? else {return None};
            for pair in tokens[1..].chunks_exact(2) {
                let facet=match builtin_facet_key(&pair[0])? {
                    "minInclusive"=>"minInclusive", "minExclusive"=>"minExclusive",
                    "maxInclusive"=>"maxInclusive", "maxExclusive"=>"maxExclusive",
                    _=>return None,
                };
                let p=point(kind,&pair[1])?;
                if matches!(p,Point::Float(b) if f32::from_bits(b).is_nan()) {return None;}
                // Keep every bound. Equal endpoints with different strictness
                // must be intersected rather than choosing the first one.
                bounds.push((facet,p));
            }
            Some(Predicate::Bounds(bounds))
        }
        _=>None,
    }
}
impl Predicate {
    fn contains(&self,p:Point)->bool {
        match self {
            Self::Bounds(bounds)=>bounds.iter().all(|&(op,b)| {
                macro_rules! compare {($a:expr,$b:expr)=>{ match op {
                    "minInclusive"=>$a >= $b,"minExclusive"=>$a > $b,
                    "maxInclusive"=>$a <= $b,"maxExclusive"=>$a < $b,_=>unreachable!() }}}
                match (p,b) {
                    (Point::Integer(a),Point::Integer(b))=>compare!(a,b),
                    (Point::Float(a),Point::Float(b))=>compare!(f32::from_bits(a),f32::from_bits(b)),
                    _=>false,
                }
            }),
            Self::Values(values)=>values.contains(&p),
            Self::Not(inner)=>!inner.contains(p),
            Self::And(parts)=>parts.iter().all(|q|q.contains(p)),
            Self::Or(parts)=>parts.iter().any(|q|q.contains(p)),
        }
    }
    // Every atomic predicate parsed by this module is contained in `kind`.
    // Boolean complements, however, use the entire OWL datatype domain.
    fn contains_outside(&self)->bool {
        match self {
            Self::Bounds(_)|Self::Values(_)=>false,
            Self::Not(inner)=>!inner.contains_outside(),
            Self::And(parts)=>parts.iter().all(Self::contains_outside),
            Self::Or(parts)=>parts.iter().any(Self::contains_outside),
        }
    }
    fn cuts(&self,out:&mut BTreeSet<Point>) {
        match self {
            Self::Bounds(bounds)=>out.extend(bounds.iter().map(|(_,p)|*p)),
            Self::Values(values)=>out.extend(values),
            Self::Not(inner)=>inner.cuts(out),
            Self::And(parts)|Self::Or(parts)=>for q in parts {q.cuts(out)},
        }
    }
}
fn adjacent(p:Point,out:&mut BTreeSet<Point>)->Option<()> {
    out.insert(p);
    match p {
        Point::Integer(n)=>{
            out.insert(Point::Integer(n.checked_sub(1)?));
            out.insert(Point::Integer(n.checked_add(1)?));
        }
        Point::Float(b)=>{
            let value=f32::from_bits(b);
            if value.is_nan() {return Some(());}
            if value==0.0 {
                for b in [0,0x8000_0000,1,0x8000_0001] {out.insert(Point::Float(b));}
            } else {
                if value!=f32::INFINITY {out.insert(Point::Float(if value>0.0 {b+1}else{b-1}));}
                if value!=f32::NEG_INFINITY {out.insert(Point::Float(if value>0.0 {b-1}else{b+1}));}
            }
        }
    }
    Some(())
}
fn literal(p:Point)->String {
    let (lexical,datatype)=match p {
        Point::Integer(n)=>(n.to_string(),"integer"),
        Point::Float(b)=>{
            let v=f32::from_bits(b);
            let s=if v.is_nan(){"NaN".into()}else if v==f32::INFINITY{"INF".into()}
                else if v==f32::NEG_INFINITY{"-INF".into()}else{v.to_string()};
            (s,"float")
        }
    };
    format!("\"{lexical}\"^^<http://www.w3.org/2001/XMLSchema#{datatype}>")
}
fn parse(kind:Kind,text:&str)->Option<Predicate> {
    let mut parser=Parser::new(text);let result=predicate(kind,&parser.parse().ok()?)?;
    if parser.peek().is_some(){return None;} Some(result)
}
/// Each returned value represents one realized vector of predicate membership
/// and literal identity. Predicates range over the chosen entire base family.
/// Caller must additionally intersect the declared property ranges, and prove
/// the source property can be collapsed without cross-property identity effects.
pub(crate) fn representatives(kind:Kind,ranges:&[String],literals:&[String],
    limit:usize)->Option<Vec<String>> {
    let predicates=ranges.iter().map(|s|parse(kind,s)).collect::<Option<Vec<_>>>()?;
    let values=literals.iter().map(|s|point(kind,s)).collect::<Option<Vec<_>>>()?;
    let mut cuts=BTreeSet::new();for p in &predicates {p.cuts(&mut cuts)}
    cuts.extend(values.iter().copied());
    match kind {
        Kind::Integer=>{cuts.insert(Point::Integer(0));}
        Kind::Float=>for v in [0.0f32,-0.0,f32::INFINITY,f32::NEG_INFINITY,f32::NAN] {
            cuts.insert(Point::Float(v.to_bits()));
        }
    }
    let mut candidates=BTreeSet::new();for p in cuts {adjacent(p,&mut candidates)?;}
    let mut profiles=BTreeMap::new();
    for p in candidates {
        let signature=predicates.iter().map(|q|q.contains(p))
            .chain(values.iter().map(|q|*q==p)).collect::<Vec<_>>();
        profiles.entry(signature).or_insert(p);
        if profiles.len()>limit{return None;}
    }
    Some(profiles.into_values().map(literal).collect())
}

/// A finite partition of the entire data domain for this module's predicates.
/// Range members index `values`, so source rewrites can use exactly the same
/// representatives for a property's global range and all of its restrictions.
/// Literal tests must all belong to `kind`; mixed-family constants decline.
/// This is a partition utility, not authorization to collapse coupled roles.
#[derive(Debug)]
pub(crate) struct ProfilePartition {
    pub values: Vec<String>,
    pub range_members: Vec<Vec<usize>>,
}
pub(crate) fn partition(kind:Kind,ranges:&[String],literals:&[String],
    limit:usize)->Option<ProfilePartition> {
    let predicates=ranges.iter().map(|s|parse(kind,s)).collect::<Option<Vec<_>>>()?;
    let constants=literals.iter().map(|s|point(kind,s)).collect::<Option<Vec<_>>>()?;
    let numeric=representatives(kind,ranges,literals,limit)?;
    let mut profiles=BTreeMap::new();
    for value in numeric {
        let p=point(kind,&value)?;
        let profile=predicates.iter().map(|q|q.contains(p))
            .chain(constants.iter().map(|q|*q==p)).collect::<Vec<_>>();
        profiles.insert(profile,value);
    }
    // xsd:string is disjoint from both supported numeric families. Since all
    // literal tests were checked above, this witness cannot alias a constant.
    let outside=predicates.iter().map(Predicate::contains_outside)
        .chain(constants.iter().map(|_|false)).collect::<Vec<_>>();
    profiles.entry(outside).or_insert_with(||
        "\"__km_numeric_outside\"^^<http://www.w3.org/2001/XMLSchema#string>".into());
    if profiles.len()>limit {return None;}
    let mut result=ProfilePartition{values:Vec::new(),range_members:vec![Vec::new();ranges.len()]};
    for (profile,value) in profiles {
        let index=result.values.len();result.values.push(value);
        for (range,&member) in profile[..ranges.len()].iter().enumerate() {
            if member {result.range_members[range].push(index);}
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn restriction(base:&str,facet:&str,lit:&str)->String {
        format!("DatatypeRestriction(xsd:{base} xsd:{facet} {lit})")
    }
    #[test]
    fn integer_cells_cover_all_small_models_and_preserve_literal_exclusions() {
        for lo in -4..=4 {for hi in lo..=4 {
            let ranges=vec![restriction("integer","minExclusive",&format!("\"{lo}\"^^xsd:integer")),
                restriction("integer","maxInclusive",&format!("\"{hi}\"^^xsd:integer"))];
            let literals=vec!["\"0\"^^xsd:integer".into()];
            let reps=representatives(Kind::Integer,&ranges,&literals,32).unwrap();
            let qs=ranges.iter().map(|s|parse(Kind::Integer,s).unwrap()).collect::<Vec<_>>();
            let profile=|n|qs.iter().map(|q|q.contains(n)).chain([n==Point::Integer(0)]).collect::<Vec<_>>();
            for n in -10..=10 {assert!(reps.iter().any(|s|profile(point(Kind::Integer,s).unwrap())==profile(Point::Integer(n))));}
        }}
        let range="DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer xsd:minExclusive \"1\"^^xsd:integer)";
        assert!(!parse(Kind::Integer,range).unwrap().contains(Point::Integer(1)));
    }
    #[test]
    fn float_cells_cover_adjacent_values_nan_and_signed_zero_identity() {
        let ranges=vec![restriction("float","minExclusive","\"0.5\"^^xsd:float"),
            restriction("float","maxInclusive","\"0.5\"^^xsd:float")];
        let literals=vec!["\"0\"^^xsd:float".into(),"\"-0\"^^xsd:float".into(),"\"NaN\"^^xsd:float".into()];
        let reps=representatives(Kind::Float,&ranges,&literals,32).unwrap();
        let qs=ranges.iter().map(|s|parse(Kind::Float,s).unwrap()).collect::<Vec<_>>();
        let vs=literals.iter().map(|s|point(Kind::Float,s).unwrap()).collect::<Vec<_>>();
        let profile=|p|qs.iter().map(|q|q.contains(p)).chain(vs.iter().map(|q|*q==p)).collect::<Vec<_>>();
        for bits in [0,0x80000000,1,0x80000001,0x3f000000-1,0x3f000000,0x3f000000+1,
            f32::MAX.to_bits(),(-f32::MAX).to_bits(),f32::INFINITY.to_bits(),f32::NEG_INFINITY.to_bits(),f32::NAN.to_bits()] {
            assert!(reps.iter().any(|s|profile(point(Kind::Float,s).unwrap())==profile(Point::Float(bits))),"bits={bits:x}");
        }
        for rep in reps {let p=point(Kind::Float,&rep).unwrap();assert_eq!(point(Kind::Float,&literal(p)),Some(p));}
    }
    #[test]
    fn full_domain_partition_retains_outside_numeric_complements() {
        let ranges=vec!["xsd:integer".into(),"DataComplementOf(xsd:integer)".into(),
            "DatatypeRestriction(xsd:integer xsd:minExclusive \"3\"^^xsd:integer)".into()];
        let result=partition(Kind::Integer,&ranges,&["\"4\"^^xsd:integer".into()],16).unwrap();
        let outside=&result.range_members[1];assert_eq!(outside.len(),1);
        assert!(result.values[outside[0]].ends_with("#string>"));
        assert!(!result.range_members[0].contains(&outside[0]));
        assert!(!result.range_members[2].contains(&outside[0]));
        assert_eq!(result.range_members[0].len()+outside.len(),result.values.len());
        // Retain the named value as well as an unequal witness in the same
        // numeric interval: negative assertions may exclude just the former.
        assert_eq!(result.range_members[2].len(),2);
        assert!(partition(Kind::Integer,&ranges,&[],1).is_none());
        assert!(partition(Kind::Integer,&ranges,&["\"text\"".into()],16).is_none());
        let floats=partition(Kind::Float,&["xsd:float".into(),
            "DataComplementOf(xsd:float)".into()],&[],8).unwrap();
        assert_eq!(floats.values.len(),2);
        assert_eq!(floats.range_members.iter().map(Vec::len).collect::<Vec<_>>(),vec![1,1]);
    }
    #[test]
    fn unknown_facets_types_trailing_tokens_and_overflow_decline() {
        for range in ["ex:float","xsd:double","DatatypeRestriction(xsd:float xsd:pattern \"x\")",
            "DatatypeRestriction(xsd:float xsd:minInclusive \"NaN\"^^xsd:float)","xsd:float xsd:float"] {
            assert!(representatives(Kind::Float,&[range.into()],&[],32).is_none());
        }
        assert!(representatives(Kind::Integer,&[],&[format!("\"{}\"^^xsd:integer",i128::MAX)],32).is_none());
        assert!(representatives(Kind::Float,&[],&[],0).is_none());
    }
}
