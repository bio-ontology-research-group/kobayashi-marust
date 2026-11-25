//! Source-preserving, bounded compilation of DL-safe object/constant-data rules.
//! Non-rule nodes survive at token level, except data assertions are expressed
//! as equivalent singleton-value class assertions. This is a development
//! compiler; its result still needs ordinary source admission and native reasoning.
use super::{data_rules, ground_rules, iri::IriRegistry, parse, profile::SourceProfileBuilder,
    sexpr::{Node, Parser}, syntax::{Axiom, Concept, Role, RuleAtom}};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

#[derive(Clone)]
pub struct GroundedRuleSource {
    pub text: String,
    pub source_rules: u64,
    pub instances: usize,
    pub private_classes: BTreeSet<String>,
}

static CACHED_GROUNDED_SOURCE: Mutex<Option<(Arc<str>, usize, Result<GroundedRuleSource, String>)>> =
    Mutex::new(None);
fn render(node: &Node<'_>) -> String {
    match node {
        Node::Atom(s) => s.to_string(),
        Node::List(h,args) => format!("{h}({})", args.iter().map(render).collect::<Vec<_>>().join(" ")),
    }
}

/// `text` with every `<iri>` that `source` spells as one prefixed name in
/// that spelling, and with the prefix declarations of `source` that `text`
/// lacks. Quoted literals are copied unchanged.
fn respell_as_source(text: &str, source: &str) -> String {
    let mut prefixes: Vec<(String, String, String)> = Vec::new();
    let mut parser = Parser::new(source);
    while parser.peek() == Some("Prefix") {
        let Ok(node) = parser.parse() else { break };
        let declaration = render(&node);
        let Node::List(_, args) = node else { break };
        let parts: Option<Vec<&str>> = args.iter().map(Node::as_atom).collect();
        let Some(definition) = parts.map(|p| p.concat()) else { continue };
        if let Some((prefix, value)) = definition.split_once(":=") {
            if let Some(iri) = value.strip_prefix('<').and_then(|v| v.strip_suffix('>')) {
                prefixes.push((prefix.to_string(), iri.to_string(), declaration));
            }
        }
    }
    let mut spelled: std::collections::HashMap<String, Option<String>> = Default::default();
    for token in super::sexpr::tokens(source) {
        if token.starts_with('"') || token.starts_with('<') { continue }
        let Some((prefix, local)) = token.split_once(':') else { continue };
        if local.starts_with('=') { continue }
        let Some((_, ns, _)) = prefixes.iter().find(|(p, _, _)| p == prefix) else { continue };
        let entry = spelled.entry(format!("{ns}{local}")).or_insert_with(|| Some(token.to_string()));
        if entry.as_deref() != Some(token) { *entry = None }
    }
    // An IRI the source also writes in full keeps its full form.
    for token in super::sexpr::tokens(source) {
        if let Some(iri) = token.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
            if let Some(entry) = spelled.get_mut(iri) { *entry = None }
        }
    }
    let mut out = String::with_capacity(text.len());
    for (prefix, _, declaration) in &prefixes {
        if !text.contains(&format!("Prefix({prefix}:=")) {
            out.push_str(declaration);
            out.push('\n');
        }
    }
    let bytes = text.as_bytes();
    let (mut i, mut start) = (0usize, 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    if bytes[i] == b'\\' { i += 1 }
                    i += 1;
                }
                i += 1;
            }
            b'<' => match text[i + 1..].find('>') {
                Some(len) => {
                    let iri = &text[i + 1..i + 1 + len];
                    if let Some(Some(token)) = spelled.get(iri) {
                        out.push_str(&text[start..i]);
                        out.push_str(token);
                        start = i + len + 2;
                    }
                    i += len + 2;
                }
                None => i += 1,
            },
            _ => i += 1,
        }
    }
    out.push_str(&text[start.min(text.len())..]);
    out
}

fn retained_axiom(node: &Node<'_>, definitions:&mut BTreeMap<String,String>,
    occupied:&mut BTreeSet<String>, next_assertion: &mut usize) -> Result<String,String> {
    let Node::List(kind,args) = node else { return Ok(render(node)) };
    if !matches!(*kind,"DataPropertyAssertion"|"NegativeDataPropertyAssertion") {
        return Ok(render(node));
    }
    let logical=parse::strip_annotations(args);
    let property=logical.first().and_then(|n|n.as_atom()).ok_or("data assertion lacks property")?;
    let individual=logical.get(1).and_then(|n|n.as_atom()).ok_or("data assertion lacks individual")?;
    let (literal,used)=parse::glue_literal(&logical,2).ok_or("data assertion lacks literal")?;
    if logical.len()!=2+used || !data_rules::exact_rule_literal(&literal) {
        return Err("data assertion has no exact supported literal value".into());
    }
    let value=format!("DataHasValue({property} {literal})");
    let alias=definitions.entry(value).or_insert_with(|| {
        loop {
            let name=format!("__ground_assertion_{}", *next_assertion);
            *next_assertion += 1;
            if occupied.insert(name.clone()) {break format!("<urn:km:ground-rule#{name}>")}
        }
    }).clone();
    let concept=if *kind=="NegativeDataPropertyAssertion" {format!("ObjectComplementOf({alias})")} else {alias};
    let annotations=args.iter().filter(|n|n.head()==Some("Annotation")).map(render).collect::<Vec<_>>().join(" ");
    Ok(format!("ClassAssertion({annotations} {concept} {individual})"))
}

pub fn compile(text: &str, max_instances: usize) -> Result<GroundedRuleSource, String> {
    if text.len() > 16 * 1024 * 1024 { return Err("ground-rule source exceeds development size bound".into()); }
    if let Some((_, _, cached)) = CACHED_GROUNDED_SOURCE
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .as_ref()
        .filter(|(src, max_inst, _)| *max_inst == max_instances && &**src == text)
    {
        return cached.clone();
    }
    let result = compile_uncached(text, max_instances);
    *CACHED_GROUNDED_SOURCE.lock().unwrap_or_else(|e| e.into_inner()) =
        Some((Arc::from(text), max_instances, result.clone()));
    result
}

fn compile_uncached(text: &str, max_instances: usize) -> Result<GroundedRuleSource, String> {
    if text.len() > 16 * 1024 * 1024 { return Err("ground-rule source exceeds development size bound".into()); }
    // Prototype integration: guarded finite numeric profiles precede rule
    // compilation; every resulting source axiom still faces native admission.
    let normalized = super::numeric_source::normalize(text, 256)?;
    let original = text;
    let text = normalized.as_deref().unwrap_or(text);
    let mut registry = IriRegistry::new();
    let mut profile = SourceProfileBuilder::new();
    let mut finite_scan = (text.contains("DLSafeRule") && text.contains("DataPropertyAtom"))
        .then(|| super::finite_data_rules::Scan::new(text));
    let ontology = parse::parse_axioms_observed(&mut registry,text,|node| {
        profile.observe(node);
        if let Some(scan) = &mut finite_scan {
            scan.observe(node);
        }
    }).map_err(|e|e.0)?;
    let names = profile.rule_individual_names().iter().map(|n|registry.short(n)).collect::<BTreeSet<_>>();
    let source = profile.finish(text.len() as u64).source;
    if source.imports != 0 { return Err("ground-rule source imports require closure evidence".into()); }
    if source.rule_axioms == 0 && text.len() > 4 * 1024 * 1024 {
        return Err("ground-rule source exceeds development size bound".into());
    }
    let has_data_assertions = ["DataPropertyAssertion", "NegativeDataPropertyAssertion"]
        .iter().any(|kind| source.axiom_types.get(*kind).copied().unwrap_or(0) != 0);
    if source.rule_axioms == 0 && !has_data_assertions {
        return Err("source has neither rules nor data assertions to normalize".into());
    }
    let mut finite_values = finite_scan.as_ref().map(|s| s.values.clone()).unwrap_or_default();
    finite_values.sort();
    finite_values.dedup();
    let mut rules: Vec<Axiom> = ontology.rules().cloned().collect();
    let mut covered_rules = rules.len() as u64;
    for rule in ontology.datatype_rules() {
        if let Some(lowered) = data_rules::constant_data_rule_plan(rule) {
            rules.push(lowered);
            covered_rules += 1;
        } else if finite_scan.as_ref().is_some_and(super::finite_data_rules::Scan::certified) {
            let lowered = data_rules::finite_data_rule_plan(rule, &finite_values, 100_000)
                .ok_or("concrete rule requires exact nonconstant normalization")?;
            rules.extend(lowered);
            covered_rules += 1;
        } else {
            return Err("concrete rule requires exact nonconstant normalization".into());
        }
    }
    if covered_rules != source.rule_axioms {
        return Err("ground-rule source/parsed rule coverage mismatch".into());
    }
    let role_bound = if source.rule_axioms > 0 && (names.len() >= 16 || rules.len() >= 16) {
        super::named_role_bound::NamedRoleBound::compute(text)
    } else {
        None
    };
    if let Some(bound) = &role_bound {
        rules.retain(|rule| bound.has_reachable_binding(rule));
    }
    let mut occupied: BTreeSet<_> = registry.owned_names().into_iter().collect();
    occupied.extend(super::sexpr::tokens(text).map(super::iri::short_base));
    // Keep concrete restrictions in independently checked source definitions.
    // The grounded object joins then refer to atomic classes, without moving a
    // datatype expression into an unsupported compound source-axiom position.
    let mut definitions: BTreeMap<Concept,String> = BTreeMap::new();
    let mut alias_definitions: BTreeMap<String, Concept> = BTreeMap::new();
    let mut next=0usize;
    for rule in &mut rules {
        let Axiom::Rule(body,head)=rule else {unreachable!()};
        for atom in body.iter_mut().chain(head.iter_mut()) {
            let RuleAtom::Class(c,_) = atom else {continue};
            if matches!(c,Concept::Name(_)) {continue}
            let alias=definitions.entry(c.clone()).or_insert_with(||loop {
                let name=format!("__ground_rule_atom_{next}");next+=1;
                if occupied.insert(name.clone()) {break name}
            }).clone();
            alias_definitions.insert(alias.clone(), c.clone());
            *c=Concept::Name(alias);
        }
    }
    let (paths, plan) = if let Some((bound_axioms, bound_instances)) = role_bound
        .as_ref()
        .and_then(|bound| bound.compile_rules(&rules, &alias_definitions, max_instances))
    {
        (
            super::rule_paths::PathPlan {
                rules: Vec::new(),
                axioms: bound_axioms,
                domain: None,
                instances: bound_instances,
            },
            ground_rules::GroundRulePlan {
                anchor: String::new(),
                cover: None,
                links: BTreeMap::new(),
                axioms: Vec::new(),
                instances: 0,
            },
        )
    } else {
        let paths = super::rule_paths::plan(&rules, &names, &occupied, max_instances)
            .map_err(str::to_owned)?;
        occupied.extend(paths.domain.iter().cloned());
        let plan = if paths.rules.is_empty() {
            ground_rules::GroundRulePlan {
                anchor: String::new(),
                cover: None,
                links: BTreeMap::new(),
                axioms: Vec::new(),
                instances: 0,
            }
        } else {
            ground_rules::plan(&paths.rules,&names,&occupied,max_instances - paths.instances)
                .map_err(str::to_owned)?
        };
        (paths, plan)
    };
    let generated: BTreeMap<_,_> = (!plan.anchor.is_empty()).then_some(&plan.anchor).into_iter().chain(plan.links.values())
        .chain(plan.cover.iter()).chain(paths.domain.iter()).chain(definitions.values())
        .map(|name|(name.clone(),format!("<urn:km:ground-rule#{name}>"))).collect();
    let name = |n: &str| -> Result<String,String> {
        if let Some(iri)=generated.get(n) {return Ok(iri.clone())}
        if !registry.is_named_iri(n) {return Err(format!("unmapped source symbol {n}"))}
        let iri=registry.full_iri(n);
        if iri.contains("://") || iri.starts_with("urn:") {Ok(format!("<{iri}>"))}
        else if iri.contains(':') {Ok(iri)}
        else {Err(format!("source symbol has no absolute or prefixed IRI: {iri}"))}
    };
    let mut parser=Parser::new(text);
    let mut prefixes=Vec::new();
    let mut retained=None;
    // Reuse the same exact definition in assertions and rule atoms. Besides
    // avoiding redundant axioms, this keeps one source symbol per expression.
    let mut assertion_definitions: BTreeMap<String,String> = definitions.iter()
        .map(|(c,n)|Ok((concept(c,&name)?,name(n)?)))
        .collect::<Result<_,String>>()?;
    // Occupied names only grow. Every skipped index stays occupied, so the
    // next free index is exactly the one a fresh search from zero would find.
    let mut next_assertion = 0usize;
    while parser.peek().is_some() {
        let node=parser.parse()?;
        match node {
            Node::List("Prefix",_)=>prefixes.push(render(&node)),
            Node::List("Ontology",children) if retained.is_none()=> {
                retained=Some(children.into_iter().filter(|node|node.head()!=Some("DLSafeRule"))
                    .map(|node|retained_axiom(&node,&mut assertion_definitions,&mut occupied,&mut next_assertion)).collect::<Result<Vec<_>,_>>()?);
            }
            _=>return Err("ground-rule source requires one ontology and prefix declarations".into()),
        }
    }
    let mut axioms=retained.ok_or("ground-rule source has no ontology")?;
    for (expression,alias) in &assertion_definitions {
        if generated.values().any(|existing|existing==alias) {continue}
        axioms.push(format!("Declaration(Class({alias}))"));
        axioms.push(format!("EquivalentClasses({alias} {expression})"));
    }
    if !plan.anchor.is_empty() {
        if let Some(iri) = generated.get(&plan.anchor) {
            axioms.push(format!("Declaration(NamedIndividual({iri}))"));
        }
    }
    for link in plan.links.values().chain(plan.cover.iter()) {axioms.push(format!("Declaration(ObjectProperty({}))",name(link)?));}
    for (expression,alias) in &definitions {
        axioms.push(format!("Declaration(Class({}))",name(alias)?));
        axioms.push(format!("EquivalentClasses({} {})",name(alias)?,concept(expression,&name)?));
    }
    for domain in &paths.domain { axioms.push(format!("Declaration(Class({}))", name(domain)?)); }
    for axiom in plan.axioms.iter().chain(&paths.axioms) {
        axioms.push(match axiom {
            Axiom::SubClassOf(a,b)=>format!("SubClassOf({} {})",concept(a,&name)?,concept(b,&name)?),
            Axiom::ConceptAssertion(c,a)=>format!("ClassAssertion({} {})",concept(c,&name)?,name(a)?),
            Axiom::RoleAssertion(r,a,b)=>format!("ObjectPropertyAssertion({} {} {})",name(r)?,name(a)?,name(b)?),
            _=>return Err("unexpected ground-rule axiom".into()),
        });
    }
    let compiled = format!("{}\nOntology(\n{}\n)\n",prefixes.join("\n"),axioms.join("\n"));
    // The numeric normalization writes every IRI in full and drops the prefix
    // declarations, so the classifier, and every row it publishes, spelled the
    // source's prefixed names as full IRIs. Spell them back as the source does.
    let compiled = if normalized.is_some() { respell_as_source(&compiled, original) } else { compiled };
    Ok(GroundedRuleSource{text:compiled,
        source_rules:source.rule_axioms,instances:plan.instances + paths.instances,
        private_classes:definitions.values().chain(paths.domain.iter()).map(|n|generated[n].trim_matches(['<','>']).to_owned())
            .chain(assertion_definitions.values().map(|n|n.trim_matches(['<','>']).to_owned())).collect()})
}
fn concept(c:&Concept,name:&impl Fn(&str)->Result<String,String>)->Result<String,String> {
    let role=|r:&Role| match r {
        Role::Name(n)=>name(n), Role::Inverse(n)=>Ok(format!("ObjectInverseOf({})",name(n)?)),
        Role::Universal=>Ok("owl:topObjectProperty".into()),
    };
    Ok(match c {
        Concept::Top=>"owl:Thing".into(), Concept::Bottom=>"owl:Nothing".into(),
        Concept::Name(n)=>name(n)?, Concept::Nominal(n)=>format!("ObjectOneOf({})",name(n)?),
        Concept::Not(c)=>format!("ObjectComplementOf({})",concept(c,name)?),
        Concept::And(cs)|Concept::Or(cs)=>format!("{}({})",if matches!(c,Concept::And(_)){"ObjectIntersectionOf"}else{"ObjectUnionOf"},
            cs.iter().map(|c|concept(c,name)).collect::<Result<Vec<_>,_>>()?.join(" ")),
        Concept::Exists(Role::Name(r),f) if matches!(f.as_ref(),Concept::Name(n) if n.starts_with("__dt__val__"))=> {
            let Concept::Name(n)=f.as_ref() else {unreachable!()};
            let literal=n.strip_prefix("__dt__val__").unwrap();
            if !data_rules::exact_rule_literal(literal) {return Err("ground-rule literal has no exact value".into())}
            format!("DataHasValue({} {literal})",name(r)?)
        }
        Concept::Exists(r,c)=>format!("ObjectSomeValuesFrom({} {})",role(r)?,concept(c,name)?),
        Concept::Forall(r,c)=>format!("ObjectAllValuesFrom({} {})",role(r)?,concept(c,name)?),
        Concept::AtLeast(n,r,c)=>format!("ObjectMinCardinality({n} {} {})",role(r)?,concept(c,name)?),
        Concept::AtMost(n,r,c)=>format!("ObjectMaxCardinality({n} {} {})",role(r)?,concept(c,name)?),
        Concept::HasSelf(r)=>format!("ObjectHasSelf({})",role(r)?),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    const SOURCE: &str = r#"Ontology(
      Declaration(Class(<http://km.test/C>)) Declaration(Class(<http://km.test/Bad>))
      SubClassOf(<http://km.test/C> ObjectOneOf(<http://km.test/b>))
      ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)
      DataPropertyAssertion(<http://km.test/p> <http://km.test/a> "NULL"^^xsd:string)
      DLSafeRule(Body(ClassAtom(<http://km.test/C> Variable(<http://km.test/y>))
        ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/x>) Variable(<http://km.test/y>))
        DataPropertyAtom(<http://km.test/p> Variable(<http://km.test/x>) "NULL"^^xsd:string))
        Head(ClassAtom(<http://km.test/Bad> Variable(<http://km.test/y>)))))"#;
    #[test]
    fn source_translation_retains_non_rule_axioms_and_concrete_values() {
        let _test_env = crate::test_env::read();
        let compiled=compile(SOURCE,4).unwrap();
        assert_eq!(compiled.source_rules,1); assert_eq!(compiled.instances,2);
        assert!(!compiled.text.contains("DLSafeRule("));
        assert!(compiled.text.contains("DataHasValue(<http://km.test/p> \"NULL\"^^xsd:string)"));
        parse::for_each_ontology_child(SOURCE,|node| {
            if !matches!(node.head(),Some("DLSafeRule"|"DataPropertyAssertion")) {
                assert!(compiled.text.contains(&render(node)));
            }
            Ok(())
        }).unwrap();
        let mut registry=IriRegistry::new();
        let parsed=parse::parse_axioms(&mut registry,&compiled.text).unwrap();
        assert_eq!(parsed.rules().count(),0);
        assert_eq!(parsed.datatype_rules().count(),0);
    }
    #[test]
    fn source_translation_rejects_missing_coverage_and_nonexact_literals() {
        let _test_env = crate::test_env::read();
        assert!(compile(SOURCE,1).is_err());
        assert!(compile(&SOURCE.replace("^^xsd:string","^^rdfs:Literal"),4).is_err());
        assert!(compile(&SOURCE.replace("ObjectPropertyAtom(","UnknownAtom("),4).is_err());
        assert!(compile(&SOURCE.replace("Ontology(","Ontology(Import(<http://km.test/import>)"),4).is_err());
    }
    #[test]
    fn fresh_anchor_does_not_capture_source_names() {
        let _test_env = crate::test_env::read();
        let source=SOURCE.replace("Ontology(","Ontology(Declaration(NamedIndividual(<urn:km:ground-rule#__ground_rule_0>))");
        let compiled=compile(&source,9).unwrap();
        assert_eq!(compiled.instances,3);
        assert!(compiled.text.contains("Declaration(NamedIndividual(<urn:km:ground-rule#__ground_rule_1>))"));
    }
    #[test]
    fn negative_data_assertion_keeps_polarity_and_annotation() {
        let _test_env = crate::test_env::read();
        let text=r#"NegativeDataPropertyAssertion(Annotation(<http://km.test/note> "retained") <http://km.test/p> <http://km.test/a> "NULL"^^xsd:string)"#;
        let node=Parser::new(text).parse().unwrap();
        let mut definitions=BTreeMap::new(); let mut occupied=BTreeSet::new();
        let mut next = 0;
        let transformed=retained_axiom(&node,&mut definitions,&mut occupied,&mut next).unwrap();
        assert_eq!(transformed,r#"ClassAssertion(Annotation(<http://km.test/note> "retained") ObjectComplementOf(<urn:km:ground-rule#__ground_assertion_0>) <http://km.test/a>)"#);
        assert_eq!(definitions.keys().next().unwrap(),r#"DataHasValue(<http://km.test/p> "NULL"^^xsd:string)"#);
        assert!(retained_axiom(&Parser::new(&text.replace("xsd:string","rdfs:Literal")).parse().unwrap(),&mut definitions,&mut occupied,&mut next).is_err());
    }

    #[test]
    fn assertion_aliases_keep_lowest_free_names_and_reuse_duplicates() {
        let _test_env = crate::test_env::read();
        let mut definitions = BTreeMap::new();
        let mut occupied = [0, 2, 5].into_iter()
            .map(|i| format!("__ground_assertion_{i}")).collect();
        let mut next = 0;
        for (value, expected) in [("red",1),("blue",3),("red",1),("green",4),("yellow",6)] {
            let text = format!("DataPropertyAssertion(<urn:p> <urn:a> \"{value}\"^^xsd:string)");
            let node = Parser::new(&text).parse().unwrap();
            let actual = retained_axiom(&node, &mut definitions, &mut occupied, &mut next).unwrap();
            assert_eq!(actual, format!("ClassAssertion( <urn:km:ground-rule#__ground_assertion_{expected}> <urn:a>)"));
        }
        assert_eq!(definitions.len(), 4);
        assert_eq!(next, 7);
    }
}
