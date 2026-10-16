//! Exact validated-origin admission reuse; never publishes a taxonomy.
use std::sync::Arc;
use crate::frontend::{conformance,sexpr::{Node,Parser}};
use crate::source_locality::{scan,fingerprint,StmtKind};
use crate::fxhash::{FxHashMap,FxHashSet};
use crate::source_reuse_grammar::outer_grammar;

#[derive(Clone,Copy,PartialEq,Eq)]
enum Form { Fixed, SubClass, DisjointRemoval, OriginRemoval }
#[derive(Clone)]
struct Entry { start:usize,end:usize,count:usize,form:Form }

/// Origin exists only after an exact successful public-source cache lookup.
/// Derived sources inherit it only through the sufficient checks below.
pub(crate) struct NamedSubclassCertificate {
    origin:Arc<String>,
    source:Arc<String>,
    header_end:usize,
    declared:Arc<FxHashSet<Box<str>>>,
    origin_entries:Arc<FxHashMap<u128,Entry>>,
}
fn increment_count(count:&mut usize)->Option<()> { *count=count.checked_add(1)?;Some(()) }
fn node(text:&str)->Option<Node<'_>> {
    let mut parser=Parser::new(text);let value=parser.parse().ok()?;
    parser.peek().is_none().then_some(value)
}
fn declared_atom<'a>(value:&Node<'a>,declared:&FxHashSet<Box<str>>)->Option<&'a str> {
    let atom=value.as_atom()?;
    (!atom.starts_with("_:") && !atom.starts_with('"') && declared.contains(atom)).then_some(atom)
}
fn head(text:&str)->&str { &text[..text.bytes().take_while(u8::is_ascii_alphabetic).count()] }
fn form(text:&str,declared:&FxHashSet<Box<str>>)->Form {
    if !matches!(head(text),"SubClassOf"|"DisjointClasses") {return Form::Fixed;}
    match node(text) {
        Some(Node::List("SubClassOf",args)) if args.len()==2 && args.iter().all(|v|declared_atom(v,declared).is_some()) => Form::SubClass,
        Some(Node::List("DisjointClasses",args)) if args.len()>=2 && args.iter().all(|v|declared_atom(v,declared).is_some()) => Form::DisjointRemoval,
        _=>Form::Fixed,
    }
}
fn origin_form(text:&str,kind:StmtKind,declared:&FxHashSet<Box<str>>)->Form {
    let named=form(text,declared);
    if named!=Form::Fixed {return named;}
    if !matches!(kind,StmtKind::Logical|StmtKind::Assertion) {return Form::Fixed;}
    // Deletion is not universally admission-preserving. A custom datatype
    // use may still need its definition, and splitting an anonymous tree can
    // remove the only vertex with at most one named assertion. Keep both
    // dependencies exact. The substring check deliberately also protects
    // harmless occurrences in annotations/literals/IRIs rather than risking
    // a missed anonymous individual or reparsing every origin assertion.
    if head(text)=="DatatypeDefinition" || (matches!(head(text),
        "ObjectPropertyAssertion"|"NegativeObjectPropertyAssertion") && text.contains("_:")) {
        return Form::Fixed;
    }
    Form::OriginRemoval
}
impl NamedSubclassCertificate {
    /// No second full check to mint. Caller passes its existing owned source.
    /// The exact public-validation cache is queried without cloning facts.
    pub(crate) fn from_success_cache(source:Arc<String>)->Option<Self> {
        if !source.is_ascii() {return None;}
        let scanned=scan(&source).ok()?;
        Self::capture_scanned(source,&scanned)
    }
    pub(crate) fn capture_scanned(source:Arc<String>,scanned:&crate::source_locality::Scan)->Option<Self> {
        if !conformance::cached_user_source_accepted(&source) || !source.is_ascii() {return None;}
        if !outer_grammar(&source,&scanned) {return None;}
        let mut declared=FxHashSet::default();
        for st in &scanned.statements {
            let text=&source[st.start..st.end];
            if head(text)!="Declaration" {continue;}
            if let Some(Node::List("Declaration",args))=node(text) {
                if let [Node::List("Class",names)]=args.as_slice() {
                    if let [Node::Atom(name)]=names.as_slice() {declared.insert(Box::<str>::from(*name));}
                }
            }
        }
        let mut entries:FxHashMap<u128,Entry>=FxHashMap::default();
        for st in &scanned.statements {
            let text=&source[st.start..st.end];
            if let Some(old)=entries.get_mut(&st.hash) {
                if &source[old.start..old.end]!=text {return None;}
                increment_count(&mut old.count)?;
            } else {entries.insert(st.hash,Entry{start:st.start,end:st.end,count:1,form:origin_form(text,st.kind,&declared)});}
        }
        let entries=Arc::new(entries);
        Some(Self{origin:source.clone(),source,header_end:scanned.open_end,declared:Arc::new(declared),origin_entries:entries})
    }
    /// NEW declarations/header/annotations and protected origin dependencies
    /// remain exact. Other original logical/assertion spans may be deleted
    /// and restored up to their origin multiplicity. With datatype definitions
    /// and anonymous object-property assertions fixed, the remaining global
    /// validators only lose constraints/uses; isolated anonymous vertices
    /// remain valid. Only supported named subclass axioms may be novel.
    /// No SourceFacts or cache entry for NEW is manufactured.
    pub(crate) fn derive(&self,source:Arc<String>)->Option<Self> {
        if !source.is_ascii() {return None;}
        let scanned=scan(&source).ok()?;
        self.derive_scanned(source,&scanned)
    }
    pub(crate) fn derive_scanned(&self,source:Arc<String>,scanned:&crate::source_locality::Scan)->Option<Self> {
        if !source.is_ascii() {return None;}
        if !outer_grammar(&source,&scanned) || source[..scanned.open_end]!=self.source[..self.header_end] {return None;}
        let mut entries:FxHashMap<u128,Entry>=FxHashMap::default();
        let mut changed=String::from(&source[..scanned.open_end]);changed.push('\n');
        let mut added=false;
        for st in &scanned.statements {
            let text=&source[st.start..st.end];
            if let Some(duplicate)=entries.get_mut(&st.hash) {
                if &source[duplicate.start..duplicate.end]!=text {return None;}
                increment_count(&mut duplicate.count)?;continue;
            }
            let kind=if let Some(old)=self.origin_entries.get(&st.hash) {
                if &self.origin[old.start..old.end]!=text {return None;}
                old.form
            } else {
                if form(text,&self.declared)!=Form::SubClass {return None;}
                changed.push_str(text);changed.push('\n');added=true;Form::SubClass
            };
            entries.insert(st.hash,Entry{start:st.start,end:st.end,count:1,form:kind});
        }
        for (hash,old) in self.origin_entries.iter() {
            let count=entries.get(hash).map_or(0,|e|e.count);
            match old.form {
                Form::Fixed if count!=old.count=>return None,
                Form::DisjointRemoval|Form::OriginRemoval if count>old.count=>return None,
                _=>{},
            }
        }
        changed.push(')');
        if added && conformance::check_source(&changed).is_err() {return None;}
        Some(Self{origin:self.origin.clone(),source,header_end:scanned.open_end,declared:self.declared.clone(),origin_entries:self.origin_entries.clone()})
    }
    pub fn source_hash(&self)->u128 {fingerprint(self.source.as_bytes())}
    pub fn origin_hash(&self)->u128 {fingerprint(self.origin.as_bytes())}
    pub fn named_disjoint_removable(&self)->usize {self.origin_entries.values().filter(|e|e.form==Form::DisjointRemoval).map(|e|e.count).sum()}
}

#[cfg(test)] mod count_tests {
    use super::*;
    #[test] fn duplicate_count_overflow_declines() {
        let mut count=usize::MAX;assert!(increment_count(&mut count).is_none());
        assert_eq!(count,usize::MAX);
    }
}

#[cfg(test)] mod tests {
    use super::*;

    fn source(axioms: &str) -> String {
        format!("Prefix(:=<urn:admission-test:>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) {axioms})")
    }

    fn captured(text: &str) -> NamedSubclassCertificate {
        conformance::check_user_source(text).expect("valid origin");
        NamedSubclassCertificate::from_success_cache(Arc::new(text.to_owned()))
            .expect("exact successful public validation in isolated test process")
    }

    fn extended_source(axioms: &str) -> String {
        format!("Prefix(:=<urn:origin-subset:>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(DataProperty(:p)) Declaration(Datatype(:D)) DatatypeDefinition(:D xsd:string) {axioms})")
    }

    // Called only by the isolated child below. Exercise the actual public
    // validator and its successful-source provenance, never a checker stub.
    fn origin_subset_public_validator_controls() {
        let axioms = [
            "ClassAssertion(:A _:isolated)",
            "ObjectPropertyAssertion(:r :i :j)",
            "DataPropertyAssertion(:p _:isolated \"value\")",
            "EquivalentClasses(:A ObjectIntersectionOf(:B ObjectComplementOf(:C)))",
            "SubClassOf(Annotation(rdfs:label \"original\") :B ObjectSomeValuesFrom(:r :C))",
            "ObjectPropertyDomain(:r :A)",
            "SubObjectPropertyOf(ObjectPropertyChain(:r :s) :r)",
            "DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:B Variable(:x))))",
            "DifferentIndividuals(:i :j)",
            "FunctionalDataProperty(:p)",
            "DataPropertyRange(:p :D)",
            "ClassAssertion(ObjectMaxCardinality(1 :s) :i)",
        ];
        let original = extended_source(&axioms.join(" "));
        let certificate = captured(&original);
        assert_eq!(certificate.named_disjoint_removable(), 0,
            "new removable forms do not change the named-disjoint diagnostic");
        for removed in 0..axioms.len() {
            let body = axioms.iter().enumerate().filter_map(|(i, a)|
                (i!=removed).then_some(*a)).collect::<Vec<_>>().join(" ");
            let text = extended_source(&body);
            let reduced = certificate.derive(Arc::new(text.clone())).expect(axioms[removed]);
            assert!(conformance::check_user_source(&text).is_ok(), "{text}");
            assert!(reduced.derive(Arc::new(original.clone())).is_some(),
                "restore exact origin span: {}", axioms[removed]);
            assert!(conformance::check_user_source(&original).is_ok());
        }
        let mut reduced = certificate.derive(Arc::new(extended_source("")))
            .expect("all unprotected origin axioms removed");
        for end in 0..=axioms.len() {
            let text = extended_source(&axioms[..end].join(" "));
            reduced = reduced.derive(Arc::new(text.clone())).expect("successive exact restorations");
            assert_eq!(reduced.origin_hash(), certificate.origin_hash());
            assert!(conformance::check_user_source(&text).is_ok());
        }
        let mixed = extended_source("SubClassOf(:C :A) ClassAssertion(:A _:isolated)");
        assert!(certificate.derive(Arc::new(mixed.clone())).is_some(),
            "origin deletions can mix with supported novel named subclass");
        assert!(conformance::cached_source_facts(&mixed).is_none(),
            "derived NEW has no manufactured source facts before public validation");
        assert!(conformance::check_user_source(&mixed).is_ok());

        let duplicate = "ClassAssertion(:A :i)";
        let twice = extended_source(&format!("{duplicate} {duplicate}"));
        let certificate = captured(&twice);
        let once = extended_source(duplicate);
        let reduced = certificate.derive(Arc::new(once.clone())).expect("remove one duplicate");
        assert!(conformance::check_user_source(&once).is_ok());
        assert!(reduced.derive(Arc::new(twice.clone())).is_some());
        let excess = extended_source(&format!("{duplicate} {duplicate} {duplicate}"));
        assert!(reduced.derive(Arc::new(excess.clone())).is_none(), "origin multiplicity bound");
        assert!(conformance::check_user_source(&excess).is_ok(), "valid source falls back");

        let definition_origin = extended_source("DataPropertyRange(:p :D)");
        let certificate = captured(&definition_origin);
        let missing = definition_origin.replace("DatatypeDefinition(:D xsd:string) ", "");
        assert!(certificate.derive(Arc::new(missing.clone())).is_none());
        assert!(conformance::check_user_source(&missing).is_err(),
            "unchanged datatype declaration cannot replace a required definition");
        let no_use = extended_source("");
        let certificate = captured(&no_use);
        let missing = no_use.replace("DatatypeDefinition(:D xsd:string) ", "");
        assert!(certificate.derive(Arc::new(missing.clone())).is_none(),
            "definitions stay fixed even when this particular removal is valid");
        assert!(conformance::check_user_source(&missing).is_ok());

        let link = "ObjectPropertyAssertion(:r _:a _:b)";
        let named = "ObjectPropertyAssertion(:r _:a :one) ObjectPropertyAssertion(:r _:a :two)";
        let forest = extended_source(&format!("{link} {named}"));
        let certificate = captured(&forest);
        let split = extended_source(named);
        assert!(certificate.derive(Arc::new(split.clone())).is_none());
        assert!(conformance::check_user_source(&split).is_err(),
            "splitting loses the only anonymous vertex with permitted named degree");
        let harmless = extended_source(link);
        assert!(certificate.derive(Arc::new(harmless.clone())).is_none(),
            "all anonymous-involving object assertions remain fixed conservatively");
        assert!(conformance::check_user_source(&harmless).is_ok());

        let original = extended_source("ClassAssertion(:A :i)");
        let certificate = captured(&original);
        for unsupported in [
            extended_source("ClassAssertion(:B :i)"),
            extended_source("ObjectPropertyAssertion(:r :i :j)"),
            extended_source("EquivalentClasses(:A :B)"),
            original.replace("<urn:origin-subset:>", "<urn:other:>"),
            original.replace(" Declaration(Class(:C))", ""),
        ] {
            assert!(certificate.derive(Arc::new(unsupported.clone())).is_none());
            assert!(conformance::check_user_source(&unsupported).is_ok(),
                "valid unsupported edits still use full validation: {unsupported}");
        }
        // Simulate a selected hash colliding with a different exact text.
        let source = Arc::new(original.clone());
        conformance::check_user_source(&source).unwrap();
        let mut collision = scan(&source).unwrap();
        let last = collision.statements.len()-1;
        collision.statements[last].hash = collision.statements[0].hash;
        assert!(NamedSubclassCertificate::capture_scanned(source.clone(), &collision).is_none());
        assert!(certificate.derive_scanned(source, &collision).is_none());
    }

    // USER_SOURCE is process-wide. Re-execute exactly this test rather than
    // changing parent environment or racing other unit tests' validators.
    #[test]
    fn public_validator_differential_in_isolated_process() {
        const CHILD: &str = "KM_NAMED_SUBCLASS_VALIDATION_TEST_CHILD";
        if std::env::var(CHILD).as_deref() != Ok("1") {
            let mut command = std::process::Command::new(std::env::current_exe().unwrap());
            for (key, _) in std::env::vars_os() {
                if key.to_string_lossy().starts_with("KM_") { command.env_remove(key); }
            }
            let output = command.args(["--exact",
                    "named_subclass_validation::tests::public_validator_differential_in_isolated_process",
                    "--nocapture", "--test-threads=1"])
                .env(CHILD, "1").env("KM_CACHE_CONFORMANCE", "1")
                .output().expect("launch isolated validator test");
            assert!(output.status.success(), "isolated validator failed:\n{}\n{}",
                String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
            assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed"));
            return;
        }

        let original = source("SubClassOf(:A :B) DisjointClasses(:B :C)");
        assert!(NamedSubclassCertificate::from_success_cache(Arc::new(original.clone())).is_none(),
            "unvalidated source cannot mint provenance");
        let origin = captured(&original);
        let deleted = origin.derive(Arc::new(source(""))).expect("named deletions");
        let added_text = source("SubClassOf(:C :A)");
        let added = deleted.derive(Arc::new(added_text.clone())).expect("named addition after deletion");
        assert_eq!(added.origin_hash(), fingerprint(original.as_bytes()));
        assert!(added.derive(Arc::new(source("DisjointClasses(:B :C)"))).is_some(),
            "exact validated origin disjointness can be restored");
        assert!(added.derive(Arc::new(source("DisjointClasses(:A :C)"))).is_none(),
            "new disjointness must use full validation");
        assert!(conformance::cached_source_facts(&added_text).is_none(),
            "certificate must not publish NEW SourceFacts");
        for duplicate in [
            source("SubClassOf(:A :B) DisjointClasses(:B :C) DisjointClasses(:B :C)"),
            source("SubClassOf(:A :B) DisjointClasses(:B :C) Declaration(Class(:A))")]
        {
            assert!(origin.derive(Arc::new(duplicate.clone())).is_none(),
                "origin disjointness and fixed declarations cannot exceed origin counts");
            assert!(conformance::check_user_source(&duplicate).is_ok(),
                "valid duplicate source must remain an ordinary-validation fallback");
        }


        let accepted = [source("SubClassOf(:B :C)"),
            source("SubClassOf(:A :A) SubClassOf(:B :A)"),
            source("SubClassOf(:A :B) SubClassOf(:A :B)")];
        for text in accepted {
            assert!(origin.derive(Arc::new(text.clone())).is_some(), "{text}");
            assert!(conformance::check_user_source(&text).is_ok(), "{text}");
        }
        let unsupported = [
            (source("SubClassOf(:B :C)").replace(" Declaration(Class(:B))", "\u{000b} Declaration(Class(:B))"), false),
            (source("SubClassOf(:B :C)").replace(" Declaration(Class(:B))", "\u{2003} Declaration(Class(:B))"), false),
            (source("SubClassOf(Annotation(rdfs:label \"x\") :B :C)"), true),
            (source("SubClassOf(:B :Unknown)"), false), (source("SubClassOf(:B <urn:bad%>)"), false),
            (source("SubClassOf(:B _:x)"), false), (source("SubClassOf(:B :C :A)"), false),
            (source("SubClassOf(:B ObjectComplementOf(:C))"), true),
            (source("SubClassOf(:B :C)").replace("Class(:C)", "Datatype(:C)"), false),
            (source("SubClassOf(:B :C)").replace("<urn:admission-test:>", "<urn:other:>"), true),
            (source("SubClassOf(:B :C)").replace("Class(:C)", "Class(<urn:admission-test:C>)"), true)];
        for (text, expected_valid) in unsupported {
            let accepted = origin.derive(Arc::new(text.clone())).is_some();
            let fully_valid = conformance::check_user_source(&text).is_ok();
            assert!(!accepted, "unsupported certificate shape: {text:?}");
            assert_eq!(fully_valid, expected_valid, "public-validator control: {text:?}");
        }

        let annotated = "Prefix(:=<urn:admission-test:>) Ontology(Annotation(rdfs:label \"x\") Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))";
        let certificate = captured(annotated);
        let reordered = annotated.replace("Annotation(rdfs:label \"x\") ", "")
            .replace(" SubClassOf", " Annotation(rdfs:label \"x\") SubClassOf");
        assert!(certificate.derive(Arc::new(reordered.clone())).is_none());
        assert!(conformance::check_user_source(&reordered).is_err());
        let hidden = annotated.replace(" Declaration(Class(:B))",
            " # hidden\rBogus()\nDeclaration(Class(:B))");
        assert!(certificate.derive(Arc::new(hidden.clone())).is_none());
        assert!(conformance::check_user_source(&hidden).is_err());

        let punned = "Prefix(:=<urn:admission-test:>) Prefix(q:=<urn:admission-test:>) Ontology(Declaration(Class(:A)) Declaration(ObjectProperty(:A)) Declaration(Class(q:B)) SubClassOf(:A q:B))";
        let certificate = captured(punned);
        let valid = punned.replace("SubClassOf(:A q:B)", "SubClassOf(q:B :A)");
        assert!(certificate.derive(Arc::new(valid.clone())).is_some());
        assert!(conformance::check_user_source(&valid).is_ok());
        let alias = punned.replace("SubClassOf(:A q:B)", "SubClassOf(:B :A)");
        assert!(certificate.derive(Arc::new(alias.clone())).is_none());
        assert!(conformance::check_user_source(&alias).is_ok(), "valid unsupported alias falls back");
        let invalid = punned.replace("SubClassOf(:A q:B)", "SubClassOf(<urn:bad\\q> :A)");
        assert!(certificate.derive(Arc::new(invalid.clone())).is_none());
        assert!(conformance::check_user_source(&invalid).is_err());

        origin_subset_public_validator_controls();
    }
}
