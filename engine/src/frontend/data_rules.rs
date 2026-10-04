//! Preserve a unary concrete rule as one named-object implication with shared
//! data witnesses. This is a reasoning plan, not a rule-admission certificate.
use std::collections::{BTreeMap, BTreeSet};
use super::syntax::{Axiom, Concept, RuleAtom, RuleDataTerm, RuleTerm};

/// Evaluation of one concrete conjunction for an already chosen data tuple.
/// Deferred bindings remain obligations; absence never makes an atom false.
#[derive(Debug, PartialEq, Eq)]
pub enum BuiltinEvaluation {
    Satisfied(BTreeMap<String, String>),
    Refuted,
    Deferred,
}

pub fn evaluate_builtin_conjunction(
    atoms: &[RuleAtom], initial: &BTreeMap<String, String>,
) -> BuiltinEvaluation {
    fn resolve(term: &RuleDataTerm, bindings: &BTreeMap<String, String>) -> Option<String> {
        match term {
            RuleDataTerm::Literal(literal) => Some(literal.clone()),
            RuleDataTerm::Var(variable) => bindings.get(variable).cloned(),
            RuleDataTerm::Iri(_) => None,
        }
    }
    let mut bindings = initial.clone();
    let mut remaining: Vec<_> = atoms.iter().collect();
    loop {
        let mut pending = Vec::new();
        let mut progress = false;
        for atom in remaining {
            let RuleAtom::Builtin(iri, args) = atom else {
                pending.push(atom);
                continue;
            };
            if let Some(values) = args.iter().map(|term| resolve(term, &bindings)).collect::<Option<Vec<_>>>() {
                let values: Vec<_> = values.iter().map(String::as_str).collect();
                match super::datatypes::swrl_numeric_relation(iri, &values) {
                    Some(false) => return BuiltinEvaluation::Refuted,
                    Some(true) => { progress = true; continue; }
                    None => {},
                }
            } else if let Some((RuleDataTerm::Var(output), operands)) = args.split_first() {
                if !bindings.contains_key(output) {
                    if let Some(values) = operands.iter().map(|term| resolve(term, &bindings)).collect::<Option<Vec<_>>>() {
                        let values: Vec<_> = values.iter().map(String::as_str).collect();
                        if super::datatypes::swrl_math_has_non_numeric_argument(iri, &values) {
                            return BuiltinEvaluation::Refuted;
                        }
                        if let Some(value) = super::datatypes::swrl_numeric_output(iri, &values) {
                            bindings.insert(output.clone(), value);
                            progress = true;
                            continue;
                        }
                    }
                }
            }
            pending.push(atom);
        }
        if pending.is_empty() { return BuiltinEvaluation::Satisfied(bindings); }
        if !progress { return BuiltinEvaluation::Deferred; }
        remaining = pending;
    }
}

/// Ground one concrete rule over a certified selected value set. The caller
/// must prove that restricting data extensions to this set preserves models.
/// A resource limit or unresolved tuple defers the whole rule atomically.
pub fn finite_data_rule_plan(
    rule: &Axiom, selected: &[String], tuple_limit: usize,
) -> Option<Vec<Axiom>> {
    let Axiom::DataRule(body, head) = rule else { return None; };
    if tuple_limit == 0 { return None; }
    if selected.iter().any(|value| !exact_rule_literal(value)) { return None; }
    if head.iter().any(|atom| matches!(atom, RuleAtom::Data(..) | RuleAtom::Builtin(..) | RuleAtom::DataRange(..))) { return None; }
    let mut variables = BTreeSet::new();
    let mut object_variables = BTreeSet::new();
    for atom in body.iter().chain(head) {
        let terms: Vec<_> = match atom {
            RuleAtom::Class(_, term) | RuleAtom::Data(_, term, _) => vec![term],
            RuleAtom::Role(_, a, b) | RuleAtom::Same(a, b) | RuleAtom::Diff(a, b) => vec![a, b],
            _ => vec![],
        };
        for term in terms { if let RuleTerm::Var(name) = term { object_variables.insert(name.clone()); } }
    }
    for atom in body {
        match atom {
            RuleAtom::Data(_, _, RuleDataTerm::Var(name)) => { variables.insert(name.clone()); }
            RuleAtom::Data(_, _, RuleDataTerm::Literal(value)) if exact_rule_literal(value) => {},
            RuleAtom::Data(..) | RuleAtom::DataRange(..) => return None,
            _ => {},
        }
    }
    if variables.iter().any(|name| object_variables.contains(name)) { return None; }
    for atom in body {
        if let RuleAtom::Builtin(_, args) = atom {
            if args.iter().any(|term| matches!(term, RuleDataTerm::Var(name) if object_variables.contains(name))) { return None; }
        }
    }
    let variables: Vec<_> = variables.into_iter().collect();
    let mut tuples = vec![BTreeMap::new()];
    for variable in variables {
        let size = tuples.len().checked_mul(selected.len())?;
        if size > tuple_limit { return None; }
        let mut next = Vec::with_capacity(size);
        for tuple in tuples {
            for value in selected {
                let mut tuple = tuple.clone();
                tuple.insert(variable.clone(), value.clone());
                next.push(tuple);
            }
        }
        tuples = next;
    }
    let builtins: Vec<_> = body.iter().filter(|atom| matches!(atom, RuleAtom::Builtin(..))).cloned().collect();
    let mut grounded = Vec::new();
    for tuple in tuples {
        let bindings = match evaluate_builtin_conjunction(&builtins, &tuple) {
            BuiltinEvaluation::Refuted => continue,
            BuiltinEvaluation::Deferred => return None,
            BuiltinEvaluation::Satisfied(bindings) => bindings,
        };
        let mut translated = Vec::new();
        for atom in body {
            match atom {
                RuleAtom::Builtin(..) => {},
                RuleAtom::Data(property, subject, RuleDataTerm::Var(name)) =>
                    translated.push(RuleAtom::Data(property.clone(), subject.clone(), RuleDataTerm::Literal(bindings.get(name)?.clone()))),
                _ => translated.push(atom.clone()),
            }
        }
        grounded.push(constant_data_rule_plan(&Axiom::DataRule(translated, head.clone()))?);
    }
    Some(grounded)
}

pub(super) fn exact_rule_literal(literal: &str) -> bool {
    if super::datatypes::exact_ieee_literal(literal) { return true; }
    if super::datatypes::exact_datetime_literal(literal) { return true; }
    super::datatypes::exact_literal_value_equal(literal, literal) == Some(true)
        || super::datatypes::swrl_numeric_relation(
            "http://www.w3.org/2003/11/swrlb#equal", &[literal, literal],
        ) == Some(true)
}

#[derive(Default)]
pub(super) struct IntegerRuleScan<'a> {
    ranges: Vec<(&'a str, &'a str)>,
    assertions: Vec<(&'a str, &'a str, String)>,
    invalid_assertion: bool,
}
impl<'a> IntegerRuleScan<'a> {
    pub(super) fn lower_finite_rules(
        &self, ontology: &mut super::syntax::Ontology,
        registry: &mut super::iri::IriRegistry, certificate: &super::finite_data_rules::Scan,
        source_count: u64, observer_count: u64,
    ) -> u64 {
        if self.invalid_assertion || !certificate.certified() { return 0; }
        let concrete: Vec<_> = ontology.datatype_rules().collect();
        if concrete.is_empty() || ontology.rules().count() as u64 + concrete.len() as u64
            + observer_count != source_count { return 0; }
        let mut values = certificate.values.clone();
        values.sort();
        values.dedup();
        let mut replacements = Vec::new();
        for rule in &concrete {
            let Some(plan) = finite_data_rule_plan(rule, &values, 100_000) else { return 0; };
            replacements.extend(plan);
        }
        let mut occupied: BTreeSet<_> = registry.owned_names().into_iter().collect();
        let mut aliases = std::collections::HashMap::<Concept, String>::new();
        let mut definitions = Vec::new();
        let mut index = 0_u64;
        for rule in &mut replacements {
            let Axiom::Rule(body, head) = rule else { return 0; };
            for atom in body.iter_mut().chain(head.iter_mut()) {
                let RuleAtom::Class(concept, _) = atom else { continue; };
                if matches!(concept, Concept::Name(_)) { continue; }
                let name = if let Some(name) = aliases.get(concept) { name.clone() } else {
                    let name = loop {
                        let name = format!("__rule_finite_data_{index}");
                        index += 1;
                        if occupied.insert(name.clone()) { break name; }
                    };
                    aliases.insert(concept.clone(), name.clone());
                    definitions.push(Axiom::EquivalentClasses(Concept::Name(name.clone()), concept.clone()));
                    name
                };
                *concept = Concept::Name(name);
            }
        }
        for (property, individual, literal) in &self.assertions {
            if !exact_rule_literal(literal) { return 0; }
            definitions.push(Axiom::ConceptAssertion(
                Concept::Exists(super::syntax::Role::Name(registry.short(property)),
                    Box::new(Concept::Name(format!("__dt__val__{literal}")))),
                registry.short(individual),
            ));
        }
        let translated = concrete.len() as u64;
        ontology.retain_axioms(|axiom| !matches!(axiom, Axiom::DataRule(..)));
        for axiom in definitions.into_iter().chain(replacements) { ontology.add(axiom); }
        translated
    }

    /// Atomically retain object joins and define private classes for constant
    /// data atoms. The resulting rules still execute on named object bindings.
    pub(super) fn lower_constant_rules(
        &self, ontology: &mut super::syntax::Ontology,
        registry: &mut super::iri::IriRegistry, source_count: u64, observer_count: u64,
    ) -> u64 {
        if self.invalid_assertion { return 0; }
        let concrete: Vec<_> = ontology.datatype_rules().collect();
        if concrete.is_empty() || ontology.rules().count() as u64 + concrete.len() as u64
            + observer_count != source_count { return 0; }
        let mut occupied: BTreeSet<_> = registry.owned_names().into_iter().collect();
        let mut definitions = Vec::new();
        let mut replacements = Vec::new();
        let mut index = 0_u64;
        for rule in &concrete {
            let Some(Axiom::Rule(mut body, mut head)) = constant_data_rule_plan(rule) else { return 0; };
            for atom in body.iter_mut().chain(head.iter_mut()) {
                let RuleAtom::Class(concept, _) = atom else { continue; };
                if matches!(concept, Concept::Name(_)) { continue; }
                let name = loop {
                    let name = format!("__rule_data_const_{index}");
                    index += 1;
                    if occupied.insert(name.clone()) { break name; }
                };
                definitions.push(Axiom::EquivalentClasses(Concept::Name(name.clone()), concept.clone()));
                *concept = Concept::Name(name);
            }
            replacements.push(Axiom::Rule(body, head));
        }
        for (property, individual, literal) in &self.assertions {
            if !exact_rule_literal(literal) { return 0; }
            definitions.push(Axiom::ConceptAssertion(
                Concept::Exists(super::syntax::Role::Name(registry.short(property)),
                    Box::new(Concept::Name(format!("__dt__val__{literal}")))),
                registry.short(individual),
            ));
        }
        let translated = concrete.len() as u64;
        ontology.retain_axioms(|axiom| !matches!(axiom, Axiom::DataRule(..)));
        for axiom in definitions.into_iter().chain(replacements) { ontology.add(axiom); }
        translated
    }
    pub(super) fn observe(&mut self, node: &super::sexpr::Node<'a>) {
        if let super::sexpr::Node::List("DataPropertyAssertion", args) = node {
            let args = super::parse::strip_annotations(args);
            let parsed = (|| {
                let property = args.first()?.as_atom()?;
                let individual = args.get(1)?.as_atom()?;
                let (literal, used) = super::parse::glue_literal(&args, 2)?;
                if args.len() != 2 + used { return None }
                Some((property, individual, literal))
            })();
            if let Some(assertion) = parsed { self.assertions.push(assertion); }
            else { self.invalid_assertion = true; }
            return;
        }
        let super::sexpr::Node::List("DataPropertyRange", args) = node else { return };
        let args = super::parse::strip_annotations(args);
        let [property, range] = args.as_slice() else { return };
        let (Some(property), Some(range)) = (property.as_atom(), range.as_atom()) else { return };
        if super::datatypes::integer_datatype_bounds(range).is_some() {
            self.ranges.push((property, range));
        }
    }
    pub(super) fn lower(
        &self, ontology: &mut super::syntax::Ontology, registry: &mut super::iri::IriRegistry,
        names: &[&str], source_count: u64, observer_count: u64,
    ) -> u64 {
        if source_count <= observer_count || self.invalid_assertion
            || ontology.datatype_rules().next().is_none() { return 0 }
        let rules: Vec<_> = ontology.rules().chain(ontology.datatype_rules()).collect();
        if rules.len() as u64 + observer_count != source_count { return 0 }
        let ranges: BTreeMap<_, _> = self.ranges.iter()
            .map(|(property, range)| (registry.short(property), (*range).to_string())).collect();
        let names: Vec<_> = names.iter().map(|name| registry.short(name)).collect();
        let mut inclusions = Vec::new();
        for rule in rules {
            let plan = match rule {
                Axiom::DataRule(..) => unary_plan(rule),
                Axiom::Rule(body, head) => unary_plan(&Axiom::DataRule(body.clone(), head.clone())),
                _ => None,
            };
            let Some(plan) = plan else { return 0 };
            let Some(lowered) = plan.guarded_integer_inclusions(&names, &ranges) else { return 0 };
            inclusions.extend(lowered);
        }
        for (property, individual, literal) in &self.assertions {
            let property = registry.short(property);
            if !exact_rule_literal(literal) {
                return 0;
            }
            // A positive data assertion is an existential with a singleton
            // value filler, not a fresh object individual for the literal.
            inclusions.push(Axiom::ConceptAssertion(
                Concept::Exists(super::syntax::Role::Name(property),
                    Box::new(Concept::Name(format!("__dt__val__{literal}")))),
                registry.short(individual),
            ));
        }
        ontology.retain_axioms(|axiom| !matches!(axiom, Axiom::Rule(..) | Axiom::DataRule(..)));
        for inclusion in inclusions { ontology.add(inclusion); }
        source_count
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueTest {
    Range(String),
    Comparison { operator: String, literal: String, variable_first: bool },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueWitness {
    pub property: String,
    pub variable: String,
    pub tests: Vec<ValueTest>,
}
/// An exact set of mathematical integers: inclusive bounds minus finitely
/// many excluded points. Unbounded sides extend beyond machine integers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerDomain {
    pub min: Option<i128>,
    pub max: Option<i128>,
    pub excluded: BTreeSet<i128>,
}
impl IntegerDomain {
    /// Encode the exact shared witness domain using the frontend's existing
    /// datatype concepts. This does not admit a rule into production.
    pub fn datatype_filler(&self) -> Option<Concept> {
        use super::syntax::mk_and;
        if self.is_empty() { return Some(Concept::Bottom); }
        let literal = |value: i128| {
            let token = format!("\"{value}\"^^xsd:integer");
            (super::datatypes::exact_swrl_integer(&token) == Some(value)).then_some(token)
        };
        let mut restriction = String::from("DatatypeRestriction(xsd:integer");
        if let Some(min) = self.min {
            restriction.push_str(&format!(" xsd:minInclusive {}", literal(min)?));
        }
        if let Some(max) = self.max {
            restriction.push_str(&format!(" xsd:maxInclusive {}", literal(max)?));
        }
        restriction.push(')');
        let base = if self.min.is_none() && self.max.is_none() {
            Concept::Name("__dt__xsd:integer".into())
        } else { Concept::Name(format!("__dt__c__{restriction}")) };
        let mut conjuncts = vec![base];
        for &excluded in &self.excluded {
            if self.min.is_some_and(|min| excluded < min)
                || self.max.is_some_and(|max| excluded > max) { continue; }
            conjuncts.push(Concept::Not(Box::new(Concept::Name(
                format!("__dt__val__{}", literal(excluded)?),
            ))));
        }
        Some(mk_and(conjuncts))
    }
    fn intersect(&mut self, min: Option<i128>, max: Option<i128>) {
        if let Some(min) = min { self.min = Some(self.min.map_or(min, |old| old.max(min))); }
        if let Some(max) = max { self.max = Some(self.max.map_or(max, |old| old.min(max))); }
    }
    pub fn is_empty(&self) -> bool {
        !self.has_at_least_distinct_values(1)
    }
    /// Decide finite cardinality obligations without constructing witnesses.
    /// The comparison remains exact even when the interval has 2^128 values.
    pub fn has_at_least_distinct_values(&self, required: u64) -> bool {
        if required == 0 { return true; }
        let (Some(min), Some(max)) = (self.min, self.max) else { return true };
        if min > max { return false; }
        // Flip the sign bit to preserve signed order in an unsigned key.
        let ordered = |value: i128| (value as u128) ^ (1u128 << 127);
        let span = ordered(max) - ordered(min);
        let excluded = self.excluded.range(min..=max).count() as u128;
        let needed = u128::from(required) + excluded;
        // width = span + 1. Subtract on the small required side, so the full
        // i128 interval needs no overflowing width or arbitrary-size integer.
        span >= needed - 1
    }
    /// Exact common value space for constraints on the same data witness.
    pub fn intersection(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.intersect(other.min, other.max);
        result.excluded.extend(other.excluded.iter().copied());
        result
    }
}
impl ValueWitness {
    /// Keep every comparison on this variable inside one existential filler.
    pub fn integer_filler(&self, property_range: &str) -> Option<Concept> {
        self.integer_domain(property_range)?.datatype_filler()
    }
    /// Solve all tests over a property whose values are known to lie in an
    /// integer datatype. No assertion list is used. Unsupported ranges or
    /// unrepresentable strict bounds defer rather than shrink the value space.
    pub fn integer_domain(&self, property_range: &str) -> Option<IntegerDomain> {
        let (min, max) = super::datatypes::integer_datatype_bounds(property_range)?;
        let mut domain = IntegerDomain { min, max, excluded: BTreeSet::new() };
        for test in &self.tests {
            match test {
                ValueTest::Range(range) => {
                    let (min, max) = super::datatypes::integer_datatype_bounds(range)?;
                    domain.intersect(min, max);
                }
                ValueTest::Comparison { operator, literal, variable_first } => {
                    let operator = if *variable_first { operator.as_str() } else {
                        match operator.as_str() {
                            "lessThan" => "greaterThan", "lessThanOrEqual" => "greaterThanOrEqual",
                            "greaterThan" => "lessThan", "greaterThanOrEqual" => "lessThanOrEqual",
                            other => other,
                        }
                    };
                    use super::datatypes::IntegerPredicate;
                    match super::datatypes::swrl_integer_predicate(operator, literal)? {
                        IntegerPredicate::Minimum(bound) => domain.intersect(Some(bound), None),
                        IntegerPredicate::Maximum(bound) => domain.intersect(None, Some(bound)),
                        IntegerPredicate::Equal(bound) => domain.intersect(Some(bound), Some(bound)),
                        IntegerPredicate::NotEqual(bound) => { domain.excluded.insert(bound); },
                        IntegerPredicate::Always => {},
                        IntegerPredicate::Never => domain.intersect(Some(1), Some(0)),
                    }
                }
            }
        }
        Some(domain)
    }
    /// Evaluate the comparison portion for one candidate literal. Range tests
    /// still require the concrete range backend; unknown is never false.
    /// Callers must enumerate/solve model witnesses, not only asserted values.
    pub fn compare_literal(&self, value: &str) -> Option<bool> {
        let mut result = true;
        for test in &self.tests {
            let ValueTest::Comparison { operator, literal, variable_first } = test else {
                return None;
            };
            let args = if *variable_first { [value, literal.as_str()] }
                else { [literal.as_str(), value] };
            result &= super::datatypes::swrl_numeric_relation(
                &format!("http://www.w3.org/2003/11/swrlb#{operator}"), &args)?;
        }
        Some(result)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnaryDataRule {
    pub object_variable: String,
    pub class_conditions: Vec<Concept>,
    pub constant_values: Vec<(String, String)>,
    pub witnesses: Vec<ValueWitness>,
    pub conclusions: Vec<Concept>,
}

/// Preserve object-variable joins while translating constant data atoms into
/// exact singleton existential class atoms. Complex class atoms still need
/// definitional names before they can enter the object-only rule worker.
/// Variable data bindings and built-ins remain concrete-domain obligations.
pub fn constant_data_rule_plan(axiom: &Axiom) -> Option<Axiom> {
    let Axiom::DataRule(body, head) = axiom else { return None };
    let translate = |atom: &RuleAtom| -> Option<RuleAtom> {
        match atom {
            RuleAtom::Data(property, subject, RuleDataTerm::Literal(literal))
                if exact_rule_literal(literal) => Some(RuleAtom::Class(
                    Concept::Exists(super::syntax::Role::Name(property.clone()),
                        Box::new(Concept::Name(format!("__dt__val__{literal}")))),
                    subject.clone(),
                )),
            RuleAtom::Class(..) | RuleAtom::Role(..)
                | RuleAtom::Same(..) | RuleAtom::Diff(..) => Some(atom.clone()),
            _ => None,
        }
    };
    Some(Axiom::Rule(
        body.iter().map(&translate).collect::<Option<Vec<_>>>()?,
        head.iter().map(&translate).collect::<Option<Vec<_>>>()?,
    ))
}

/// Complete rule coverage with an empty named-object domain. Every rule must
/// have an object variable in its body; explicit object constants defer even
/// when a source-name observer did not collect them. This is independent of
/// concrete arithmetic because there can be no DL-safe object binding.
pub(super) fn empty_named_domain_rules(
    ontology: &super::syntax::Ontology, names: &[&str], source_count: u64,
) -> u64 {
    if !names.is_empty() || source_count == 0 { return 0 }
    fn variable(term: &RuleTerm) -> bool { matches!(term, RuleTerm::Var(_)) }
    fn object_terms(atom: &RuleAtom) -> Vec<&RuleTerm> {
        match atom {
            RuleAtom::Class(_, t) | RuleAtom::Data(_, t, _) => vec![t],
            RuleAtom::Role(_, a, b) | RuleAtom::Same(a, b) | RuleAtom::Diff(a, b) => vec![a, b],
            RuleAtom::Builtin(..) | RuleAtom::DataRange(..) => Vec::new(),
        }
    }
    let rules: Vec<_> = ontology.rules().chain(ontology.datatype_rules()).collect();
    if rules.len() as u64 != source_count { return 0 }
    for rule in rules {
        let (Axiom::Rule(body, head) | Axiom::DataRule(body, head)) = rule else { return 0 };
        if !body.iter().any(|atom| object_terms(atom).iter().any(|t| variable(t)))
            || !body.iter().chain(head).all(|atom| object_terms(atom).iter().all(|t| variable(t))) {
            return 0;
        }
    }
    source_count
}

/// Extract a complete unary data-rule obligation. A witness is shared by all
/// tests on its variable; separate existential tests would lose conjunction.
/// Cross-property joins and arithmetic output variables require the general
/// concrete backend and return `None`. The original rule remains untouched.
pub fn unary_plan(axiom: &Axiom) -> Option<UnaryDataRule> {
    let Axiom::DataRule(body, head) = axiom else { return None };
    let object = match head.first()? {
        RuleAtom::Class(Concept::Name(_), RuleTerm::Var(object))
        | RuleAtom::Data(_, RuleTerm::Var(object), RuleDataTerm::Literal(_)) => object,
        _ => return None,
    };
    let mut plan = UnaryDataRule {
        object_variable: object.clone(), class_conditions: Vec::new(),
        constant_values: Vec::new(), witnesses: Vec::new(), conclusions: Vec::new(),
    };
    for atom in head {
        match atom {
            RuleAtom::Class(concept @ Concept::Name(_), RuleTerm::Var(variable))
                if variable == object => plan.conclusions.push(concept.clone()),
            RuleAtom::Data(property, RuleTerm::Var(variable), RuleDataTerm::Literal(literal))
                if variable == object && exact_rule_literal(literal) => {
                // A constant data head requires this exact singleton witness;
                // it never binds a literal as an object individual.
                plan.conclusions.push(Concept::Exists(super::syntax::Role::Name(property.clone()),
                    Box::new(Concept::Name(format!("__dt__val__{literal}")))));
            }
            _ => return None,
        }
    }
    let mut witnesses: BTreeMap<String, ValueWitness> = BTreeMap::new();
    for atom in body {
        match atom {
            RuleAtom::Class(concept @ Concept::Name(_), RuleTerm::Var(variable)) if variable == object =>
                plan.class_conditions.push(concept.clone()),
            RuleAtom::Role(property, RuleTerm::Var(left), RuleTerm::Var(right))
                if left == object && right == object =>
                plan.class_conditions.push(Concept::HasSelf(super::syntax::Role::Name(property.clone()))),
            RuleAtom::Data(property, RuleTerm::Var(variable), value) if variable == object => match value {
                RuleDataTerm::Literal(literal) => plan.constant_values.push((property.clone(), literal.clone())),
                RuleDataTerm::Var(data_variable) if data_variable != object => {
                    let witness = witnesses.entry(data_variable.clone()).or_insert_with(|| ValueWitness {
                        property: property.clone(), variable: data_variable.clone(), tests: Vec::new(),
                    });
                    if witness.property != *property { return None; }
                }
                _ => return None,
            },
            RuleAtom::Builtin(..) | RuleAtom::DataRange(..) => {},
            _ => return None,
        }
    }
    for atom in body {
        match atom {
            RuleAtom::DataRange(range, RuleDataTerm::Var(variable)) =>
                witnesses.get_mut(variable)?.tests.push(ValueTest::Range(range.clone())),
            RuleAtom::DataRange(..) => return None,
            RuleAtom::Builtin(iri, args) => {
                let iri = if iri.starts_with('<') { iri.strip_prefix('<')?.strip_suffix('>')? } else { iri };
                let operator = iri.strip_prefix("http://www.w3.org/2003/11/swrlb#")?;
                if !matches!(operator, "equal" | "notEqual" | "lessThan" | "lessThanOrEqual" | "greaterThan" | "greaterThanOrEqual") {
                    return None;
                }
                let (variable, literal, variable_first) = match args.as_slice() {
                    [RuleDataTerm::Var(variable), RuleDataTerm::Literal(literal)] => (variable, literal, true),
                    [RuleDataTerm::Literal(literal), RuleDataTerm::Var(variable)] => (variable, literal, false),
                    _ => return None,
                };
                witnesses.get_mut(variable)?.tests.push(ValueTest::Comparison {
                    operator: operator.to_string(), literal: literal.clone(), variable_first,
                });
            }
            _ => {},
        }
    }
    plan.witnesses = witnesses.into_values().collect();
    Some(plan)
}

impl UnaryDataRule {
    /// Construct equivalent nominal-guarded inclusions for integer witnesses.
    /// Callers must supply source individual names and proved property ranges.
    /// This planning API does not remove or admit the original source rule.
    pub fn guarded_integer_inclusions(
        &self, source_individuals: &[String], property_ranges: &BTreeMap<String, String>,
    ) -> Option<Vec<Axiom>> {
        use super::syntax::{mk_and, mk_or, Role};
        let guard = mk_or(source_individuals.iter().cloned().map(Concept::Nominal));
        let mut conditions = vec![guard];
        conditions.extend(self.class_conditions.iter().cloned());
        for (property, literal) in &self.constant_values {
            if !exact_rule_literal(literal) {
                return None;
            }
            conditions.push(Concept::Exists(Role::Name(property.clone()),
                Box::new(Concept::Name(format!("__dt__val__{literal}")))));
        }
        for witness in &self.witnesses {
            let range = property_ranges.get(&witness.property)?;
            conditions.push(Concept::Exists(Role::Name(witness.property.clone()),
                Box::new(witness.integer_filler(range)?)));
        }
        let body = mk_and(conditions);
        Some(self.conclusions.iter().cloned()
            .map(|head| Axiom::SubClassOf(body.clone(), head)).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_10906_rules_have_complete_constant_data_translation_plans() {
        let source = include_str!("../../tests/fixtures/multi_object_constant_data_rules.ofn");
        let mut registry = super::super::iri::IriRegistry::new();
        let ontology = super::super::parse::parse_axioms(&mut registry, source).unwrap();
        assert_eq!(ontology.rules().count(), 10);
        assert_eq!(ontology.datatype_rules().count(), 1);
        for rule in ontology.datatype_rules() {
            let Axiom::DataRule(original_body, original_head) = rule else { unreachable!() };
            let Some(Axiom::Rule(body, head)) = constant_data_rule_plan(rule) else { panic!("10906 rule not represented") };
            assert_eq!(body.len(), original_body.len());
            assert_eq!(&head, original_head);
            assert!(body.iter().all(|atom| !matches!(atom,
                RuleAtom::Data(..) | RuleAtom::Builtin(..) | RuleAtom::DataRange(..))));
            assert!(body.iter().zip(original_body).all(|(lowered, original)|
                matches!(original, RuleAtom::Data(..)) || lowered == original));
        }
    }

    #[test]
    fn constant_data_plan_preserves_multiple_object_bindings_and_literal_identity() {
        let x = RuleTerm::Var("x".into());
        let y = RuleTerm::Var("y".into());
        let edge = RuleAtom::Role("partOf".into(), x.clone(), y.clone());
        let data = |literal: &str| RuleAtom::Data("default".into(), x.clone(),
            RuleDataTerm::Literal(literal.into()));
        let head = RuleAtom::Role("min0".into(), y, x.clone());
        let original = Axiom::DataRule(vec![edge.clone(), data("\"NULL\"^^xsd:string")], vec![head.clone()]);
        let Some(Axiom::Rule(body, conclusions)) = constant_data_rule_plan(&original) else { panic!("exact constant atom") };
        assert_eq!(body[0], edge);
        assert_eq!(conclusions, vec![head]);
        assert_eq!(body[1], RuleAtom::Class(Concept::Exists(
            super::super::syntax::Role::Name("default".into()),
            Box::new(Concept::Name("__dt__val__\"NULL\"^^xsd:string".into()))), x.clone()));
        let output = Axiom::DataRule(vec![edge], vec![data("\"NULL\"^^xsd:string")]);
        assert!(constant_data_rule_plan(&output).is_some());
        for unsupported in [
            RuleAtom::Data("default".into(), x.clone(), RuleDataTerm::Var("v".into())),
            data("\"NULL\"^^rdfs:Literal"),
            RuleAtom::Builtin("unknown".into(), Vec::new()),
        ] {
            assert!(constant_data_rule_plan(&Axiom::DataRule(vec![unsupported], Vec::new())).is_none());
        }
    }

    #[test]
    fn source_integer_lowering_is_atomic_when_any_rule_is_unrepresented() {
        let rule = "DLSafeRule(Body(ClassAtom(<Person> Variable(<p>)) DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<v>) \"17\"^^xsd:integer)) Head(ClassAtom(<Adult> Variable(<p>))))";
        for extra in ["", "DLSafeRule(Body(ClassAtom(<Person> Variable(<p>))) Head(DataPropertyAtom(<age> Variable(<p>) Variable(<unbound>))))"] {
            let text = format!("Ontology(DataPropertyRange(<age> xsd:int) ClassAssertion(<Person> <i>) {rule} {extra})");
            let node = super::super::sexpr::Parser::new(&text).parse().unwrap();
            let super::super::sexpr::Node::List(_, children) = &node else { panic!("ontology") };
            let mut scan = IntegerRuleScan::default();
            for child in children { scan.observe(child); }
            let mut registry = super::super::iri::IriRegistry::new();
            let mut ontology = super::super::parse::parse_axioms(&mut registry, &text).unwrap();
            let count = if extra.is_empty() { 1 } else { 2 };
            let lowered = scan.lower(&mut ontology, &mut registry, &["<i>"], count, 0);
            if extra.is_empty() {
                assert_eq!(lowered, 1);
                assert_eq!(ontology.datatype_rules().count(), 0);
            } else {
                assert_eq!(lowered, 0);
                assert_eq!(ontology.datatype_rules().count(), 2);
            }
        }
    }

    #[test]
    fn integer_witness_lowering_has_the_expected_datatype_membership() {
        use super::super::clauses::{Atom, Term};
        let p = plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<v>) \"17\"^^xsd:long)").unwrap();
        let Concept::Name(filler) = p.witnesses[0].integer_filler("xsd:integer").unwrap() else { panic!("interval filler") };
        let names = [filler.clone(), "__dt__val__\"18\"^^xsd:int".into(), "__dt__val__\"17\"^^xsd:int".into()].into();
        let clauses = super::super::datatypes::datatype_relation_clauses(&names, 100);
        // The existing datatype oracle must derive membership for 18 and
        // disjointness for 17, rather than merely accept a generated string.
        let atom = |name: &str| Atom::Concept(name.into(), Term::Var("x".into()));
        assert!(clauses.iter().any(|clause|
            clause.body == vec![atom("__dt__val__\"18\"^^xsd:int")]
                && clause.head == vec![atom(&filler)]));
        assert!(clauses.iter().any(|clause| clause.head.is_empty()
            && clause.body.contains(&atom("__dt__val__\"17\"^^xsd:int"))
            && clause.body.contains(&atom(&filler))));
    }

    #[test]
    fn empty_named_domain_and_query_observers_cover_disjoint_source_rules() {
        let result = super::super::ofn_to_clauses(
            "Ontology(Declaration(Class(<urn:test:A>)) DLSafeRule(Body(ClassAtom(<urn:test:A> Variable(<urn:test:x>))) Head(DataPropertyAtom(<urn:test:p> Variable(<urn:test:x>) \"a\"))) DLSafeRule(Body(ClassAtom(<urn:test:A> Variable(<urn:test:x>))) Head(BuiltInAtom(<http://sqwrl.stanford.edu/ontologies/built-ins/3.4/sqwrl.owl#select> Variable(<urn:test:x>)))))",
        ).unwrap();
        assert_eq!(result.profile.source.rule_axioms, 2);
        assert_eq!(result.profile.vacuous_named_domain_rules, 1);
        assert_eq!(result.profile.source.unsupported_rule_axioms, 0);
        assert!(result.rules.is_empty());
    }

    #[test]
    fn empty_named_domain_elides_object_guarded_concrete_rules() {
        let result = super::super::ofn_to_clauses(
            "Ontology(Declaration(Class(<urn:test:A>)) DLSafeRule(Body(ClassAtom(<urn:test:A> Variable(<urn:test:x>))) Head(DataPropertyAtom(<urn:test:p> Variable(<urn:test:x>) \"a\"))))",
        ).unwrap();
        assert_eq!(result.profile.vacuous_named_domain_rules, 1);
        assert_eq!(result.profile.source.rule_axioms, 1);
        assert_eq!(result.profile.source.unsupported_rule_axioms, 0);
        assert!(result.rules.is_empty());
    }

    #[test]
    fn empty_domain_certificate_defers_constants_and_data_only_bodies() {
        for rule in [
            "DLSafeRule(Body(ClassAtom(<urn:test:A> <urn:test:i>)) Head(DataPropertyAtom(<urn:test:p> <urn:test:i> \"a\")))",
            "DLSafeRule(Body(BuiltInAtom(<http://www.w3.org/2003/11/swrlb#equal> Variable(<urn:test:v>) \"1\"^^xsd:integer)) Head(ClassAtom(<urn:test:A> Variable(<urn:test:x>))))",
        ] {
            let mut registry = super::super::iri::IriRegistry::new();
            let ontology = super::super::parse::parse_axioms(&mut registry,
                &format!("Ontology({rule})")).unwrap();
            assert_eq!(empty_named_domain_rules(&ontology, &[], 1), 0);
        }
    }

    #[test]
    fn named_assertions_or_imports_prevent_vacuous_rule_admission() {
        let source = "Ontology(ClassAssertion(<urn:test:A> <urn:test:i>) DLSafeRule(Body(ClassAtom(<urn:test:A> Variable(<urn:test:x>))) Head(DataPropertyAtom(<urn:test:p> Variable(<urn:test:x>) \"a\"))))";
        let mut registry = super::super::iri::IriRegistry::new();
        let ontology = super::super::parse::parse_axioms(&mut registry, source).unwrap();
        assert_eq!(empty_named_domain_rules(&ontology, &["<urn:test:i>"], 1), 0);
        let result = super::super::ofn_to_clauses(source).unwrap();
        assert_eq!(result.profile.vacuous_named_domain_rules, 0);
        assert_eq!(result.profile.normalized_unary_rules, 1);
        assert!(super::super::ofn_to_clauses(
            "Ontology(Import(<http://example.org/ontology>) DLSafeRule(Body(ClassAtom(<urn:test:A> Variable(<urn:test:x>))) Head(DataPropertyAtom(<urn:test:p> Variable(<urn:test:x>) \"a\"))))"
        ).is_err());
    }
    use super::super::{iri::IriRegistry, parse::parse_axioms};
    fn plan(body: &str) -> Option<UnaryDataRule> {
        let source = format!("Ontology(DLSafeRule(Body({body}) Head(ClassAtom(<Adult> Variable(<p>)))))");
        let ontology = parse_axioms(&mut IriRegistry::new(), &source).unwrap();
        let result = unary_plan(ontology.datatype_rules().next().unwrap());
        result
    }
    #[test]
    fn shared_witness_keeps_every_comparison_and_operand_direction() {
        let p = plan("ClassAtom(<Person> Variable(<p>)) DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<v>) \"17\"^^xsd:long) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> \"21\"^^xsd:integer Variable(<v>))").unwrap();
        assert_eq!(p.class_conditions.len(), 1);
        assert_eq!(p.witnesses.len(), 1);
        assert_eq!(p.witnesses[0].tests.len(), 2);
        assert!(matches!(&p.witnesses[0].tests[1], ValueTest::Comparison { variable_first: false, .. }));
        assert_eq!(p.witnesses[0].compare_literal("\"18\"^^xsd:int"), Some(true));
        assert_eq!(p.witnesses[0].compare_literal("\"21\"^^xsd:int"), Some(false));
        assert_eq!(p.witnesses[0].compare_literal("\"16\"^^xsd:int"), Some(false));
        let domain = p.witnesses[0].integer_domain("xsd:int").unwrap();
        assert_eq!((domain.min, domain.max), (Some(18), Some(20)));
        assert!(!domain.is_empty());
    }
    #[test]
    fn cross_property_join_is_not_split_into_independent_witnesses() {
        assert!(plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) DataPropertyAtom(<other> Variable(<p>) Variable(<v>))").is_none());
        assert!(plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://example.org/greaterThan> Variable(<v>) \"17\"^^xsd:integer)").is_none());
        assert!(plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#add> Variable(<output>) Variable(<v>) \"1\"^^xsd:integer)").is_none());
    }
    #[test]
    fn integer_domain_keeps_unasserted_values_and_finite_exclusions() {
        let p = plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<v>) \"17\"^^xsd:long)").unwrap();
        let domain = p.witnesses[0].integer_domain("xsd:integer").unwrap();
        assert_eq!((domain.min, domain.max), (Some(18), None));
        assert!(!domain.is_empty());
        let mut finite = IntegerDomain { min: Some(18), max: Some(19), excluded: [18, 19].into() };
        assert!(finite.is_empty());
        finite.excluded.remove(&19);
        assert!(!finite.is_empty());
        let unbounded = IntegerDomain { min: Some(i128::MAX), max: None, excluded: [i128::MAX].into() };
        assert!(!unbounded.is_empty());
        assert!(p.witnesses[0].integer_domain("xsd:double").is_none());
    }
    #[test]
    fn cardinality_constraints_do_not_enumerate_large_integer_ranges() {
        let full = IntegerDomain { min: Some(i128::MIN), max: Some(i128::MAX), excluded: BTreeSet::new() };
        assert!(full.has_at_least_distinct_values(u64::MAX));
        let million = IntegerDomain { min: Some(1), max: Some(1_000_000), excluded: [0, 1, 1_000_001].into() };
        assert!(million.has_at_least_distinct_values(999_999));
        assert!(!million.has_at_least_distinct_values(1_000_000));
        let negative = IntegerDomain { min: Some(-3), max: Some(-1), excluded: [-2].into() };
        assert!(negative.has_at_least_distinct_values(2));
        assert!(!negative.has_at_least_distinct_values(3));
        let empty = negative.intersection(&million);
        assert!(empty.is_empty());
        assert!(empty.has_at_least_distinct_values(0));
    }
    #[test]
    fn small_domain_capacities_agree_with_explicit_value_sets() {
        for min in -3..=3 {
            for max in min..=3 {
                for mask in 0u8..128 {
                    let excluded: BTreeSet<i128> = (-3..=3)
                        .filter(|value| mask & (1 << (value + 3)) != 0).collect();
                    let expected = (min..=max).filter(|value| !excluded.contains(value)).count();
                    let domain = IntegerDomain { min: Some(min), max: Some(max), excluded };
                    for required in 0..=8 {
                        assert_eq!(domain.has_at_least_distinct_values(required), expected >= required as usize);
                    }
                }
            }
        }
    }
    #[test]
    fn fractional_thresholds_are_exact_over_integer_witnesses() {
        let p = plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<v>) \"-1.5\"^^xsd:decimal) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#lessThan> Variable(<v>) \"2.5\"^^xsd:decimal)").unwrap();
        let domain = p.witnesses[0].integer_domain("xsd:integer").unwrap();
        assert_eq!((domain.min, domain.max), (Some(-1), Some(2)));
        assert!(domain.has_at_least_distinct_values(4));
        assert!(!domain.has_at_least_distinct_values(5));
        let equal = plan("DataPropertyAtom(<age> Variable(<p>) Variable(<v>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#equal> Variable(<v>) \"17.5\"^^xsd:decimal)").unwrap();
        assert!(equal.witnesses[0].integer_domain("xsd:integer").unwrap().is_empty());
    }
}

#[cfg(test)]
mod builtin_join_tests {
    use super::*;
    fn variable(name: &str) -> RuleDataTerm { RuleDataTerm::Var(name.into()) }
    fn literal(value: &str) -> RuleDataTerm { RuleDataTerm::Literal(value.into()) }
    fn builtin(name: &str, args: Vec<RuleDataTerm>) -> RuleAtom {
        RuleAtom::Builtin(format!("http://www.w3.org/2003/11/swrlb#{name}"), args)
    }
    #[test]
    fn graph_arithmetic_resolves_dependencies_in_either_body_order() {
        let subtract = builtin("subtract", vec![variable("difference"), variable("later"), variable("earlier")]);
        let positive = builtin("greaterThan", vec![variable("difference"), literal("\"0\"^^xsd:int")]);
        let values = BTreeMap::from([
            ("later".into(), "\"102.92\"^^xsd:float".into()),
            ("earlier".into(), "\"100.89\"^^xsd:float".into()),
        ]);
        let forward = evaluate_builtin_conjunction(&[subtract.clone(), positive.clone()], &values);
        assert_eq!(forward, evaluate_builtin_conjunction(&[positive.clone(), subtract.clone()], &values));
        assert!(matches!(forward, BuiltinEvaluation::Satisfied(ref bindings) if bindings.contains_key("difference")));
        assert!(!values.contains_key("difference"));
        let reversed = BTreeMap::from([
            ("earlier".into(), "\"102.92\"^^xsd:float".into()),
            ("later".into(), "\"100.89\"^^xsd:float".into()),
        ]);
        assert_eq!(evaluate_builtin_conjunction(&[positive.clone(), subtract.clone()], &reversed), BuiltinEvaluation::Refuted);
        assert_eq!(evaluate_builtin_conjunction(&[positive, subtract], &BTreeMap::new()), BuiltinEvaluation::Deferred);
    }
    #[test]
    fn finite_tuple_plan_preserves_object_joins_and_defers_atomically() {
        let source = "Ontology(DLSafeRule(Body(ObjectPropertyAtom(<linked> Variable(<x>) Variable(<y>)) DataPropertyAtom(<value> Variable(<x>) Variable(<a>)) DataPropertyAtom(<value> Variable(<y>) Variable(<b>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<d>) \"0\"^^xsd:int) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#subtract> Variable(<d>) Variable(<b>) Variable(<a>))) Head(ObjectPropertyAtom(<increases> Variable(<x>) Variable(<y>)))))";
        let mut registry = super::super::iri::IriRegistry::new();
        let ontology = super::super::parse::parse_axioms(&mut registry, source).unwrap();
        let rule = ontology.datatype_rules().next().unwrap();
        let selected = vec!["\"1\"^^xsd:float".into(), "\"2\"^^xsd:float".into(), "\"title\"^^xsd:string".into()];
        let grounded = finite_data_rule_plan(rule, &selected, 9).unwrap();
        assert_eq!(grounded.len(), 1);
        let Axiom::Rule(body, head) = &grounded[0] else { panic!("object rule") };
        assert_eq!(body.len(), 3);
        assert!(matches!(&body[0], RuleAtom::Role(property, _, _) if property == "linked"));
        assert!(matches!(&head[0], RuleAtom::Role(property, _, _) if property == "increases"));
        assert!(finite_data_rule_plan(rule, &selected, 8).is_none());
        let unknown = vec!["\"1\"^^<http://example.org/unknown>".into()];
        assert!(finite_data_rule_plan(rule, &unknown, 9).is_none());
    }

    #[test]
    fn bound_output_is_checked_and_unknown_obligations_remain() {
        let subtract = builtin("subtract", vec![variable("d"), literal("\"3\"^^xsd:integer"), literal("\"1\"^^xsd:integer")]);
        assert_eq!(evaluate_builtin_conjunction(&[subtract.clone()], &BTreeMap::from([("d".into(), "\"7\"^^xsd:integer".into())])), BuiltinEvaluation::Refuted);
        assert_eq!(evaluate_builtin_conjunction(&[subtract, builtin("unknown", vec![])], &BTreeMap::new()), BuiltinEvaluation::Deferred);
        let cycle = builtin("subtract", vec![variable("d"), variable("d"), literal("\"1\"^^xsd:integer")]);
        assert_eq!(evaluate_builtin_conjunction(&[cycle], &BTreeMap::new()), BuiltinEvaluation::Deferred);
    }
}
