#!/bin/bash
# Isolate Konclude's post-preprocessing expressivity flags on tiny OFN inputs.
# This is deliberately run through the official binary rather than inferred
# from OWL constructor names.
#SBATCH --job-name=kon-expr-probe
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/kon-expr-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715
kon=/ibex/scratch/hohndor/km/Konclude-official
km=$root/km-profiled
mkdir -p "$root/expressivity-probe" "$root/slurm"
export LD_LIBRARY_PATH="/ibex/scratch/hohndor/km${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

write_ontology() {
  local name=$1
  local body=$2
  /usr/bin/printf 'Prefix(:=<http://e#>)\nOntology(\n%s\n)\n' "$body" \
    > "$root/expressivity-probe/$name.owl"
}

write_ontology declarations 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A :B)'
write_ontology classes_only 'Declaration(Class(:A))
Declaration(Class(:B))
SubClassOf(:A :B)'
write_ontology data_property_declaration 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(DataProperty(:p))
SubClassOf(:A :B)'
write_ontology datatype_declaration 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Datatype(:D))
SubClassOf(:A :B)'
write_ontology existential 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectSomeValuesFrom(:r :B))'
write_ontology hierarchy 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
SubObjectPropertyOf(:r :s)
SubClassOf(:A ObjectSomeValuesFrom(:r :B))'
write_ontology transitive 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
TransitiveObjectProperty(:r)
SubClassOf(:A ObjectSomeValuesFrom(:r :B))'
write_ontology transitive_unused 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
TransitiveObjectProperty(:r)
SubClassOf(:A ObjectSomeValuesFrom(:s :B))'
write_ontology chain_transitive_used 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubObjectPropertyOf(ObjectPropertyChain(:r :r) :r)
SubClassOf(:A ObjectSomeValuesFrom(:r :B))'
write_ontology chain_transitive_unused 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
SubObjectPropertyOf(ObjectPropertyChain(:r :r) :r)
SubClassOf(:A ObjectSomeValuesFrom(:s :B))'
write_ontology hierarchy_transitive 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
SubObjectPropertyOf(:r :s)
TransitiveObjectProperty(:s)
SubClassOf(:A ObjectSomeValuesFrom(:r :B))'
write_ontology functional 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
FunctionalObjectProperty(:r)
SubClassOf(:A ObjectSomeValuesFrom(:r :B))'
write_ontology min_qualified 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectMinCardinality(2 :r :B))'
write_ontology max_unqualified 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectMaxCardinality(3 :r))'
write_ontology max_one_qualified 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectMaxCardinality(1 :r :B))'
write_ontology union 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
SubClassOf(:A ObjectUnionOf(:B :C))'
write_ontology nominal 'Declaration(Class(:A))
Declaration(NamedIndividual(:i))
EquivalentClasses(:A ObjectOneOf(:i))'
write_ontology complex_chain 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(ObjectProperty(:t))
SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)
SubClassOf(:A ObjectSomeValuesFrom(:t :B))'
write_ontology datatype_some 'Declaration(Class(:A))
Declaration(DataProperty(:p))
SubClassOf(:A DataSomeValuesFrom(:p xsd:string))'
write_ontology equivalent_named 'Declaration(Class(:A))
Declaration(Class(:B))
EquivalentClasses(:A :B)'
write_ontology disjoint_classes 'Declaration(Class(:A))
Declaration(Class(:B))
DisjointClasses(:A :B)'
write_ontology disjoint_union 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
DisjointUnion(:A :B :C)'
write_ontology intersection 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
SubClassOf(:A ObjectIntersectionOf(:B :C))'
write_ontology complement 'Declaration(Class(:A))
Declaration(Class(:B))
SubClassOf(:A ObjectComplementOf(:B))'
write_ontology universal 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectAllValuesFrom(:r :B))'
write_ontology lhs_some 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(ObjectSomeValuesFrom(:r :B) :A)'
write_ontology lhs_all 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(ObjectAllValuesFrom(:r :B) :A)'
write_ontology lhs_intersection 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
SubClassOf(ObjectIntersectionOf(:A :B) :C)'
write_ontology lhs_union 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
SubClassOf(ObjectUnionOf(:A :B) :C)'
write_ontology lhs_complement 'Declaration(Class(:A))
Declaration(Class(:B))
SubClassOf(ObjectComplementOf(:A) :B)'
write_ontology lhs_min_one 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(ObjectMinCardinality(1 :r :B) :A)'
write_ontology lhs_max_one 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(ObjectMaxCardinality(1 :r :B) :A)'
write_ontology equivalent_intersection 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
EquivalentClasses(:A ObjectIntersectionOf(:B :C))'
write_ontology equivalent_some 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
EquivalentClasses(:A ObjectSomeValuesFrom(:r :B))'
write_ontology equivalent_some_and_subclass 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
EquivalentClasses(:A ObjectSomeValuesFrom(:r :B))
SubClassOf(:A :B)'
write_ontology equivalent_named_and_subclass 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
EquivalentClasses(:A :B)
SubClassOf(:A :C)'
write_ontology equivalent_some_cycle 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
EquivalentClasses(:A ObjectSomeValuesFrom(:r :B))
EquivalentClasses(:B ObjectSomeValuesFrom(:r :A))'
write_ontology has_value 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:i))
SubClassOf(:A ObjectHasValue(:r :i))'
write_ontology has_self 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectHasSelf(:r))'
write_ontology min_one_qualified 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectMinCardinality(1 :r :B))'
write_ontology min_one_unqualified 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectMinCardinality(1 :r))'
write_ontology max_zero_qualified 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectMaxCardinality(0 :r :B))'
write_ontology exact_one_qualified 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectExactCardinality(1 :r :B))'
write_ontology exact_one_unqualified 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectExactCardinality(1 :r))'
write_ontology exact_two_unqualified 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
SubClassOf(:A ObjectExactCardinality(2 :r))'
write_ontology equivalent_roles 'Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
EquivalentObjectProperties(:r :s)'
write_ontology inverse_roles 'Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
InverseObjectProperties(:r :s)'
write_ontology shared_inverse_roles 'Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(ObjectProperty(:t))
InverseObjectProperties(:r :s)
InverseObjectProperties(:r :t)'
write_ontology inverse_hierarchy_existential 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(ObjectProperty(:t))
Declaration(ObjectProperty(:u))
Declaration(ObjectProperty(:v))
SubClassOf(:A ObjectSomeValuesFrom(:r :B))
InverseObjectProperties(:s :t)
SubObjectPropertyOf(:u :v)'
write_ontology disjoint_roles 'Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
DisjointObjectProperties(:r :s)'
write_ontology symmetric_role 'Declaration(ObjectProperty(:r))
SymmetricObjectProperty(:r)'
write_ontology asymmetric_role 'Declaration(ObjectProperty(:r))
AsymmetricObjectProperty(:r)'
write_ontology reflexive_role 'Declaration(ObjectProperty(:r))
ReflexiveObjectProperty(:r)'
write_ontology irreflexive_role 'Declaration(ObjectProperty(:r))
IrreflexiveObjectProperty(:r)'
write_ontology inverse_functional_role 'Declaration(ObjectProperty(:r))
InverseFunctionalObjectProperty(:r)'
write_ontology object_domain 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
ObjectPropertyDomain(:r :A)'
write_ontology object_range 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
ObjectPropertyRange(:r :A)'
write_ontology sub_data_role 'Declaration(DataProperty(:p))
Declaration(DataProperty(:q))
SubDataPropertyOf(:p :q)'
write_ontology equivalent_data_roles 'Declaration(DataProperty(:p))
Declaration(DataProperty(:q))
EquivalentDataProperties(:p :q)'
write_ontology disjoint_data_roles 'Declaration(DataProperty(:p))
Declaration(DataProperty(:q))
DisjointDataProperties(:p :q)'
write_ontology functional_data_role 'Declaration(DataProperty(:p))
FunctionalDataProperty(:p)'
write_ontology data_domain 'Declaration(Class(:A))
Declaration(DataProperty(:p))
DataPropertyDomain(:p :A)'
write_ontology data_range 'Declaration(DataProperty(:p))
DataPropertyRange(:p xsd:integer)'
write_ontology data_has_value 'Declaration(Class(:A))
Declaration(DataProperty(:p))
SubClassOf(:A DataHasValue(:p "1"^^xsd:integer))'
write_ontology data_max_one 'Declaration(Class(:A))
Declaration(DataProperty(:p))
SubClassOf(:A DataMaxCardinality(1 :p xsd:integer))'
write_ontology datatype_definition 'Declaration(Datatype(:D))
DatatypeDefinition(:D DataOneOf("x" "y"))'
write_ontology class_assertion 'Declaration(Class(:A))
Declaration(NamedIndividual(:i))
ClassAssertion(:A :i)'
write_ontology negative_class_assertion 'Declaration(Class(:A))
Declaration(NamedIndividual(:i))
ClassAssertion(ObjectComplementOf(:A) :i)'
write_ontology object_assertion 'Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
ObjectPropertyAssertion(:r :i :j)'
write_ontology negative_object_assertion 'Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
NegativeObjectPropertyAssertion(:r :i :j)'
write_ontology data_assertion 'Declaration(DataProperty(:p))
Declaration(NamedIndividual(:i))
DataPropertyAssertion(:p :i "1"^^xsd:integer)'
write_ontology negative_data_assertion 'Declaration(DataProperty(:p))
Declaration(NamedIndividual(:i))
NegativeDataPropertyAssertion(:p :i "1"^^xsd:integer)'
write_ontology same_individual 'Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
SameIndividual(:i :j)'
write_ontology different_individuals 'Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
DifferentIndividuals(:i :j)'
write_ontology different_with_disjoint 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
DisjointClasses(:A :B)
DifferentIndividuals(:i :j)'
write_ontology different_with_union_equivalence 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
EquivalentClasses(:A ObjectUnionOf(:B :C))
DifferentIndividuals(:i :j)'
write_ontology different_with_intersection_equivalence 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(NamedIndividual(:i))
Declaration(NamedIndividual(:j))
EquivalentClasses(:A ObjectIntersectionOf(:B :C))
DifferentIndividuals(:i :j)'
write_ontology oneof_with_disjoint 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(NamedIndividual(:i))
DisjointClasses(:B :C)
EquivalentClasses(:A ObjectOneOf(:i))'
write_ontology oneof_before_disjoint 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(NamedIndividual(:i))
EquivalentClasses(:A ObjectOneOf(:i))
DisjointClasses(:B :C)'
write_ontology has_value_domain_unused 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(NamedIndividual(:i))
ObjectPropertyDomain(:r ObjectHasValue(:s :i))'
write_ontology has_value_domain_used 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(NamedIndividual(:i))
ObjectPropertyDomain(:r ObjectHasValue(:s :i))
SubClassOf(:A ObjectSomeValuesFrom(:r owl:Thing))'
write_ontology complex_chain_transitive_same_super 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(ObjectProperty(:t))
TransitiveObjectProperty(:t)
SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)
SubClassOf(:A ObjectSomeValuesFrom(:t :B))'
write_ontology complex_chain_transitive_unrelated 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(ObjectProperty(:r))
Declaration(ObjectProperty(:s))
Declaration(ObjectProperty(:t))
Declaration(ObjectProperty(:u))
TransitiveObjectProperty(:u)
SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)
SubClassOf(:A ObjectSomeValuesFrom(:t :B))'
write_ontology has_key 'Declaration(Class(:A))
Declaration(ObjectProperty(:r))
Declaration(DataProperty(:p))
HasKey(:A (:r) (:p))'
write_ontology top_object_role 'Declaration(Class(:A))
SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :A))'
write_ontology top_object_role_all 'Declaration(Class(:A))
SubClassOf(:A ObjectAllValuesFrom(owl:topObjectProperty :A))'
write_ontology rule 'Declaration(Class(:A))
Declaration(Class(:B))
DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:B Variable(:x))))'
write_ontology rule_with_nominal 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(NamedIndividual(:i))
EquivalentClasses(:A ObjectOneOf(:i))
DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:B Variable(:x))))'
write_ontology rule_with_nested_nominal 'Declaration(Class(:A))
Declaration(Class(:B))
Declaration(Class(:C))
Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:i))
EquivalentClasses(:A ObjectIntersectionOf(:B ObjectSomeValuesFrom(:r ObjectOneOf(:i))))
DLSafeRule(Body(ClassAtom(:A Variable(:x))) Head(ClassAtom(:C Variable(:x))))'

/usr/bin/find "$root/expressivity-probe" -maxdepth 1 -name '*taxonomy*' -delete
for input in "$root"/expressivity-probe/*.owl; do
  name=${input##*/}
  name=${name%.owl}
  set +e
  "$kon" classification -w 1 -v -i "$input" \
    -o "$root/expressivity-probe/$name.taxonomy.owl" \
    > "$root/expressivity-probe/$name.stdout" \
    2> "$root/expressivity-probe/$name.stderr"
  kon_rc=$?
  set -e
  expression=$(/usr/bin/sed -n "s/.*expressiveness '\([^']*\)'.*/\1/p" \
    "$root/expressivity-probe/$name.stdout" | /usr/bin/head -1)
  km_expression=NA
  km_rc=NA
  if [[ -x "$km" ]]; then
    set +e
    "$km" profile "$input" > "$root/expressivity-probe/$name.km.json" \
      2> "$root/expressivity-probe/$name.km.stderr"
    km_rc=$?
    set -e
    if (( km_rc == 0 )); then
      km_expression=$(/usr/bin/python3 -c \
        'import json,sys; d=json.load(open(sys.argv[1])); print(((d.get("profile") or {}).get("expressivity") or {}).get("code", "NA"))' \
        "$root/expressivity-probe/$name.km.json")
    fi
  fi
  verdict=MISMATCH
  [[ -n "$expression" && "$expression" == "$km_expression" ]] && verdict=MATCH
  /usr/bin/printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "${expression:-NA}" "$km_expression" "$verdict" "$kon_rc" "$km_rc"
done
