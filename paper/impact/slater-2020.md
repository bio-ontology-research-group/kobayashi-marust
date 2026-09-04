# Primary-source note: Slater, Gkoutos, and Hoehndorf (2020)

Primary article: Karin T. Slater, Georgios V. Gkoutos, and Robert Hoehndorf,
“Towards semantic interoperability: finding and repairing hidden contradictions
in biomedical ontologies,” *BMC Medical Informatics and Decision Making* 20,
article 311 (2020), DOI
[10.1186/s12911-020-01336-2](https://doi.org/10.1186/s12911-020-01336-2).
The article is open access under CC BY 4.0. The accompanying primary software
and result repository is
[UNMIREOT](https://github.com/bio-ontology-research-group/UNMIREOT), whose
latest commit is `e579133d34b6e579da2b673f9cd0ffe0c8427fec` (2020-12-04).

## What the study did

The authors downloaded 132 obtainable, non-deprecated OBO ontologies on
2018-03-28. They first combined nine OBO Foundry ontologies, then combined a
repaired form of that meta-ontology with each wider OBO ontology. OWLAPI 5.1.4
performed loading and merging; ELK 0.5.0-SNAPSHOT performed classification and
the repeated satisfiability checks used during justification extraction.

The classifier found 636 unsatisfiable named classes in the nine-ontology
OBO Foundry merge. Across the wider combinations, the paper reports 866,494
unsatisfiable occurrences and 312,398 distinct unsatisfiable classes. The
repair heuristic repeatedly:

1. classified the current ontology;
2. retained the most general unsatisfiable classes under asserted subclass
   links;
3. prioritized those with the most direct asserted subclasses;
4. generated black-box minimal justifications for at most 25 selected classes;
5. removed the most frequent axiom from those justifications; and
6. reclassified until no unsatisfiable named classes remained.

It reported 117 removed axioms across the wider experiment. This is a heuristic
repair candidate set, not a proof that every removed axiom is scientifically
incorrect. The paper explicitly warns that removing an implicated axiom need
not repair the conceptual root cause.

## The full-DL generalization

The article states that ELK supports OWL 2 EL, lacks negation in class
descriptions and universal quantification, and could therefore miss additional
contradictions that a more expressive reasoner might reveal. The defensible KM
generalization is to replace each classification/satisfiability oracle call
with complete OWL 2 DL reasoning. This expands the detectable interaction set
while preserving the merge, witness, expert-review, and reclassification
workflow.

What is already supported here:

* KM classifies the synthetic merged example and detects an unsatisfiable class
  whose conflict depends on a universal restriction, an existential
  restriction, and disjointness.
* `km explain ... unsatisfiable <CLASS>` returns a bounded source-axiom witness
  for that example.
* KM classification reports consistency separately from unsatisfiable named
  classes.

What remains a proposed experiment:

* rerunning the paper's exact 2018 corpus is blocked because the repository says
  the ontology files themselves must be reacquired and its permanent links now
  resolve newer releases;
* running all pairwise/current OBO combinations under full OWL 2 DL and
  comparing newly detected conflicts with the 2020 EL results;
* reproducing the entire iterative 25-sample greedy repair loop with KM as the
  oracle; and
* validating candidate repairs with ontology maintainers and downstream
  scientific tasks.

The frozen 2026-08-30 OBO corpus already in the paper benchmark is the sound
starting point for a new, date-bounded experiment. It is not interchangeable
with the paper's 2018 corpus and must be reported as a replication on new data.
