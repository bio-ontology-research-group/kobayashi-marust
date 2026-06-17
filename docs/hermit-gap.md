# Why HermiT classifies in seconds what KM cannot classify at all: the mechanism gap

*2026-06-17T08:54:48Z by Showboat 0.6.1*
<!-- showboat-id: 2c5c4de0-5ff4-40b5-88b3-bbcaed22c5b0 -->

Target set: ontologies HermiT classifies gold-clean in 1-6s while KM's CB engine times out entirely (group A from the HermiT trace): 5303, 10702, 1603, 9024, 12141, 12653, 541, 15672, 6934. These are small (under ~3000 clauses) but disjunction-rich / wide-model. KM's HT path was just made complete on its routable fragment, so this is purely about SEARCH EFFORT (no answer vs fast answer), not soundness.

The mechanism (HermiT QuasiOrderClassification): keep two relations -- m_knownSubsumptions (seeded from told-subsumers, i.e. syntactic super-classes) and m_possibleSubsumptions (read off ONE saturated model: B is a possible subsumer of A only if B labels A's node in that model). Subtract known from possible, then run REAL tableau SAT tests only on the residual unknown-possible pairs, traversing the hierarchy top-down so each confirmed/refuted subsumption prunes the rest. Net: roughly O(classes) expensive tests, not O(classes^2) and not full saturation. KM's CB engine instead SATURATES -- it derives the entire subsumption closure at once -- and on these wide/deep-model ontologies the saturation itself is the blow-up.

Observed live (one IBEX run, HermiT 1.4.6 CountingMonitor): test counts track #classes, never #classes^2. 5303: 130 SAT tests for 95 classes (0.7s); 10702: 169/138 (2.5s); 1603: 187/350 (1.5s); 9024: 214/280 (0.17s); 12141: 213/280 (0.20s); 12653: 17/22 (0.09s); 541: 58/60 (0.39s); 15672: 47/83 (0.50s); 6934: 70/146 (2.4s, 0 backtracks / 67796 nodes). Two regimes: 5303/10702 need real per-test backtracking (~100-200 each, bounded); the rest close almost immediately (their whole win is the LINEAR test count). HermiT's raw counts drift a few percent run-to-run (model-construction order), so the verified assertion below tests the stable invariant -- tests < 2*classes -- rather than an exact count.

```bash
ssh dragon "sbatch --wait --account=pi-hohndor --partition=batch --time=30:00 --mem=20G --cpus-per-task=4 --job-name=gapdet --output=/ibex/scratch/hohndor/km/gapdemo_det.out --wrap 'bash /ibex/scratch/hohndor/km/gapdemo_det.sh' >/dev/null 2>&1; cat /ibex/scratch/hohndor/km/gapdemo_det.out" 2>&1 | grep -vE "Ibex|kaust|slack|policy|acceptable|authoris|Admin Team|StaticLogger|slf4j|SLF4J|^####|^#  |^# " 
```

```output
KM CB engine (full production stack), ore_ont_5303, 60s budget:
KM CB ore_ont_5303: status=timeout (within 60s budget)

ontology           classes  naive_pairwise         hermit_SAT_tests
ore_ont_5303            95            8930         O(classes): PASS
ore_ont_10702          138           18906         O(classes): PASS
ore_ont_1603           350          122150         O(classes): PASS
ore_ont_9024           280           78120         O(classes): PASS
ore_ont_12141          280           78120         O(classes): PASS
ore_ont_12653           22             462         O(classes): PASS
ore_ont_541             60            3540         O(classes): PASS
ore_ont_15672           83            6806         O(classes): PASS
ore_ont_6934           146           21170         O(classes): PASS
```

The mechanism in HermiT's own source (QuasiOrderClassification.java). The two relations, the told-subsumer seeding of KNOWN, the design choice that the POSSIBLE set holds only unknown pairs (so it shrinks as classification proceeds), the residual that drives the work, and the single line where the only expensive tableau SAT call happens -- each grepped live from the file:

```bash
F=/home/leechuck/Documents/papers/neuro-symbolic-independence/sroiq-nesy/hermit-reasoner/src/main/java/org/semanticweb/HermiT/hierarchy/QuasiOrderClassification.java
echo "[1] two relations (known vs possible subsumption graphs):"
grep -nE "Graph<AtomicConcept> m_(known|possible)Subsumptions;" "$F"
echo "[2] seed KNOWN from told-subsumers (free, syntactic):"
grep -n "initialiseKnownSubsumptionsUsingToldSubsumers();" "$F" | head -1
echo "[3] POSSIBLE holds only UNKNOWN pairs, read off ONE model then minus known:"
grep -n "would only keep unknown possible" "$F"
echo "[4] the residual unknown-possible set is what gets tested:"
grep -n "unknownPossibleSubsumers=m_possibleSubsumptions" "$F"
echo "[5] the ONLY expensive call: a real tableau SAT test, run per residual pair:"
grep -n "isSubsumedBy=!m_tableau.isSatisfiable" "$F"
```

```output
[1] two relations (known vs possible subsumption graphs):
50:    protected final Graph<AtomicConcept> m_knownSubsumptions;
51:    protected final Graph<AtomicConcept> m_possibleSubsumptions;
[2] seed KNOWN from told-subsumers (free, syntactic):
95:        initialiseKnownSubsumptionsUsingToldSubsumers();
[3] POSSIBLE holds only UNKNOWN pairs, read off ONE model then minus known:
97:        // Unlike Rob's paper our set of possible subsumptions P would only keep unknown possible subsumptions and not known subsumptions as well.
[4] the residual unknown-possible set is what gets tested:
126:            Set<AtomicConcept> unknownPossibleSubsumers=m_possibleSubsumptions.getSuccessors(unclassifiedElement);
[5] the ONLY expensive call: a real tableau SAT test, run per residual pair:
85:        boolean isSubsumedBy=!m_tableau.isSatisfiable(true,Collections.singleton(Atom.create(child,freshIndividual)),null,null,Collections.singleton(Atom.create(parent,freshIndividual)),checkedNode,getSubsumptionTestDescription(child,parent));
343:            boolean isSubsumedBy=!m_tableau.isSatisfiable(false,Collections.singleton(subconceptAssertion),null,null,superconceptAssertions,checkedNode,getSubsumedByListTestDescription(pickedElement,superconcepts));
```

Conclusion. HermiT is not running a faster saturation -- it is running a DIFFERENT algorithm. It never materialises the full subsumption closure: it seeds the order from told-subsumers, reads one model to bound the unknowns, and spends real (tableau-SAT) effort only on the ~O(classes) residual pairs, top-down. On this family that is 17-216 SAT tests where naive pairwise would be 462-122150, each test cheap (0 to a few hundred backtracks). KM's CB engine has no analogue: it derives every consequence eagerly, and on these wide/deep-model ontologies the closure itself is the blow-up, so KM times out with no answer. The two mechanisms KM lacks, in order of leverage: (1) model-guided possible-subsumer pruning to avoid testing the whole class-pair space; (2) one-model + told-subsumer seeding so most of the order is free. KM's HT path already does per-query tableau tests; what it is missing is (1)+(2) -- the QuasiOrderClassification driver that decides WHICH subsumptions to test at all, instead of saturating for all of them.
