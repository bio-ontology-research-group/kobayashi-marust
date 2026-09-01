# MORe baseline adapter

MORe is pinned to public source commit
`9d29fb15352b781a3dba015696b1b269320603b2`. Its original dependency graph is
retained: OWLAPI 3.4.10, HermiT 1.3.8.4, ELK 0.4.2, and JRDFox build 2213.
The default configuration uses ELK and HermiT; JRDFox remains packaged because
it is part of the published source build but is not enabled for the benchmark.

`FullIriClassifier3.java` is an OWLAPI 3 source adapter for the same atomic
full-IRI output contract used by the newer OWLAPI baselines. Building on a
current JDK changes the POM's source and target levels from 7 to 8; this is a
bytecode compatibility change only. No MORe source or dependency version is
replaced.

MORe's OWLAPI `isConsistent()` and `getUnsatisfiableClasses()` methods are
unsupported stubs. The adapter therefore invokes its documented
`classifyClasses()` and `getAllUnsatisfiableClasses()` methods and records
consistency as `unknown`. This avoids converting the consistency stub's
hard-coded `false` into a false inconsistency result.
