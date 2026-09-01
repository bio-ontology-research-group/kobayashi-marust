# STATO_0000073 satisfiability adjudication

Slurm job `51037832` extracted a STAR locality module for the query
`STATO_0000073 SubClassOf owl:Nothing` from the frozen STATO source and tested
that exact module with the pinned HermiT, JFact, and Openllet artifacts.

- Frozen source SHA-256: `bf310eeeeade2d8f9042acf00a9f187678f2203ed9a3d9790ac3ac9abd719aad`
- Module SHA-256: `2e6e66e653c377c416ddf611051c424eba88474698616cebb23c82c66d1d464f`
- Slurm script SHA-256: `322f97e3ee94fbc56cf4cf7ceed75fb50453056764613ea9a84b19d8f7eb21f9`
- Module size: 2,072 axioms, including 443 logical axioms

HermiT returned `entailed=false`. JFact completed the module and retained the
single disputed bottom classification. Openllet completed the same module with
zero unsatisfiable named classes. The result records bind the module, runner,
and reasoner artifacts by SHA-256. This establishes a reproducible three-way
split; HermiT and Openllet independently agree against JFact.

