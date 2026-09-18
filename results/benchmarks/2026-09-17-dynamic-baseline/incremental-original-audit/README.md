# Original incremental peer audit

All 1,188 planned attempts terminated, including one warmup and five measured
repetitions. `main-audit.json.gz` retains every attempt and available state digest.
Slurm audit 51982323 completed successfully. Payload verification 52045248
independently hashed all 4,518 inputs and seven runtimes, checked ordered manifests
and driver source hashes, and bound them to every measurement.

See `../incremental-final-comparison/` for the independent parent review, final
KM comparison, failure accounting, and time/memory tables. Successful job exits
alone do not establish correct reasoning. Complete HermiT/JFact reference pairs
are unavailable for VTO, TO, Uberon and MRO; their completed outputs remain
unverified. Available-state digest comparisons found no disagreement.
