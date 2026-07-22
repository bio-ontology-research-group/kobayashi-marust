# ORE 2015 full-panel verification

*2026-07-22T19:14:13Z by Showboat 0.6.1*
<!-- showboat-id: 49663624-10b2-4842-a334-8389ac7676f7 -->

This executable record verifies the generated 2026-07-22 ORE panel artifacts without rerunning the reasoners. The fail-closed aggregation already checked source, binary, driver, ontology, oracle, and per-row identities; these commands check the committed publication boundary.

```bash
sha256sum -c full-panel-generated-files.sha256
```

```output
full-panel-contract.tsv: OK
procedure-runtime-identities.tsv: OK
full-panel-results.tsv.gz: OK
full-panel-summary.tsv: OK
full-panel-summary.json: OK
headline-summary.tsv: OK
headline-summary.json: OK
optimization-effects.tsv: OK
ontology-route-performance.tsv: OK
ore-4669-targeted-soundness.tsv: OK
full-panel-raw-results.sha256: OK
full-panel-raw-results.jsonl.gz: OK
full-panel-receipt.json: OK
```

The receipt and the committed tabular artifacts must agree on ontology, procedure, measurement, and Slurm-task cardinalities.

```python3
import csv, gzip, json
receipt = json.load(open("full-panel-receipt.json"))
with gzip.open("full-panel-results.tsv.gz", "rt", newline="") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))
with open("full-panel-contract.tsv", newline="") as handle:
    contract = list(csv.DictReader(handle, delimiter="\t"))
with open("ontology-route-performance.tsv", newline="") as handle:
    ledger = list(csv.DictReader(handle, delimiter="\t"))
with gzip.open("full-panel-raw-results.jsonl.gz", "rt") as handle:
    raw_rows = sum(1 for line in handle if line.strip())
print("receipt ontologies={} procedures={} measurements={}".format(receipt["ontology_count"], receipt["procedure_count"], receipt["measurement_count"]))
print("receipt distinct_slurm_tasks={} primary_array={} aggregation={}".format(receipt["distinct_slurm_task_job_ids"], receipt["array_job_id"], receipt["aggregation_slurm_job_id"]))
print("normalized rows={} ontologies={} procedures={}".format(len(rows), len({row["ontology"] for row in rows}), len({row["arm"] for row in rows})))
print("raw rows={} contract procedures={} ledger ontologies={}".format(raw_rows, len(contract), len(ledger)))
```

```output
receipt ontologies=592 procedures=66 measurements=39072
receipt distinct_slurm_tasks=592 primary_array=49290191 aggregation=49311162
normalized rows=39072 ontologies=592 procedures=66
raw rows=39072 contract procedures=66 ledger ontologies=592
```

The headline counts below are read directly from the generated summary. They distinguish automatic KM, preselected current routes, the post hoc current-route upper bound, and each primary baseline.

```python3
import csv
wanted = ["km_documented_selected", "km_best_current_route", "km_auto", "konclude", "hermit", "elk", "rustdl", "sequoia"]
rows = {row["arm"]: row for row in csv.DictReader(open("headline-summary.tsv"), delimiter="\t")}
print("arm\tsound_yes\tcomplete_yes\tboth_yes\tok\twall_mean_s\twall_median_s\tpeak_mean_mib\tpeak_median_mib")
for arm in wanted:
    row = rows[arm]
    values = [arm, row["sound_yes"], row["complete_yes"], row["sound_complete"], row["ok"], row["wall_mean_s"], row["wall_median_s"], row["peak_mean_mb"], row["peak_median_mb"]]
    print("\t".join(values))
```

```output
arm	sound_yes	complete_yes	both_yes	ok	wall_mean_s	wall_median_s	peak_mean_mib	peak_median_mib
km_documented_selected	575	575	575	583	5.0168	0.2336	643.158	37.12
km_best_current_route	579	579	579	579	3.4477	0.1893	385.4331	29.72
km_auto	562	562	562	571	5.3	0.2807	789.9226	44.43
konclude	587	585	585	589	3.2657	0.2813	558.0915	76.53
hermit	549	550	549	558	13.1261	1.8868	1330.5641	714.005
elk	576	529	529	592	1.7449	0.7466	505.8606	234.11
rustdl	542	525	525	551	4.9596	0.1928	299.4854	49.8
sequoia	340	339	339	341	7.3405	2.5371	2197.3128	536.15
```

Finally, the Slurm export itself must be intact. It contains master jobs, array tasks, batch/extern steps, diagnostics, and the final aggregation record.

```bash
gzip -t provenance/slurm-accounting.tsv.gz && sha256sum provenance/slurm-accounting.tsv.gz && zcat provenance/slurm-accounting.tsv.gz | wc -l
```

```output
6a52c200309bc6984fc4f608ff813fff13d54dd0710c3dc65a5aa384fd8471df  provenance/slurm-accounting.tsv.gz
1822
```
