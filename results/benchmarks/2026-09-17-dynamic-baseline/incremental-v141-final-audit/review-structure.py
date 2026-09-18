"""Recheck the archived KM-only audit; does not establish peer correctness."""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

root = Path(__file__).resolve().parent
payload = gzip.decompress((root / "main-audit.json.gz").read_bytes())
audit = json.loads(payload)
assert set(audit["cases"]) == {
    f"{ontology}-n{size}"
    for ontology in ("mmo", "hao", "vto", "mfomd", "to", "uberon", "zfa", "mro")
    for size in (1, 10, 100)
}
counts, measured = Counter(), Counter()
checked = agreeing = 0
for case in audit["cases"].values():
    assert case["expected_states"] == 251
    assert set(case["repetitions"]) == {"warmup", "0", "1", "2", "3", "4"}
    for rep, record in case["repetitions"].items():
        assert set(record["arms"]) == {"km/session", "km/fresh"}
        for arm in record["arms"].values():
            measurement = arm["measurement"]
            counts[arm["status"]] += 1
            if rep != "warmup":
                measured[arm["status"]] += 1
            assert measurement["manifest_sha256"] == case["manifest_sha256"]
            assert measurement["slurm_array_job"] == "51983825"
            assert measurement["runtime_sha256"] == "680d9002583468e7c68115bf67cb60b89e420339db4c6aa22b5ca802206c8629"
            assert tuple(measurement[k] for k in ("history_timeout_s", "state_timeout_s", "memcap_mib")) == (7200, 240, 20480)
            assert measurement["completed_states"] == len(arm["states"])
            if arm["complete"]:
                assert set(arm["states"]) == set(map(str, range(251)))
                assert not arm["issues"]
        left, right = (record["arms"][f"km/{mode}"] for mode in ("session", "fresh"))
        shared = left["states"].keys() & right["states"].keys()
        assert all(left["states"][i]["sha256"] == right["states"][i]["sha256"] for i in shared)
        own = record["own_session_fresh"]["km"]
        assert own["checked_states"] == len(shared)
        assert not own["mismatch_revisions"]
        checked += len(shared)
        agreeing += bool(own["full_agreement"])
assert dict(counts) == audit["summary"]["measurement_statuses"]
prior = json.loads((root / "parent-structural-review.json").read_text())
assert hashlib.sha256(payload).hexdigest() == prior["audit_sha256"]
assert dict(measured) == prior["measured_statuses"]
assert checked == prior["own_session_fresh_checked_states_including_warmup"]
assert agreeing == prior["fully_agreeing_history_pairs_including_warmup"]
print(json.dumps({"status": "pass", "attempts": sum(counts.values()), "measured": dict(measured), "self_comparison_states": checked, "peer_correctness": "not checked by this script"}))
