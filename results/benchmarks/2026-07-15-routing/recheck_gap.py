#!/usr/bin/env python3
"""Repeat one >20% KM/Konclude gap on a single exclusive IBEX node."""

import argparse
import csv
import hashlib
import json
import os
import shutil
import subprocess


COMMON = [
    "KM_ROUTE=manual",
    "KM_THREADS=16",
    "KM_PAR_MEM_GB=18",
    "KM_HT_MEM_GB=18",
    "KM_KEEP_CHAIN_AXIOMS=1",
]

AUTO_COMMON = [
    "KM_ROUTE=auto",
    "KM_THREADS=16",
    "KM_PAR_MEM_GB=18",
    "KM_HT_MEM_GB=18",
    "KM_KEEP_CHAIN_AXIOMS=1",
]


def arm_environment(arm):
    configurations = {
        "default": [],
        "default8": ["KM_THREADS=8"],
        "default1": ["KM_THREADS=1"],
        "production_all": [
            "KM_TRIGGER_ABSORB=1",
            "KM_BRIDGE_PROBE_BUDGET_S=30",
            "KM_BRIDGE_RETRY_ROUNDS=0",
            "KM_HT_SATURATION_BUDGET_S=180",
        ],
        "production_all8": [
            "KM_THREADS=8",
            "KM_TRIGGER_ABSORB=1",
            "KM_BRIDGE_PROBE_BUDGET_S=30",
            "KM_BRIDGE_RETRY_ROUNDS=0",
            "KM_HT_SATURATION_BUDGET_S=180",
        ],
        "production_all1": [
            "KM_THREADS=1",
            "KM_TRIGGER_ABSORB=1",
            "KM_BRIDGE_PROBE_BUDGET_S=30",
            "KM_BRIDGE_RETRY_ROUNDS=0",
            "KM_HT_SATURATION_BUDGET_S=180",
        ],
        "cb_plain16": [
            "KM_NO_ELC=1",
            "KM_NO_HT_RACE=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
        ],
        "cb_plain8": [
            "KM_NO_ELC=1",
            "KM_NO_HT_RACE=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_THREADS=8",
        ],
        "cb_plain1": [
            "KM_NO_ELC=1",
            "KM_NO_HT_RACE=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_THREADS=1",
        ],
        "cb_absorb16": [
            "KM_NO_ELC=1",
            "KM_NO_HT_RACE=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=1",
        ],
        "cb_absorb_portfolio16": [
            "KM_NO_ELC=1",
            "KM_NO_HT_RACE=1",
            "KM_ABSORB=1",
        ],
        "elc_cert": [
            "KM_NO_HT_RACE=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_ELC_FORCE=1",
            "KM_ELC_CERT=2",
        ],
        "lean": [
            "KM_NO_ELC_PORTFOLIO=1",
            "KM_NO_HT_RACE=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_CENTRAL=1",
            "KM_THREADS=1",
        ],
        "ht_general": [
            "KM_NO_ELC=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_SHOQ=1",
            "KM_NO_HT_CARD=1",
            "KM_HT_MODE=race",
        ],
        "ht_qo": [
            "KM_NO_ELC=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_HT_SHOQ=1",
            "KM_NO_HT_CARD=1",
            "KM_HT_MODE=race",
        ],
        "ht_shoq": [
            "KM_NO_ELC=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_CARD=1",
            "KM_HT_MODE=race",
        ],
        "ht_card": [
            "KM_NO_ELC=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_SHOQ=1",
            "KM_HT_MODE=race",
        ],
        "ht_bridge": [
            "KM_NO_ELC=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_SHOQ=1",
            "KM_NO_HT_CARD=1",
            "KM_TRIGGER_ABSORB=1",
            "KM_BRIDGE_PROBE_BUDGET_S=30",
            "KM_BRIDGE_RETRY_ROUNDS=0",
            "KM_HT_SATURATION_BUDGET_S=180",
            "KM_HT_MODE=race",
        ],
        "ht_rules": [
            "KM_NO_ELC=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
            "KM_NO_HT_RACE=1",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_SHOQ=1",
            "KM_NO_HT_CARD=1",
        ],
        "tab_race": [
            "KM_TAB_RACE=1",
            "KM_TAB_FEAT=1",
            "KM_NO_ELC_PORTFOLIO=1",
            "KM_NO_HT_RACE=1",
        ],
        "card_fn": ["KM_HT_CARD_FN=1"],
        "nominals": ["KM_NOMINALS=1"],
        "seq_on": ["KM_SEQ_ORDER=1"],
        "seq_off": ["KM_NO_SEQ_ORDER=1"],
    }
    if arm not in configurations:
        raise ValueError(f"unknown arm {arm}")
    return COMMON + configurations[arm]


def sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def execute(argv, output):
    completed = subprocess.run(argv, check=True, stdout=subprocess.PIPE, text=True)
    row = json.loads(completed.stdout)
    output.write(json.dumps(row, sort_keys=True) + "\n")
    output.flush()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--task", required=True, type=int)
    parser.add_argument("--replicates", type=int, default=3)
    parser.add_argument("--mode", choices=("oracle", "auto"), default="oracle")
    args = parser.parse_args()

    root = os.path.abspath(args.root)
    gaps_name = (
        "gaps-over-20-percent.csv"
        if args.mode == "oracle"
        else "auto-over-20-percent.csv"
    )
    rows = list(csv.DictReader(open(os.path.join(root, gaps_name))))
    if args.task >= len(rows):
        return
    gap = rows[args.task]
    ont = gap["ont"]
    arm = gap["oracle_arm"] if args.mode == "oracle" else "auto"
    km_root = "/ibex/scratch/hohndor/km"
    source = os.path.join(km_root, "corpus", ont)
    local = os.path.join(os.environ.get("SLURM_TMPDIR", "/tmp"), ont)
    shutil.copy2(source, local)
    # The procedure matrix uses its immutable, separately named frozen runner.
    # All post-matrix paired validation uses the artifact committed as
    # `bench_one.py`, whose hash is recorded before submission.
    runner = os.path.join(root, "bench_one.py")
    km = os.path.join(
        root, "km-profiled-final3" if args.mode == "oracle" else "km-auto-final"
    )
    kon = os.path.join(km_root, "Konclude-official")
    gold = os.path.join(km_root, "gold", f"konclude__{ont}.sig.gz")
    work = os.path.join(os.environ.get("SLURM_TMPDIR", "/tmp"), "km-gap-work")
    prefix = "gap" if args.mode == "oracle" else "auto-gap"
    artifacts = os.path.join(root, f"{prefix}-artifacts", ont)
    result_dir = os.path.join(root, f"{prefix}-rechecks")
    os.makedirs(work, exist_ok=True)
    os.makedirs(artifacts, exist_ok=True)
    os.makedirs(result_dir, exist_ok=True)
    result_path = os.path.join(result_dir, ont + ".jsonl")
    km_sha = sha256(km)
    kon_sha = sha256(kon)

    def km_command(rep, position):
        command = [
            "/usr/bin/python3",
            runner,
            "--kind",
            "km",
            "--arm",
            arm,
            "--ontology",
            local,
            "--binary",
            km,
            "--binary-sha",
            km_sha,
            "--gold",
            gold,
            "--workdir",
            work,
            "--failures-dir",
            artifacts,
            "--keep-artifacts",
            "--replicate",
            str(rep),
            "--order-index",
            str(position),
            "--timeout",
            "240",
            "--memcap-mb",
            "20480",
        ]
        settings = AUTO_COMMON if args.mode == "auto" else arm_environment(arm)
        for setting in settings + ["KM_TIMING=1", "KM_OFN_TIMING=1"]:
            command.extend(["--env", setting])
        return command

    def konclude_command(workers, rep, position):
        return [
            "/usr/bin/python3",
            runner,
            "--kind",
            "konclude",
            "--arm",
            f"konclude_w{workers}",
            "--ontology",
            local,
            "--binary",
            kon,
            "--binary-sha",
            kon_sha,
            "--workers",
            str(workers),
            "--workdir",
            work,
            "--failures-dir",
            artifacts,
            "--keep-artifacts",
            "--replicate",
            str(rep),
            "--order-index",
            str(position),
            "--timeout",
            "240",
            "--memcap-mb",
            "20480",
        ]

    orders = (("k1", "km", "k16"), ("km", "k16", "k1"), ("k16", "k1", "km"))
    with open(result_path, "w", encoding="utf-8") as output:
        for replicate in range(1, args.replicates + 1):
            for position, item in enumerate(orders[(replicate - 1) % len(orders)]):
                if item == "km":
                    command = km_command(replicate, position)
                elif item == "k1":
                    command = konclude_command(1, replicate, position)
                else:
                    command = konclude_command(16, replicate, position)
                execute(command, output)
    os.remove(local)


if __name__ == "__main__":
    main()
