#!/usr/bin/env python3
"""Read Konclude's post-preprocessing expressivity and stop before classification.

Konclude prints the structure-summary code after preprocessing.  Waiting for a
possibly 240-second classification merely to collect that code would confound
the expressivity validation with reasoner coverage, so this probe terminates the
process group as soon as the official line is durable on disk.
"""

import argparse
import json
import os
import re
import signal
import subprocess
import tempfile
import time


EXPRESSION = re.compile(rb"expressiveness '([^']+)'")


def process_group_rss(pgid, page_size):
    total = 0
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/stat", encoding="ascii") as handle:
                fields = handle.read().split()
            if int(fields[4]) == pgid:
                total += int(fields[23]) * page_size
        except (OSError, IndexError, ValueError):
            pass
    return total


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True)
    parser.add_argument("--ontology", required=True)
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument("--memcap-mb", type=int, default=20480)
    args = parser.parse_args()

    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = "/ibex/scratch/hohndor/km:" + env.get(
        "LD_LIBRARY_PATH", ""
    )
    tmp = os.environ.get("SLURM_TMPDIR") or tempfile.gettempdir()
    tag = f"kon-expr-{os.getpid()}"
    stdout_path = os.path.join(tmp, tag + ".stdout")
    taxonomy_path = os.path.join(tmp, tag + ".owl")
    start = time.monotonic()
    peak = 0
    expression = None
    status = "running"
    page_size = os.sysconf("SC_PAGE_SIZE")
    cap = args.memcap_mb * 1024 * 1024

    with open(stdout_path, "wb") as stdout_handle:
        proc = subprocess.Popen(
            [
                args.binary,
                "classification",
                "-w",
                "1",
                "-v",
                "-i",
                args.ontology,
                "-o",
                taxonomy_path,
            ],
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=stdout_handle,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
        pgid = os.getpgid(proc.pid)
        offset = 0
        buffered = b""
        while proc.poll() is None:
            peak = max(peak, process_group_rss(pgid, page_size))
            try:
                with open(stdout_path, "rb") as reader:
                    reader.seek(offset)
                    chunk = reader.read()
                    offset += len(chunk)
            except OSError:
                chunk = b""
            if chunk:
                buffered = (buffered + chunk)[-8192:]
                match = EXPRESSION.search(buffered)
                if match:
                    expression = match.group(1).decode("ascii", "replace")
                    status = "ok"
                    break
            elapsed = time.monotonic() - start
            if elapsed > args.timeout:
                status = "timeout"
                break
            if peak > cap:
                status = "memout"
                break
            time.sleep(0.04)
        if expression is None:
            # Tiny ontologies can finish between two 40 ms samples. Read the
            # durable final log once before classifying that normal exit as an
            # error.
            try:
                with open(stdout_path, "rb") as reader:
                    match = EXPRESSION.search(reader.read())
            except OSError:
                match = None
            if match:
                expression = match.group(1).decode("ascii", "replace")
                status = "ok"
            elif proc.poll() is not None:
                status = "error"
        try:
            os.killpg(pgid, signal.SIGKILL)
        except OSError:
            pass
        proc.wait()

    record = {
        "ont": os.path.basename(args.ontology),
        "status": status,
        "expressivity": expression,
        "preprocess_wall_s": round(time.monotonic() - start, 4),
        "peak_mb": round(peak / 1024 / 1024, 2),
        "host": os.uname().nodename,
    }
    print(json.dumps(record, sort_keys=True))
    for path in (stdout_path, taxonomy_path):
        try:
            os.remove(path)
        except OSError:
            pass


if __name__ == "__main__":
    main()
