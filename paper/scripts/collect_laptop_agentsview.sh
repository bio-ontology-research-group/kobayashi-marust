#!/usr/bin/env bash
# Export aggregate, project-filtered AgentsView telemetry from the original
# laptop without syncing or exporting conversation bodies.

set -euo pipefail
umask 077

usage() {
  echo "usage: $0 OUTPUT_DIR [PROJECT_ID] [SINCE_UTC] [UNTIL_UTC]" >&2
  echo "defaults: PROJECT_ID=kobayashi_marust SINCE_UTC=2026-06-02 UNTIL_UTC=2026-07-11" >&2
  exit 2
}

[[ $# -ge 1 && $# -le 4 ]] || usage
output=$1
project=${2:-kobayashi_marust}
since=${3:-2026-06-02}
until=${4:-2026-07-11}

command -v agentsview >/dev/null 2>&1 || {
  echo "agentsview is not installed or is absent from PATH" >&2
  exit 1
}
[[ ! -e "$output" ]] || {
  echo "refusing to overwrite existing output: $output" >&2
  exit 1
}
mkdir -p "$output"
output=$(realpath "$output")

# This script never invokes `agentsview sync`. The operator must first verify
# the laptop's include-path/project configuration and perform any desired sync
# separately. `--no-sync` freezes all three reports to one existing database.
agentsview --version > "$output/version.txt"
agentsview usage daily --all --since "$since" --until "$until" \
  --timezone UTC --breakdown --no-sync --json \
  > "$output/usage-daily-all.json"
agentsview stats --include-project "$project" --since "$since" --until "$until" \
  --timezone UTC --include-one-shot --include-automated --format json \
  > "$output/stats-project.json"
agentsview activity report --project "$project" --preset custom \
  --from "${since}T00:00:00Z" --to "${until}T00:00:00Z" \
  --timezone UTC --bucket 1d --no-sync --json \
  > "$output/activity-project.json"

python3 - "$output" "$project" "$since" "$until" <<'PY'
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
project, since, until = sys.argv[2:]
reports = {}
for name in ("usage-daily-all.json", "stats-project.json", "activity-project.json"):
    path = root / name
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"AgentsView report is not a JSON object: {name}")
    reports[name] = value

for name, value in reports.items():
    rendered = json.dumps(value).lower()
    for forbidden in ("prompt_text", "response_text", "tool_result", "shell_command"):
        if forbidden in rendered:
            raise SystemExit(f"potential conversation body field in {name}: {forbidden}")

usage_projects = reports["usage-daily-all.json"].get("projects", {})
usage_labels = {entry.get("display_label") for entry in usage_projects.values()
                if isinstance(entry, dict)}
if usage_labels != {project}:
    raise SystemExit(
        "usage report is not restricted to the requested project: "
        + repr(sorted(str(value) for value in usage_labels))
    )
stats_filters = reports["stats-project.json"].get("filters", {})
included = stats_filters.get("projects_included")
if included is not None and included != [project]:
    raise SystemExit("stats report project filter differs from the requested project")

readme = f"""# Laptop AgentsView aggregate evidence

Project filter: `{project}`
UTC half-open reporting window: `{since}` through `{until}`

The workstation evidence begins on 2026-07-11. The default interval therefore
ends at that boundary and must not overlap the frozen workstation reports.
This collector invoked every reporting command with `--no-sync`; it did not
modify the AgentsView database or export prompts, responses, commands, or tool
results. Review the JSON and project identity before transfer.
"""
(root / "README.md").write_text(readme, encoding="utf-8")
PY

(cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | \
  xargs -0 sha256sum > SHA256SUMS)
(cd "$output" && sha256sum -c SHA256SUMS)
printf 'LAPTOP_AGENTSVIEW_COLLECTION_OK\t%s\t%s\t%s\n' "$project" "$since" "$until"
