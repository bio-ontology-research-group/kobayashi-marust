#!/bin/bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
./tools/workspace-preflight.sh

runner=$root/paper/benchmark/runners/owlapi
target=$root/.work/artifacts/paper-baselines
m2=$root/.work/target/m2-paper-baselines
mkdir -p "$target" "$m2"

for baseline in hermit jfact openllet elk whelk; do
  mvn -q -f "$runner/pom.xml" -Dmaven.repo.local="$m2" -P"$baseline" clean package
  jar="$runner/target/classifier-$baseline.jar"
  test -s "$jar"
  cp "$jar" "$target/"
done

(
  cd "$target"
  sha256sum classifier-*.jar > SHA256SUMS
  sha256sum --check SHA256SUMS
)
