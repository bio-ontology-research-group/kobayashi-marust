#!/bin/bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
./tools/workspace-preflight.sh

source_root=$root/.work/inputs/baseline-src/more
expected_commit=9d29fb15352b781a3dba015696b1b269320603b2
test "$(git -C "$source_root" rev-parse HEAD)" = "$expected_commit"
test -s "$source_root/lib/RDFox/Linux/JRDFox.jar"

maven=$root/.work/inputs/apache-maven-3.9.16/bin/mvn
m2=$root/.work/target/m2-more
artifact=$root/.work/artifacts/paper-baselines/classifier-more.jar
test -x "$maven"
mkdir -p "$source_root/repo" "$m2" "$(dirname "$artifact")" \
  "$source_root/src/org/kmbenchmark"
cp paper/benchmark/runners/more/FullIriClassifier3.java \
  "$source_root/src/org/kmbenchmark/FullIriClassifier3.java"

# JDK 21 no longer accepts source level 7. Signed dependency metadata must also
# be excluded from the aggregate JAR because shading invalidates its digests.
# Neither compatibility change alters reasoner source or dependencies.
if grep -q '<source>1\.7</source>' "$source_root/pom.xml"; then
  git -C "$source_root" apply "$root/paper/benchmark/runners/more/jdk8-shade.patch"
fi
grep -q '<source>1\.8</source>' "$source_root/pom.xml"
grep -q '<exclude>META-INF/\*.SF</exclude>' "$source_root/pom.xml"

"$maven" -q -Dmaven.repo.local="$m2" deploy:deploy-file \
  -Durl="file:$source_root/repo" -DrepositoryId=project.local \
  -Dfile="$source_root/lib/RDFox/Linux/JRDFox.jar" \
  -DgroupId=uk.ac.ox.cs -DartifactId=JRDFox -Dpackaging=jar -Dversion=build2213
"$maven" -q -f "$source_root/pom.xml" -Dmaven.repo.local="$m2" \
  -DskipTests clean package
cp "$source_root/target/uber-MORe-0.2.0-SNAPSHOT.jar" "$artifact"
test -s "$artifact"
sha256sum "$artifact"
