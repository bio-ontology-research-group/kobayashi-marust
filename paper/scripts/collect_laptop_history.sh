#!/usr/bin/env bash
# Collect the narrow, non-credential laptop evidence needed for the KM Methods
# chronology. Run this on the original laptop, not on the workstation.

set -euo pipefail
umask 077

usage() {
  echo "usage: $0 OUTPUT_DIR [ORIGINAL_REPOSITORY]" >&2
  echo "default repository: \$HOME/Documents/papers/neuro-symbolic-independence" >&2
  exit 2
}

[[ $# -ge 1 && $# -le 2 ]] || usage
output=$1
repository=${2:-"$HOME/Documents/papers/neuro-symbolic-independence"}
cutoff=2026-06-02T00:00:00Z

[[ ! -e "$output" ]] || {
  echo "refusing to overwrite existing output: $output" >&2
  exit 1
}
mkdir -p "$output"/{git,memory,inventories,agentsview}
output=$(realpath "$output")

{
  echo "KM laptop-history evidence"
  echo "collection_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "cutoff_utc=$cutoff"
  echo "original_repository=$repository"
  echo
  echo "This collection intentionally omits credentials and raw agent sessions."
  echo "The git bundle and named KM memory files are substantive evidence."
  echo "The session inventory contains only path, timestamp, size, and SHA-256."
  echo "Review every file before transfer. Do not add credentials or unrelated conversations."
} > "$output/README.txt"

if git -C "$repository" rev-parse --git-dir >/dev/null 2>&1; then
  git -C "$repository" bundle create "$output/git/neuro-symbolic-independence.bundle" --all
  git -C "$repository" show-ref > "$output/git/show-ref.txt"
  git -C "$repository" log --all --date=iso-strict --format='%H%x09%aI%x09%an%x09%s' \
    --before="$cutoff" > "$output/git/pre-cutoff-commits.tsv"
  git -C "$repository" status --short --untracked-files=all \
    > "$output/git/working-tree-status.txt"
else
  echo "repository_not_found=true" >> "$output/README.txt"
fi

# Copy only explicitly named KM auto-memory records. Keep their source roots
# separate so case-sensitive ~/.Codex and ~/.codex layouts cannot collide.
for root_name in .Codex .codex; do
  root="$HOME/$root_name/projects"
  [[ -d "$root" ]] || continue
  while IFS= read -r -d '' source; do
    relative=${source#"$HOME/"}
    destination="$output/memory/$relative"
    mkdir -p "$(dirname "$destination")"
    cp --preserve=timestamps "$source" "$destination"
  done < <(find "$root" -type f \
    \( -name 'project_km_*' -o -name 'feedback_no_heavy_laptop*' \) -print0)
done

# Raw conversations stay on the laptop by default. Inventory only files whose
# path or text mentions the project, and suppress content and machine identity.
inventory="$output/inventories/km-session-candidates.tsv"
printf 'source_root\trelative_path\tmtime_utc\tbytes\tsha256\n' > "$inventory"
for root_name in .Codex .codex .claude; do
  root="$HOME/$root_name/projects"
  [[ -d "$root" ]] || continue
  while IFS= read -r -d '' source; do
    relative=${source#"$root/"}
    if [[ "$relative" =~ [Kk]obayashi|[Mm]arust|(^|/)km([^[:alnum:]]|$) ]] || \
       LC_ALL=C grep -IliqE 'Kobayashi-MaRust|kobayashi.marust|Sequoia.*reasoner|ORE 2015' "$source"; then
      mtime=$(date -u -r "$source" +%Y-%m-%dT%H:%M:%SZ)
      bytes=$(stat -c %s "$source")
      digest=$(sha256sum "$source" | awk '{print $1}')
      printf '%s\t%s\t%s\t%s\t%s\n' "$root_name/projects" "$relative" \
        "$mtime" "$bytes" "$digest" >> "$inventory"
    fi
  done < <(find "$root" -type f -not -path '*/credentials/*' \
    -not -name '*.sqlite*' -print0)
done

# Inventory likely untracked pre-standalone source/design files without copying
# their contents. The git bundle already contains every tracked revision.
if [[ -d "$repository" ]]; then
  candidates="$output/inventories/prehistory-worktree-candidates.tsv"
  printf 'relative_path\tmtime_utc\tbytes\tsha256\n' > "$candidates"
  while IFS= read -r -d '' source; do
    relative=${source#"$repository/"}
    if [[ "$relative" =~ [Kk]obayashi|[Mm]arust|(^|/)km([^[:alnum:]]|$) ]] || \
       LC_ALL=C grep -IliqE 'Kobayashi-MaRust|Sequoia.*reasoner|ORE 2015|Lean certification' "$source"; then
      printf '%s\t%s\t%s\t%s\n' "$relative" \
        "$(date -u -r "$source" +%Y-%m-%dT%H:%M:%SZ)" \
        "$(stat -c %s "$source")" "$(sha256sum "$source" | awk '{print $1}')" \
        >> "$candidates"
    fi
  done < <(find "$repository" -type f -not -path '*/.git/*' \
    -not -path '*/target/*' -not -path '*/.lake/*' \
    -not -path '*/node_modules/*' -print0)
fi

(cd "$output" && find . -type f ! -name SHA256SUMS -print0 | sort -z | \
  xargs -0 sha256sum > SHA256SUMS)
echo "COLLECTION_OK $output"
