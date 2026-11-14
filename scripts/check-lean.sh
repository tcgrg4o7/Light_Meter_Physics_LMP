#!/usr/bin/env bash
# Run each project's existing instructions, then enforce the repository audit policy.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m unittest discover -s scripts -p 'test_audit_lean.py'
logs="$(mktemp -d)"
trap 'rm -rf "$logs"' EXIT
while IFS= read -r project; do
  [[ -z "$project" || "$project" == \#* ]] && continue
  echo "::group::Checking $project"
  python3 scripts/audit_lean.py source "$project"
  bash "$project/check.sh" 2>&1 | tee "$logs/$(basename "$(dirname "$project")").log"
  python3 scripts/audit_lean.py log "$project" "$logs/$(basename "$(dirname "$project")").log"
  echo "::endgroup::"
done < scripts/lean-projects.txt
