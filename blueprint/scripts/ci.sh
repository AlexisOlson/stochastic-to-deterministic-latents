#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
task_logs="${VBP_LOG_DIR:-$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/verso-blueprint.XXXXXX")}"
mkdir -p -- "$task_logs"
echo "Build logs: $task_logs"

run_logged() {
  local label="$1"
  shift
  if [[ "$1" == lake ]] && pgrep -x 'lean|lake|lean.exe|lake.exe' > "$task_logs/active-processes.txt"; then
    echo "Lean/Lake slot occupied; wait for the existing build." >&2
    return 75
  fi
  local started=$SECONDS status
  set +e
  "$@" 2>&1 | tee "$task_logs/$label.log"
  status=${PIPESTATUS[0]}
  set -e
  printf '%s | exit=%s | seconds=%s\n' "$*" "$status" "$((SECONDS - started))" >> "$task_logs/commands.log"
  return "$status"
}

run_logged vbp-build lake exe vbp build
run_logged public-sources python3 -B scripts/public_sources.py
run_logged vbp-check lake exe vbp check
test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
test -f _out/site/html-multi/-verso-search/search-page.js
run_logged check-tiers python3 -B scripts/check_tiers.py
