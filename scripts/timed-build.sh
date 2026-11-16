#!/usr/bin/env bash
set -euo pipefail
LOG="${LEANASM_TIMING_LOG:-.lake/build-timings.jsonl}"
mkdir -p "$(dirname "$LOG")"
START_NS=$(date +%s%N)
lake build -v "$@" 2>&1 | tee /tmp/lake_last_build.log
END_NS=$(date +%s%N)
ELAPSED_MS=$(( (END_NS - START_NS) / 1000000 ))
COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
BRANCH=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")
BUILT=$(grep -c '^✔ \[' /tmp/lake_last_build.log || true)
printf '{"ts":"%s","branch":"%s","commit":"%s","args":"%s","built_jobs":%d,"elapsed_ms":%d}\n' \
  "$(date -Iseconds)" "$BRANCH" "$COMMIT" "$*" "$BUILT" "$ELAPSED_MS" >> "$LOG"
echo "[timing] built_jobs=${BUILT} elapsed=${ELAPSED_MS}ms (logged to ${LOG})"
