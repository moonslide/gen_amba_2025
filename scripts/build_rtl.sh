#!/usr/bin/env bash
set -euo pipefail

PROJECT="$(dirname "$0")/../project.json"
OUTDIR="$(dirname "$0")/../out"
LOGDIR="$(dirname "$0")/../logs"
mkdir -p "$LOGDIR"

BUILD_ID="bd_$(date -u +%Y%m%d_%H%M)_$RANDOM"
echo "Starting RTL build $BUILD_ID" >> "$LOGDIR/batch.log"
python3 "$(dirname "$0")/../axi4gen.py" -c "$PROJECT" -o "$OUTDIR" --log-format json --log-file "$LOGDIR/build.jsonl" gen-rtl
RET=$?
echo "Exit: $RET (build_id=$BUILD_ID)" >> "$LOGDIR/batch.log"
exit $RET