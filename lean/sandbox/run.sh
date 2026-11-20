#!/usr/bin/env bash
# UNTESTED. Runs scripts/verify_all.sh inside the container with no network.
# Usage: sandbox/run.sh [docker|podman]     (from the repository root, after `lake exe cache get`)
set -euo pipefail
engine=${1:-docker}
root=$(cd "$(dirname "$0")/.." && pwd)
image=mosaic-verify:$(tr -d '[:space:]' < "$root/lean-toolchain" | tr ':/' '--')
"$engine" build -f "$root/sandbox/Containerfile" -t "$image" "$root"
mkdir -p "$root/logs"
"$engine" run --rm --network none --memory 16g --cpus 4 --pids-limit 4096 \
  --security-opt no-new-privileges \
  -v "$root":/src:ro -v "$root/logs":/out \
  --tmpfs /work:exec,size=24g,uid=1000 \
  "$image" bash -c 'cp -a /src/. /work/ && cd /work && scripts/verify_all.sh; code=$?; cp -a /work/logs/. /out/; exit $code'
