#!/usr/bin/env bash
# verify_all.sh -- run every verification step and keep the evidence.
#
# Requirements: Linux x86_64, the toolchain named in lean-toolchain (elan, or its bin/ on PATH),
# python3, a populated .lake (Mathlib built or `lake exe cache get` run beforehand; this script
# does not use the network), and bubblewrap (`bwrap`) for the sandboxed Comparator / check steps.
#
# Sandbox policy. `lake comparator` and `lake check` sandbox the project with bwrap. If bwrap is
# absent, the sandboxed steps are recorded as "not-run". Only if the caller sets
# ALLOW_NO_SANDBOX=1 are the same steps additionally run with `--inadvisably-no-sandbox`; those
# steps carry the suffix "-NOSANDBOX" in their names and must never be reported as sandboxed runs.
#
# Each step writes <out>/<step>.log and one line to <out>/steps.tsv:
#   step <TAB> exit code <TAB> seconds <TAB> command
# Nothing is ever recorded as passed unless its command exited 0. The negative controls are
# expected to FAIL; their recorded exit code is that of the comparator run, and the summary line
# states whether the failure happened with the expected message.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
out="$root/logs/verify-$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$out"
steps="$out/steps.tsv"
: > "$steps"

run() {  # run <name> <command...>
  local name=$1; shift
  local start=$SECONDS
  echo "== $name: $*"
  "$@" > "$out/$name.log" 2>&1
  local code=$?
  printf '%s\t%s\t%s\t%s\n' "$name" "$code" "$((SECONDS - start))" "$*" >> "$steps"
  return 0
}
skip() { printf '%s\tnot-run\t0\t%s\n' "$1" "$2" >> "$steps"; echo "== $1: NOT RUN ($2)"; }

prefix=$(lean --print-prefix 2>/dev/null || true)

# --- provenance
{
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "uname=$(uname -srm)"
  echo "git_head=$(git rev-parse HEAD 2>/dev/null || echo 'not a git checkout')"
  echo "lean_toolchain=$(tr -d '[:space:]' < lean-toolchain)"
  lean --version 2>&1 | sed 's/^/lean_version=/'
  lake --version 2>&1 | sed 's/^/lake_version=/'
  echo "lean_prefix=$prefix"
  for t in lake lean leanexport leanchecker leanchecker-paranoid lean4lean nanoda_bin con-leche con-ron; do
    if [ -x "$prefix/bin/$t" ]; then echo "sha256 $t $(sha256sum "$prefix/bin/$t" | cut -d' ' -f1)"; else echo "absent $t"; fi
  done
  command -v bwrap >/dev/null 2>&1 && bwrap --version || echo "bwrap=absent"
  echo "mathlib_rev=$(python3 -c 'import json;print([p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"]=="mathlib"][0])')"
  echo "source_sha256=$(find . -path ./.lake -prune -o -path ./logs -prune -o -type f \( -name '*.lean' -o -name 'lakefile.toml' -o -name 'lake-manifest.json' -o -name 'lean-toolchain' -o -name 'comparator.json' \) -print | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -d' ' -f1)"
} > "$out/provenance.txt" 2>&1

# 0. static source checks (no project code runs)
run 00-sources python3 scripts/check_sources.py "$root"

# 1. clean build of this project's own modules (Mathlib's build products are kept)
run 01-clean rm -rf .lake/build
run 01-build lake build
run 01-build-challenge lake build Challenge

# 2. declaration-level axiom audit
run 02-axioms-print lake env lean scripts/axioms.lean
run 02-axioms-check sh -c "python3 scripts/check_axioms.py < '$out/02-axioms-print.log'"

palomar_cfg() {  # write a Comparator config as Palomar's template script does
  python3 - comparator.json "$1" "$prefix" <<'PY'
import json, pathlib, sys
src, dst, prefix = sys.argv[1:]
c = json.loads(pathlib.Path(src).read_text(encoding="utf-8"))
assert "external_kernels" not in c, "external_kernels is not a submitter field"
c.pop("enable_nanoda", None)
c["external_kernels"] = {"nanoda": [f"{prefix}/bin/nanoda_bin"], "con-ron": [f"{prefix}/bin/con-ron"]}
pathlib.Path(dst).write_text(json.dumps(c, indent=2) + "\n", encoding="utf-8")
PY
}

negative_controls() {  # negative_controls <extra comparator flags...>
  local sfx=$1; shift
  cp Solution.lean "$out/Solution.lean.orig"; cp Challenge.lean "$out/Challenge.lean.orig"
  python3 - <<'PY'
p = "Solution.lean"; s = open(p, encoding="utf-8").read()
old = "theorem prop_2_7_t2 [T2Space X] [SequentialSpace X] : IsMosaicSpace X := isMosaicSpace_of_t2"
assert old in s
open(p, "w", encoding="utf-8").write(s.replace(old, old.replace(" : IsMosaicSpace X := isMosaicSpace_of_t2", " : IsMosaicSpace X := sorry")))
PY
  run "08-negative-sorry$sfx" lake comparator "$@"
  cp "$out/Solution.lean.orig" Solution.lean
  python3 - <<'PY'
p = "Challenge.lean"; s = open(p, encoding="utf-8").read()
old = "  IsCompact K ∧ IsConnected K ∧ MetrizableSpace K\n"
assert old in s
open(p, "w", encoding="utf-8").write(s.replace(old, "  IsCompact K ∧ IsConnected K\n", 1))
PY
  run "09-negative-definition$sfx" lake comparator "$@"
  cp "$out/Challenge.lean.orig" Challenge.lean
  cmp -s Solution.lean "$out/Solution.lean.orig" && cmp -s Challenge.lean "$out/Challenge.lean.orig" \
    || echo "ERROR: sources not restored after negative controls" | tee -a "$out/restore-error.txt"
  [ -f "$out/restore-error.txt" ] || rm -f "$out/Solution.lean.orig" "$out/Challenge.lean.orig"
}

cfg=$(mktemp); palomar_cfg "$cfg"
if command -v bwrap >/dev/null 2>&1; then
  run 03-comparator lake comparator --config comparator.json
  run 04-check lake check
  run 05-check-paranoid lake check --paranoid
  run 06-comparator-paranoid lake comparator --config comparator.json --paranoid
  run 07-palomar-local lake comparator --config "$cfg"
  negative_controls "" --config comparator.json
else
  for s in 03-comparator 04-check 05-check-paranoid 06-comparator-paranoid 07-palomar-local; do
    skip "$s" "bwrap not installed: sandboxed run impossible"
  done
  if [ "${ALLOW_NO_SANDBOX:-0}" = 1 ]; then
    run 03-comparator-NOSANDBOX lake comparator --config comparator.json --inadvisably-no-sandbox
    run 04-check-NOSANDBOX lake check --inadvisably-no-sandbox
    run 05-check-paranoid-NOSANDBOX lake check --paranoid --inadvisably-no-sandbox
    run 06-comparator-paranoid-NOSANDBOX lake comparator --config comparator.json --paranoid --inadvisably-no-sandbox
    run 07-palomar-local-NOSANDBOX lake comparator --config "$cfg" --inadvisably-no-sandbox
    negative_controls "-NOSANDBOX" --config comparator.json --inadvisably-no-sandbox
  fi
fi
rm -f "$cfg"

echo; echo "Summary ($steps):"; column -t -s $'\t' "$steps" 2>/dev/null || cat "$steps"
for n in 08-negative-sorry 09-negative-definition; do
  for f in "$out/$n"*.log; do
    [ -f "$f" ] || continue
    case $n in
      08-*) pat="Illegal axiom detected: 'sorryAx'";;
      09-*) pat="Const does not match between challenge and target 'MosaicSpaces.IsMetricContinuum'";;
    esac
    if grep -qF "$pat" "$f"; then echo "negative control $(basename "$f" .log): rejected as expected"
    else echo "negative control $(basename "$f" .log): NOT rejected as expected"; fi
  done
done
echo "Evidence directory: $out"
# Exit status: 1 if a positive step failed or a negative control was not rejected; 2 if every run
# step succeeded but some step was not run (for example no bwrap); 0 only if everything ran and passed.
status=0
awk -F'\t' '$1 !~ /^0[89]-/ && $2 != "0" && $2 != "not-run"' "$steps" | grep -q . && status=1
for f in "$out"/08-negative-sorry*.log; do [ -f "$f" ] && ! grep -qF "Illegal axiom detected: 'sorryAx'" "$f" && status=1; done
for f in "$out"/09-negative-definition*.log; do [ -f "$f" ] && ! grep -qF "Const does not match between challenge and target 'MosaicSpaces.IsMetricContinuum'" "$f" && status=1; done
[ -f "$out/restore-error.txt" ] && status=1
[ "$status" = 0 ] && grep -qP '\tnot-run\t' "$steps" && status=2
echo "exit status: $status (0 = all steps ran and passed; 2 = some steps not run; 1 = failure)"
exit $status
