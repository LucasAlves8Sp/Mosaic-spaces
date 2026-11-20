# Verification plan

These are the seven checks requested, with the exact command for each. Results are in
`reports/verification_report.md`. All checks are scripted in `scripts/verify_all.sh`, which also
runs negative controls.

| # | Check | Command (sandboxed form) | Needs |
|---|---|---|---|
| 1 | Clean Lean build | `rm -rf .lake/build && lake build && lake build Challenge` (Mathlib's build products are kept) | any OS |
| 2 | Declaration-level axiom audit | `lake env lean scripts/axioms.lean`, then `python3 scripts/check_axioms.py` (136 declarations: the 70 compared theorems and 66 principal library theorems) | any OS |
| 3 | Comparator | `lake comparator --config comparator.json` | Linux + bwrap |
| 4 | Fresh kernel replay | `lake check`: export the default targets (MosaicSpaces, Solution) and replay them with Lean's kernel | Linux + bwrap |
| 5 | NanoDa in the documented paranoid mode | `lake check --paranoid` and `lake comparator --config comparator.json --paranoid` | Linux + bwrap |
| 6 | con-ron | included in step 5 (bundled con-ron) and in step 7 (con-ron registered as an external kernel) | Linux + bwrap |
| 7 | Local equivalent of the Palomar pipeline | protected config with `nanoda_bin` and `con-ron` as `external_kernels` (as in the template's `verify-comparator.sh`), then `lake comparator --config <protected>` | Linux + bwrap |
| neg | Negative controls | (a) `sorry` in one Solution proof; (b) one definition changed in Challenge.lean. Comparator must reject both | Linux + bwrap |

On paranoid mode: Lake's `--paranoid` runs `leanchecker-paranoid`, `lean4lean`, `nanoda`,
`con-leche` and `con-ron` besides the Lean kernel. NanoDa itself has no separate "paranoid" flag.

## Sandbox policy

Without bubblewrap, the sandboxed steps are recorded as `not-run` and are never reported as
passed. With `ALLOW_NO_SANDBOX=1`, the same commands are also run with `--inadvisably-no-sandbox`.
They are logged under step names ending in `-NOSANDBOX` and must be reported as unsandboxed.

The script's exit status is:

| Exit | Meaning |
|---|---|
| 0 | every step ran and passed, and the negative controls were rejected |
| 2 | every step that ran passed, but some step did not run |
| 1 | a failure |

## What a local run cannot reproduce from Palomar's pipeline

- Palomar compiles the Challenge separately against frozen canonical Mathlib, under a per-run
  namespace.
- Palomar verifies the Challenge source closure byte for byte.
- Palomar runs con-ron with its own pinned executable (v4.36.0-rc1 for 4.35 toolchains), with
  positive and negative controls.
- Palomar builds with its own bubblewrap.

## Evidence

Each run writes the directory `logs/verify-<UTC timestamp>/` containing:

- `provenance.txt`: date, kernel, git HEAD, toolchain, Lean and Lake versions, the SHA-256 of every
  bundled checker executable, the presence of bwrap, the Mathlib revision, and a hash of the source
  tree;
- one log file per step;
- `steps.tsv`: step, exit code, seconds and command for each step.
