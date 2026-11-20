# Review and verification

This file collects, for the whole repository, what was checked and how. The Lean project in
[`lean/`](lean/) has its own, more detailed documents:

| Document | Content |
| --- | --- |
| [`lean/docs/COVERAGE_LEDGER.md`](lean/docs/COVERAGE_LEDGER.md) | every assertion of the paper → Lean declaration and status (106 rows) |
| [`lean/docs/ARTICLE_AUDIT.md`](lean/docs/ARTICLE_AUDIT.md) | mathematical read-through of the paper and its delicate points |
| [`lean/docs/ARCHITECTURE.md`](lean/docs/ARCHITECTURE.md) | modules, definitions, the Challenge/Solution design |
| [`lean/docs/MATHLIB_GAPS.md`](lean/docs/MATHLIB_GAPS.md) | classical theorems absent from Mathlib, and which are now proved here |
| [`lean/reports/verification_report.md`](lean/reports/verification_report.md) | the verification report reproduced below |
| [`lean/reports/ai_adversarial_review.md`](lean/reports/ai_adversarial_review.md) | the AI reviews (adversarial reviewer; sceptic and referee) and the responses |
| [`lean/formalization.yaml`](lean/formalization.yaml) | Palomar metadata, with one alignment entry per compared statement |

## Coverage in one table

| Part of the paper | Status |
| --- | --- |
| Section 1 (the hierarchy) | compared |
| Section 2 (Definition 2.1 to Corollary 2.15) | compared, all items |
| Classical facts of the conventions | compared, except the Hahn–Mazurkiewicz theorem (not needed) |
| Section 3 and the Appendix ($E(K)$) | **not formalized** (example) |
| Remark 3.7 (Curtis) | the implication is compared; Curtis's space is not formalized |
| Section 4 (the space $G$) | compared: Theorems 4.5 and 4.11, Propositions 4.7 and 4.9, Remarks 4.10 and 4.13, Corollary 4.12, null fans; Lemmas 4.2–4.8 proved in the library |
| Section 5 | Lemma 5.2 and the Section 5.1 translation compared; van Douwen's space **not formalized** (example) |
| Section 6 (cones) | compared, all items, Corollary 6.4 in full |
| Section 7 | compared; Example 7.3 and the strictness claims that need $E(K)$ or $\mathsf cZ$ **not formalized** |

## Verification report (2026-11-17)

The evidence for this report is in `lean/logs/verify-20261117T144600Z/`: `provenance.txt`, `steps.tsv`,
and one log per step. These were produced by `ALLOW_NO_SANDBOX=1 bash scripts/verify_all.sh` on
the delivered sources (Lean sources and configuration hash `9b6ed277…40702`, in
`provenance.txt`). The machine-readable form of this report is `lean/reports/summary.json`. The
evidence of the earlier run (32 statements) is kept in `lean/logs/superseded/`.

### The five statuses

| Status | Result |
|---|---|
| **Lean build passed** | **yes** |
| **Comparator passed** | **yes, unsandboxed only**, all 70 statements. bubblewrap is not installed in the workspace, so every Comparator run used `--inadvisably-no-sandbox`. No sandboxed Comparator run has happened. |
| **Independent kernel checks passed** | **not fully**; see the table below |
| **Locally prepared for submission** | **no**. There is no remote and no commit. No sandboxed run has been made on the commit to be submitted. The CONFIRM fields of `formalization.yaml` are unconfirmed. |
| **Registered by Palomar** | **yes** (since 20 November 2026). Nothing had been pushed or submitted when this report was written. Update, 20 November 2026: submitted as `p5uwkylf4s8p` (commit `5037400`, branch `palomar`); Palomar's sandboxed verification [completed successfully](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/44668068779); the automated review identified no problems; registered as [PALOMAR-2026-11-20-000009 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-20-000009&version=1). |

Results of the independent kernel checks:

| Check | Declarations | Result |
|---|---|---|
| Comparator `--paranoid` on the Solution closure | 21,708 | accepted by the Lean paranoid checker, lean4lean, NanoDa, con-leche, con-ron and the Lean default kernel (unsandboxed) |
| `lake check --paranoid` on the whole project export | 296,805 | accepted by the Lean paranoid checker, lean4lean, con-leche, con-ron and the Lean default kernel; **NanoDa was killed with exit 137** (out of memory: about 8 GB RAM, no swap), so this step is recorded as **failed** |

### The seven checks

| # | Check | Step(s) | Exit | Result |
|---|---|---|---|---|
| 0 | Static source checks | `00-sources` | 0 | passed: 31 Lean files, every file has a `module` header, no forbidden token, Challenge imports only Mathlib. One warning: Challenge.lean has 724 lines / 38 KiB, above the 300-line / 32 KiB review preference (hard limits 1,000 lines / 100 KiB) |
| 1 | Clean build | `01-clean`, `01-build`, `01-build-challenge` | 0 | passed: the project's `.lake/build` was deleted and all 28 library modules, Solution and Challenge were rebuilt ("Built" lines in the log). Mathlib's build products were reused. |
| 2 | Axiom audit | `02-axioms-print`, `02-axioms-check` | 0 | passed: 136 declarations (the 70 compared theorems and 66 principal library theorems) depend only on `propext`, `Quot.sound` and `Classical.choice` |
| 3 | Comparator | `03-comparator` | not-run | sandboxed form not run: bwrap absent |
| | | `03-comparator-NOSANDBOX` | 0 | passed **unsandboxed**: all 70 theorems |
| 4 | Kernel replay (`lake check`) | `04-check` | not-run | sandboxed form not run |
| | | `04-check-NOSANDBOX` | 0 | passed **unsandboxed** |
| 5 | Paranoid mode incl. NanoDa | `05-check-paranoid` | not-run | sandboxed form not run |
| | | `05-check-paranoid-NOSANDBOX` | **1** | **failed**: NanoDa ran out of memory (exit 137) on the 296,805-declaration export; the other five checkers accepted |
| | | `06-comparator-paranoid` | not-run | sandboxed form not run |
| | | `06-comparator-paranoid-NOSANDBOX` | 0 | passed **unsandboxed**: all six checkers accepted the Solution closure, NanoDa included |
| 6 | con-ron | in 5 and 7 | — | the bundled con-ron accepted, both in step 5 (whole project) and as an external kernel in step 7. **Palomar's pinned v4.36.0-rc1 con-ron was not available offline and was not run.** |
| 7 | Local equivalent of Palomar's pipeline | `07-palomar-local` | not-run | sandboxed form not run |
| | | `07-palomar-local-NOSANDBOX` | 0 | passed **unsandboxed**: protected config with `nanoda_bin` and `con-ron` as `external_kernels` |
| neg | Negative controls | `08-negative-sorry-NOSANDBOX` | 1 (expected) | rejected as expected: `Illegal axiom detected: 'sorryAx'` |
| | | `09-negative-definition-NOSANDBOX` | 1 (expected) | rejected as expected: `Const does not match between challenge and target 'MosaicSpaces.IsMetricContinuum'` |

The script exited with status 1 because of step 5. That is the correct outcome: step 5 did not
pass.

### Why the sandbox and NanoDa problems were not resolved here

- **bwrap.** The workspace has no network access, so bubblewrap could not be installed. Lake's
  sandbox cannot be emulated, so the sandboxed steps are recorded as `not-run`. They are not
  silently downgraded: the unsandboxed runs are reported separately under `-NOSANDBOX`.
- **NanoDa on the whole export.** The workspace cannot be given more memory. NanoDa did accept the
  Comparator closure of the Solution (step 6), which contains every declaration the compared
  theorems depend on.
- **What would resolve both.** The CI workflow (`.github/workflows/ci.yml`; on the branch `palomar` at the repository root) installs bubblewrap
  and runs `lean/scripts/verify_all.sh` sandboxed on a GitHub runner, which has more memory. It has
  never run, because no remote exists.

### Toolchain and tools

- **Toolchain.** Lean 4.35.0-rc2 (commit `11acb17e…`), Lake 5.0.0-src+11acb17.
- **Mathlib.** `065356127b1dc0016f66b7283ce0ce2c4055aa55` (tag v4.35.0-rc2), built from source.
- **Checker hashes.** The SHA-256 of every bundled checker executable is in `provenance.txt`.

### What is formalized

Ledger (`lean/docs/COVERAGE_LEDGER.md`, 106 rows): 59 compared, 13 proved, 5 partial, 23 not
formalized, 1 blocked, 5 documentation. All 23 not-formalized rows and the blocked row are
examples, excluded at the author's request (Section 3 and the Appendix, Section 5's van Douwen
space, Example 7.3). The 5 partial rows are:

| Row | What is missing |
|---|---|
| C-1 (classical facts) | the Hahn–Mazurkiewicz theorem itself; no formalized result uses it |
| C-Q1 | the article's route through `E(K)` (an example); Q1a/Q1b are answered via `𝖼G` |
| R-curtis (Remark 3.7) | Curtis's example (cited, unverified in the article); the implication is compared |
| S-fst (Section 5.1) | the space HE (cited); the translation is compared |
| T-chain-strict (Thm 7.4) | (H) ⇏ (QC), (LC) ⇏ (LmS), (H) ⇏ LAC, which need `E(K)` and `𝖼Z` (examples) |

| Item | Status |
|---|---|
| Q3 | answered as asked (`answer_Q3`): Tychonoff, locally arcwise connected, not a quasi-curve space, not path-determined |
| Q2 | Corollary 6.4 in full (`answer_Q2`) |
| Q1a, Q1b | answered via the cone over `G` (`answer_Q1a`, `answer_Q1b`) |
| Classical theory built here | the arc theorem; compact locally connected metrizable ⇒ locally path connected; boundary bumping; the fan metric |
| Not formalized | examples (see above); Hahn–Mazurkiewicz |

### Review

`lean/reports/ai_adversarial_review.md` records two rounds of review by separate Claude agents with
fresh contexts and read-only snapshots. They are AI reviews and **not** independent human reviews.

- **Round 1** (32 statements) found documentation problems, which were fixed.
- **Round 2.** A sceptic and a referee reviewed the 54-statement snapshot.
  - The sceptic found one medium problem: the Proposition 4.9 statement was not tied to `G`. This
    was fixed by merging it into `theorem_4_11`.
  - The referee asked for a minor revision: stale docstrings and more compared statements. Both
    were done.
- **Re-check.** The sceptic re-checked the 69-statement snapshot and judged every fix adequate. It
  raised one new low-severity point (`IsSeparable` versus a separable subspace), which was then
  fixed.

The last few edits were not re-reviewed by an agent. They are listed at the end of that file, and
the Comparator and axiom runs above cover them. No human has reviewed the Lean code.

### AI involvement

| Task | Models |
|---|---|
| Lean sources, scripts and documents | Claude Fable 5.2 (preparation session); Claude Opus 5.5 (sessions of 2026-11-16/17) |
| Reviews | Claude Opus 5.5 subagents (adversarial reviewer, sceptic, referee) |
| Article (per its disclosure) | Claude Fable 5.2 and ChatGPT Astra |
