# Checkpoint -- 2026-11-17 (second round)

## One-paragraph status

The Lean development builds without `sorry` and uses only the axioms `propext`, `Quot.sound`
and `Classical.choice`. `Challenge.lean` contains 70 statements, and Comparator accepted
`Solution.lean` against all of them (unsandboxed).

- **Answers.** All three questions are answered in the negative as asked: Q3 by the space `G`
  (`answer_Q3`), Q2 by Corollary 6.4 in full (`answer_Q2`), Q1a and Q1b by the cone over `G`.
- **Scope.** Every non-example result of the article is formalized: Sections 2, 4, 6 and 7, the
  classical facts they use (arc theorem; compact locally connected metrizable ⇒ locally path
  connected), boundary bumping and the null-fan metric. Not formalized: the examples (Section 3
  and the Appendix, van Douwen's space in Section 5, Example 7.3 and the Theorem 7.4 strictness
  claims that use them), excluded at the author's request; the Hahn–Mazurkiewicz theorem, which
  no formalized result needs.
- **Verification.** Every Comparator / `lake check` run was made **without** the bwrap sandbox,
  because bubblewrap is not installed in the workspace. `lake check --paranoid` on the full export
  failed because NanoDa ran out of memory; the other five checkers accepted, and NanoDa accepted
  the Comparator closure. The project was pushed to
  https://github.com/LucasAlves8Sp/Mosaic-spaces on 2026-11-20 (branch `main`: paper and `lean/`;
  branch `palomar`: the Lean project at the root, for submission). It was submitted to Palomar
  as `p5uwkylf4s8p`; Palomar's sandboxed mechanical verification completed successfully
  (https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/44668068779); the automated review identified no problems. It was registered by Palomar on 2026-11-20 as
  PALOMAR-2026-11-20-000009 v1 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-20-000009&version=1).

## What exists

| Item | State |
|---|---|
| `MosaicSpaces/**/*.lean` (28 modules, root `MosaicSpaces.lean`) | compiled, `lake build` (clean rebuild in the verification run) |
| `Challenge.lean` (70 statements, Mathlib-only imports, definitions copied verbatim) | compiled |
| `Solution.lean` | compiled; Comparator accepted (unsandboxed, also `--paranoid`) |
| `lake check` / `lake check --paranoid` (unsandboxed) | replay passed. In paranoid mode NanoDa ran out of memory on the full 296,805-declaration export, so that step failed; the other checkers accepted |
| `comparator.json` | 70 theorem names, permitted axioms `propext`, `Quot.sound`, `Classical.choice`, NanoDa on |
| Axiom audit `scripts/axioms.lean` + `scripts/check_axioms.py` | 136 declarations, all clean |
| Static checks `scripts/check_sources.py` | 0 errors (1 warning: Challenge 724 lines / 38 KiB, above the 300-line / 32 KiB review preference; hard limit 1,000 lines / 100 KiB) |
| Negative controls (sorry in Solution; changed definition in Challenge) | both rejected by Comparator |
| Coverage ledger | `docs/COVERAGE_LEDGER.md`, `ledger/coverage.json`: 59 compared, 13 proved, 5 partial, 23 not formalized (examples), 1 blocked (cited, example), 5 documentation |
| `formalization.yaml` | 70 alignment entries; fields marked CONFIRM need the author |
| CI workflow | pushed with the repository on 2026-11-20; see the Actions tab for its runs |
| AI reviews (sceptic, referee, re-check) | `reports/ai_adversarial_review.md`; findings fixed. Not a human review |

## Toolchain

`lean-toolchain` is `leanprover/lean4:v4.35.0-rc2` and Mathlib is pinned to tag `v4.35.0-rc2`
(commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`).

## Remaining work

1. Examples, if wanted later: Section 3 and Appendix A (parametric in the arcless continuum `K`;
   the existence of `K`, EXT-ARCLESS, is research-scale), van Douwen's space (Lemma 5.1,
   Proposition 5.3), Example 7.3 (needs EXT-Z).
2. The Hahn–Mazurkiewicz theorem (not needed by any formalized result).
3. A sandboxed run of `scripts/verify_all.sh` on a machine with bubblewrap and enough memory for
   NanoDa on the full export.

## Before any submission (author)

- **Repository.** Supply the destination repository; see `docs/PUSH_AND_SUBMIT.md`.
- **Sandboxed run.** Run `scripts/verify_all.sh` on a Linux machine *with bubblewrap*, or let CI
  run it. Every sandboxed step must exit 0 on the exact commit to be submitted.
- **Metadata.** Confirm the CONFIRM fields of `formalization.yaml` and the licence.
