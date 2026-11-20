# Palomar requirements digest

Read on 2026-11-16 (UTC). Sources are primary: the registry's own pages and repositories and the
Lean source tree. Where a page could only be read through a web fetch (the shell in the build
session could not reach `palomar-registry.org`), that is said.

## Revisions consulted

| Source | Revision / date | How read |
|---|---|---|
| `PalomarRegistry/PalomarPolicy` (binding policy, `CONTRIBUTING.md`, `docs/specification.md`) | `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`, 2026-10-22 | git clone |
| `PalomarRegistry/PalomarTemplate` (starter repository, `formalization.yaml` template) | `2891de4c48955af824969a263d31b25e7a9a1406`, 2026-09-28 | git clone |
| `PalomarRegistry/PalomarSubmission` (verification pipeline, `toolchains.json`, `checker-revisions.json`, `verification-profile.json`, `allowed-challenge-repositories.json`) | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, 2026-10-28 | git clone |
| `leanprover/comparator` (README; deprecated in favour of `lake comparator`) | `865edc14486c3388e9225daa971da8e157488c3e`, 2026-10-14 | git clone |
| `leanprover/lean4` tag `v4.35.0` (`src/lake/Lake/CLI/Help.lean`, `Check.lean`, `Main.lean`) | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | git sparse clone |
| `ammkrn/nanoda_lib` | `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, 2026-11-07 | git clone |
| `mathlib-initiative/formalization.yaml` (metadata standard) | `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`, 2026-08-25 | git clone |
| `leanprover-community/mathlib4` tag `v4.35.0` | `56a005855ea17e0b0958f73ec801ae140b0a1679` | git clone |
| https://palomar-registry.org/how-to-submit | page as served 2026-11-16; no revision date on the page | web fetch (summarised by the fetch tool) |
| https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/ | 2026-10-15 | web fetch |

## Files a submission must contain

- Exactly one of `lakefile.toml` / `lakefile.lean`; a committed `lake-manifest.json` (required for
  `lakefile.lean`, strongly recommended otherwise; `lake comparator` itself requires one).
- `lean-toolchain` pinned to a release or release candidate at or above the floor in
  `toolchains.json`: **`v4.35.0-rc2`** (that is where `lake comparator` first ships).
- A Challenge module and a Solution module (conventionally `Challenge.lean`, `Solution.lean`), named
  in the Comparator configuration; distinct dotted module names.
- A Comparator JSON configuration (conventionally `comparator.json`).
- `formalization.yaml` (the only file with a fixed name), version `v0.4`.
- One licence file at the repository root, matching one standard SPDX licence, identical to
  `project.license`. The starter template supports Apache-2.0 only.

## Lean source rules (binding: policy section 2.1)

- Every regular `.lean` file in the repository begins with a `module` header and has at most
  10,000 physical lines (blank and comment lines count). `lakefile.lean` is exempt from the header
  only. Files under `.git` and `.lake` are excluded; `.lean` symlinks are refused.
- No compiled artefacts outside `.lake`; no Git submodules; no Git LFS pointers.
- Git dependencies: credential-free `https://github.com/owner/repo` URLs pinned to full 40-character
  lowercase SHAs in `lake-manifest.json`.

## Challenge rules (policy section 2.2, 2.4)

- Hard limits 1,000 lines and 100 KiB; a mechanical warning above 300 lines or 32 KiB.
- Transitive imports may resolve only to Lean core, Mathlib (canonical repository, verified
  revision, with Mathlib's own pinned dependencies), Tau Ceti, or CSLib. Tau Ceti and CSLib mark the
  entry as having qualified statement dependencies. No project source, and not the Solution, may be
  in the Challenge's import closure.
- "Deliberate holes in Challenge declarations are allowed" (policy 2.3) and expected by the
  template: one `sorry` per advertised declaration. Comparator's README states the Challenge theorem
  may carry "a `sorry` (or any other proof)".
- Every principal claim must be stated in the Challenge; definitions need docstrings and their
  ordinary mathematical meaning; no hidden hypotheses or convenient surrogates.
- The pipeline compiles the Challenge separately, without the candidate Lake configuration, against
  frozen canonical Mathlib output, and publishes it under a per-run verifier-owned namespace.

## Comparator configuration (policy section 2.3)

Required keys: `challenge_module`, `solution_module`, `theorem_names` (nonempty array),
`permitted_axioms` (subset of `propext`, `Quot.sound`, `Classical.choice`). Optional:
`definition_names`, `enable_nanoda`. No other key is accepted; a submitted `external_kernels` is
rejected. `enable_nanoda` is ignored: the runner always registers the bundled NanoDa kernel.

Semantics (`PalomarSubmission/docs/comparator-declaration-closure.md`): each named theorem must have
the same kind and statement in both exported environments; the constants used by the statement are
followed transitively and must be identical on both sides. A `sorry` on a Challenge declaration that
is **not** named in `theorem_names` is a mismatch. The axiom pass walks the Solution proofs and
rejects any axiom outside the permitted list (so `sorryAx`, `Lean.ofReduceBool` and custom axioms are
rejected).

## What the registry runs (PalomarSubmission README)

1. Validate files, pinned commit and `formalization.yaml`.
2. Install the submitted toolchain, which brings `lake comparator`, `leanexport`, `leanchecker` and
   the bundled independent kernels.
3. Compile the Challenge against frozen canonical Mathlib (or Tau Ceti / CSLib) output.
4. Compute and verify the Challenge's transitive source closure.
5. Build the Solution under the registry's own bubblewrap sandbox, export Challenge and Solution with
   the toolchain's exporter, and judge with
   `lake comparator --challenge-from-export ... --solution-from-export ...`. Lean's kernel and the
   bundled NanoDa kernel must both accept. con-ron then replays the Solution export in a separate
   sandbox; a recognised decline is advisory, a rejection blocks.
6. Publish a machine-readable report.

Execution profile `palomar-standard-v1`: GitHub-hosted `ubuntu-24.04`, x86_64, 350-minute job
timeout, 19,800 s execution budget, at least 15,032,385,536 bytes of host memory, bubblewrap source
tag `v0.12.0`.

con-ron pin (`checker-revisions.json`): for toolchains `v4.35.0-rc2` ... `v4.35.0` the registry uses
the con-ron executable from the Lean **v4.36.0-rc1** release (commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, archive SHA-256
`26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2`, executable SHA-256
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`), not the one bundled with 4.35.

## Tool names and flags, as verified in the Lean v4.35.0 source

From `src/lake/Lake/CLI/Help.lean`:

```
lake comparator [--config <FILE>] [--challenge-from-export <FILE>]
                [--solution-from-export <FILE>] [--paranoid] [--inadvisably-no-sandbox]
lake check [--from-export <FILE>] [--paranoid] [--inadvisably-no-sandbox]
```

- `--paranoid` "also run[s] all external checkers bundled with Lean besides Lean's own kernel:
  `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche` and `con-ron`".
- The sandbox is `bwrap` (bubblewrap), which "needs either unprivileged user namespaces or to be
  installed setuid root"; override path with `COMPARATOR_BWRAP`. Linux only.
- Bundled executables (from `Check.lean` and the template script): `leanexport`, `leanchecker`,
  `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`.
- **There is no NanoDa "paranoid mode".** The string `paranoid` does not occur anywhere in
  `ammkrn/nanoda_lib` at `0da9f98`. The documented paranoid mode is Lake's `--paranoid` flag, which
  runs NanoDa among the other bundled kernels. The `"--paranoid"` in Comparator's README is an
  illustrative argument for a hypothetical `kernel_bin`, not a NanoDa option. The request
  "NanoDa verification in its documented paranoid mode" is therefore implemented as
  `lake check --paranoid` / `lake comparator --paranoid`, and reported under that name.
- Landrun and `lean4export` belong to the deprecated standalone Comparator; the supported path is
  the toolchain-bundled `lake comparator` with `bwrap` and `leanexport`.

## `formalization.yaml` minimum (policy section 3, template)

`version: "v0.4"`; `project.name`, `project.description`, `project.authors`, `project.license`,
`project.responsible_maintainers`; `classification.arxiv` (1-2 identifiers) and
`classification.msc2020` (1-8 codes); nonempty `sources`, each with a title and a `relationship` in
{`formalizes`, `adapts`, `independently-proves`, `background`, `other`}; `status` (scope, sorry
counts excluding the Challenge holes, axioms); `automation.methods`; `fidelity.divergences`;
`review.status`; `alignment`. ORCID iDs are optional and, if given, checked.

## Editorial floor (policy section 1) -- not a mechanical matter

The result as stated in the Challenge must plausibly warrant a research paper or serious research
note and have an identifiable specialist audience. Mechanical correctness is necessary, not
sufficient. Registration is a separate, permanent step after verification and review.

## Submission mechanics

Public GitHub repository; one commit identified by its full 40-character SHA; only committed and
pushed content counts; write access proved by GitHub sign-in or by a tag plus gist. Revised source
needs a new submission at a new SHA.
