# Pushing the repository and selecting the commit to submit

The repository is https://github.com/LucasAlves8Sp/Mosaic-spaces (public; pushed 2026-11-20).
Branch `main` holds the paper and this project under `lean/`; branch `palomar` holds this project
at the repository root with the Apache-2.0 `LICENSE`, which is the layout Palomar requires. The
steps below are kept for reference.

## 1. Create the repository and push

```
cd mosaic-spaces
git init -b main
git add -A                      # .gitignore excludes .lake/; logs/ (evidence, ~0.5 MB) is committed
git status                      # check: no .lake, no build products, no credentials
git commit -m "Mosaic spaces: Lean formalization"
git remote add origin https://github.com/<owner>/<repository>.git    # supplied by the author
git push -u origin main
```

## 2. Verify the exact commit

On Linux with bubblewrap, from a **fresh clone** of the pushed commit, run:

```
git clone https://github.com/<owner>/<repository>.git && cd <repository>
lake exe cache get
bash scripts/verify_all.sh      # do NOT set ALLOW_NO_SANDBOX
echo $?                         # must be 0
```

Alternatively, let the CI workflow run. Its `comparator` job runs the same script sandboxed and
uploads the logs.

Then record the commit:

1. Run `git rev-parse HEAD` and note the full 40-character SHA.
2. Write that SHA into `reports/summary.json` (`git_commit`), together with the name of the log
   directory of that run.

The verified commit and the submitted commit must be the same SHA. Any later commit, including a
documentation-only fix, needs a new verification run.

## 3. Before submitting

- The author confirms the CONFIRM fields of `formalization.yaml`: authors, maintainers, licence
  and endorsement.
- The repository is public on GitHub, with the licence file at the root matching
  `project.license`.
- `README.md` and `formalization.yaml` state the scope: the examples (Section 3 and the
  Appendix, van Douwen's space, Example 7.3) and the Hahn–Mazurkiewicz theorem are not formalized.

## 4. Submit

Submit the verified SHA at https://submit.palomar-registry.org/ .

Palomar's own verification and its registration are later, separate steps. "Locally prepared for
submission" is not "registered by Palomar". Add registration details to the repository only after
Palomar reports success.
