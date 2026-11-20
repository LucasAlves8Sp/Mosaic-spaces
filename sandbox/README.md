# Verification sandbox

STATUS: UNTESTED design. Nothing in this directory has been executed.

## What isolates what

1. **Lake's own sandbox (official mechanism).** `lake comparator` and `lake check` build and export
   the project inside `bwrap`; the project's `.olean` files are never loaded into Lake's own
   process. This is the mechanism Lean v4.35.0 documents and the one Palomar relies on. It protects
   the judge from the project's build-time code. It does not hide the rest of the file system from
   reads, and `bwrap` "cannot narrow [the network] to particular ports" (Lake source comment).
2. **Outer container (this directory).** `Containerfile` builds an image with the pinned toolchain
   and bubblewrap. `run.sh` starts it with
   - `--network none` (no network after dependency preparation),
   - the repository mounted read-only at `/src` and copied to a tmpfs work directory, so project
     build code cannot modify the checkout, the verification scripts, or `comparator.json`,
   - the toolchain owned by root and the build run as an unprivileged user, so project code cannot
     replace `lake`, `leanchecker`, `nanoda_bin` or `con-ron`,
   - memory, CPU and process limits, no credentials, no host environment variables.
   Nested `bwrap` inside a container needs unprivileged user namespaces; with Docker's default
   seccomp profile this may require `--security-opt seccomp=unconfined` or a custom profile. That
   weakens the outer container and must be recorded in the report if used.

A directory named `sandbox` isolates nothing by itself; only (1) and (2), when actually run on
Linux, do. On Windows and macOS neither runs.

## Dependency preparation (network needed once, before the sandboxed run)

```
elan toolchain install "$(cat lean-toolchain)"
lake update          # only if lake-manifest.json is not yet committed
lake exe cache get   # downloads prebuilt Mathlib; trust in this cache is discussed in
                     # PalomarSubmission/docs/mathlib-cache-trust.md
```

## Platform and resources

Linux x86_64, kernel with unprivileged user namespaces, bubblewrap >= 0.12 (Palomar pins source tag
v0.12.0). Palomar's profile: 15 GiB host memory minimum, 20 GiB free disk, 19,800 s budget.
