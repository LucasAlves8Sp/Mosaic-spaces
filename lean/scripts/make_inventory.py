#!/usr/bin/env python3
"""Regenerate INVENTORY.md and SHA256SUMS for the delivery archive.

Usage: python3 scripts/make_inventory.py [repo_root]

Covers every regular file except .lake/, .git/, build caches, INVENTORY.md and SHA256SUMS
themselves. Verify later with `sha256sum -c SHA256SUMS`.
"""
import hashlib, pathlib, sys

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
skip_dirs = {".lake", ".git", "__pycache__"}
skip_files = {"INVENTORY.md", "SHA256SUMS"}
files = sorted(p for p in root.rglob("*") if p.is_file()
               and not (set(p.relative_to(root).parts) & skip_dirs)
               and p.relative_to(root).as_posix() not in skip_files)
DESC = {
    "Challenge.lean": "statement file: 70 compared statements (sorry), definitions copied from the library",
    "Solution.lean": "proofs of the 70 statements from the library",
    "comparator.json": "Comparator configuration",
    "formalization.yaml": "Palomar metadata (CONFIRM fields to be confirmed by the author)",
    "lakefile.toml": "the only Lake configuration",
    "lake-manifest.json": "dependency pins",
    "lean-toolchain": "Lean toolchain pin",
    "MosaicSpaces.lean": "library root module",
    "LICENSE": "Apache-2.0 licence text",
    "README.md": "overview, status, AI disclosure",
    "CHECKPOINT.md": "current state and remaining work",
    "AGENTS.md": "rules and workflow for agents and reviewers",
    "reports/verification_report.md": "human-readable verification report",
    "reports/summary.json": "machine-readable summary",
    "reports/ai_adversarial_review.md": "review by a separate AI agent, with responses",
    "docs/COVERAGE_LEDGER.md": "coverage ledger (generated)",
    "ledger/coverage.json": "coverage ledger (generated, JSON)",
    "ledger/build_ledger.py": "ledger source",
    "article/mosaic_article.tex": "the article",
    "scripts/verify_all.sh": "runs all checks and negative controls",
}
lines, md = [], ["# Inventory", "",
    "Every file of the delivery, with size and SHA-256 (also in `SHA256SUMS`; check with "
    "`sha256sum -c SHA256SUMS`). Excluded: `.lake/` (regenerable build products and dependency "
    "checkouts) and `.git/`. No credentials are included.", "",
    "| File | Bytes | SHA-256 | Description |", "|---|---|---|---|"]
for p in files:
    rel = p.relative_to(root).as_posix()
    h = hashlib.sha256(p.read_bytes()).hexdigest()
    lines.append(f"{h}  {rel}")
    d = DESC.get(rel, "verification log" if rel.startswith("logs/") else "")
    md.append(f"| `{rel}` | {p.stat().st_size} | `{h}` | {d} |")
(root / "SHA256SUMS").write_text("\n".join(lines) + "\n", encoding="utf-8")
(root / "INVENTORY.md").write_text("\n".join(md) + "\n", encoding="utf-8")
print(len(files), "files")
