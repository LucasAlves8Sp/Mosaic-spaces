#!/usr/bin/env python3
"""Static source checks. Runs nothing from the project.

Usage: python3 scripts/check_sources.py [repo_root]

Fails (exit 1) if
  * a .lean file (outside .lake/.git) lacks a `module` header, exceeds 10,000 lines, or is a symlink;
  * Challenge.lean exceeds 1,000 lines or 100 KiB (warns above 300 lines / 32 KiB);
  * a forbidden token occurs outside comments: sorry, admit, native_decide, ofReduceBool,
    `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque`, `sorryAx`
    -- except `sorry` in Challenge.lean, which is the deliberate statement hole;
  * more than one Lake configuration file exists, or lake-manifest.json / lean-toolchain is missing.
This is a lexical check; it complements, and does not replace, the axiom audit and Comparator.
"""
import pathlib, re, sys

root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
errors, warnings = [], []
FORBIDDEN = ["sorry", "admit", "native_decide", "ofReduceBool", "sorryAx", "axiom", "unsafe",
             "implemented_by", "extern", "opaque"]

def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
            continue
        out.append(text[i]); i += 1
    return "".join(out)


def check_challenge_imports(path):
    """Challenge.lean may import only Mathlib modules."""
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\s*(?:public\s+)?import\s+(\S+)", line)
        if m and not (m.group(1) == "Mathlib" or m.group(1).startswith("Mathlib.")):
            errors.append(f"Challenge.lean imports a non-Mathlib module: {m.group(1)}")

files = [p for p in root.rglob("*.lean") if ".lake" not in p.parts and ".git" not in p.parts]
for p in sorted(files):
    rel = p.relative_to(root).as_posix()
    if p.is_symlink():
        errors.append(f"{rel}: symbolic link"); continue
    raw = p.read_bytes()
    text = raw.decode("utf-8")
    nlines = len(re.split(r"\r\n|\n", text)) - (1 if text.endswith("\n") else 0)
    if nlines > 10000:
        errors.append(f"{rel}: {nlines} lines (limit 10,000)")
    code = strip_comments(text)
    if p.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
        errors.append(f"{rel}: no `module` header")
    if rel == "Challenge.lean":
        if nlines > 1000 or len(raw) > 100 * 1024:
            errors.append(f"{rel}: {nlines} lines, {len(raw)} bytes (limits 1,000 / 100 KiB)")
        elif nlines > 300 or len(raw) > 32 * 1024:
            warnings.append(f"{rel}: {nlines} lines, {len(raw)} bytes (review preference 300 / 32 KiB)")
    for tok in FORBIDDEN:
        for m in re.finditer(r"(?<![A-Za-z0-9_.'])" + re.escape(tok) + r"(?![A-Za-z0-9_'])", code):
            if tok == "sorry" and rel == "Challenge.lean":
                continue
            line = code.count("\n", 0, m.start()) + 1
            errors.append(f"{rel}:{line}: forbidden token `{tok}`")

lakes = [n for n in ("lakefile.toml", "lakefile.lean") if (root / n).exists()]
if len(lakes) != 1:
    errors.append(f"expected exactly one Lake configuration file, found {lakes}")
for need in ("lean-toolchain", "lake-manifest.json"):
    if not (root / need).exists():
        errors.append(f"missing {need}")

for w in warnings: print("warning:", w)
for e in errors: print("error:", e)
if (root / "Challenge.lean").exists():
    check_challenge_imports(root / "Challenge.lean")
print(f"checked {len(files)} Lean files: {len(errors)} error(s), {len(warnings)} warning(s)")
sys.exit(1 if errors else 0)
