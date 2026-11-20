#!/usr/bin/env python3
"""Parse the output of `lake env lean scripts/axioms.lean` (stdin) and fail unless every
declaration depends only on propext, Quot.sound and Classical.choice."""
import re, sys
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
text = sys.stdin.read()
n, bad = 0, []
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
    n += 1
    axs = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    if not axs <= ALLOWED:
        bad.append((m.group(1), sorted(axs - ALLOWED)))
expected = sum(1 for l in open("scripts/axioms.lean") if l.startswith("#print axioms"))
print(f"declarations audited: {n} (expected {expected})")
for d, a in bad:
    print(f"FORBIDDEN AXIOMS in {d}: {a}")
if bad or n != expected:
    sys.exit(1)
print("all audited declarations use only propext, Quot.sound, Classical.choice")
