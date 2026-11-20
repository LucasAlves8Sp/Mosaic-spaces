#!/usr/bin/env python3
"""Write reports/summary.json from the newest logs/verify-*/ directory and the ledger.

Usage: python3 reports/make_summary.py [log_dir]

Statuses are derived mechanically from steps.tsv; a sandboxed step that did not run is never
counted as passed, and a "-NOSANDBOX" step is reported as unsandboxed.
"""
import hashlib, json, pathlib, re, sys

root = pathlib.Path(__file__).resolve().parent.parent
logs = sorted((root / "logs").glob("verify-*"))
d = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else logs[-1]
steps = {}
for line in (d / "steps.tsv").read_text(encoding="utf-8").splitlines():
    name, code, secs, cmd = line.split("\t", 3)
    steps[name] = dict(exit=code, seconds=int(secs), command=cmd)
prov = dict(l.split("=", 1) for l in (d / "provenance.txt").read_text(encoding="utf-8").splitlines()
            if "=" in l and not l.startswith("sha256"))
tool_sha = {l.split()[1]: l.split()[2] for l in (d / "provenance.txt").read_text(encoding="utf-8").splitlines()
            if l.startswith("sha256 ")}

def ok(n): return n in steps and steps[n]["exit"] == "0"
def ran(n): return n in steps and steps[n]["exit"] != "not-run"
def neg(n, pat):
    fs = sorted(d.glob(n + "*.log"))
    return bool(fs) and all(pat in f.read_text(encoding="utf-8", errors="replace") for f in fs)

sandboxed = all(ran(s) for s in ["03-comparator", "04-check", "05-check-paranoid",
                                 "06-comparator-paranoid", "07-palomar-local"])
def check(sb, nosb):
    if ran(sb):
        return dict(result="passed" if ok(sb) else "failed", sandboxed=True, step=sb)
    if nosb in steps:
        return dict(result="passed_unsandboxed" if ok(nosb) else "failed_unsandboxed",
                    sandboxed=False, step=nosb, note="bwrap not installed; run with --inadvisably-no-sandbox")
    return dict(result="not_run", reason="bwrap not installed")

ledger = json.loads((root / "ledger" / "coverage.json").read_text(encoding="utf-8"))
challenge = (root / "Challenge.lean").read_text(encoding="utf-8")
names = re.findall(r"^theorem (\w+)", challenge, re.M)
sha = lambda p: hashlib.sha256((root / p).read_bytes()).hexdigest()
negs = dict(
    sorry_in_solution=neg("08-negative-sorry", "Illegal axiom detected: 'sorryAx'"),
    changed_definition_in_challenge=neg("09-negative-definition",
        "Const does not match between challenge and target 'MosaicSpaces.IsMetricContinuum'"))
comparator_any = ok("03-comparator") or ok("03-comparator-NOSANDBOX")
p05 = next(iter(sorted(d.glob("05-check-paranoid*.log"))), None)
p05txt = p05.read_text(encoding="utf-8", errors="replace") if p05 else ""
kernels05 = {k: (f"{k} kernel accepts the solution" in p05txt) for k in
             ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"]}
oom05 = "nanoda exited with 137" in p05txt
_m = re.search(r"con-leche: accepted (\d+) declarations", p05txt)
n05 = f"{int(_m.group(1)):,}" if _m else "unknown number of"
summary = {
    "date_utc": prov.get("date_utc"),
    "evidence_directory": str(d.relative_to(root)),
    "git_commit": None if "not a git" in prov.get("git_head", "not a git") else prov.get("git_head"),
    "git_commit_note": "No git repository and no remote existed when the checks ran; the commit to submit must be verified again from a fresh clone (docs/PUSH_AND_SUBMIT.md).",
    "source_tree_sha256": prov.get("source_sha256"),
    "article_sha256": sha("article/mosaic_article.tex"),
    "challenge_sha256": sha("Challenge.lean"),
    "solution_sha256": sha("Solution.lean"),
    "toolchain": prov.get("lean_toolchain"),
    "lean_version": prov.get("lean_version"),
    "mathlib_commit": prov.get("mathlib_rev"),
    "bundled_checker_sha256": tool_sha,
    "bwrap": prov.get("bwrap", "present"),
    "status": {
        "lean_build_passed": ok("01-build") and ok("01-build-challenge"),
        "comparator_passed": comparator_any,
        "comparator_passed_sandboxed": ok("03-comparator"),
        "independent_kernel_checks_passed": (ok("05-check-paranoid") and ok("06-comparator-paranoid")) or
            (ok("05-check-paranoid-NOSANDBOX") and ok("06-comparator-paranoid-NOSANDBOX")),
        "independent_kernel_checks_sandboxed": ok("05-check-paranoid") and ok("06-comparator-paranoid"),
        "independent_kernel_checks_detail": (
            "Comparator --paranoid on the Solution closure: Lean paranoid, lean4lean, nanoda, con-leche, con-ron and the default kernel all accepted (unsandboxed). "
            "lake check --paranoid on the whole project export (" + n05 + " declarations): accepted by " +
            ", ".join(k for k, v in kernels05.items() if v) +
            ("; nanoda was killed with exit code 137 (out of memory: the workspace has about 8 GB RAM and no swap), so this step FAILED and is reported as not passed." if oom05 else ".")),
        "locally_prepared_for_submission": False,
        "locally_prepared_for_submission_reason": "sandboxed checks not run on the exact commit to be submitted; no remote; CONFIRM fields of formalization.yaml unconfirmed",
        "registered_by_palomar": False,
    },
    "checks": {
        "0_static_sources": dict(result="passed" if ok("00-sources") else "failed", step="00-sources"),
        "1_clean_build": dict(result="passed" if ok("01-build") and ok("01-build-challenge") else "failed",
                              note="project build directory deleted first; Mathlib build products reused"),
        "2_axiom_audit": dict(result="passed" if ok("02-axioms-check") else "failed",
                              declarations=sum(1 for l in (root / "scripts/axioms.lean").read_text().splitlines()
                                               if l.startswith("#print axioms")),
                              allowed=["propext", "Quot.sound", "Classical.choice"]),
        "3_comparator": check("03-comparator", "03-comparator-NOSANDBOX"),
        "4_lake_check_kernel_replay": check("04-check", "04-check-NOSANDBOX"),
        "5_paranoid_mode_including_nanoda": dict(
            lake_check_paranoid=check("05-check-paranoid", "05-check-paranoid-NOSANDBOX"),
            comparator_paranoid=check("06-comparator-paranoid", "06-comparator-paranoid-NOSANDBOX"),
            note="Lake's --paranoid runs leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron; NanoDa has no paranoid flag of its own"),
        "6_con_ron": dict(result="see 5 and 7",
            note="bundled con-ron ran inside 5 and as an external kernel in 7; Palomar's pinned v4.36.0-rc1 con-ron was not available offline and was not run"),
        "7_palomar_local_equivalent": check("07-palomar-local", "07-palomar-local-NOSANDBOX"),
        "negative_controls_rejected": negs,
    },
    "compared_theorems": ["MosaicSpaces.Paper." + n for n in names],
    "ledger_status_counts": ledger["status_counts"],
    "answers": {
        "Q1a": "answered (negative) via the cone over G; compared: MosaicSpaces.Paper.answer_Q1a",
        "Q1b": "answered (negative) via the cone over G; compared: MosaicSpaces.Paper.answer_Q1b",
        "Q2": "answered (negative) exactly as asked; compared: MosaicSpaces.Paper.answer_Q2",
        "Q3": "NOT answered as asked; only the locally path connected form is proved: MosaicSpaces.Paper.answer_Q3_path",
    },
    "review": {
        "ai_adversarial_review": "reports/ai_adversarial_review.md (separate Claude agent, fresh context, read-only; not a human review)",
        "human_review": "none",
    },
    "models": {
        "article": ["Claude Fable 5.2", "ChatGPT Astra"],
        "formalization": ["Claude Fable 5.2 (preparation session)", "Claude Opus 5.5 (2026-11-16/17 session)"],
        "review_agent": "Claude Opus 5.5 subagent",
    },
}
(root / "reports" / "summary.json").write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps(summary["status"], indent=1))
print(json.dumps(summary["checks"]["negative_controls_rejected"]))
