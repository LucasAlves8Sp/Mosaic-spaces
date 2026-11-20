> **Provenance of this file.** This review was produced on 2026-11-17 by a separate Claude agent,
> launched by the formalizing session with a fresh context and read-only instructions. It is an
> AI review, **not** an independent human review. It was made on a snapshot *before* the fixes
> listed in the "Response" section at the end; line numbers refer to that snapshot.

# Adversarial review: statement fidelity and honesty of claims

Snapshot: `/home/claude/review-snapshot` (Challenge.lean, Solution.lean, MosaicSpaces/, docs/, formalization.yaml).
Scope: read-only review. No build was run. I took compilation, Comparator acceptance and the axiom audit as given.
Article numbering below is worked out from the `.tex` file, where all theorem-like environments share one counter per section and equations have their own counter.

## Summary verdict

**The statements are faithful.** The 32 Challenge statements match the article results they cite, or are explicitly labelled weakenings of them.

- **Definitions.** `IsMosaicSpace` and the related class definitions are a correct intrinsic rendering of Definition 2.1. They are equivalent to it by Prop 2.3(1) and Lemma 2.2. The proved `prop_2_7` (mosaic ⇔ sequential with unique sequential limits) independently pins `IsMosaicSpace` down to the right class.
- **Vacuity.** None of the definitions is vacuous.
  - `¬ IsQuasiCurveSpace` and `¬ IsMContinuumSpace` are meaningful: the proved `prop_7_2_path` and `cor_2_9_qc` show both classes are inhabited, for example by ℝ.
  - The existential answers cannot be witnessed by a degenerate space. `IsMContinuumSpace ∅` holds, so `¬ IsMContinuumSpace U` forces `U` to be nonempty. The singleton `{x}` is a metric continuum, so the capture-failure clause in `theorem_4_10` forces `u` not to be eventually constant.
- **Questions.**
  - `answer_Q1a`, `answer_Q1b` and `answer_Q2` refute Q1a, Q1b and Q2 exactly as posed (article lines 65-68).
  - `answer_Q3_path` does **not** refute Q3 as posed. It gives a locally *path* connected space, and LPC is formally weaker than LAC. This is disclosed correctly in the Challenge header, the yaml and the ledger, with two small exceptions (finding 3).
- **Space G.** Its topology is the article's topology.

**The main problems are in the documentation, not in Lean.**

- Several status files in the snapshot are stale and contradict the ledger and the yaml. Examples: "no Lean file has been compiled" and "not a formalization yet".
- The yaml sends readers to a verification report that does not contain what the yaml says it contains.
- The theorem numbers in Challenge.lean, the yaml and the library docstrings do not match the article.
- Some ledger rows are marked `compared` although parts of their statements are not formalized.

## Findings

1. **major — stale and contradictory status documents.**
   - **Files:**
     - `README.md:8-9` says "not a formalization yet. Two Lean modules are written and have never been compiled".
     - `CHECKPOINT.md:5-7` says "none of which has been compiled … Challenge.lean, Solution.lean … not written".
     - `reports/verification_report.md:9-16` and `reports/summary.json` say "Lean build passed: No", "Comparator: Not run", "0 compiled. Direct Comparator targets: none".
     - `INVENTORY.md` lists only 2 Lean files and a `formalization.draft.yaml` that does not exist.
     - `AGENTS.md:5` describes the project as "in progress", mentions a `ci-logs/` folder that does not exist, and its checklist refers to status `compiled`, which the ledger no longer uses.
   - **Conflict:** all of this contradicts `docs/COVERAGE_LEDGER.md:5,7` (25 rows `compared`) and `formalization.yaml:79` ("Formalized and Comparator-checked: the 32 statements").
   - **False pointer:** `formalization.yaml:136-138` tells the reader to see `reports/verification_report.md` "for the checks that were run, including which ran without the bwrap sandbox, and for the result of the AI adversarial review". That report contains none of this.
   - **Checksums:** `SHA256SUMS` is stale. Nine entries mismatch, two files are missing, and Challenge.lean, Solution.lean and most of `MosaicSpaces/` are not covered at all.
   - **Toolchain:** `README.md:20` says `v4.35.0`, but `lean-toolchain` is `v4.35.0-rc2` (the yaml correctly says rc2).
   - **Fix:** regenerate the README, CHECKPOINT, verification report, `summary.json`, INVENTORY and SHA256SUMS from the current state. Make the report actually record the build, Comparator (non-bwrap, `--paranoid`) and axiom results, or remove the yaml's pointer to it.

2. **minor — theorem numbers in docstrings and yaml do not match the article.**
   - **Correct numbering in the `.tex`:**
     - Section 2: `prop:pathdet` = 2.10, `def:local` = 2.11, `prop:lav52` = 2.12, `prop:qcopen` = 2.13, `lem:lac` = 2.14, `cor:qclac` = 2.15. The local-implications display `eq:localimpl` is (2.1).
     - Section 4: `thm:tych` = 4.5, `prop:Glac` = 4.7, `lem:cut` = 4.8, `thm:G` = 4.11, `cor:Q3` = 4.12, `rem:Gprops` = 4.13.
   - **Wrong labels found:**
     - Challenge.lean cites "Definition 2.10" (l.114, 119), "Display (2.2)" (l.244), "Proposition 2.11" (l.251), "Proposition 2.12" (l.256), "Lemma 2.15" (l.260), "Theorem 4.10 and Remark 4.12(1)" (l.274) and "Corollary 4.11" (l.289).
     - `formalization.yaml` (e.g. l.84 "Theorem 4.6", l.123 "Proposition 4.8") and `MosaicSpaces/G/Capture.lean:13` ("Lemma 4.10, the cut lemma") use yet other numbers.
     - `docs/ARCHITECTURE.md:78` uses a third scheme (lav52 = 2.13).
   - **Ledger:** the ledger uses `\label` names and line ranges, which are correct.
   - **Fix:** cite `\label` names (or correct numbers) everywhere. Once the docstrings are corrected, Comparator needs to be re-run, or at least checked to confirm that docstring changes are irrelevant to it.

3. **minor — two places still overstate the Q3 result.**
   - **The overstatement:**
     - `MosaicSpaces/Answers.lean:10` says "All three questions are answered here in the negative". The same docstring, l.20-24, then says Q3 as stated is not answered.
     - `Challenge.lean:289` titles the theorem "**Answer to Q3**". The parenthesis after it does say that "arcwise" is replaced by "path".
   - **Fix:**
     - In Answers.lean, say "Q1a, Q1b and Q2 are answered; Q3 only in a weakened form".
     - In Challenge.lean, retitle to "Partial answer to Q3 (does not refute Q3 as posed: LPC is weaker than LAC)".
   - **Rest of the record is accurate:** the Challenge header (l.37-40), `formalization.yaml:19-20, 83, 221` and ledger row C-Q3 are all correct.

4. **minor — the stated obstacle for the arcwise form of Q3 is overstated.**
   - **Files:** `Challenge.lean:38-39`, `Answers.lean:21-24` and `Local.lean:12-15` say the LAC form needs "the arc theorem for Hausdorff spaces and the Hausdorff property of G".
   - **Why that is too much:** the article's route (Cor 2.6(2) ⇒ display (2.1)) does not use Hausdorffness of the ambient space. In any mosaic space the image of a path is a Peano continuum. That is already proved here as `isPeanoContinuum_range_path`, from Lemma 2.4. So LPC ⇒ LAC for every mosaic space, G included, needs only one fact: every Peano continuum (compact metrizable) is arcwise connected.
   - **Supporting evidence:** `docs/MATHLIB_GAPS.md:42-44` says exactly this ("needs EXT-ARC once").
   - **Fix:** correct the three docstrings. The gap for Q3 is a single classical theorem about compact metric spaces; the Tychonoff property of G is not needed for it.

5. **minor — ledger rows marked `compared` that contain parts which are not formalized at all.** The status legend says `compared` means the statement is in Challenge.lean.
   - **C-Q2 (l.123):** the statement includes "Hausdorff", "locally arcwise connected" and "also a counterexample to … Q3". None of these is formalized; the note concedes the first two. `answer_Q2` contains only the Q2 core. Contractibility and "not quasi-curve" are proved only in the library (`cone_G_properties`), not compared.
   - **T-chain-impl (l.130):** the statement includes "(QC) ⇒ LAC", which the note itself says is blocked.
   - **Fix:** mark both rows `partial`, or split off the unformalized parts.

6. **minor — ledger rows marked `compared` whose extra parts are proved in the library but not compared.**
   - **I-1:** the step "m-continuum ⇒ mosaic" is only `IsMContinuumSpace.isMosaicSpace`.
   - **P-cone3:** the mosaic of cones over pieces, and continuity of π.
   - **P-fc:** the tail-capture form at a point, `exists_metricContinuum_tail`. `prop_7_1` states only the consequence.
   - **L-generate:** the "is a mosaic" half has no content in the intrinsic setting, which is fine but worth a note.
   - **Fix:** make the status `compared (part)`, or note which part is compared.

7. **minor — `lemma_2_4` restricts universes** (`Challenge.lean:201`). It takes `C : Type u`, the same universe as `X`. The article quantifies over all compact metrizable `C`. The yaml note (l.152) discloses this. This is harmless in practice, but the compared form is formally weaker than the library lemma. **Fix:** use `{C : Type*}` if Comparator allows it.

8. **minor — the docstring of `theorem_4_10` does not list what is left out** (`Challenge.lean:274-278`). It says "formalized parts" but does not name the omissions:
   - Tychonoff and Hausdorff (Thm 4.11(1));
   - "arcwise" in (2);
   - the countable-spread form of Prop 4.9;
   - the second sentence of Cor 4.12 (completely regular).

   The yaml (l.216) and the ledger (T-G) do list them. **Fix:** copy the list into the Challenge docstring, because the Challenge is what reviewers read.

9. **minor — `lemma_2_15` is weaker on both sides than the article's Lemma 2.14** (`Challenge.lean:262-267`).
   - **Hypothesis:** the alternative to the sequence condition is "the piece is locally *path* connected". The article says "locally connected"; bridging the two needs EXT-PLPC. This makes the Lean hypothesis stronger.
   - **Conclusion:** "arcwise connected" and "in particular LAC" are dropped.
   - **Disclosure:** the "path-connected form" label, the yaml note (l.207) and ledger row L-lac (partial) disclose this. **No action needed beyond finding 2's renumbering.**

10. **note — the remaining statements check out against the article.** No quantifier or hypothesis problems were found in:
    - Section 2: `prop_2_3_t1`, `cor_2_6_union` (sequential + USL in place of "mosaic", equivalent by Prop 2.7), `prop_2_7`, `prop_2_7_t2`, `prop_2_7_open`, `lemma_2_8`, `cor_2_9_1`, `cor_2_9_2` ((a)-(c) TFAE plus (d)⇒(b); (c)⇒(d) is correctly listed as blocked), `cor_2_9_qc`, `display_2_2` (only the trivial direction LAC ⇒ LPC of the ⟺; labelled "the parts proved"), `prop_2_11`, `prop_2_12`.
    - Section 4: `exists_madFamily` (`IsMADFamily` is exactly AD plus (4.1), which together with AD is equivalent to maximality).
    - Section 6: `lemma_6_1` (Hausdorff dropped, which makes it stronger), `theorem_6_3_1` (for empty Y the cone is empty and the conclusion holds trivially, consistent with the article), `theorem_6_3_2` (LAC dropped, disclosed), `theorem_6_3_3`, `theorem_6_3_5`.
    - Section 7: `prop_7_1`, `prop_7_2`, `prop_7_2_path` (stronger than the article: LPC hypothesis, curve-space conclusion), and the three `theorem_7_4_*` statements (implications stated for all mosaic spaces, which is stronger).

    Theorem 6.3(4) and the two other strictness claims of Theorem 7.4 are absent. That is correctly declared in the yaml (l.85-86) and the ledger (T-cone4, T-chain-strict).

11. **note — the G construction matches the article.**
    - **Fans:** `Fan J` is the subspace of `J → ℝ` (product topology) of `[0,1]`-valued functions with at most one nonzero value. A basic neighbourhood of the centre constrains finitely many coordinates. It therefore contains every other spine entirely, plus an initial segment of each constrained spine, which is exactly (F1). Away from the centre it is locally the spine. So for countable `J` the topology equals the article's metric fan. For uncountable `J` it is the compact non-metrizable fan of the remark after Construction 4.1. The yaml (l.125-126) and ledger row F-metric honestly say the equality with φ is not proved; the argument above shows it holds.
    - **Topology of G:** it is the final topology of the injective piece maps for (P1)-(P4) (`G/Basic.lean:294-298`). The piece maps are shown to be closed embeddings with metrizable compact domains. This is the mosaic topology.
    - **Harmless deviations:** the witness `(n,i)` sits at `1/(i+1)`; `Λ_∅ = {∞}` is allowed; the arc is parametrised from ∞.
    - **What the compared statements need:** they only use mosaic, LPC, capture failure, the path finiteness clause and the non-countable neighbourhood filter of ∞. These are all proved, and none needs the Tychonoff property. The isolating neighbourhoods of the `p_D`, which Prop 4.9 needs, are proved directly (`exists_isolating_nhd`).
    - **Not proved:** G Tychonoff or Hausdorff. This matters only for Cor 4.12's second sentence and for "cG is Hausdorff" in Cor 6.4. Both are declared not formalized.

12. **note — `comparator.json` has `"definition_names": []`.** The claim that the Challenge definitions are "copied verbatim" rests on Comparator comparing every constant the theorem types depend on, transitively, between the two environments. That is how Comparator is described as working (`ARCHITECTURE.md:69-73`), and it was accepted. A reviewer who wants certainty could check that `MosaicSpaces.IsMosaicSpace` and the other definitions are compared by hash, or diff the definition blocks of Challenge.lean against `MosaicSpaces/*.lean` by hand.

13. **note — small metadata inaccuracies.**
    - `formalization.yaml:87` has `sorry_count: 0` while Challenge.lean has 32 `sorry` by design. Say "0 outside the Challenge holes".
    - `docs/MATHLIB_GAPS.md:42-47` still describes Q1 as blocked on E(K), although Q1 is now answered by the cone over G. It also says the Q2 answer depends on the word "arcwise", which it does not.
    - `docs/ARCHITECTURE.md:76-82` still lists "planned Comparator targets … not yet stated" under old names (`answer_Q3`, `answer_Q1`).


---

## Response by the formalizing session (2026-11-17)

| Finding | Action |
|---|---|
| 1 (stale documents) | `README.md`, `CHECKPOINT.md`, `AGENTS.md`, `docs/ARCHITECTURE.md`, `docs/VERIFICATION_PLAN.md`, `docs/PUSH_AND_SUBMIT.md`, `docs/MATHLIB_GAPS.md` (Q1 paragraph), `reports/verification_report.md` and `reports/summary.json` were rewritten. `INVENTORY.md` and `SHA256SUMS` were regenerated for the final archive. |
| 2 (numbering) | The article's numbers were recomputed from the shared counter. Compared theorems were renamed: `display_2_2` → `display_2_1`, `prop_2_11` → `prop_2_12`, `prop_2_12` → `prop_2_13`, `lemma_2_15` → `lemma_2_14`, `theorem_4_10` → `theorem_4_11`. Docstrings, `formalization.yaml`, the ledger and the docs were renumbered. Comparator and the full verification were rerun after the change. |
| 3 (Q3 wording) | `Answers.lean` no longer says that all three questions are answered. The Challenge docstring now reads "Partial answer to Q3 … does NOT refute Q3 as asked". The incorrect claim that the arcwise form needs the Hausdorff property of `G` was replaced, everywhere, by a reference to the arcwise form of Lemma 2.14 and EXT-ARC / EXT-PLPC. |
| 4 (ledger statuses) | C-Q2 and T-chain-impl → `partial`. I-1, P-cone3 and P-fc → `proved`, with notes naming the compared parts. |
| 5 (statement details) | The `theorem_4_11` docstring now lists what it leaves out. The `lemma_2_4` universe restriction and the `lemma_2_15`→`lemma_2_14` weakening remain disclosed as before. |
| 6 (notes) | `definition_names` stays empty, as in Palomar's template. The negative control that changes `IsMetricContinuum` in Challenge.lean is rejected (`Const does not match between challenge and target`), which shows the definitions are compared. The `sorry_count` field now carries a comment explaining the 32 statement holes. |

---

# Second round (2026-11-17, after the arc theorem, Peano local path connectedness and the remaining results)

> **Provenance.** Two separate Claude agents were launched by the formalizing session with fresh
> contexts on a read-only snapshot (`/home/claude/review-snapshot2`, 54 compared statements): a
> **sceptic** told to look for unfaithful, weakened or vacuous statements, and a **referee** told
> to judge completeness for the declared scope (examples excluded). After the fixes, the sceptic
> re-checked a second snapshot (`/home/claude/review-snapshot3`, 69 statements) by reading only.
> These are AI reviews, **not** independent human reviews. Their reports are condensed below;
> every finding is listed.

## Sceptic, first pass (snapshot2)

Checks it ran: reading every focus statement against the article; a grep of `MosaicSpaces/**` and
`Solution.lean` for `sorry`, `admit`, `native_decide`, `implemented_by`, `unsafe`, `opaque`,
`axiom`, `set_option`, `macro`, `elab`, `extern` (only docstring mentions of "axiom"); one scratch
file confirming that `mosaicTopology` has the article's closed sets.

| # | Severity | Finding |
|---|---|---|
| 1 | medium | `prop_4_9_remark_4_13_2` was a separate existential not tied to `G`; Arens' space would satisfy it. Its docstring claimed more than the statement. |
| 2 | low | `theorem_4_11` and the `answer_*` statements are existential; harmless because every witness is a counterexample, but "this is the article's G" cannot be read off. |
| 3 | low | `remark_3_7` is an implication with no exhibited instance (Curtis's space is not formalized); the docstring says so. |
| 4 | low | `IsQuotientOfIntervals` puts the index type in the universe of `X`, so `prop_2_10`'s "(c)" is narrower than the article's. |
| 5 | low | `AGENTS.md` stale (32 statements, Q3 path form only). |

Dismissed after checking: Definition 2.1 (`IsAbstractMosaic`, `mosaicTopology`), the four
`def_2_1_*`, `lemma_2_2`, `prop_2_3_1`, the path-determined definitions, the open-set forms of
local properties, `ArcwiseConnected`/`IsArc`, `lemma_2_14_article`, `cor_2_15`, the Theorem 7.4
statements, `lemma_5_2`, `theorem_6_3_4`, `theorem_6_3_2`, `answer_Q1a/b`, `answer_Q2`, the
classical facts, `arc_theorem`, `cor_2_6_2_arc`, `display_2_1_iff`, `cor_2_9_2_full`.
Uncovered (non-example) claims it listed: Lemma 2.2's "in particular" clauses; Prop. 2.3(3); Cor.
2.6(2) first sentence; Cor. 2.6(3); Remark 2.5; Hahn–Mazurkiewicz; Prop. 4.9 for the actual `G`;
Remark 4.10; Prop. 6.2; the tail forms of Props. 7.1 and 7.2; Cor. 4.12 "not path-determined".

## Referee (snapshot2)

Checks it ran: full read of the article, Challenge.lean, Solution.lean and the library statements;
a scratch file deriving Cor. 4.12's "not path-determined" and Theorem 7.4's "LAC ⇏ (H)" from the
compared statements, and `#print axioms` on eight declarations (all `[propext, Classical.choice,
Quot.sound]`). Verdict: **minor revision**. Every in-scope numbered result has a proof; the
compared statements spot-checked (12) are faithful and often slightly stronger. Requested:

1. Fix stale docstrings in `Classes.lean`, `Cone.lean` (two places), `G/Mosaic.lean`,
   `Local.lean`, `G/Capture.lean` (they said proved things were not formalized).
2. Recommended: compare the library-only results (Prop. 2.3(3), Cor. 2.6(2),(3), Prop. 6.2, full
   Thm. 6.3(5), tail forms of Props. 7.1/7.2, the `p_D` isolation clause of Thm. 4.5).
3. Add Cor. 4.12 "not path-determined" and Thm. 7.4 "LAC ⇏ (H)" as compared statements.
4. Optional: Remark 4.10; state in the Challenge header that Hahn–Mazurkiewicz is not formalized.

## Response by the formalizing session

| Finding | Action |
|---|---|
| Sceptic 1 | `prop_4_9_remark_4_13_2` removed; its content merged into one existential `theorem_4_11` with a single witness `(G, x, u, W, ι, p)`, together with Thm. 4.5's isolation of the `p_D` and a new Remark 4.10 clause. |
| Sceptic 2 | Header of `Challenge.lean` now says that statements about `G` and `𝖼G` are existential and that `theorem_4_11` packs the properties of `G` for one witness. |
| Sceptic 3 | Kept; the docstring and ledger (`R-curtis`: partial) say Curtis's example is not formalized. |
| Sceptic 4 | Added `prop_2_10_quotient`: (c) ⇒ (b) for sums indexed in any universe. |
| Sceptic 5, Referee 1 | All listed docstrings fixed, also `PathComponents.lean` and `Fan.lean`; `AGENTS.md` and the other documents rewritten. |
| Referee 2 | New compared statements: `lemma_2_2_closed`, `lemma_2_2_finite`, `prop_2_3_3`, `prop_2_3_456`, `remark_2_5`, `cor_2_6_2`, `cor_2_6_3`, `prop_6_2_1`, `prop_6_2_2`, `prop_6_2_3`, `theorem_6_3_5_sep`, `prop_7_1_tail`, `prop_7_2_tail`; isolation clause in `theorem_4_11`. |
| Referee 3 | `answer_Q3` now includes `¬ IsPathDetermined X`; new `theorem_7_4_strict_LAC_H`. |
| Referee 4 | Remark 4.10 proved (`GSpace.remark_4_10`) and compared inside `theorem_4_11`; Challenge header states the scope and that Hahn–Mazurkiewicz is not formalized. |
| (own) | Fan metric: `fan_metric` (the article's φ is a metric inducing the fan topology, for every injection ν), and library (F1), (F2), (F4). `sec_5_1_translation` (Section 5.1's general implication). |

## Sceptic, re-check (snapshot3, reading only)

| Change | Verdict |
|---|---|
| merged `theorem_4_11` | **fixed**: the conjunction (in particular local path connectedness together with the spread clause and Remark 4.10) excludes Arens' space and other cheap witnesses. New low-severity point: the Remark 4.10 clause used Mathlib's `IsSeparable K`, weaker than "separable as a subspace". |
| `answer_Q3` not path-determined | fixed |
| new compared statements | fixed, no new problems; `fan_metric`'s `phi` matches the article's φ (ν shifted by one); typo "continuum" for "continua" in the `cor_2_6_3` docstring |
| library changes | no escape hatches found |
| header | fixed |

Verdict: every fix answers its problem; only the `IsSeparable` point is new.

Response: the Remark 4.10 clause now states `SeparableSpace K` (separable as a subspace), proved by
a countable dense set inside `K` (`GSpace.remark_4_10`); the typo is fixed. These two edits,
`sec_5_1_translation` and the library lemmas for (F1), (F2), (F4) came after the re-check and were
not re-reviewed by an agent; they are
covered by the Comparator and axiom runs reported in `reports/verification_report.md`.
