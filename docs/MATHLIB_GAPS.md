# Mathlib gap analysis

(Written in the preparation session for Mathlib v4.35.0; the build now uses tag v4.35.0-rc2, commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, and the gaps listed are still absent there.)
Mathlib tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, searched by `grep` over
`Mathlib/`, `Counterexamples/`, `Archive/` and `Wanted/` on 2026-11-16. A search that finds nothing
is evidence, not proof, that a result is absent; names in Mathlib can be unexpected. Each "absent"
below means: no file matches the listed patterns (case-insensitive).

## Absent classical theory the article depends on

Status as of 2026-11-17 in the last column: what this project now proves itself.

| Id | Theorem | Patterns with no match | Used by | Status here |
|---|---|---|---|---|
| EXT-HM | Hahn-Mazurkiewicz (Peano continuum => image of a path) | `Hahn.?Mazurkiewicz`, `Peano continu`, `PeanoContinu`, `peano space` | in the article: Cor. 2.9(2) (c)=>(d), Prop. 2.10 (d)=>(a) | **not formalized and not needed**: both uses are proved by another route (a convergent sequence in a Peano continuum has a tail on one path: `IsPeanoContinuum.exists_pathImage_tail`) |
| EXT-PLPC | compact + locally connected + metrizable => locally path connected | same, and `Mazurkiewicz`, `Moore.*Menger` | Lemma 2.14, Cor. 2.15, Thm 7.4 | **proved**: `MosaicSpaces/Peano/{Chain,Path,LPC}.lean` (uniform local connectedness, chains, refinement, Cauchy limit); compared as `compact_locallyConnected_lpc` |
| EXT-ARC | path connected Hausdorff => arcwise connected | `arcwise`, `arc.?connected`, `IsArc\b` | every "arcwise" statement | **proved**: `MosaicSpaces/Arc/{Minimal,Param}.lean` (Zorn-minimal parameter set, collapse of gaps by a countable dense order); compared as `arc_theorem` |
| EXT-ARCLESS | a nondegenerate metric continuum containing no arc | `pseudo.?arc`, `indecomposable continu`, `hereditarily indecomposable` | Section 3, Cor. 3.5, Thm 7.4 strictness | not formalized (example; out of scope by request) |
| EXT-MMM | completely metrizable + locally connected => locally arcwise connected | `Mazurkiewicz`, `Moore.*Menger` | Remark 3.6 only | not formalized (Section 3; out of scope) |
| EXT-Z | connected, locally connected plane set without nondegenerate subcontinua | `Bernstein set`, `IsBernstein`, `Jordan curve`, `unicoheren`, `Janiszewski` | Example 7.3, Thm 7.4 strictness | not formalized (example; out of scope) |

Also absent, but short and self-contained (class A in the ledger): boundary bumping
(`boundary bumping`), maximal almost disjoint families (`almost disjoint`, `AlmostDisjoint`),
Arens-type spaces (`Arens`, `sequential fan`), a topological cone construction (no `def Cone` under
`Mathlib/Topology`), a general "quotient map times locally compact space" theorem
(`Mathlib/Topology/CompactOpen.lean` has `IsQuotientMap.continuous_lift_prod_left/right`, which is
enough for the uses in Section 6), a general theorem that a closed continuous image of a compact
metrizable space is metrizable (proved in `MosaicSpaces/Image.lean`).

## Present and used

`SequentialSpace`, `FrechetUrysohnSpace`, `IsSeqClosed` (`Topology/Sequences.lean`,
`Topology/Defs/Sequences.lean`); `IsCompact.tendsto_subseq`; `Tendsto.isCompact_insert_range`;
`OnePoint.continuous_iff_from_nat` and `MetrizableSpace (OnePoint ℕ)`;
`metrizableSpace_of_t3_secondCountable` (Urysohn); `IsClosedMap.isQuotientMap`;
`connectedComponent_eq_iInter_isClopen` (compact Hausdorff); `IsOpen.connectedComponentIn`
(components of open sets in locally connected spaces are open); `IsOpen.pathComponentIn` and
`IsQuotientMap.locPathConnectedSpace`; Tietze (`ContinuousMap.exists_restrict_eq`,
`exists_extension_forall_mem_Icc_of_isClosedEmbedding`); Urysohn's lemma; Baire
(`nonempty_interior_of_iUnion_of_closed`); `Metric.InductiveLimit` (`MetricSpace/Gluing.lean`);
`zorn_subset`; `Perfect.exists_nat_bool_injection`; `ContractibleSpace`.

## Consequence for the headline results

- **Q3 (space G)**: answered as asked (`answer_Q3`), using EXT-ARC (proved here).
- **Q2 (cone over G)**: Corollary 6.4 in full (`answer_Q2`).
- **Q1a, Q1b via the cone over G**: answered (`answer_Q1a`, `answer_Q1b`), as the article remarks
  after Corollary 6.4. The article's own route through E(K) needs EXT-ARCLESS and is not
  formalized.
- **Theorem 7.4**: all implications, (QC) => LAC => (LmS), (LmS) =/=> (H) and LAC =/=> (H) are
  formalized; the other strictness claims need E(K) and cZ (EXT-ARCLESS, EXT-Z).
- **Boundary bumping (Lemma 5.2)**: proved (`lemma_5_2`). Proposition 5.3 (van Douwen's space) is
  not formalized (example).
