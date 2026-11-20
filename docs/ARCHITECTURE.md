# Architecture

## Layout

```
lean-toolchain            leanprover/lean4:v4.35.0-rc2
lakefile.toml             the only Lake configuration; Mathlib pinned by commit; libs MosaicSpaces,
                          Challenge, Solution; defaultTargets = MosaicSpaces, Solution
lake-manifest.json        committed
MosaicSpaces.lean         root module, imports every module below
MosaicSpaces/             proof development (every file starts with `module`)
  Image.lean              UniqueSeqLimits; Lemma 2.4; Remark 2.5; ℕ ∪ {∞} is metrizable
  Mosaic.lean             intrinsic definitions; Prop 2.3 (2),(4),(5),(6); Prop 2.7
  Abstract.lean           Def 2.1 (abstract mosaics, mosaic topology) and its equivalence with the
                          intrinsic definitions; Lemma 2.2 and its special cases; Prop 2.3(1)
  Continua.lean           Cor 2.6 (1),(2a),(3); open subspaces (Prop 2.7, last part)
  Classes.lean            transfer lemmas; Captures; Lemma 2.8; Cor 2.9
  Local.lean              Def 2.11 and arc notions; display (2.1); Props 2.12, 2.13
  PathComponents.lean     Lemma 2.14 (path-connected variant)
  Arc/Minimal.lean        arc theorem, part 1: Zorn-minimal admissible parameter set
  Arc/Param.lean          arc theorem, part 2: collapse of gaps, the arc (EXT-ARC)
  ArcConsequences.lean    Cor 2.6(2) arcwise; display (2.1) LPC ⇔ LAC; Lemma 2.14 arcwise form
  Peano/Chain.lean        chains in preconnected sets; uniform local connectedness of compacta
  Peano/Path.lean         paths as limits of refining chains
  Peano/LPC.lean          compact locally connected metrizable ⇒ locally path connected (EXT-PLPC)
  Peano/Consequences.lean classical facts on Peano continua; Lemma 2.14 (article form); Cor 2.15;
                          Cor 2.9(2) (c)⇒(d); Thm 7.4 LAC parts; Remark 3.7 implication
  PathDetermined.lean     Prop 2.10 (path-determined spaces)
  Classical/Bump.lean     Lemma 5.2 (boundary bumping)
  FirstCountable.lean     Props 7.1, 7.2
  Cone.lean               Prop 2.3(3); Lemma 6.1; Prop 6.2; Thm 6.3 (1),(2),(3),(5)
  Cone4.lean              Thm 6.3(4)
  Fan.lean                null fans Fan(J) (Section 4.2, (F2),(F3)); fanLift
  FanMetric.lean          the article's metric φ induces the fan topology; (F1), (F2), (F4)
  G/Basic.lean            𝒞, MAD families (Zorn), the type GSpace, piece maps, final topology,
                          shapes of pieces, closed-map property of every piece map
  G/Mosaic.lean           Lemma 4.2 (mosaic family), Lemma 4.3, Lemma 4.6 (routes),
                          Prop 4.7 (path form)
  G/Capture.lean          isolating neighbourhoods of p_D, Lemma 4.8 (cut), Prop 4.9
  G/Tychonoff.lean        Lemma 4.4 (binary functions), Thm 4.5 (Tychonoff)
  G/Remarks.lean          Remark 4.10, Remark 4.13(2)
  Answers.lean            G fixed by choice; Thm 4.11; Cor 4.12; Cor 6.4; Q1a, Q1b;
                          Remark 4.13; Theorem 7.4 (strictness via 𝖼G); Thm 6.3(4)
Challenge.lean            70 statements; Mathlib imports only; definitions copied verbatim
Solution.lean             imports MosaicSpaces; same names and statements, proved
comparator.json
formalization.yaml
scripts/                  verify_all.sh, check_sources.py, axioms.lean, check_axioms.py
sandbox/                  container recipe (not used in this session)
docs/, ledger/, reports/, logs/
```

## Toolchain and dependency pins

- **Lean:** `leanprover/lean4:v4.35.0-rc2`, the Palomar floor. The preparation package planned
  v4.35.0. The session that compiled the project had only the rc2 toolchain locally, and had no
  network access to install another.
- **Mathlib:** tag `v4.35.0-rc2`, commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`, pinned by SHA.
  The manifest's `inputRev` is the same SHA.
- **Verification tools:** the ones bundled with the toolchain (`lake comparator`, `lake check`,
  leanchecker(-paranoid), lean4lean, nanoda_bin, con-leche, con-ron). Their SHA-256 values are
  recorded in `provenance.txt` of every `scripts/verify_all.sh` run.

## Module system

Every source file starts with `module`, uses `public import`, and opens `@[expose] public section`.

## Definitions

| Article | Lean | Correspondence |
|---|---|---|
| unique limits of convergent sequences | `UniqueSeqLimits X` | literal |
| mosaic space (Def 2.1) | `IsMosaicSpace X`: there is an `IsMosaicFamily` (cover, closed members, coherence) of compact metrizable subsets | intrinsic reformulation, proved equivalent to the abstract Def 2.1 (`IsAbstractMosaic`, `mosaicTopology`; compared as `def_2_1_*`) |
| metric continuum | `IsMetricContinuum K` (`IsCompact`, `IsConnected`, `MetrizableSpace ↥K`) | literal; nonempty because of `IsConnected` |
| quasi-Peano / Peano | `IsQuasiPeano`, `IsPeanoContinuum` | literal |
| m-continuum / quasi-curve / curve space | `IsMContinuumSpace`, `IsQuasiCurveSpace`, `IsCurveSpace` | same pattern |
| m-strongly connected, locally m-strongly connected | `MStronglyConnected`, `LocallyMStronglyConnected` | literal, open-set form |
| arc, arcwise connected, locally arcwise connected | `IsArc`, `IsArcBetween` (embedding of `[0,1]`), `ArcwiseConnected`, `LocallyArcwiseConnected` | literal |
| path-determined (van Douwen) | `Determines`, `IsPathDetermined`, `ClosedTestedByPaths`, `IsQuotientOfIntervals` | literal |
| locally path connected | Mathlib `LocallyPathConnectedSpace` | proved equivalent to the open-set form (`locallyPathConnectedOpen_iff`) |
| cone | `Cone Y := Quotient (coneSetoid Y)` on `Y × [0,1]` collapsing `Y × {1}` | literal |

## The space G

- **Points.** `GSpace 𝒟` is an inductive type. Its constructors are the article's points: `∞`, the
  `p_D`, the rows `R_n(t)`, the interior arc points and the interior spoke points.
- **Pieces.** The five piece maps of the article are realised as follows:
  - `rowMap n : [0,1] → G`;
  - `sigMap : ℕ ∪ {∞} → G`;
  - `phiMap D : Fan(D) → G`;
  - `lamMap S : Fan(S) → G`, for countable `S ⊆ 𝒟`.
- **Topology.** The *final topology* of the piece maps (`gTop`), i.e. the mosaic topology of the
  article.
- **Every piece map is a closed embedding.** For two piece maps `f`, `g`, the preimage
  `f⁻¹(g(C))` of the image of a closed set `C` is closed. This is shown in one of two ways:
  - when the two ranges meet in a finite set, by the generic lemma
    `isClosed_preimage_image_of_finite`;
  - for two Λ-pieces, by the restriction map `restr`.
  This replaces the compatibility table of Lemma 4.2.
- **Fan(J).** The subspace of `J → ℝ` (product topology) of functions with values in `[0,1]` and at
  most one nonzero coordinate. It is compact, and metrizable for countable `J`. The article's metric
  φ is defined (`Fan.phi`) and proved to induce exactly this topology for every injection ν
  (`Fan.isOpen_iff_phi`, compared as `fan_metric`). The properties used are proved directly:
  - local path connectedness;
  - points on distinct spines converge to the centre;
  - a closed set missing the centre meets finitely many spines.
- **MAD family.** It is a parameter with the hypothesis `IsMADFamily 𝒟`. Its existence is proved by
  Zorn's lemma (`exists_isMADFamily`). `Answers.lean` fixes one by `Classical.choose`.

## Challenge / Solution

- **Holes.** `Challenge.lean` has one `sorry` per compared statement and nothing else unproved.
  `Solution.lean` and `MosaicSpaces/` contain no `sorry`.
- **Definitions.** `Challenge.lean` copies the library definitions verbatim: same names, namespace,
  universe names and section variables. Comparator checks that they are the same constants. A
  negative control that changes one definition is rejected
  (`Const does not match between challenge and target`).
- **Names.** The compared theorems live in `MosaicSpaces.Paper`, so they do not clash with the
  library names. `Solution.lean` proves each one by a library theorem.
- **Existential statements.** Statements about `G` and the cone over `G` are compared in
  existential form, `∃ (X : Type) (_ : TopologicalSpace X), …`. This keeps the definition of `G`
  out of the Challenge. `theorem_4_11` packs every property of `G` (Thm 4.5, Prop 4.7, Prop 4.9,
  Remarks 4.10 and 4.13, Thm 4.11) for one witness, so the properties cannot be met separately by
  different, simpler spaces. The cone itself is restated, so that Theorem 6.3 can be compared for an
  arbitrary `Y`.

## Environments

- **Development.**
  - Linux cloud container, without network access.
  - Mathlib was built from source because the cache server was unreachable.
  - `lake build` and `lake env lean` were used.
- **Verification.** `scripts/verify_all.sh` runs the seven checks and the negative controls. In the
  development container bubblewrap is absent, so the sandboxed steps are recorded as `not-run`.
  With `ALLOW_NO_SANDBOX=1` they are additionally run with `--inadvisably-no-sandbox`, under step
  names ending in `-NOSANDBOX`. The CI workflow installs bubblewrap and runs the sandboxed steps.
  It has never run, because no remote exists.
