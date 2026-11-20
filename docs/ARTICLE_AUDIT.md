# Mathematical audit of the article

Scope: a line-by-line read of `article/mosaic_article.tex`
(SHA-256 `4fa533f0b12af1a9668fa3f0f196ada8bc58778b3de3d88e86108da095804ca7`, 853 lines) by the
formalizing agent (Claude Fable 5.2), checking each proof step against its hypotheses. This is a
manual read by an AI system. It is **not** machine verification and **not** human review. Items
whose Lean proofs have been compiled are marked as such in the coverage ledger; everything else
here rests on the read alone.

## Result

No mathematical error was found. No repair of a statement was needed. The points below are the
places where the argument is delicate, what was checked, and what a formalization must do there.

## Delicate points requested in the task

**Mosaic compatibility and sequence capture (Def. 2.1, Lemma 2.2, Prop. 2.3).**
- Prop. 2.3(1) is what makes pieces subspaces; every later use of "a piece is a subspace" depends on
  it. In the intrinsic Lean definition (`IsMosaicFamily`) closedness of the pieces is an axiom of the
  structure, and the equivalence with Def. 2.1 (ledger `D-mosaic-eq`) must be proved for the
  definition to be faithful. Without the closedness requirement the intrinsic notion would be
  strictly weaker: a coherent cover by compact metrizable subspaces need not have closed members in
  a non-Hausdorff space.
- Proof of (5): after `(*)` the point `z` may equal one of `x`, `y`; the proof correctly picks the
  one that differs. The set `C` is closed because it is compact in the Hausdorff piece and the piece
  is closed; it would be wrong to argue "compact, hence closed" in `X`, which is not known to be
  Hausdorff. The Lean proof follows the article here.
- `(*)` is stated for injective sequences. The Lean proof (`exists_subseq_tendsto_in_piece`) does
  not need injectivity: finitely many indices give a finite, hence closed, set (T1), so the indices
  of the approximating sequence tend to infinity.
- Lemma 2.2, last clause: for T1 spaces with finite pairwise intersections, the intersection is
  finite and T1 in both, hence closed and discrete in both. Correct; it applies to distinct pieces.

**Compact metrizable images without a Hausdorff ambient space (Lemma 2.4, Remark 2.5, Cor. 2.6).**
- The lemma needs only: sequential + unique sequential limits (T1 follows). Closedness of `f(B)`
  uses sequential compactness of `C` and uniqueness of limits; Hausdorffness and second countability
  of `f(C)` are then intrinsic. The Lean statement has no separation hypothesis on `X` (see the ledger for its build status).
- Cor. 2.6(3): continuity at the point at infinity uses exactly the hypothesis that every open
  neighbourhood of `x` contains all but finitely many `K_n`; metrizability of the one-point
  compactification of a countable sum of compact metrizable spaces is used and is standard.

**Chain metric and E(Y) (Constr. 3.1-3.3, Lemma 3.2, Appendix A, Thm 3.4).**
- Cost is well defined on overlaps because `E_e ∩ Y = {x,y}` and `rho_e = d` there (this uses
  `rho(a,b) = 1`), and `E_e ∩ E_f ⊆ Y` for `e ≠ f`.
- Claim 1: all points `z_{i-1},...,z_j` lie in `E_e` by repeated use of the Observation; every pair
  in that segment contains a point of the open edge, so its cost is a value of `rho_e`. Checked.
- Claim 2 uses Claim 1 for the middle segment; Claim 3 only the Observation. Positivity covers the
  three cases (both in `Y`, both in one edge, otherwise). Checked.
- Stages are closed in `E(Y)`: for `u` first appearing at stage `j+1 > n`, Lemma 3.2(3) in
  `X_{j+1}` gives `d(u,w) ≥ r(u)` for all `w ∈ X_j ⊇ X_n`; this is enough because only points of
  `X_n` matter. Open edges are open in the next stage, not in `E(Y)`; the proof of (3) uses only the
  former. Checked.
- Baire argument: the minimal `n` with an arc in `X_n`; `L' ∩ X_{n-1}` has empty interior in `L'`
  because a nonempty open subset of an arc contains an arc. Checked.
- Degenerate cases: `Y` with fewer than two points gives `E(Y) = Y`; the theorem assumes two points.
  `K minus {a,b}` is nonempty because a nondegenerate connected T1 space is infinite.
- (4) needs no appeal to Cor. 2.6(3): in a metric space the union of sets through `y` with
  diameters tending to 0 is compact directly.

**Maximal almost disjoint families, finite sections, null fans (Section 4).**
- (4.1) follows from maximality, including the case `Y ∈ D`.
- The intersection table of Lemma 4.2 was checked row by row; `R_n ∩ Phi_D` is finite exactly
  because members of `C` have finite sections.
- (F4) is what makes `Lambda_S ∩ Lambda_S'` a common closed subspace.
- Nonvacuity: `C` is nonempty; `D` is infinite, indeed uncountable (the diagonal argument is the one
  carried out inside Prop. 4.9). `Lambda_S` requires `S` nonempty, as stated.

**Complete regularity, routes, countable spread (Lemma 4.4 - Prop. 4.9).**
- Lemma 4.4 (binary extension): the mixed case is well defined because an end point with value 1 is
  not in `F`, hence isolated in `{u,w} ∪ (I ∩ F)`. Continuity at `x_n`, `p_D`, `infinity` uses
  (i), (ii), (iii) together with Lemma 4.3(3), (2), (1) respectively. All five cases of Thm 4.5 were
  checked against (i)-(iii).
- Lemma 4.6 (routes): `Y ∩ B = ∅` gives `D ∉ D_F`; then `A_D ∩ F = ∅` and so `p_D ∉ F`. Checked.
- Lemma 4.8 (cut): `W` is open because its trace on each `Phi_D` is a finite union (finite
  sections); `K ∩ W` is clopen in `K`. Checked.
- Prop. 4.9 needs the points `p_D` to be relatively discrete (Thm 4.5, last assertion) and `K`
  closed (for `p_D ∈ K`); metric continua are closed by Lemma 2.4.

**Van Douwen's condition on the range of lambda (Section 5.2).**
- The article's own results (Lemma 5.1, Prop. 5.3) use only `lambda(f) ∈ [2/5, 3/5]`; this was
  confirmed step by step: 5.1(1) uses `lambda ≥ 2/5` and `epsilon > 0`; 5.1(6) uses `lambda ≥ 2/5`;
  Prop. 5.3 uses `lambda ≤ 3/5 < 4/5`.
- The Frechet property of `SHE` is van Douwen's theorem and is only quoted. Any Lean statement that
  mentions the Frechet property must take the range condition (no uncountable compact subset) as
  part of the definition of the space. None is planned without it.
- Not checked: whether the article's description of the topology of `SHE` agrees with van Douwen's
  paper. The source was not available to the agent. The Lean development would formalize the space
  as defined in the article.

**Boundary bumping (Lemma 5.2, Prop. 5.3).**
- `cl_K(K ∩ O) ⊆ K ∩ H` because `H` is closed; the boundary points lie on height 4/5. The component
  `C` of `k` is contained in `H`, which is what makes `C_1 ∪ C_2 = C`. Checked.
- `g ∈ Phi` because `K ∩ N` is infinite; if `g ∈ M_Phi` take `f = g`.

**Quotient-product arguments and the cone (Section 6).**
- Prop. 6.2(2): the displayed formula for `kappa^{-1}(g_alpha(C)) ∩ (X_beta × [0,1])` was checked in
  both cases `v ∈ C`, `v ∉ C`. Equality of the two induced topologies on `X_alpha ∩ X_beta` follows
  from Prop. 2.3(1).
- Joint continuity of the contraction uses Whitehead's lemma for `kappa × id`, as the article says;
  continuity on each `P_alpha × [0,1]` separately would not suffice.
- Thm 6.3(3)/(4) do not project to the base to prove that the cone is an m-continuum space; capture
  at the vertex uses the mosaic property of `{P_alpha}`.

**Nested neighbourhoods (Prop. 7.2).** The recursive choice `W_{k+1} ⊆ W_k ∩ V_{k+1}` is necessary;
`x_{n+1} ∈ W_{k(n+1)} ⊆ W_{k(n)}` uses monotonicity of `k(n)`. In Prop. 7.1 nesting of the `W_k` is
not needed. Checked.

**Witnesses for strictness and independence (Thm 7.4).**
- (H) not => (QC): `E(K)` (needs EXT-ARCLESS, EXT-PLPC, EXT-ARC).
- (LmS) not => (H): `cG` (class A).
- (LC) not => (LmS): `cZ` (needs EXT-Z, which the article cites without proof).
- LAC not => (H): `cG`. (H) not => LAC: `E(K)`.
All five witnesses are m-continuum spaces, as required by the statement.

## Other observations

1. Empty space. With Def. 2.1 the empty space is a mosaic space (empty mosaic). The qualifier
   "nonempty" in "every nonempty open subspace" is therefore harmless but not needed; the Lean
   statements quantify over all open subspaces.
2. Lemma 2.4 lists T1 as a hypothesis; it is implied by the other two.
3. Corollary 2.9(2) (a) => (c) does not use Hahn-Mazurkiewicz: it needs only that components of a
   compact locally connected space are open. Hence "quasi-curve = curve" is independent of EXT-HM.
4. Cor. 4.12, "not path-determined": this follows directly from Thm 4.11(4) (the set `{x_n}` meets
   every path image in a finite, hence closed, set but is not closed), without Prop. 2.10.
5. Example 7.3, last clause ("not a quasi-curve space") can be obtained from Prop. 2.13 and
   Prop. 2.12 instead of Cor. 2.15, avoiding EXT-PLPC and EXT-ARC.

## Statement-fidelity risks for the formalization

- "Locally arcwise connected" must not be silently replaced by "locally path connected". Where the
  Lean theorem proves the path form, the ledger says so and the arcwise form stays open.
- "Metric continuum" is a subspace property (compact, connected, metrizable in the subspace
  topology); it must not be replaced by "compact connected subset of a metric space".
- Counterexamples must be constructed (existential statements proved by exhibiting the space), not
  assumed. `K` and `Z` are currently the two objects that cannot be constructed from Mathlib.
