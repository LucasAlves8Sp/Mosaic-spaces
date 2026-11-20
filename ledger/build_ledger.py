#!/usr/bin/env python3
"""Coverage ledger for `article/mosaic_article.tex`.

Single source of truth: the ROWS table below. Running this file regenerates
`ledger/coverage.json` and `docs/COVERAGE_LEDGER.md`.

Columns
  id      stable ledger id
  label   article label (LaTeX \\label, or a descriptive tag for unlabelled text)
  lines   line range in article/mosaic_article.tex holding the exact informal statement
  stmt    short paraphrase (the exact wording is at `lines`)
  lean    Lean declaration (existing if status is not "not-started", otherwise planned name)
  module  Lean module (existing or planned)
  deps    ledger ids / external ids this item depends on
  cls     feasibility class
            A  provable from Mathlib v4.35.0 without new classical theory
            B  needs an external classical theorem absent from Mathlib (see EXT)
            C  cited from the literature in the article itself, not proved there
            D  documentation only (history, attribution, heuristics)
  status  set by the UPD table near the end of this file:
          compared | proved | partial | not-formalized | blocked | documentation
          (the planning values of the ROWS table are overridden there).
"""
import json, pathlib, collections

EXT = {
 "EXT-HM": "Hahn-Mazurkiewicz: a Peano continuum is the image of a path (Willard Sect. 31; Engelking 6.3). Not in Mathlib v4.35.0.",
 "EXT-HMC": "Converse: a Hausdorff continuous image of [0,1] is locally connected (closed quotient of a locally connected space). Short; provable from Mathlib.",
 "EXT-PLPC": "A compact, locally connected, metrizable space is locally path connected (Mazurkiewicz-Moore-Menger for compacta; Engelking 6.3). Not in Mathlib v4.35.0.",
 "EXT-ARC": "A path connected Hausdorff space is arcwise connected (Willard Sect. 31). Not in Mathlib v4.35.0 (no notion of arc at all).",
 "EXT-ARCLESS": "Existence of a nondegenerate metric continuum containing no arc (pseudo-arc: Knaster 1922, Moise 1948, Bing 1948). Not in Mathlib v4.35.0.",
 "EXT-MMM": "Mazurkiewicz-Moore-Menger: completely metrizable + locally connected => locally arcwise connected (Engelking 6.3). Not in Mathlib v4.35.0.",
 "EXT-Z": "Existence of a connected, locally connected subset of the plane with more than one point containing no nondegenerate continuum (Curtis 1980 Ex. 1.7; Hocking-Young). Needs a Bernstein decomposition and a plane separation theorem. Not in Mathlib v4.35.0.",
 "EXT-VD": "van Douwen 1981: existence of the injection lambda, and SHE is regular, Frechet, locally pathwise connected, not path-determined. Cited, not proved, in the article.",
 "EXT-FST": "Franklin-Smith-Thomas 1979: the space HE and its properties. Cited, not proved, in the article.",
 "EXT-CURTIS": "Curtis 1980, Example 1.8. Cited; the article explicitly has not verified it.",
}

R = []
def row(id, label, lines, stmt, lean, module, deps="", cls="A", status="not-started", note=""):
    R.append(dict(id=id, label=label, lines=lines, stmt=stmt, lean=lean, module=module,
                  deps=[d for d in deps.split() if d], cls=cls, status=status, note=note))

M = "MosaicSpaces."
# ---------------------------------------------------------------- Section 1 (introduction)
row("I-1", "intro: hierarchy", "74-76", "curve = quasi-curve => m-continuum => mosaic.", "IsCurveSpace.isQuasiCurveSpace, IsQuasiCurveSpace.isMContinuumSpace, IsMContinuumSpace.isMosaicSpace", M+"Mosaic / Classes", "P-classes2", "A", note="The equality curve = quasi-curve is P-classes2 (a)<=>(b).")
row("I-2", "intro: Q1b hypothesis stronger than Q1a", "72", "Local m-strong connectedness implies local connectedness.", "LocallyMStronglyConnected.locallyConnectedSpace", M+"Local", "", "A")
row("I-3", "intro: metric spaces and CW complexes are mosaic", "51", "Every Hausdorff sequential space is a mosaic space (CW complexes: illustration only).", "isMosaicSpace_of_t2", M+"Mosaic", "P-char", "A", "written-unchecked", "CW-complex remark is illustration; not formalized.")
row("I-4", "Sections 1.3-1.6", "78-119", "Table of answers, attribution, sources, organisation.", "-", "-", "", "D", "documentation")
# ---------------------------------------------------------------- Section 2
row("C-1", "conventions: classical facts", "126", "Hahn-Mazurkiewicz; Peano continua are arcwise and locally arcwise connected; compact locally connected metrizable => finitely many components, each open and Peano; nondegenerate Peano continuum contains an arc.", "External.*", M+"External.*", "EXT-HM EXT-PLPC EXT-ARC", "B", "blocked", "Finitely many open components: class A from Mathlib (IsOpen.connectedComponentIn + compactness).")
row("D-mosaic", "def:mosaic", "129-133", "Mosaic on a set; mosaic topology; mosaic space; m-continuum, quasi-curve, curve space.", "Mosaic, Mosaic.topology, IsMosaicFamily, IsMosaicSpace, IsMContinuumSpace, IsQuasiCurveSpace, IsCurveSpace", M+"Mosaic / Abstract", "", "A", "written-unchecked", "Intrinsic definition via coherent closed covers; equivalence with the abstract Definition 2.1 is D-mosaic-eq.")
row("D-mosaic-eq", "def:mosaic (fidelity)", "129-133, 147", "A space is the mosaic space of an abstract mosaic of compact metric spaces iff it has a mosaic family of compact metrizable subspaces.", "isMosaicSpace_iff_exists_mosaic (planned)", M+"Abstract", "P-basic1", "A", note="Required to justify the intrinsic definitions. Universe: index type in the universe of X.")
row("L-recognise", "lem:recognise", "135-140", "Pairwise intersections closed in both with equal induced topologies => mosaic; closed subspaces of a space covering X; T1 spaces with finite pairwise intersections.", "Mosaic.ofClosedCompatible, ofClosedSubspaces, ofFiniteInter (planned)", M+"Abstract", "", "A")
row("P-basic1", "prop:basic(1)", "147,156", "Each piece is closed in the mosaic topology, which induces the piece topology.", "Mosaic.isClosed_piece, Mosaic.induced_eq (planned)", M+"Abstract", "", "A")
row("P-basic2", "prop:basic(2)", "148,158", "A mosaic space is T1.", "IsMosaicFamily.t1Space", M+"Mosaic", "", "A", "written-unchecked")
row("P-basic3", "prop:basic(3)", "149,158", "A map is continuous iff its restrictions to pieces are; the natural map from the sum of the pieces is a quotient map.", "IsMosaicFamily.continuous_iff, isQuotientMap_sigma (planned)", M+"Mosaic", "", "A")
row("P-basic-star", "prop:basic (*)", "164-166", "A sequence converging to a point it avoids has a subsequence in one piece converging there to a point outside its range.", "IsMosaicFamily.exists_subseq_tendsto_in_piece", M+"Mosaic", "P-basic2", "A", "written-unchecked", "Proved without the injectivity hypothesis of the article (stronger statement).")
row("P-basic4", "prop:basic(4)", "150,170,172", "If x_k -> x, some piece contains x and x_k for infinitely many k (and the subsequence converges in the piece).", "IsMosaicFamily.exists_piece_subseq", M+"Mosaic", "P-basic-star P-basic5", "A", "written-unchecked")
row("P-basic5", "prop:basic(5)", "151,168", "Convergent sequences have unique limits.", "IsMosaicFamily.uniqueSeqLimits", M+"Mosaic", "P-basic-star", "A", "written-unchecked")
row("P-basic6", "prop:basic(6)", "152,160", "A mosaic space is sequential.", "IsMosaicFamily.sequentialSpace", M+"Mosaic", "", "A", "written-unchecked")
row("L-image", "lem:image", "174-183", "In a sequential T1 space with unique sequential limits the continuous image of a compact metrizable space is closed, compact and metrizable.", "range_closed_compact_metrizable", M+"Image", "", "A", "written-unchecked", "T1 is not a hypothesis: it follows (UniqueSeqLimits.t1Space).")
row("R-hausimage", "rem:hausimage", "185-187", "Hausdorff continuous image of a compact metrizable space is compact metrizable.", "range_compact_metrizable_of_t2", M+"Image", "", "A", "written-unchecked")
row("C-image1", "cor:image(1)", "192,198", "Union of two metric continua with a common point is a metric continuum.", "IsMetricContinuum.union (planned)", M+"Continua", "L-image", "A")
row("C-image2a", "cor:image(2), compactness part", "193,198", "The image of a path in a mosaic space is a metric continuum; any two points of a path connected subset lie in a metric continuum inside it.", "isMetricContinuum_range_path (planned)", M+"Continua", "L-image", "A")
row("C-image2b", "cor:image(2), Peano/arc part", "193,198", "The image of a path is a Peano continuum; every path connected subset is arcwise connected.", "isPeanoContinuum_range_path, IsPathConnected.isArcwiseConnected (planned)", M+"External.Arc", "L-image EXT-HMC EXT-ARC", "B", "blocked")
row("C-image3", "cor:image(3)", "194,198", "Metric continua K_n through x, eventually inside every neighbourhood of x: their union is a metric continuum.", "IsMetricContinuum.iUnion_of_null (planned)", M+"Continua", "L-image", "A", note="Needs metrizability of the one-point compactification of a countable sum of compact metrizable spaces, or a direct proof.")
row("P-char", "prop:char", "201-208", "Mosaic space <=> sequential with unique sequential limits; Hausdorff sequential spaces are mosaic; open subspaces of mosaic spaces are mosaic.", "isMosaicSpace_iff, isMosaicSpace_of_t2, IsMosaicSpace.of_isOpen (planned)", M+"Mosaic", "P-basic5 P-basic6 L-image", "A", "written-unchecked", "Open-subspace part not yet written.")
row("L-generate", "lem:generate", "212-217", "A covering family of compact metrizable subspaces of a mosaic space is a mosaic; it generates the topology iff every convergent sequence has a subsequence lying with its limit in a member.", "isMosaicFamily_iff_capture (planned)", M+"Classes", "L-image P-basic4", "A")
row("P-classes1", "cor:classes(1)", "222,227", "m-continuum space <=> every convergent sequence has a subsequence lying with its limit in a metric continuum.", "isMContinuumSpace_iff (planned)", M+"Classes", "L-generate", "A")
row("P-classes2", "cor:classes(2) (a)<=>(b)<=>(c)", "223,229", "Quasi-curve <=> curve <=> every convergent sequence is captured by a Peano continuum.", "isQuasiCurveSpace_iff_isCurveSpace, isCurveSpace_iff (planned)", M+"Classes", "L-generate", "A", note="(a)=>(c) uses only that components of a compact locally connected space are open.")
row("P-classes2d", "cor:classes(2) (c)<=>(d)", "223,229", "... <=> every convergent sequence is captured by the image of a path.", "isCurveSpace_iff_path (planned)", M+"Classes", "EXT-HM EXT-HMC", "B", "blocked")
row("D-pathdet", "path-determined (definition)", "233", "A family determines X; X is path-determined.", "Determines, IsPathDetermined (planned)", M+"PathDetermined", "", "A")
row("P-pathdet-abc", "prop:pathdet (a)<=>(b)<=>(c)", "235-246", "For Hausdorff X: path-determined <=> closedness tested by preimages under paths <=> quotient of a sum of intervals.", "isPathDetermined_tfae_abc (planned)", M+"PathDetermined", "", "A")
row("P-pathdet-de", "prop:pathdet (a)<=>(d)<=>(e)", "235-249", "For Hausdorff X: path-determined <=> curve space <=> quasi-curve space.", "isPathDetermined_iff_isCurveSpace (planned)", M+"PathDetermined", "P-classes2 EXT-HM EXT-HMC", "B", "blocked", "(a)=>(d) needs EXT-HMC only; (d)=>(a) needs EXT-HM.")
row("D-local", "def:local", "252-255", "m-strongly connected; locally m-strongly connected, locally connected, locally path connected, locally arcwise connected (open-set forms).", "MStronglyConnected, LocallyMStronglyConnected, IsArcwiseConnected, LocallyArcwiseConnected (planned)", M+"Local", "", "A", note="Equivalence of the open-set form of local (path) connectedness with Mathlib's LocallyConnectedSpace / LocPathConnectedSpace to be proved.")
row("E-localimpl-a", "eq:localimpl (LPC => LmS => LC)", "257-263", "In a mosaic space: locally path connected => locally m-strongly connected => locally connected.", "LocallyMStronglyConnected.of_locPathConnected (planned)", M+"Local", "C-image2a", "A")
row("E-localimpl-b", "eq:localimpl (LPC <=> LAC)", "257-263", "In a mosaic space: locally path connected <=> locally arcwise connected.", "locallyArcwiseConnected_iff (planned)", M+"External.Arc", "EXT-ARC", "B", "blocked")
row("P-lav52", "prop:lav52", "265-270", "If every nonempty open subspace of a mosaic space is an m-continuum space, the space is locally m-strongly connected.", "locallyMStronglyConnected_of_open_mContinuum (planned)", M+"Local", "C-image1 P-classes1", "A")
row("P-qcopen", "prop:qcopen", "272-277", "Every nonempty open subspace of a quasi-curve space is an m-continuum space.", "IsQuasiCurveSpace.open_isMContinuumSpace (planned)", M+"Local", "P-classes2 P-classes1", "A")
row("L-lac", "lem:lac", "281-286", "Criterion: path components of open sets are open (and arcwise connected) if sequences in non-locally-connected pieces are eventually in the path component of their limit.", "IsMosaicFamily.isOpen_pathComponentIn (planned)", M+"Local", "P-basic4 EXT-PLPC EXT-ARC", "B", note="A class-A variant with hypothesis 'piece locally PATH connected or sequence condition' suffices for G and gives openness of path components.")
row("C-qclac", "cor:qclac", "288-294", "Every quasi-curve space is locally arcwise connected, hence locally m-strongly connected.", "IsQuasiCurveSpace.locallyArcwiseConnected (planned)", M+"Local", "L-lac EXT-PLPC EXT-ARC", "B", "blocked", "The consequence 'locally m-strongly connected' alone is class A via P-qcopen + P-lav52.")
# ---------------------------------------------------------------- Section 3 + Appendix A
row("K-exist", "fixed continuum K", "302-304", "A nondegenerate metric continuum K without arcs exists; compatible metric with rho(a,b)=diam K=1; K minus {a,b} nonempty.", "exists_arcless_continuum (planned)", M+"External.ArclessContinuum", "EXT-ARCLESS", "B", "blocked", "Normalisation and nonemptiness of K minus {a,b} are class A once K exists.")
row("Cn-plus", "con:plus", "306-311", "Y+ = Y with a copy of K attached along every ordered pair of distinct points; edges E_e with metric rho_e.", "Arcless.Plus (planned)", M+"Arcless.Glue", "", "A", note="Parametric in (K, rho, a, b).")
row("A-obs", "app:glue Observation", "818", "An elementary pair with one point in the interior of an edge lies in that edge.", "Arcless.Plus.elementary_of_interior (planned)", M+"Arcless.Glue", "", "A")
row("A-claim1", "app:glue Claim 1", "820-822", "Chains between points of Y cost at least d.", "Arcless.Plus.cost_ge_dist (planned)", M+"Arcless.Glue", "A-obs", "A")
row("A-claim2", "app:glue Claim 2", "824", "Chains between points of an edge cost at least rho_e.", "Arcless.Plus.cost_ge_edgeDist (planned)", M+"Arcless.Glue", "A-claim1", "A")
row("A-claim3", "app:glue Claim 3", "826", "Chains from an interior edge point to outside the open edge cost at least r(u).", "Arcless.Plus.cost_ge_r (planned)", M+"Arcless.Glue", "A-obs", "A")
row("L-plus", "lem:plus", "313-321, 816-828", "d+ is a metric on Y+ extending d and each rho_e, with separation (3); Y closed, open edges open, edges homeomorphic to K.", "Arcless.Plus.instMetricSpace, isometry_inl, isometry_edge, r_le_dist (planned)", M+"Arcless.Glue", "A-claim1 A-claim2 A-claim3", "A")
row("Cn-EY", "con:EY", "323-325", "E(Y) = union of the tower X_0 = Y, X_{n+1} = X_n^+, with the union metric.", "Arcless.E (planned; Metric.InductiveLimit)", M+"Arcless.Tower", "L-plus", "A")
row("T-arcless0", "thm:arcless, preliminaries", "339", "Each stage X_n is closed in E(Y); open edges are open in the next stage.", "Arcless.isClosed_stage (planned)", M+"Arcless.Main", "Cn-EY", "A")
row("T-arcless1", "thm:arcless(1)", "331,339", "Y is a closed subspace of E(Y) and d extends d_Y.", "Arcless.isometry_base, isClosed_range_base (planned)", M+"Arcless.Main", "T-arcless0", "A")
row("T-arcless2", "thm:arcless(2)", "332,341", "Any two distinct points lie in a copy of K of diameter d(x,y); open balls are m-strongly connected; E(Y) is connected.", "Arcless.exists_edge, mStronglyConnected_ball, connectedSpace (planned)", M+"Arcless.Main", "Cn-EY", "A")
row("T-arcless3a", "thm:arcless(3), no arcs", "333,343", "E(Y) contains no arc (Baire category argument).", "Arcless.not_isArc (planned)", M+"Arcless.Main", "T-arcless0", "A", note="Hypotheses: K and Y contain no arc.")
row("T-arcless3b", "thm:arcless(3), locally connected compacta finite", "333,345", "Every compact, locally connected subspace of E(Y) is finite.", "Arcless.finite_of_isQuasiPeano (planned)", M+"Arcless.Main", "T-arcless3a EXT-PLPC EXT-ARC", "B", "blocked")
row("T-arcless4", "thm:arcless(4)", "334,347", "E(Y) is a locally m-strongly connected mosaic space; it and all nonempty open subspaces are m-continuum spaces.", "Arcless.isMContinuumSpace_open (planned)", M+"Arcless.Main", "T-arcless2 P-classes1", "A")
row("T-arcless5", "thm:arcless(5)", "335,349", "E(Y) is not a quasi-curve space and not locally arcwise connected.", "Arcless.not_isQuasiCurveSpace, not_locallyArcwiseConnected (planned)", M+"Arcless.Main", "T-arcless3b", "B", "blocked", "'Not locally arcwise connected' follows from T-arcless3a alone (class A).")
row("C-Q1", "cor:Q1", "352-355", "E(K) is a metrizable, locally m-strongly connected m-continuum space, all of whose nonempty open subspaces are m-continuum spaces, and it is not a quasi-curve space.", "answer_Q1 (planned)", M+"Answers", "T-arcless4 T-arcless5 K-exist", "B", "blocked", "Blocked on EXT-ARCLESS, EXT-PLPC, EXT-ARC.")
row("R-complete", "rem:complete", "357-359", "E(Y) is never completely metrizable; the no-arc hypothesis on Y is necessary.", "Arcless.not_completelyMetrizable (planned)", M+"Arcless.Main", "EXT-MMM T-arcless5", "B", "blocked", "Necessity of the hypothesis is immediate from T-arcless1 (class A).")
row("R-curtis", "rem:curtis", "361-363", "Granting its stated properties, Curtis's Example 1.8 answers Q1a and Q1b.", "answers_Q1_of_not_locPathConnected (planned, conditional implication)", M+"Answers", "P-fc C-qclac EXT-CURTIS", "C", note="Only the implication can be formalized: first countable + locally m-strongly connected + not locally path connected => m-continuum and not quasi-curve. The example itself is cited and unverified in the article.")
# ---------------------------------------------------------------- Section 4
row("F-metric", "null fans: metric", "378-380", "phi is a metric on Fan(I) (isometric to a subset of l1(I)).", "Fan.instMetricSpace (planned)", M+"G.Fan", "", "A")
row("F-1", "(F1)", "382", "Neighbourhoods of the centre; the topology does not depend on nu.", "Fan.mem_nhds_centre_iff (planned)", M+"G.Fan", "F-metric", "A")
row("F-2", "(F2)", "383", "Fan(I) is a Peano continuum; spines are arcs; spines minus the centre are open.", "Fan.compactSpace, connectedSpace, locPathConnectedSpace, isOpen_spine_diff (planned)", M+"G.Fan", "F-metric", "A", note="'Spines are arcs' needs only the definition of arc, not EXT-ARC.")
row("F-3", "(F3)", "384", "Points on pairwise distinct spines converge to the centre.", "Fan.tendsto_centre (planned)", M+"G.Fan", "F-metric", "A")
row("F-4", "(F4)", "385", "Fan(J) is a closed subspace of Fan(I) for nonempty J.", "Fan.isClosedEmbedding_incl (planned)", M+"G.Fan", "F-1", "A")
row("Cn-G-mad", "con:G: family D and (4.1)", "390-395", "A maximal almost disjoint family D of infinite subsets of N x N with finite sections exists (Zorn); maximality in the form (4.1).", "G.exists_mad, G.MAD.exists_inter_infinite (planned)", M+"G.MAD", "", "A")
row("Cn-G", "con:G: set and pieces", "397-412", "Underlying set of G; pieces R_n, Sigma, Phi_D, Lambda_S; G has the mosaic topology.", "G.Pt, G.instTopologicalSpace (planned)", M+"G.Construction", "Cn-G-mad F-metric L-recognise", "A")
row("L-Gmosaic", "lem:Gmosaic", "414-437", "The pieces form a mosaic of compact metric spaces; pieces are closed subspaces; x_n -> infinity; injective sequences in D converge to p_D.", "G.isMosaicSpace, G.tendsto_x, G.tendsto_pD (planned)", M+"G.Construction", "Cn-G F-3 F-4", "A", note="Includes the whole intersection table.")
row("G-term", "vertices and elementary intervals", "439", "Every non-vertex lies in the interior of exactly one elementary interval; only the x_n lie on none; continuity is tested on pieces.", "G.elementaryInterval_unique (planned)", M+"G.Construction", "Cn-G P-basic3", "A")
row("L-closed", "lem:closed (1)-(3)", "443-455", "How a closed set meets the pieces.", "G.finite_of_infty_notMem, G.finite_spines, G.exists_eps (planned)", M+"G.Closed", "L-Gmosaic", "A")
row("L-binary", "lem:binary", "460-479", "Binary extension lemma (Tietze on elementary intervals).", "G.exists_binary_extension (planned)", M+"G.Tychonoff", "L-closed G-term", "A")
row("T-tych", "thm:tych", "481-500", "G is Tychonoff; each p_D has a neighbourhood containing no other p_D'.", "G.completelyRegularSpace, G.t1Space, G.exists_nhds_pD (planned)", M+"G.Tychonoff", "L-binary", "A")
row("L-routes", "lem:routes", "503-512", "For closed F missing infinity, all but finitely many x_n are joined to infinity by a path missing F.", "G.eventually_joinedIn (planned)", M+"G.Routes", "L-closed Cn-G-mad", "A")
row("P-Glac", "prop:Glac", "514-519", "Path components of open subsets of G are open and arcwise connected; G is locally arcwise connected.", "G.isOpen_pathComponentIn, G.locPathConnectedSpace (planned)", M+"G.Routes", "L-routes L-lac", "A", note="Open path components / local path connectedness: class A. The words 'arcwise connected': E-localimpl-b (EXT-ARC).")
row("L-cut", "lem:cut", "524-535", "A closed connected set containing infinity and x_n contains infinitely many witnesses of row n.", "G.infinite_witnesses (planned)", M+"G.NoCapture", "L-Gmosaic", "A")
row("P-nocapture", "prop:nocapture", "537-546", "A closed connected K containing infinity with countable spread contains only finitely many x_n; no metric continuum contains infinity and infinitely many x_n.", "G.finite_x_of_countable_spread, G.not_capture (planned)", M+"G.NoCapture", "L-cut T-tych Cn-G-mad L-image", "A")
row("R-spread", "rem:spread", "548-550", "Countable spread cannot be weakened to separability (explicit K).", "G.exists_separable_capture (planned)", M+"G.NoCapture", "P-nocapture", "A")
row("T-G", "thm:G (1)-(4)", "553-564", "Summary: G is a Tychonoff mosaic space, locally arcwise connected, x_n -> infinity uncaptured, not an m-continuum space, no path through infinitely many x_n.", "G.main (planned)", M+"G.Main", "L-Gmosaic T-tych P-Glac P-nocapture", "A", note="With 'locally path connected' in place of 'locally arcwise connected'; the arcwise form needs EXT-ARC.")
row("C-Q3", "cor:Q3", "566-571", "G is a locally arcwise connected mosaic space that is not a quasi-curve space; completely regular, sequential, locally pathwise connected, not path-determined.", "answer_Q3 (planned)", M+"Answers", "T-G", "A", note="'Not path-determined' is proved directly from thm:G(4) (class A). 'Locally ARCWISE connected' needs EXT-ARC; everything else is class A.")
row("R-Gprops1", "rem:Gprops(1)", "574", "G is not first countable at infinity.", "G.not_firstCountable_at_infty (planned)", M+"G.Main", "T-G P-fc", "A")
row("R-Gprops2", "rem:Gprops(2)", "574", "G is not Frechet-Urysohn.", "G.not_frechetUrysohn (planned)", M+"G.Main", "L-Gmosaic P-basic4", "A")
row("R-Gprops3", "rem:Gprops(3)", "574", "G is locally m-strongly connected and not an m-continuum space.", "G.locallyMStronglyConnected (planned)", M+"G.Main", "T-G E-localimpl-a", "A")
row("R-Gprops4", "rem:Gprops(4)", "574", "Use of the axiom of choice; role of finite sections.", "-", "-", "", "D", "documentation")
# ---------------------------------------------------------------- Section 5
row("S-fst", "sec:fst: translation", "581-583", "A Hausdorff, sequential, locally pathwise connected space that is not path-determined is a locally arcwise connected mosaic space that is not a quasi-curve space; HE is such a space.", "not_isQuasiCurveSpace_of_not_pathDetermined (planned)", M+"PathDetermined", "P-char P-pathdet-de E-localimpl-b EXT-FST", "C", note="General implication: needs EXT-HM (through P-pathdet (e)=>(a)) and EXT-ARC. HE itself is cited only.")
row("S-vd-def", "sec:vd: definition of SHE", "588-604", "Underlying set, families Phi, M_Phi, lambda, sets A, B, basic neighbourhoods; they generate a topology; L_f.", "SHE.Pt, SHE.instTopologicalSpace (planned)", M+"SHE.Defs", "", "A", note="Parametric in a maximal almost disjoint family of partial functions and an injection lambda into [2/5,3/5]; existence of the family by Zorn is class A.")
row("S-vd-lambda", "sec:vd: lambda with thin range", "591-592", "An injection lambda whose range contains no uncountable compact set exists.", "SHE.exists_lambda (planned)", M+"SHE.Defs", "EXT-VD", "C", note="Not used by the article's own proofs (stated at line 592). Provable from Mathlib with a Bernstein-set argument; needed only where van Douwen's Frechet conclusion is quoted.")
row("S-vd-cited", "sec:vd: van Douwen's theorem", "586, 606, 662", "SHE is sigma-compact, cosmic, regular, locally pathwise connected, Frechet, not path-determined.", "-", "-", "EXT-VD", "C", "blocked", "Cited. Any Lean statement using the Frechet property must carry the range condition on lambda.")
row("L-SHEbasic", "lem:SHEbasic (1)-(6)", "608-630", "Basic neighbourhoods are open; Hausdorff; k -> infinity; arcs embed openly; H(k,a) closed; L_f closed discrete.", "SHE.isOpen_basic, t2Space, tendsto_nat, isOpenEmbedding_arc, isClosed_H, isClosed_L, discrete_L (planned)", M+"SHE.Basic", "S-vd-def", "A")
row("L-bump", "lem:bump", "634-639", "Boundary bumping for compact connected Hausdorff spaces.", "boundary_bumping (planned)", M+"SHE.Bump", "", "A", note="Uses connectedComponent_eq_iInter_isClopen from Mathlib.")
row("P-SHE", "prop:SHE", "641-660", "No compact connected subset of SHE contains infinitely many points of N; SHE is not an m-continuum space.", "SHE.finite_nat_of_compact_connected, SHE.not_isMContinuumSpace (planned)", M+"SHE.NoContinuum", "L-SHEbasic L-bump P-basic4", "A", note="Uses only that lambda takes values in [2/5,3/5].")
row("S-vd-compare", "sec:vd: closing comparison", "662", "Comparison of the mechanisms of SHE and G.", "-", "-", "", "D", "documentation")
# ---------------------------------------------------------------- Section 6
row("L-whitehead", "lem:whitehead", "673-678", "q quotient, L locally compact Hausdorff => q x id_L quotient.", "isQuotientMap_prodMap_id (planned)", M+"Cone.Whitehead", "", "A", note="Mathlib has IsQuotientMap.continuous_lift_prod_left (CompactOpen), which covers the uses.")
row("Cone-prelim", "cone: preliminaries", "681", "Definition of the cone; cone over a compact metrizable space is a metric continuum; neighbourhood base at the vertex.", "Cone, Cone.isMetricContinuum, Cone.nhds_vertex_basis (planned)", M+"Cone.Basic", "R-hausimage", "A")
row("P-cone1", "prop:cone(1)", "686,692", "The punctured cone is open and homeomorphic to Y x [0,1).", "Cone.homeomorphPunctured (planned)", M+"Cone.Basic", "", "A")
row("P-cone2", "prop:cone(2)", "687,694-700", "Each P_alpha is a closed subspace homeomorphic to the cone over the piece.", "Cone.isClosedEmbedding_piece (planned)", M+"Cone.Basic", "L-whitehead P-basic3", "A")
row("P-cone3", "prop:cone(3)", "688,702,705", "The cones over the pieces form a mosaic generating the cone topology; the cone is an m-continuum space; pi is continuous.", "Cone.isMContinuumSpace (planned)", M+"Cone.Basic", "P-cone2", "A")
row("T-cone1", "thm:conetransfer(1)", "710,718", "The cone over a nonempty mosaic space is a contractible m-continuum space.", "Cone.contractibleSpace (planned)", M+"Cone.Transfer", "P-cone3 L-whitehead", "A")
row("T-cone2", "thm:conetransfer(2)", "711,720", "Y locally path connected => path components of open subsets of the cone are open; cone locally arcwise and locally m-strongly connected.", "Cone.locPathConnectedSpace (planned)", M+"Cone.Transfer", "E-localimpl-a", "A", note="Arcwise form needs EXT-ARC.")
row("T-cone3", "thm:conetransfer(3)", "712,722", "Y not m-continuum => the punctured cone is not an m-continuum space.", "Cone.not_isMContinuumSpace_punctured (planned)", M+"Cone.Transfer", "P-cone1 P-classes1 L-image", "A")
row("T-cone4", "thm:conetransfer(4)", "713,724-732", "Every nonempty open subspace of the cone is m-continuum iff the same holds for Y.", "Cone.open_isMContinuumSpace_iff (planned)", M+"Cone.Transfer", "P-cone1 P-cone3 P-classes1", "A")
row("T-cone5", "thm:conetransfer(5)", "714,734", "Continuous real functions separate points of the cone if they separate points of Y; then the cone is Hausdorff.", "Cone.separatesPoints, Cone.t2Space (planned)", M+"Cone.Transfer", "", "A")
row("C-Q2", "cor:Q2", "737-744", "cG is a contractible Hausdorff m-continuum space, locally arcwise connected, whose punctured open subspace is not m-continuum; not a quasi-curve space; also a counterexample to Q1a, Q1b, Q3.", "answer_Q2 (planned)", M+"Answers", "T-G T-cone1 T-cone2 T-cone3 T-cone5 P-qcopen", "A", note="Arcwise form needs EXT-ARC; all else class A.")
row("R-coneSHE", "rem:coneSHE", "746-748", "cSHE is another counterexample to Q2.", "-", M+"Answers", "P-SHE EXT-VD", "C", "blocked", "Depends on van Douwen's local path connectedness of SHE (cited).")
# ---------------------------------------------------------------- Section 7
row("P-fc", "prop:fc", "755-765", "First countable point with small open m-strongly connected neighbourhoods: a tail of every convergent sequence in U lies with the limit in a metric continuum inside U. Consequence for first countable spaces; equivalence of (H) and (LmS).", "exists_metricContinuum_tail, FirstCountable.open_isMContinuumSpace (planned)", M+"FirstCountable", "C-image3 P-classes1 P-char P-lav52", "A")
row("P-fcpath1", "prop:fcpath, path through a tail", "767-776", "First countable point with small open path connected neighbourhoods: a path f with f(1)=x and f(1-1/j)=x_{N+j-1}.", "exists_path_through_tail (planned)", M+"FirstCountable", "", "A", note="Nested choice of W_k as in the article.")
row("P-fcpath2", "prop:fcpath, consequence", "770,777", "Every first countable, locally arcwise connected mosaic space is a quasi-curve space.", "FirstCountable.isQuasiCurveSpace (planned)", M+"FirstCountable", "P-fcpath1 P-classes2 EXT-HMC", "A", note="Needs 'path image is a Peano continuum' (EXT-HMC, short).")
row("Z-exist", "existence of Z", "781", "A connected, locally connected plane set with more than one point and no nondegenerate continuum exists.", "exists_Z (planned)", M+"External.PlaneBernstein", "EXT-Z", "C", "blocked", "The article itself uses this without proof.")
row("X-cZ", "ex:cZ", "783-792", "cZ is an m-continuum space, locally connected, not locally m-strongly connected, not a quasi-curve space.", "ConeZ.main (planned; parametric in Z)", M+"ConeZ", "P-cone3 P-cone1 C-qclac", "A", note="Parametric statement is class A (the last clause via P-qcopen + P-lav52, avoiding C-qclac). Unconditional existence needs Z-exist.")
row("T-chain-impl", "thm:chain: implications", "795-806", "(QC) => (H) => (LmS) => (LC); (QC) => LAC => (LmS).", "chain_implications (planned)", M+"Chain", "P-qcopen P-lav52 I-2 C-qclac E-localimpl-a", "A", note="(QC) => LAC needs EXT-PLPC + EXT-ARC.")
row("T-chain-strict", "thm:chain: strictness and independence", "803-808", "None of the three implications reverses; LAC is independent of (H).", "chain_strict (planned)", M+"Chain", "C-Q1 C-Q2 X-cZ Z-exist", "B", "blocked", "Blocked on EXT-ARCLESS (E(K)), EXT-Z (cZ), EXT-PLPC, EXT-ARC. The witness cG for (LmS) not=> (H) is class A.")
row("T-chain-fc", "closing remark", "810", "For first countable m-continuum spaces (H) <=> (LmS) and (QC) <=> LAC.", "FirstCountable.chain (planned)", M+"Chain", "P-fc P-fcpath2 C-qclac", "B", note="(QC) => LAC needs EXT-PLPC + EXT-ARC.")
row("AI", "Use of artificial intelligence", "830-831", "Disclosure statement.", "-", "-", "", "D", "documentation")

# ---------------------------------------------------------------- state after the 2026-11-16 session
# Overrides of the planning table above: the Lean declarations that actually exist, the module
# that holds them, and the status. Status vocabulary (replaces the planning vocabulary):
#   compared       stated in Challenge.lean; proved under the same name in Solution.lean;
#                  `lake comparator` (unsandboxed, also --paranoid) accepted it; axioms audited.
#   proved         library declaration, compiled by `lake build`; not itself a Comparator target
#                  (it is used by compared results or is a supporting statement).
#   partial        a variant or part of the article's statement is proved (see note); the rest is not.
#   not-formalized no Lean statement.
#   blocked        needs an external classical theorem that is not formalized (see EXT).
#   documentation  no Lean content intended.
P = "MosaicSpaces.Paper."
UPD = {
 "I-1": ("compared", P + "cor_2_9_qc, " + P + "cor_2_9_2_full; IsCurveSpace.isQuasiCurveSpace, IsMContinuumSpace.isMosaicSpace", "Mosaic, Classes, Peano.Consequences", "m-continuum => mosaic is a library lemma."),
 "I-2": ("compared", P + "display_2_1 (third conjunct); LocallyMStronglyConnected.locallyConnectedSpace", "Local", ""),
 "I-3": ("compared", P + "prop_2_7_t2; isMosaicSpace_of_t2", "Mosaic", "CW-complex remark is illustration only."),
 "C-1": ("partial", P + "compact_locallyConnected_lpc, " + P + "peano_classical, " + P + "quasiPeano_components, " + P + "arc_theorem", "Peano.LPC, Peano.Consequences, Arc.Param", "Proved and compared: compact locally connected metrizable => locally path connected; Peano continua are path connected, arcwise connected, locally path/arcwise connected and contain arcs; quasi-Peano spaces have finitely many open Peano components; the arc theorem. NOT formalized: the Hahn-Mazurkiewicz theorem itself (Hausdorff path image <=> Peano continuum, direction <=). No formalized result depends on it."),
 "D-mosaic": ("compared", P + "def_2_1_mosaic, " + P + "def_2_1_mContinuum, " + P + "def_2_1_quasiCurve, " + P + "def_2_1_curve; IsAbstractMosaic, mosaicTopology, IsAbstractMosaicSpaceWith", "Abstract", "Abstract Definition 2.1 formalized and shown equivalent to the intrinsic definitions used throughout."),
 "D-mosaic-eq": ("compared", P + "def_2_1_mosaic (and the three variants); isMosaicSpaceWith_iff_abstract", "Abstract", ""),
 "L-recognise": ("compared", P + "lemma_2_2, " + P + "lemma_2_2_closed, " + P + "lemma_2_2_finite", "Abstract", "Main statement and both 'in particular' clauses."),
 "P-basic1": ("compared", P + "prop_2_3_1; isClosedEmbedding_val", "Abstract", "No compact-metric hypothesis needed."),
 "P-basic2": ("compared", P + "prop_2_3_t1; IsMosaicFamily.t1Space, IsMosaicSpace.t1Space", "Mosaic", ""),
 "P-basic3": ("compared", P + "prop_2_3_3; IsMosaicFamily.continuous_iff, IsMosaicFamily.isQuotientMap_sigma", "Cone", ""),
 "P-basic-star": ("proved", "IsMosaicFamily.exists_subseq_tendsto_in_piece", "Mosaic", "Proved without the injectivity hypothesis."),
 "P-basic4": ("compared", P + "prop_2_3_456 (first conjunct); IsMosaicFamily.exists_piece_subseq", "Mosaic", ""),
 "P-basic5": ("compared", P + "prop_2_3_456 (second conjunct); IsMosaicFamily.uniqueSeqLimits", "Mosaic", ""),
 "P-basic6": ("compared", P + "prop_2_3_456 (third conjunct); IsMosaicFamily.sequentialSpace", "Mosaic", ""),
 "L-image": ("compared", P + "lemma_2_4; range_closed_compact_metrizable", "Image", ""),
 "R-hausimage": ("compared", P + "remark_2_5; range_compact_metrizable_of_t2", "Image", ""),
 "C-image1": ("compared", P + "cor_2_6_union; IsMetricContinuum.union", "Continua", ""),
 "C-image2a": ("compared", P + "cor_2_6_2; isMetricContinuum_range_path, IsPathConnected.exists_metricContinuum", "Continua", ""),
 "C-image2b": ("compared", P + "cor_2_6_2, " + P + "cor_2_6_2_arc, " + P + "arc_theorem; isPeanoContinuum_range_path, isArcBetween_of_joinedIn", "Classes, ArcConsequences, Arc.Param", ""),
 "C-image3": ("compared", P + "cor_2_6_3; isMetricContinuum_iUnion_of_null", "Continua", ""),
 "P-char": ("compared", P + "prop_2_7, " + P + "prop_2_7_t2, " + P + "prop_2_7_open", "Mosaic, Continua", ""),
 "L-generate": ("compared", P + "lemma_2_8; isMosaicFamily_iff_captures", "Classes", ""),
 "P-classes1": ("compared", P + "cor_2_9_1; isMContinuumSpace_iff_captures", "Classes", ""),
 "P-classes2": ("compared", P + "cor_2_9_2_full, " + P + "cor_2_9_2, " + P + "cor_2_9_2_path", "Classes, Peano.Consequences", ""),
 "P-classes2d": ("compared", P + "cor_2_9_2_full; IsCurveSpace.capturesPath, IsPeanoContinuum.exists_pathImage_tail", "Peano.Consequences", "(c) => (d) is proved WITHOUT Hahn-Mazurkiewicz: a convergent sequence in a Peano continuum has a tail on one path (Peano continua are locally path connected and first countable; Prop. 7.2's construction)."),
 "D-pathdet": ("compared", "Determines, IsPathDetermined, ClosedTestedByPaths, IsQuotientOfIntervals (in Challenge.lean); " + P + "prop_2_10", "PathDetermined", ""),
 "P-pathdet-abc": ("compared", P + "prop_2_10, " + P + "prop_2_10_quotient", "PathDetermined", "(c) in prop_2_10 indexes the sum by a type in the universe of X; prop_2_10_quotient gives (c) => (b) for any universe."),
 "P-pathdet-de": ("compared", P + "prop_2_10; IsPathDetermined.isCurveSpace, IsCurveSpace.closedTestedByPaths", "PathDetermined", "(d) => (b) is proved through Corollary 2.9(2)(d) instead of Hahn-Mazurkiewicz."),
 "D-local": ("proved", "MStronglyConnected, LocallyMStronglyConnected, LocallyConnectedOpen, LocallyPathConnectedOpen, IsArcBetween, ArcwiseConnected, LocallyArcwiseConnected, IsArc; locallyConnectedOpen_iff, locallyPathConnectedOpen_iff", "Local", "Open-set forms, shown equivalent to Mathlib's classes where these exist."),
 "E-localimpl-a": ("compared", P + "display_2_1", "Local", "LAC => LPC => LmS => LC."),
 "E-localimpl-b": ("compared", P + "display_2_1_iff; IsMosaicSpace.locallyArcwiseConnected_iff", "ArcConsequences", "LPC <=> LAC in every mosaic space (path images are compact metrizable, hence Hausdorff)."),
 "P-lav52": ("compared", P + "prop_2_12; locallyMStronglyConnected_of_forall_isOpen", "Local", ""),
 "P-qcopen": ("compared", P + "prop_2_13; IsQuasiCurveSpace.isMContinuumSpace_of_isOpen", "Local", ""),
 "L-lac": ("compared", P + "lemma_2_14_article, " + P + "lemma_2_14; IsMosaicFamily.lemma_2_14_lc", "Peano.Consequences, ArcConsequences", "Article's hypothesis (pieces not locally connected) and conclusion (open, arcwise connected path components; LAC)."),
 "C-qclac": ("compared", P + "cor_2_15; IsQuasiCurveSpace.cor_2_15", "Peano.Consequences", ""),
 "R-curtis": ("partial", P + "remark_3_7; mContinuum_not_quasiCurve_of_firstCountable", "Peano.Consequences", "The implication used in the remark is compared. Curtis's example itself is cited and, as the article says, unverified; it is not formalized."),
 "C-Q1": ("partial", P + "answer_Q1a, " + P + "answer_Q1b (via the cone over G)", "Answers", "Q1a and Q1b are answered, and Comparator-checked, by the cone over G, as the article itself remarks after Corollary 6.4. The article's own route (Corollary 3.5 via E(K)) is an example and is not formalized (out of scope by request)."),
 "F-metric": ("compared", P + "fan_metric; Fan.phi, Fan.isOpen_iff_phi, Fan.phi_spine_same, Fan.phi_spine_ne", "FanMetric", "Fan(J) is the subspace of J -> R (product topology); the article's metric phi (nu shifted by 1) is proved to be a metric inducing exactly this topology, for every injection nu."),
 "F-1": ("proved", P + "fan_metric (topology independent of nu); Fan.mem_nhds_centre_iff", "FanMetric", "Independence of nu is compared; the neighbourhood characterization of the centre is a library theorem."),
 "F-2": ("proved", "Fan.isCompact_fan, Fan instances CompactSpace / MetrizableSpace, Fan.pathConnectedSpace, Fan.locallyPathConnectedSpace, Fan.spine_arc", "Fan, FanMetric", ""),
 "F-3": ("proved", "Fan.tendsto_centre", "Fan", ""),
 "F-4": ("proved", "Fan.extend, Fan.isClosedEmbedding_extend", "FanMetric", "Not used by the proofs: the Lambda-Lambda compatibility is proved with GSpace.restr."),
 "Cn-G-mad": ("compared", P + "exists_madFamily; exists_isMADFamily, IsC, IsMADFamily", "G/Basic", "Zorn's lemma."),
 "Cn-G": ("proved", "GSpace, GSpace.gTop, rowMap, sigMap, phiMap, lamMap, arcMap, spokeMap, witT", "G/Basic", "Inductive type; topology = final topology of the piece maps. Witness (n,i) at 1/(i+1); arcMap runs from infinity to p_D."),
 "L-Gmosaic": ("proved", "GSpace.isMosaicFamily_pieces, GSpace.isMosaicSpace, GSpace.isClosedEmbedding_rowMap/_sigMap/_phiMap/_lamMap, GSpace.tendsto_xpt, GSpace.pnt_mem_of_infinite", "G/Basic, G/Mosaic, G/Capture", "Enters the compared statement " + P + "theorem_4_11."),
 "G-term": ("documentation", "-", "-", "Terminology."),
 "L-closed": ("proved", "GSpace.finite_xpt_mem, GSpace.finite_arc_mem, GSpace.finite_spoke_mem, GSpace.finite_wit_mem, GSpace.exists_row_nmem", "G/Mosaic", ""),
 "L-binary": ("proved", "GSpace.exists_binary", "G/Tychonoff", "Enters " + P + "theorem_4_11 through T35Space."),
 "T-tych": ("compared", P + "theorem_4_11 (T35Space; injective p with isolating neighbourhoods); GSpace.t35Space, GSpace.exists_isolating_nhd", "G/Tychonoff, G/Capture", ""),
 "L-routes": ("proved", "GSpace.routes", "G/Mosaic", ""),
 "P-Glac": ("compared", P + "theorem_4_11; GSpace.isOpen_pathComponentIn, G_arcwise", "G/Mosaic, Answers", ""),
 "L-cut": ("proved", "GSpace.infinite_wit_of_isPreconnected", "G/Capture", "Only closedness and preconnectedness of K are used."),
 "P-nocapture": ("compared", P + "theorem_4_11 (countable-spread clause and metric-continuum clause); GSpace.finite_xpt_of_spread", "G/Capture", ""),
 "R-spread": ("compared", P + "theorem_4_11 (Remark 4.10 clause); GSpace.remark_4_10", "G/Remarks", ""),
 "T-G": ("compared", P + "theorem_4_11; MosaicSpaces.G_properties", "Answers", "All of (1)-(4)."),
 "C-Q3": ("compared", P + "answer_Q3", "Answers", "Including 'not path-determined'."),
 "R-Gprops1": ("compared", P + "theorem_4_11; G_not_isCountablyGenerated_nhds_infty, G_not_firstCountable", "Answers", ""),
 "R-Gprops2": ("compared", P + "theorem_4_11; GSpace.not_frechetUrysohnSpace", "G/Remarks", ""),
 "R-Gprops3": ("compared", P + "theorem_4_11", "Answers", ""),
 "S-fst": ("partial", P + "sec_5_1_translation", "Answers", "The general translation is compared; the space HE is cited, not formalized."),
 "L-bump": ("compared", P + "lemma_5_2; boundary_bumping", "Classical.Bump", ""),
 "L-whitehead": ("compared", P + "lemma_6_1; isQuotientMap_prodMap_id", "Cone", "Without the Hausdorff hypothesis on L."),
 "Cone-prelim": ("proved", "Cone, Cone.mk, Cone.vertex, Cone.compactSpace, Cone.metrizableSpace, Cone.connectedSpace, Cone.isMetricContinuum_univ", "Cone", ""),
 "P-cone1": ("compared", P + "prop_6_2_1; Cone.isOpenEmbedding_punctured, Cone.range_punctured", "Cone", ""),
 "P-cone2": ("compared", P + "prop_6_2_2; Cone.isClosedEmbedding_pieceMap, Cone.isMetricContinuum_piece", "Cone", ""),
 "P-cone3": ("compared", P + "prop_6_2_3, " + P + "theorem_6_3_1; Cone.isMosaicFamily_pieces, Cone.isMContinuumSpace", "Cone", ""),
 "T-cone1": ("compared", P + "theorem_6_3_1; Cone.contractibleSpace", "Cone", ""),
 "T-cone2": ("compared", P + "theorem_6_3_2; Cone.locallyPathConnectedSpace, Cone.locallyMStronglyConnected", "Cone", ""),
 "T-cone3": ("compared", P + "theorem_6_3_3; Cone.not_isMContinuumSpace_punctured", "Cone", ""),
 "T-cone4": ("compared", P + "theorem_6_3_4; Cone.allOpenMCont_of_cone, Cone.allOpenMCont_cone", "Cone4", ""),
 "T-cone5": ("compared", P + "theorem_6_3_5, " + P + "theorem_6_3_5_sep; Cone.separatesPoints, Cone.t2Space", "Cone", ""),
 "C-Q2": ("compared", P + "answer_Q2; answer_Q2_full", "Answers", "Corollary 6.4 in full (Hausdorff, contractible, LAC, LmS, open non-m-continuum subspace, not QC)."),
 "P-fc": ("compared", P + "prop_7_1, " + P + "prop_7_1_tail; exists_metricContinuum_tail, isMContinuumSpace_of_isOpen_of_firstCountable", "FirstCountable", ""),
 "P-fcpath1": ("compared", P + "prop_7_2_tail; exists_path_through_tail, exists_concat_path", "FirstCountable", "No mosaic hypothesis needed."),
 "P-fcpath2": ("compared", P + "prop_7_2, " + P + "prop_7_2_path; isCurveSpace_of_firstCountable, isQuasiCurveSpace_of_firstCountable", "FirstCountable", "Only local path connectedness is used."),
 "T-chain-impl": ("compared", P + "theorem_7_4_impl, " + P + "theorem_7_4_lac; chain_implications, chain_lac", "Answers, Peano.Consequences", "Stated for all mosaic spaces."),
 "T-chain-strict": ("partial", P + "theorem_7_4_strict_H_LmS, " + P + "theorem_7_4_strict_LAC_H; chain_strict_H_LmS, chain_LAC_not_H", "Answers", "(LmS) =/=> (H) and LAC =/=> (H) (witness cG) are compared. (H) =/=> (QC), (LC) =/=> (LmS) and (H) =/=> LAC need E(K) and cZ: examples, out of scope by request."),
 "T-chain-fc": ("compared", P + "theorem_7_4_firstCountable, " + P + "theorem_7_4_firstCountable_lac", "Answers, Peano.Consequences", ""),
}
for _k in ["K-exist","Cn-plus","A-obs","A-claim1","A-claim2","A-claim3","L-plus","Cn-EY","T-arcless0","T-arcless1","T-arcless2","T-arcless3a","T-arcless3b","T-arcless4","T-arcless5","R-complete","S-vd-def","S-vd-lambda","L-SHEbasic","P-SHE","Z-exist","X-cZ","R-coneSHE"]:
    UPD[_k] = ("not-formalized", "-", "-", "Out of scope by request (examples are not formalized).")
for r in R:
    if r["id"] in UPD:
        st, lean, mod, note = UPD[r["id"]]
        r["status"], r["lean"] = st, lean
        r["module"] = mod if mod == "-" else ", ".join(M + m.strip() for m in mod.split(","))
        r["note"] = note
    elif r["status"] in ("not-started", "written-unchecked"):
        r["status"] = "not-formalized"
assert set(UPD) <= {r["id"] for r in R}, set(UPD) - {r["id"] for r in R}

def main():
    root = pathlib.Path(__file__).resolve().parent.parent
    ids = [r["id"] for r in R]
    assert len(ids) == len(set(ids)), "duplicate ids"
    known = set(ids) | set(EXT)
    for r in R:
        for d in r["deps"]:
            assert d in known, (r["id"], d)
    counts = collections.Counter(r["status"] for r in R)
    cls = collections.Counter(r["cls"] for r in R)
    out = dict(article="article/mosaic_article.tex", external=EXT, rows=R,
               status_counts=dict(counts), class_counts=dict(cls))
    (root / "ledger" / "coverage.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    md = ["# Coverage ledger", "",
          "Generated by `ledger/build_ledger.py` from the article `article/mosaic_article.tex`. "
          "The exact informal statement of each item is at the cited line range of that file; "
          "the `Statement` column is a short paraphrase.", "",
          "Status values: `compared` = stated in `Challenge.lean`, proved under the same name in "
          "`Solution.lean`, accepted by `lake comparator` (run WITHOUT the bwrap sandbox, which was not "
          "available; also with `--paranoid`) and axiom-audited; `proved` = library declaration "
          "accepted by `lake build`, not itself a Comparator target; `partial` = only the part or "
          "variant named in the note is proved; `not-formalized`; `blocked` = depends on an external "
          "theorem that is not formalized; `documentation` = no Lean content intended. None of these "
          "statuses means 'registered by Palomar'.", "",
          "Status counts: " + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) + ".", "",
          "Class counts: " + ", ".join(f"{k}: {v}" for k, v in sorted(cls.items())) + ".", "",
          "## External dependencies", ""]
    for k, v in EXT.items():
        md.append(f"- **{k}** {v}")
    md += ["", "## Items", "",
           "| Id | Article label | Lines | Statement | Lean declaration(s) | Module | Depends on | Class | Status | Notes |",
           "|---|---|---|---|---|---|---|---|---|---|"]
    esc = lambda s: s.replace("|", "\\|")
    for r in R:
        md.append("| " + " | ".join([r["id"], esc(r["label"]), r["lines"], esc(r["stmt"]),
              "`" + esc(r["lean"]) + "`", "`" + r["module"] + "`", " ".join(r["deps"]) or "-",
              r["cls"], r["status"], esc(r["note"]) or "-"]) + " |")
    (root / "docs" / "COVERAGE_LEDGER.md").write_text("\n".join(md) + "\n", encoding="utf-8")
    print(len(R), "rows;", dict(counts), dict(cls))

if __name__ == "__main__":
    main()
