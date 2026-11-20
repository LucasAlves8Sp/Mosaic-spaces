module

public import MosaicSpaces.Classes

/-!
# Local properties (article: Definition 2.11, display (2.1), Propositions 2.11 and 2.12)

All local properties are stated in the article's open-set form: every open set containing a
point contains an *open* set with the property containing the point. For local connectedness and
local path connectedness these forms are proved equivalent to Mathlib's `LocallyConnectedSpace`
and `LocallyPathConnectedSpace`.

Arcs: `IsArcBetween s x y` says that some topological embedding `[0,1] → X` with image in `s`
runs from `x` to `y`. The implication "locally path connected ⇒ locally arcwise connected" of
display (2.1) uses the arc theorem and is `IsMosaicSpace.locallyArcwiseConnected_iff`
(`MosaicSpaces.ArcConsequences`); the other implications are proved here.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ### Definitions -/

/-- **Definition 2.11**: a set is *m-strongly connected* if any two of its points lie in a metric
continuum contained in it. -/
def MStronglyConnected (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ L ⊆ s, IsMetricContinuum L ∧ x ∈ L ∧ y ∈ L

/-- **Definition 2.11**: every open set containing a point contains an open m-strongly connected
set containing the point. -/
def LocallyMStronglyConnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (O : Set X), IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ MStronglyConnected W

/-- Local connectedness in the article's open-set form. -/
def LocallyConnectedOpen (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (O : Set X), IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsConnected W

/-- Local path connectedness in the article's open-set form. -/
def LocallyPathConnectedOpen (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (O : Set X), IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPathConnected W

/-- An arc in `s` from `x` to `y`: a topological embedding of `[0,1]` with image in `s`,
`0 ↦ x`, `1 ↦ y`. -/
def IsArcBetween (s : Set X) (x y : X) : Prop :=
  ∃ f : unitInterval → X, IsEmbedding f ∧ f 0 = x ∧ f 1 = y ∧ range f ⊆ s

/-- A set is *arcwise connected* if any two distinct points of it are the end points of an arc
contained in it (article, after Definition 2.11). -/
def ArcwiseConnected (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsArcBetween s x y

/-- Local arcwise connectedness in the article's open-set form. -/
def LocallyArcwiseConnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (O : Set X), IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ ArcwiseConnected W

/-- A subset is an *arc* if it is homeomorphic to `[0,1]` (as the image of an embedding). -/
def IsArc (A : Set X) : Prop :=
  ∃ f : unitInterval → X, IsEmbedding f ∧ range f = A

/-! ### Agreement with Mathlib's classes -/

theorem locallyConnectedOpen_iff : LocallyConnectedOpen X ↔ LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  constructor
  · intro h x U hU
    obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.1 hU
    obtain ⟨W, hW, hxW, hWO, hWc⟩ := h x O hO hxO
    exact ⟨W, hWO.trans hOU, hW, hxW, hWc⟩
  · intro h x O hO hxO
    obtain ⟨W, hWO, hW, hxW, hWc⟩ := h x O (hO.mem_nhds hxO)
    exact ⟨W, hW, hxW, hWO, hWc⟩

theorem locallyPathConnectedOpen_iff :
    LocallyPathConnectedOpen X ↔ LocallyPathConnectedSpace X := by
  constructor
  · intro h
    rw [locallyPathConnectedSpace_iff_isOpen_pathComponentIn]
    intro x U hU
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    have hyU : y ∈ U := pathComponentIn_subset hy
    obtain ⟨W, hW, hyW, hWU, hWp⟩ := h y U hU hyU
    refine ⟨W, ?_, hW, hyW⟩
    have h1 : W ⊆ pathComponentIn U y := hWp.subset_pathComponentIn hyW hWU
    rwa [pathComponentIn_congr hy] at h1
  · intro h x O hO hxO
    exact ⟨pathComponentIn O x, hO.pathComponentIn x, mem_pathComponentIn_self hxO,
      pathComponentIn_subset, isPathConnected_pathComponentIn hxO⟩

/-! ### display (2.1) -/

/-- An arcwise connected nonempty set is path connected. -/
theorem ArcwiseConnected.isPathConnected {s : Set X} (hs : ArcwiseConnected s)
    (hne : s.Nonempty) : IsPathConnected s := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hx, fun {y} hy => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact JoinedIn.refl hx
  · obtain ⟨f, hf, hf0, hf1, hfs⟩ := hs x hx y hy hxy
    refine ⟨⟨⟨f, hf.continuous⟩, hf0, hf1⟩, fun t => hfs ⟨t, rfl⟩⟩

/-- display (2.1): locally arcwise connected ⇒ locally path connected (open-set forms). -/
theorem LocallyArcwiseConnected.locallyPathConnectedOpen (h : LocallyArcwiseConnected X) :
    LocallyPathConnectedOpen X := fun x O hO hxO =>
  let ⟨W, hW, hxW, hWO, hWa⟩ := h x O hO hxO
  ⟨W, hW, hxW, hWO, hWa.isPathConnected ⟨x, hxW⟩⟩

/-- A path connected set is m-strongly connected (Corollary 2.6(2)). -/
theorem IsPathConnected.mStronglyConnected [SequentialSpace X] (hX : UniqueSeqLimits X)
    {s : Set X} (hs : IsPathConnected s) : MStronglyConnected s :=
  fun _ hx _ hy => MosaicSpaces.IsPathConnected.exists_metricContinuum hX hs hx hy

/-- display (2.1): in a mosaic space, locally path connected ⇒ locally m-strongly connected. -/
theorem LocallyPathConnectedOpen.locallyMStronglyConnected (hX : IsMosaicSpace X)
    (h : LocallyPathConnectedOpen X) : LocallyMStronglyConnected X := by
  haveI := hX.sequentialSpace
  intro x O hO hxO
  obtain ⟨W, hW, hxW, hWO, hWp⟩ := h x O hO hxO
  exact ⟨W, hW, hxW, hWO,
    MosaicSpaces.IsPathConnected.mStronglyConnected hX.uniqueSeqLimits hWp⟩

/-- An m-strongly connected nonempty set is connected. -/
theorem MStronglyConnected.isConnected {s : Set X} (hs : MStronglyConnected s) {x : X}
    (hx : x ∈ s) : IsConnected s := by
  refine ⟨⟨x, hx⟩, ?_⟩
  have hcov : s = ⋃ y : s, (hs x hx y y.2).choose := by
    apply Subset.antisymm
    · intro y hy
      exact mem_iUnion.2 ⟨⟨y, hy⟩, (hs x hx y hy).choose_spec.2.2.2⟩
    · exact iUnion_subset fun y => (hs x hx y y.2).choose_spec.1
  rw [hcov]
  exact isPreconnected_iUnion ⟨x, mem_iInter.2 fun y => (hs x hx y y.2).choose_spec.2.2.1⟩
    fun y => (hs x hx y y.2).choose_spec.2.1.2.1.2

/-- display (2.1) and the introduction: locally m-strongly connected ⇒ locally connected. -/
theorem LocallyMStronglyConnected.locallyConnectedOpen (h : LocallyMStronglyConnected X) :
    LocallyConnectedOpen X := fun x O hO hxO =>
  let ⟨W, hW, hxW, hWO, hWm⟩ := h x O hO hxO
  ⟨W, hW, hxW, hWO, hWm.isConnected hxW⟩

theorem LocallyMStronglyConnected.locallyConnectedSpace (h : LocallyMStronglyConnected X) :
    LocallyConnectedSpace X :=
  locallyConnectedOpen_iff.1 h.locallyConnectedOpen

/-! ### Proposition 2.12 (Lavallee, Theorem 5.2) -/

/-- Pushing a metric continuum of an open subspace that captures a sequence into the ambient
space. -/
theorem captures_in_open (hX : IsMosaicSpace X) {O : Set X} (hO : IsOpen O)
    (hm : IsMContinuumSpace O) {u : ℕ → X} {z : X} (hzO : z ∈ O)
    (hu : Tendsto u atTop (𝓝 z)) :
    ∃ L ⊆ O, IsMetricContinuum L ∧ z ∈ L ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ L := by
  have hev : ∀ᶠ n in atTop, u n ∈ O := hu.eventually (hO.mem_nhds hzO)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let v : ℕ → O := fun n => ⟨u (n + N), hN _ (Nat.le_add_left N n)⟩
  have hv : Tendsto v atTop (𝓝 ⟨z, hzO⟩) :=
    tendsto_subtype_rng.2 (hu.comp (tendsto_add_atTop_nat N))
  obtain ⟨L, hL, hzL, φ, hφ, hφL⟩ :=
    (isMContinuumSpace_iff_captures (hX.of_isOpen hO)).1 hm v _ hv
  refine ⟨(↑) '' L, fun _ ⟨y, _, hy⟩ => hy ▸ y.2, isMetricContinuum_val_image.2 hL,
    ⟨_, hzL, rfl⟩, fun n => φ n + N, fun i j hij => Nat.add_lt_add_right (hφ hij) N,
    fun n => ⟨_, hφL n, rfl⟩⟩

/-- **Proposition 2.12** (Lavallee, Theorem 5.2). A mosaic space every nonempty open subspace of
which is an m-continuum space is locally m-strongly connected. -/
theorem locallyMStronglyConnected_of_forall_isOpen (hX : IsMosaicSpace X)
    (h : ∀ U : Set X, IsOpen U → U.Nonempty → IsMContinuumSpace U) :
    LocallyMStronglyConnected X := by
  haveI := hX.sequentialSpace
  have hU := hX.uniqueSeqLimits
  intro x O hO hxO
  let C : Set X := {y | ∃ L ⊆ O, IsMetricContinuum L ∧ x ∈ L ∧ y ∈ L}
  have hxC : x ∈ C :=
    ⟨{x}, singleton_subset_iff.2 hxO, isMetricContinuum_singleton hU x, rfl, rfl⟩
  have hCO : C ⊆ O := fun y ⟨L, hLO, _, _, hyL⟩ => hLO hyL
  have hsub : ∀ L ⊆ O, IsMetricContinuum L → x ∈ L → L ⊆ C :=
    fun L hLO hL hxL y hyL => ⟨L, hLO, hL, hxL, hyL⟩
  refine ⟨C, ?_, hxC, hCO, ?_⟩
  · rw [← isClosed_compl_iff]
    refine IsSeqClosed.isClosed fun u z hu hz => ?_
    intro hzC
    obtain ⟨K, hKO, hK, hxK, hzK⟩ := hzC
    obtain ⟨L, hLO, hL, hzL, φ, -, hφL⟩ :=
      captures_in_open hX hO (h O hO ⟨x, hxO⟩) (hKO hzK) hz
    have hKL : IsMetricContinuum (K ∪ L) := hK.union hU hL ⟨z, hzK, hzL⟩
    exact hu (φ 0) (hsub _ (union_subset hKO hLO) hKL (Or.inl hxK) (Or.inr (hφL 0)))
  · rintro y ⟨K, hKO, hK, hxK, hyK⟩ y' ⟨K', hK'O, hK', hxK', hyK'⟩
    have hKK' : IsMetricContinuum (K ∪ K') := hK.union hU hK' ⟨x, hxK, hxK'⟩
    exact ⟨K ∪ K', hsub _ (union_subset hKO hK'O) hKK' (Or.inl hxK), hKK', Or.inl hyK,
      Or.inr hyK'⟩

/-! ### Proposition 2.13 -/

/-- **Proposition 2.13**. Every open subspace of a quasi-curve space is an m-continuum space.
(The article says "nonempty"; for the empty subspace the statement holds as well.) -/
theorem IsQuasiCurveSpace.isMContinuumSpace_of_isOpen (h : IsQuasiCurveSpace X) {U : Set X}
    (hU : IsOpen U) : IsMContinuumSpace U := by
  have hX : IsMosaicSpace X := h.isMosaicSpace
  haveI := hX.sequentialSpace
  rw [isMContinuumSpace_iff_captures (hX.of_isOpen hU)]
  intro v b hv
  have hv' : Tendsto (fun n => (v n : X)) atTop (𝓝 (b : X)) := tendsto_subtype_rng.1 hv
  obtain ⟨P, ⟨⟨hPc, -, hPm⟩, hPl⟩, hbP, φ, hφ, hφP⟩ := h.capturesPeano _ _ hv'
  haveI := hPm
  haveI := hPl
  haveI : CompactSpace P := isCompact_iff_compactSpace.1 hPc
  let b' : P := ⟨b, hbP⟩
  have hV : (↑) ⁻¹' U ∈ 𝓝 b' := (hU.preimage continuous_subtype_val).mem_nhds b.2
  obtain ⟨F, hF, hFc, hFU⟩ := exists_mem_nhds_isClosed_subset hV
  let W : Set P := connectedComponentIn (interior F) b'
  have hbW : b' ∈ W := mem_connectedComponentIn (mem_interior_iff_mem_nhds.2 hF)
  have hWo : IsOpen W := isOpen_interior.connectedComponentIn
  have hWF : closure W ⊆ F :=
    closure_minimal ((connectedComponentIn_subset _ _).trans interior_subset) hFc
  have hM : IsMetricContinuum (closure W) :=
    ⟨isClosed_closure.isCompact, (isConnected_connectedComponentIn_iff.2
      (mem_interior_iff_mem_nhds.2 hF)).closure, inferInstance⟩
  have hM1 : IsMetricContinuum ((↑) '' closure W : Set X) := isMetricContinuum_val_image.2 hM
  have hM1U : ((↑) '' closure W : Set X) ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hFU (hWF hy)
  have hconv : Tendsto (fun n => (⟨v (φ n), hφP n⟩ : P)) atTop (𝓝 b') :=
    tendsto_subtype_rng.2 (hv'.comp hφ.tendsto_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hconv.eventually (hWo.mem_nhds hbW))
  refine ⟨(↑) ⁻¹' ((↑) '' closure W : Set X), hM1.preimage_val hM1U,
    ⟨b', subset_closure hbW, rfl⟩, fun n => φ (n + N), fun i j hij => hφ (by omega),
    fun n => ⟨_, subset_closure (hN (n + N) (Nat.le_add_left N n)), rfl⟩⟩

end MosaicSpaces
