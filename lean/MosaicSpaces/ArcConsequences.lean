module

public import MosaicSpaces.PathComponents
public import MosaicSpaces.Arc.Param

/-!
# Arcs in mosaic spaces

With the arc theorem (`Arc.exists_arc`) the arcwise statements of the article follow from the
path statements:

* `isArcBetween_of_joinedIn` (Corollary 2.6(2), "hence every path connected subset of `X` is
  arcwise connected"): in a sequential space with unique sequential limits, in particular in a
  mosaic space, two distinct points joined by a path in `s` are joined by an arc in `s`. The
  image of the path is compact and metrizable (Lemma 2.4), hence Hausdorff, and the arc theorem is
  applied inside it; no Hausdorff hypothesis on the space is needed.
* `IsMosaicSpace.locallyArcwiseConnected_iff` (display (2.1), first line): for mosaic spaces,
  locally path connected ⟺ locally arcwise connected.
* `IsMosaicFamily.arcwiseConnected_pathComponentIn`, `IsMosaicFamily.locallyArcwiseConnected`:
  Lemma 2.14 as stated (path components of open sets are open *and arcwise connected*).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- An arc in a Hausdorff space, from a path. -/
theorem isArcBetween_of_joinedIn_t2 [T2Space X] {s : Set X} {x y : X} (h : JoinedIn s x y)
    (hxy : x ≠ y) : IsArcBetween s x y := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨f, hf, hf0, hf1, hfr⟩ := Arc.exists_arc γ hxy
  exact ⟨f, hf, hf0, hf1, hfr.trans (range_subset_iff.2 hγ)⟩

/-- **Corollary 2.6(2)**, arcwise part: in a sequential space with unique sequential limits (for
example a mosaic space), two distinct points joined by a path in `s` are the end points of an arc
in `s`. -/
theorem isArcBetween_of_joinedIn [SequentialSpace X] (hX : UniqueSeqLimits X) {s : Set X}
    {x y : X} (h : JoinedIn s x y) (hxy : x ≠ y) : IsArcBetween s x y := by
  obtain ⟨γ, hγ⟩ := h
  set P := range γ
  haveI : MetrizableSpace P := (isMetricContinuum_range_path hX γ).2.2
  let γ' : Path (⟨x, 0, γ.source⟩ : P) ⟨y, 1, γ.target⟩ :=
    { toFun := fun t => ⟨γ t, t, rfl⟩
      continuous_toFun := Continuous.subtype_mk γ.continuous _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  obtain ⟨f, hf, hf0, hf1, hfr⟩ := Arc.exists_arc γ' (fun h => hxy (congrArg Subtype.val h))
  refine ⟨Subtype.val ∘ f, IsEmbedding.subtypeVal.comp hf, by simp [hf0], by simp [hf1], ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨u, hu⟩ := (f t).2
  simp only [Function.comp_apply, ← hu]
  exact hγ u

/-- In a sequential space with unique sequential limits, path connected sets are arcwise
connected. -/
theorem IsPathConnected.arcwiseConnected [SequentialSpace X] (hX : UniqueSeqLimits X)
    {s : Set X} (h : IsPathConnected s) : ArcwiseConnected s :=
  fun x hx y hy hxy => isArcBetween_of_joinedIn hX (h.joinedIn x hx y hy) hxy

theorem LocallyPathConnectedOpen.locallyArcwiseConnected [SequentialSpace X]
    (hX : UniqueSeqLimits X) (h : LocallyPathConnectedOpen X) : LocallyArcwiseConnected X :=
  fun x O hO hxO =>
    let ⟨W, hW, hxW, hWO, hWp⟩ := h x O hO hxO
    ⟨W, hW, hxW, hWO, IsPathConnected.arcwiseConnected hX hWp⟩

/-- **Display (2.1)**, first line: a mosaic space is locally arcwise connected iff it is locally
path connected. -/
theorem IsMosaicSpace.locallyArcwiseConnected_iff (hX : IsMosaicSpace X) :
    LocallyArcwiseConnected X ↔ LocallyPathConnectedSpace X := by
  haveI := hX.sequentialSpace
  exact ⟨fun h => locallyPathConnectedOpen_iff.1 h.locallyPathConnectedOpen,
    fun h => (locallyPathConnectedOpen_iff.2 h).locallyArcwiseConnected hX.uniqueSeqLimits⟩

/-- **Lemma 2.14**, the conclusion "arcwise connected": path components of subsets of a mosaic
space are arcwise connected. -/
theorem IsMosaicSpace.arcwiseConnected_pathComponentIn (hX : IsMosaicSpace X) {O : Set X} {x : X}
    (hx : x ∈ O) : ArcwiseConnected (pathComponentIn O x) := by
  haveI := hX.sequentialSpace
  exact IsPathConnected.arcwiseConnected hX.uniqueSeqLimits (isPathConnected_pathComponentIn hx)

/-- **Lemma 2.14** as stated in the article (with the hypothesis imposed on the pieces that are not
locally path connected): the path components of every open set are open and arcwise connected, and
the space is locally arcwise connected. -/
theorem IsMosaicFamily.lemma_2_14 {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    (hK : ∀ K ∈ 𝒦, LocallyPathConnectedSpace K ∨
      ∀ (O : Set X), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → X, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z) :
    (∀ O : Set X, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected X := by
  have hX : IsMosaicSpace X := ⟨𝒦, h𝒦, hcm⟩
  refine ⟨fun O hO x hx => ⟨h𝒦.isOpen_pathComponentIn hcm hK hO x,
    hX.arcwiseConnected_pathComponentIn hx⟩, ?_⟩
  exact hX.locallyArcwiseConnected_iff.2 (h𝒦.locallyPathConnectedSpace hcm hK)

end MosaicSpaces
