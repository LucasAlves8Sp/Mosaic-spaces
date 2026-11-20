module

public import MosaicSpaces.Peano.LPC
public import MosaicSpaces.Arc.Param
public import MosaicSpaces.FirstCountable
public import MosaicSpaces.Classes

/-!
# Consequences of "Peano continua are locally path connected"

* the classical facts of the article's conventions (line 126) that do not need the
  Hahn–Mazurkiewicz theorem: Peano continua are path connected, arcwise connected and locally
  arcwise connected, and a nondegenerate Peano continuum contains an arc;
* **Lemma 2.14** with the article's hypothesis (imposed on the pieces that are *not locally
  connected*);
* **Corollary 2.15**: quasi-curve spaces are locally arcwise connected, hence locally m-strongly
  connected;
* **Corollary 2.9(2)** with all four conditions (a)–(d), including capture by images of paths;
* **Theorem 7.4**: `(QC) ⇒ LAC ⇒ (LmS)`, and `(QC) ⇔ LAC` for first countable mosaic spaces;
* **Remark 3.7 (Curtis)**: the implication that a first countable, locally m-strongly connected
  mosaic space which is not locally path connected is an m-continuum space and not a quasi-curve
  space.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

universe u

namespace MosaicSpaces

variable {X : Type u} [TopologicalSpace X]

/-! ### Classical facts about Peano continua -/

theorem IsPeanoContinuum.isPathConnected {K : Set X} (h : IsPeanoContinuum K) :
    IsPathConnected K := by
  have := h.locallyPathConnectedSpace
  have : ConnectedSpace K := isConnected_iff_connectedSpace.1 h.1.2.1
  have : PathConnectedSpace K := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  exact isPathConnected_iff_pathConnectedSpace.2 ‹_›

/-- Paths in a compact metrizable subspace give arcs (no separation axiom on `X`). -/
theorem IsCompactMetrizable.isArcBetween {K : Set X} (h : IsCompactMetrizable K) {x y : X}
    (hxy : JoinedIn K x y) (hne : x ≠ y) : IsArcBetween K x y := by
  have := h.2
  have hx : x ∈ K := hxy.source_mem
  have hy : y ∈ K := hxy.target_mem
  obtain ⟨f, hf, hf0, hf1, -⟩ := Arc.exists_arc (hxy.joined_subtype).somePath
    (fun e => hne (congrArg Subtype.val e))
  refine ⟨fun t => (f t : X), IsEmbedding.subtypeVal.comp hf, by simp [hf0], by simp [hf1], ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (f t).2

/-- Peano continua are arcwise connected. -/
theorem IsPeanoContinuum.arcwiseConnected {K : Set X} (h : IsPeanoContinuum K) :
    ArcwiseConnected K := fun x hx y hy hxy =>
  h.isCompactMetrizable.isArcBetween (h.isPathConnected.joinedIn x hx y hy) hxy

/-- A nondegenerate Peano continuum contains an arc. -/
theorem IsPeanoContinuum.exists_isArc {K : Set X} (h : IsPeanoContinuum K) {x y : X}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) : ∃ A ⊆ K, IsArc A := by
  obtain ⟨f, hf, -, -, hfK⟩ := h.arcwiseConnected x hx y hy hxy
  exact ⟨range f, hfK, f, hf, rfl⟩

/-- Peano continua are locally arcwise connected (as spaces). -/
theorem IsPeanoContinuum.locallyArcwiseConnected {K : Set X} (h : IsPeanoContinuum K) :
    LocallyArcwiseConnected K := by
  have := h.locallyPathConnectedSpace
  have := h.1.2.2
  exact (locallyPathConnectedOpen_iff.2 ‹_›).locallyArcwiseConnected uniqueSeqLimits_of_t2

/-- Quasi-Peano spaces are locally arcwise connected (as spaces). -/
theorem IsQuasiPeano.locallyArcwiseConnected {K : Set X} (h : IsQuasiPeano K) :
    LocallyArcwiseConnected K := by
  have := h.locallyPathConnectedSpace
  have := h.2.1
  exact (locallyPathConnectedOpen_iff.2 ‹_›).locallyArcwiseConnected uniqueSeqLimits_of_t2


/-- A quasi-Peano space has finitely many components, each open and a Peano continuum. -/
theorem IsQuasiPeano.components {Q : Set X} (h : IsQuasiPeano Q) :
    (range fun a : Q => connectedComponent a).Finite ∧
    ∀ a : Q, IsOpen (connectedComponent a) ∧
      IsPeanoContinuum ((↑) '' connectedComponent a : Set X) := by
  obtain ⟨hQc, hQm, hQl⟩ := h
  have := hQm
  have := hQl
  have : CompactSpace Q := isCompact_iff_compactSpace.1 hQc
  refine ⟨?_, fun a => ⟨isOpen_connectedComponent, ?_⟩⟩
  · obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun a : Q => connectedComponent a)
      (fun a => isOpen_connectedComponent) (fun b _ => mem_iUnion.2 ⟨b, mem_connectedComponent⟩)
    refine (t.finite_toSet.image fun a : Q => connectedComponent a).subset ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, hba⟩ := mem_iUnion₂.1 (ht (mem_univ b))
    exact ⟨a, ha, connectedComponent_eq hba⟩
  · refine (isPeanoContinuum_image_iff IsEmbedding.subtypeVal).2
      ⟨⟨isClosed_connectedComponent.isCompact, isConnected_connectedComponent, inferInstance⟩,
        isOpen_connectedComponent.locallyConnectedSpace⟩

/-! ### Lemma 2.14 with the article's hypothesis, and Corollary 2.15 -/

/-- **Lemma 2.14**, with the article's hypothesis: for the pieces that are not locally connected,
sequences converging to `z ∈ O` are eventually in the path component of `z` in `O`. Then the path
components of open sets are open and arcwise connected, and `X` is locally arcwise connected. -/
theorem IsMosaicFamily.lemma_2_14_lc {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    (hK : ∀ K ∈ 𝒦, ¬ LocallyConnectedSpace K →
      ∀ (O : Set X), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → X, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z) :
    (∀ O : Set X, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected X := by
  refine h𝒦.lemma_2_14 hcm fun K hKm => ?_
  by_cases hlc : LocallyConnectedSpace K
  · exact Or.inl (IsQuasiPeano.locallyPathConnectedSpace ⟨(hcm K hKm).1, (hcm K hKm).2, hlc⟩)
  · exact Or.inr (hK K hKm hlc)

/-- **Corollary 2.15**: every quasi-curve space is locally arcwise connected (indeed the path
components of its open sets are open and arcwise connected), hence locally m-strongly
connected. -/
theorem IsQuasiCurveSpace.cor_2_15 (h : IsQuasiCurveSpace X) :
    (∀ O : Set X, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected X ∧ LocallyMStronglyConnected X := by
  obtain ⟨𝒦, h𝒦, hK⟩ := h
  have hX : IsMosaicSpace X := ⟨𝒦, h𝒦, fun K hK' => (hK K hK').isCompactMetrizable⟩
  have h1 := h𝒦.lemma_2_14 (fun K hK' => (hK K hK').isCompactMetrizable)
    (fun K hK' => Or.inl (hK K hK').locallyPathConnectedSpace)
  exact ⟨h1.1, h1.2, h1.2.locallyPathConnectedOpen.locallyMStronglyConnected hX⟩

theorem IsQuasiCurveSpace.locallyArcwiseConnected (h : IsQuasiCurveSpace X) :
    LocallyArcwiseConnected X :=
  h.cor_2_15.2.1

theorem IsQuasiCurveSpace.locallyPathConnectedSpace (h : IsQuasiCurveSpace X) :
    LocallyPathConnectedSpace X :=
  locallyPathConnectedOpen_iff.1 h.locallyArcwiseConnected.locallyPathConnectedOpen

/-! ### Corollary 2.9(2), condition (d) -/

/-- A sequence in a Peano continuum `K` converging to `a ∈ K` has a tail lying, with `a`, in the
image of a path in `K`. -/
theorem IsPeanoContinuum.exists_pathImage_tail {K : Set X} (hK : IsPeanoContinuum K) {u : ℕ → X}
    {a : X} (ha : a ∈ K) (huK : ∀ n, u n ∈ K) (hu : Tendsto u atTop (𝓝 a)) :
    ∃ L ⊆ K, IsPathImage L ∧ a ∈ L ∧ ∃ N, ∀ n, u (N + n) ∈ L := by
  have := hK.locallyPathConnectedSpace
  have := hK.1.2.2
  let a' : K := ⟨a, ha⟩
  let u' : ℕ → K := fun n => ⟨u n, huK n⟩
  have hu' : Tendsto u' atTop (𝓝 a') := tendsto_subtype_rng.2 hu
  obtain ⟨N, f, hf1, hfj⟩ :=
    exists_path_through_tail ((locallyPathConnectedOpen_iff.2 ‹_›) a') hu'
  let g : C(unitInterval, X) := ⟨fun t => (f t : X), continuous_subtype_val.comp f.continuous⟩
  let γ : Path (g 0) (g 1) := ⟨g, rfl, rfl⟩
  refine ⟨range γ, ?_, ⟨_, _, γ, rfl⟩, ⟨1, ?_⟩, N, fun n => ⟨tailPt n, ?_⟩⟩
  · rintro _ ⟨t, rfl⟩; exact (f t).2
  · show (f 1 : X) = a; rw [hf1]
  · show (f (tailPt n) : X) = u (N + n); rw [hfj n]

/-- In a curve space every convergent sequence has a subsequence lying, together with its limit,
in the image of a path. -/
theorem IsCurveSpace.capturesPath (h : IsCurveSpace X) : Captures X IsPathImage := by
  intro u a hu
  obtain ⟨K, hK, haK, φ, hφ, hφK⟩ := h.isQuasiCurveSpace.capturesPeano u a hu
  obtain ⟨L, -, hL, haL, N, hNL⟩ :=
    hK.exists_pathImage_tail haK hφK (hu.comp hφ.tendsto_atTop)
  exact ⟨L, hL, haL, fun n => φ (N + n), hφ.comp fun i j hij => Nat.add_lt_add_left hij N, hNL⟩

/-- **Corollary 2.9(2)**: for a mosaic space, (a) quasi-curve space, (b) curve space, (c) capture
of convergent sequences by Peano continua, (d) capture by images of paths, are equivalent. -/
theorem cor_2_9_2_tfae (hX : IsMosaicSpace X) :
    [IsQuasiCurveSpace X, IsCurveSpace X, Captures X IsPeanoContinuum,
      Captures X IsPathImage].TFAE := by
  have h3 := isQuasiCurveSpace_tfae hX
  tfae_have 1 ↔ 2 := h3.out 1 2
  tfae_have 2 ↔ 3 := h3.out 2 3
  tfae_have 2 → 4 := fun h => h.capturesPath
  tfae_have 4 → 2 := isCurveSpace_of_capturesPath hX
  tfae_finish

/-! ### Theorem 7.4 and the closing remark -/

/-- **Theorem 7.4**, local arcwise connectedness: `(QC) ⇒ LAC ⇒ (LmS)`. -/
theorem chain_lac (hX : IsMosaicSpace X) :
    (IsQuasiCurveSpace X → LocallyArcwiseConnected X) ∧
    (LocallyArcwiseConnected X → LocallyMStronglyConnected X) :=
  ⟨fun h => h.locallyArcwiseConnected,
    fun h => h.locallyPathConnectedOpen.locallyMStronglyConnected hX⟩

/-- After Theorem 7.4: for first countable mosaic spaces `(QC) ⇔ LAC`. -/
theorem firstCountable_QC_iff_LAC [FirstCountableTopology X] (hX : IsMosaicSpace X) :
    IsQuasiCurveSpace X ↔ LocallyArcwiseConnected X :=
  ⟨fun h => h.locallyArcwiseConnected, isQuasiCurveSpace_of_firstCountable hX⟩

/-- **Remark (Curtis's example)**, the implication used there: a first countable, locally
m-strongly connected mosaic space that is not locally path connected is an m-continuum space and
not a quasi-curve space. (Curtis's example itself is not formalized.) -/
theorem mContinuum_not_quasiCurve_of_firstCountable [FirstCountableTopology X]
    (hX : IsMosaicSpace X) (hloc : LocallyMStronglyConnected X)
    (hnot : ¬ LocallyPathConnectedSpace X) : IsMContinuumSpace X ∧ ¬ IsQuasiCurveSpace X := by
  refine ⟨?_, fun h => hnot h.locallyPathConnectedSpace⟩
  rw [isMContinuumSpace_iff_captures hX]
  intro u a hu
  obtain ⟨N, L, -, hL, haL, huL⟩ :=
    exists_metricContinuum_tail hX isOpen_univ (mem_univ a) (hloc a) hu
  exact ⟨L, hL, haL, fun n => n + N, fun i j hij => Nat.add_lt_add_right hij N,
    fun n => huL _ (Nat.le_add_left _ _)⟩

end MosaicSpaces
