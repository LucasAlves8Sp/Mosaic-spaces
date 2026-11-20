module

public import MosaicSpaces.Local

/-!
# A criterion for open path components (article: Lemma 2.14, path-connected form)

**Lemma 2.14** of the article: if, for every open `O`, every piece `X_α` that is *not locally
connected*, every `z ∈ O ∩ X_α` and every sequence `z_k → z` in `X_α`, eventually `z_k` lies in
the path component of `z` in `O`, then path components of open sets are open (and arcwise
connected).

This module proves the path-connected form, with the hypothesis imposed on the pieces that are
*not locally path connected*. The article's form (hypothesis on the pieces that are not locally
connected) and the conclusion "arcwise connected" are `IsMosaicFamily.lemma_2_14_lc`
(`MosaicSpaces.Peano.Consequences`) and `IsMosaicFamily.lemma_2_14`
(`MosaicSpaces.ArcConsequences`); they use that compact, locally connected, metrizable pieces are
locally path connected (`MosaicSpaces.Peano.LPC`) and the arc theorem (`MosaicSpaces.Arc`).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- **Lemma 2.14**, path-connected form. -/
theorem IsMosaicFamily.isOpen_pathComponentIn {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    (hK : ∀ K ∈ 𝒦, LocallyPathConnectedSpace K ∨
      ∀ (O : Set X), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → X, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z)
    {O : Set X} (hO : IsOpen O) (x : X) : IsOpen (pathComponentIn O x) := by
  haveI : SequentialSpace X := h𝒦.sequentialSpace fun K hK' => by
    haveI := (hcm K hK').2
    infer_instance
  -- if `z ∈ C` and `u → z`, then `u` is eventually in `C`
  have key : ∀ z ∈ pathComponentIn O x, ∀ u : ℕ → X, Tendsto u atTop (𝓝 z) →
      ∀ᶠ n in atTop, u n ∈ pathComponentIn O x := by
    intro z hz u hu
    have hzO : z ∈ O := pathComponentIn_subset hz
    have hCz : pathComponentIn O z = pathComponentIn O x := pathComponentIn_congr hz
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨ψ, hψ, hψC⟩ := extraction_of_frequently_atTop hcon
    obtain ⟨K, hK𝒦, hzK, φ, hφ, hφK⟩ :=
      h𝒦.exists_piece_subseq hcm (hu.comp hψ.tendsto_atTop)
    have hw : Tendsto (fun n => u (ψ (φ n))) atTop (𝓝 z) :=
      hu.comp (hψ.comp hφ).tendsto_atTop
    have hev : ∀ᶠ n in atTop, u (ψ (φ n)) ∈ pathComponentIn O z := by
      rcases hK K hK𝒦 with hlpc | hcond
      · -- the piece is locally path connected
        have hw' : Tendsto (fun n => (⟨u (ψ (φ n)), hφK n⟩ : K)) atTop (𝓝 ⟨z, hzK⟩) :=
          tendsto_subtype_rng.2 hw
        have hOK : IsOpen ((↑) ⁻¹' O : Set K) := hO.preimage continuous_subtype_val
        have hmem : pathComponentIn ((↑) ⁻¹' O : Set K) ⟨z, hzK⟩ ∈ 𝓝 (⟨z, hzK⟩ : K) :=
          (hOK.pathComponentIn _).mem_nhds (mem_pathComponentIn_self hzO)
        filter_upwards [hw'.eventually hmem] with n hn
        have hj : JoinedIn ((↑) ⁻¹' O : Set K) ⟨z, hzK⟩ ⟨u (ψ (φ n)), hφK n⟩ := hn
        have hj' := hj.map continuous_subtype_val.continuousOn
        rw [Subtype.image_preimage_coe] at hj'
        exact hj'.mono inter_subset_right
      · exact hcond O hO z ⟨hzO, hzK⟩ _ hφK hw
    obtain ⟨n, hn⟩ := hev.exists
    exact hψC (φ n) (hCz ▸ hn)
  rw [← isClosed_compl_iff]
  refine IsSeqClosed.isClosed fun u z hu hz hzC => ?_
  obtain ⟨n, hn⟩ := (key z hzC u hz).exists
  exact hu n hn

/-- **Lemma 2.14**, consequence: the space is locally path connected. -/
theorem IsMosaicFamily.locallyPathConnectedSpace {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    (hK : ∀ K ∈ 𝒦, LocallyPathConnectedSpace K ∨
      ∀ (O : Set X), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → X, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z) :
    LocallyPathConnectedSpace X :=
  locallyPathConnectedSpace_iff_isOpen_pathComponentIn.2 fun x _ hO =>
    h𝒦.isOpen_pathComponentIn hcm hK hO x

end MosaicSpaces
