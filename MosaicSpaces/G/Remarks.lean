module

public import MosaicSpaces.G.Capture
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Remarks 4.10 and 4.13(2)

**Remark 4.10.** The countable-spread hypothesis of Proposition 4.9 cannot be weakened to
separability: for `D₀ ∈ 𝒟` the closure `K` of `⋃_{n ∈ N'} R_n ∪ Φ_{D₀} ∪ A_{D₀}` (`N'` the rows
met by `D₀`) is closed, connected and separable, contains `∞` and infinitely many `x_n`, and
contains `p_D` for uncountably many `D` (`remark_4_10`).

**Remark 4.13(2)**: `G` is not a Fréchet–Urysohn space.

`∞` lies in the closure of the set `M` of witnesses, since each `x_n` does and `x_n → ∞`, but no
sequence of witnesses converges to `∞`: by Proposition 2.3(4) a subsequence would lie, with `∞`,
in one piece, and the pieces containing `∞` (`Σ` and the fans `Λ_S`) contain no witness.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval Function

namespace MosaicSpaces

namespace GSpace

variable {𝒟 : Set (Set (ℕ × ℕ))}

theorem xpt_mem_closure_wit (n : ℕ) :
    (xpt n : GSpace 𝒟) ∈ closure (range wit) := by
  have h1 : Tendsto (fun i : ℕ => witT i) atTop (𝓝 (0 : I)) := by
    refine tendsto_subtype_rng.2 ?_
    show Tendsto (fun i : ℕ => ((witT i : I) : ℝ)) atTop (𝓝 0)
    simp only [witT_coe]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := ((continuous_rowMap (𝒟 := 𝒟) n).tendsto 0).comp h1
  exact mem_closure_of_tendsto h2 (Eventually.of_forall fun i => ⟨(n, i), rfl⟩)

theorem infty_mem_closure_wit : (infty : GSpace 𝒟) ∈ closure (range wit) := by
  rw [← closure_closure]
  exact mem_closure_of_tendsto tendsto_xpt (Eventually.of_forall fun n => xpt_mem_closure_wit n)

/-- No piece containing `∞` contains a witness. -/
theorem wit_not_mem_of_infty_mem {P : Set (GSpace 𝒟)} (hP : P ∈ pieces 𝒟) (hinf : infty ∈ P)
    (m : ℕ × ℕ) : wit m ∉ P := by
  rcases hP with ⟨n, rfl⟩ | rfl | ⟨D, rfl⟩ | ⟨S, rfl⟩
  · obtain ⟨t, ht⟩ := hinf
    exact absurd ht (by simp [rowMap])
  · rintro ⟨c, hc⟩
    have := range_sigMap_subset ⟨c, hc⟩
    rcases this with h | ⟨n, h⟩
    · simp [wit] at h
    · exact wit_ne_xpt m n h
  · exfalso
    rcases range_phiMap_subset D hinf with h | ⟨m', -, h⟩ | ⟨m', s, h⟩ <;> simp [wit] at h
  · rintro ⟨c, hc⟩
    have := range_lamMap_subset S.1 ⟨c, hc⟩
    rcases this with h | ⟨D, -, h⟩ | ⟨D, -, s, h⟩ <;> simp [wit] at h

/-- No sequence of witnesses converges to `∞`. -/
theorem not_tendsto_wit (h𝒟 : IsMADFamily 𝒟) {u : ℕ → GSpace 𝒟} (huM : ∀ n, u n ∈ range wit) :
    ¬ Tendsto u atTop (𝓝 infty) := by
  intro hu
  obtain ⟨P, hP, hinfP, φ, -, hφP⟩ :=
    (isMosaicFamily_pieces h𝒟).exists_piece_subseq (isCompactMetrizable_pieces h𝒟) hu
  obtain ⟨m, hm⟩ := huM (φ 0)
  exact wit_not_mem_of_infty_mem hP hinfP m (hm ▸ hφP 0)

/-- **Remark 4.13(2)**: `G` is not a Fréchet–Urysohn space. -/
theorem not_frechetUrysohnSpace (h𝒟 : IsMADFamily 𝒟) : ¬ FrechetUrysohnSpace (GSpace 𝒟) := by
  intro hF
  obtain ⟨u, huM, hu⟩ := hF.closure_subset_seqClosure _ infty_mem_closure_wit
  exact not_tendsto_wit h𝒟 huM hu



theorem exists_countable_dense_in_range {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]
    [SeparableSpace A] {f : A → Y} (hf : Continuous f) :
    ∃ c ⊆ range f, c.Countable ∧ range f ⊆ closure c := by
  obtain ⟨d, hdc, hd⟩ := exists_countable_dense A
  exact ⟨f '' d, image_subset_range _ _, hdc.image f, hf.range_subset_closure_image_dense hd⟩

theorem separableSpace_of_subset_closure {Y : Type*} [TopologicalSpace Y] {K c : Set Y}
    (hc : c.Countable) (hcK : c ⊆ K) (hKc : K ⊆ closure c) : SeparableSpace K := by
  refine ⟨⟨Subtype.val ⁻¹' c, hc.preimage Subtype.val_injective, fun x => ?_⟩⟩
  rw [closure_subtype, Subtype.image_preimage_coe, inter_eq_right.2 hcK]
  exact hKc x.2

/-- **Remark 4.10**: a closed, connected, separable set containing `∞` and infinitely many `x_n`;
it contains uncountably many of the points `p_D`. -/
theorem remark_4_10 (h𝒟 : IsMADFamily 𝒟) (D₀ : 𝒟) :
    ∃ K : Set (GSpace 𝒟), IsClosed K ∧ IsConnected K ∧ SeparableSpace K ∧ infty ∈ K ∧
      {n | xpt n ∈ K}.Infinite ∧ ¬ ({D | pnt D ∈ K} : Set 𝒟).Countable := by
  have : PathConnectedSpace (Fan (D₀ : Set (ℕ × ℕ))) := Fan.pathConnectedSpace
  let N' : Set ℕ := {n | ∃ i, (n, i) ∈ (D₀ : Set (ℕ × ℕ))}
  let T : Set (GSpace 𝒟) := range (phiMap D₀) ∪ range (arcMap D₀)
  have hpT : pnt D₀ ∈ T := Or.inl ⟨Fan.centre, phiMap_centre D₀⟩
  have hT : IsPreconnected T :=
    (isPreconnected_range (continuous_phiMap D₀)).union (pnt D₀) ⟨Fan.centre, phiMap_centre D₀⟩
      ⟨1, arcMap_one D₀⟩ (isPreconnected_range (continuous_arcMap D₀))
  have hRT : ∀ n ∈ N', IsPreconnected (range (rowMap n) ∪ T) := by
    rintro n ⟨i, hi⟩
    have h1 : (wit (n, i) : GSpace 𝒟) ∈ range (rowMap n) := ⟨witT i, rfl⟩
    have h2 : (wit (n, i) : GSpace 𝒟) ∈ T :=
      Or.inl ⟨Fan.spine ⟨(n, i), hi⟩ 1, by rw [phiMap_spine, spokeMap_one]⟩
    exact (isPreconnected_range (continuous_rowMap n)).union _ h1 h2 hT
  let F : Set (Set (GSpace 𝒟)) := insert T ((fun n => range (rowMap n) ∪ T) '' N')
  have hS : IsPreconnected (⋃₀ F) := by
    refine isPreconnected_sUnion (pnt D₀) F ?_ ?_
    · rintro s (rfl | ⟨n, -, rfl⟩)
      · exact hpT
      · exact Or.inr hpT
    · rintro s (rfl | ⟨n, hn, rfl⟩)
      · exact hT
      · exact hRT n hn
  have hdense : ∀ s ∈ F, ∃ c ⊆ s, c.Countable ∧ s ⊆ closure c := by
    obtain ⟨c₁, hc₁s, hc₁, hc₁d⟩ := exists_countable_dense_in_range (continuous_phiMap D₀)
    obtain ⟨c₂, hc₂s, hc₂, hc₂d⟩ := exists_countable_dense_in_range (continuous_arcMap D₀)
    have hTd : ∃ c ⊆ T, c.Countable ∧ T ⊆ closure c :=
      ⟨c₁ ∪ c₂, union_subset_union hc₁s hc₂s, hc₁.union hc₂, by
        rw [closure_union]; exact union_subset_union hc₁d hc₂d⟩
    rintro s (rfl | ⟨n, -, rfl⟩)
    · exact hTd
    · obtain ⟨c, hcs, hc, hcd⟩ := hTd
      obtain ⟨c₃, hc₃s, hc₃, hc₃d⟩ := exists_countable_dense_in_range (continuous_rowMap (𝒟 := 𝒟) n)
      exact ⟨c₃ ∪ c, union_subset_union hc₃s hcs, hc₃.union hc, by
        rw [closure_union]; exact union_subset_union hc₃d hcd⟩
  choose! cF hcFs hcF hcFd using hdense
  have hFc : F.Countable := ((Set.to_countable N').image _).insert T
  set c := ⋃ s ∈ F, cF s
  set K := closure (⋃₀ F)
  have hKc : IsClosed K := isClosed_closure
  have hinf : infty ∈ K := subset_closure ⟨T, mem_insert _ _, Or.inr ⟨0, arcMap_zero D₀⟩⟩
  have hconn : IsConnected K := ⟨⟨infty, hinf⟩, hS.closure⟩
  have hN'K : N' ⊆ {n | xpt n ∈ K} := fun n hn =>
    subset_closure ⟨_, mem_insert_of_mem _ ⟨n, hn, rfl⟩, Or.inl ⟨0, rfl⟩⟩
  have hN' : N'.Infinite := by
    intro hfin
    have hD₀ := h𝒟.mem D₀ D₀.2
    refine hD₀.1 ((hfin.biUnion fun n _ => hD₀.finite_fst n).subset ?_)
    intro m hm
    exact mem_iUnion₂.2 ⟨m.1, ⟨m.2, hm⟩, hm, rfl⟩
  have hsep : SeparableSpace K := by
    refine separableSpace_of_subset_closure (hFc.biUnion fun s hs => hcF s hs) ?_ ?_
    · exact (iUnion₂_subset fun s hs => (hcFs s hs).trans (subset_sUnion_of_mem hs)).trans
        subset_closure
    · refine closure_minimal (sUnion_subset fun s hs => (hcFd s hs).trans
        (closure_mono (subset_biUnion_of_mem (u := cF) hs))) isClosed_closure
  refine ⟨K, hKc, hconn, hsep, hinf, hN'.mono hN'K, fun hcount => ?_⟩
  refine (hN'.mono hN'K) (finite_xpt_core h𝒟 hKc hconn.isPreconnected hinf (hcount.mono ?_))
  intro D hD
  exact pnt_mem_of_infinite hKc hD

end GSpace

end MosaicSpaces
