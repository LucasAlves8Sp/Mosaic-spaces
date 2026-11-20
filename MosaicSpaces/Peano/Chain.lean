module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Peano continua are locally path connected, part 1: chains

* `exists_chain`: two points of a preconnected subset `C` of a metric space are joined by a
  finite `δ`-chain in `C`, for every `δ > 0`.
* `ulc_of_compact`: a compact, locally connected metric space is uniformly locally connected:
  points closer than some `δ` lie in a preconnected set inside the `ε`-ball about either.
-/

@[expose] public section

open Set Filter Topology Metric

namespace MosaicSpaces.Peano

variable {X : Type*} [MetricSpace X]

/-- A finite `δ`-chain in `C` from `a` to `b`. -/
def ChainIn (C : Set X) (δ : ℝ) (a b : X) : Prop :=
  ∃ (n : ℕ) (c : ℕ → X), c 0 = a ∧ c n = b ∧ (∀ i ≤ n, c i ∈ C) ∧
    ∀ i < n, dist (c i) (c (i + 1)) < δ

theorem ChainIn.refl {C : Set X} {δ : ℝ} {a : X} (ha : a ∈ C) : ChainIn C δ a a :=
  ⟨0, fun _ => a, rfl, rfl, fun _ _ => ha, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem ChainIn.extend {C : Set X} {δ : ℝ} {a x y : X} (h : ChainIn C δ a x) (hy : y ∈ C)
    (hxy : dist x y < δ) : ChainIn C δ a y := by
  classical
  obtain ⟨n, c, h0, hn, hC, hstep⟩ := h
  refine ⟨n + 1, fun i => if i ≤ n then c i else y, by simp [h0], by simp, fun i hi => ?_,
    fun i hi => ?_⟩
  · by_cases h : i ≤ n
    · simp only [h, ite_true]; exact hC i h
    · simp only [h, ite_false]; exact hy
  · by_cases h : i + 1 ≤ n
    · simp only [h, ite_true, show i ≤ n by omega]; exact hstep i (by omega)
    · have hi' : i = n := by omega
      subst hi'
      simp only [le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false, hn]
      exact hxy

/-- Two points of a preconnected set are joined by a `δ`-chain in it. -/
theorem exists_chain {C : Set X} (hC : IsPreconnected C) {δ : ℝ} (hδ : 0 < δ) {a b : X}
    (ha : a ∈ C) (hb : b ∈ C) : ChainIn C δ a b := by
  by_contra hab
  set R := {x | x ∈ C ∧ ChainIn C δ a x}
  have hRa : a ∈ R := ⟨ha, ChainIn.refl ha⟩
  obtain ⟨y, hyC, hyu, hyv⟩ := hC (⋃ x ∈ R, ball x δ) (⋃ x ∈ C \ R, ball x δ)
    (isOpen_biUnion fun _ _ => isOpen_ball) (isOpen_biUnion fun _ _ => isOpen_ball)
    (fun x hx => by
      by_cases h : x ∈ R
      · exact Or.inl (mem_biUnion h (mem_ball_self hδ))
      · exact Or.inr (mem_biUnion ⟨hx, h⟩ (mem_ball_self hδ)))
    ⟨a, ha, mem_biUnion hRa (mem_ball_self hδ)⟩
    ⟨b, hb, mem_biUnion ⟨hb, fun h => hab h.2⟩ (mem_ball_self hδ)⟩
  obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.1 hyu
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyv
  have hyR : ChainIn C δ a y := hr.2.extend hyC (by rw [mem_ball, dist_comm] at hyr; exact hyr)
  exact hx.2 ⟨hx.1, hyR.extend hx.1 (by rw [mem_ball] at hyx; exact hyx)⟩

/-- A compact, locally connected metric space is uniformly locally connected. -/
theorem ulc_of_compact [CompactSpace X] [LocallyConnectedSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : X, dist a b < δ →
      ∃ C : Set X, IsPreconnected C ∧ a ∈ C ∧ b ∈ C ∧ C ⊆ ball a ε := by
  have hloc := locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 ‹_›
  have hU : ∀ x : X, ∃ V : Set X, V ⊆ ball x (ε / 2) ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V :=
    fun x => hloc x _ (ball_mem_nhds x (by linarith))
  choose V hVsub hVo hxV hVc using hU
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hVo
    (fun x _ => mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨δ, hδ, fun a b hab => ?_⟩
  obtain ⟨x, hx⟩ := hleb a (mem_univ a)
  refine ⟨V x, (hVc x).isPreconnected, hx (mem_ball_self hδ), hx (by rw [mem_ball, dist_comm]; exact hab), ?_⟩
  intro z hz
  have h1 := hVsub x hz
  have h2 := hVsub x (hx (mem_ball_self hδ))
  rw [mem_ball] at h1 h2 ⊢
  calc dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
    _ = dist z x + dist a x := by rw [dist_comm x a]
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end MosaicSpaces.Peano
