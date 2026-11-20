module

public import MosaicSpaces.Peano.Path
public import MosaicSpaces.ArcConsequences

/-!
# Peano continua are locally path connected, part 3

A compact, locally connected metrizable space is locally path connected
(`locallyPathConnectedSpace_of_compact`). Consequently every quasi-Peano subspace is locally
path connected (`IsQuasiPeano.locallyPathConnectedSpace`), and so is every Peano continuum.

This is the classical theorem that Peano continua are locally path connected (in the article it
is used through the Hahn–Mazurkiewicz theorem); Hahn–Mazurkiewicz itself is not needed.
-/

@[expose] public section

open Set Filter Topology Metric TopologicalSpace

namespace MosaicSpaces.Peano

/-- **Uniform local path connectedness.** In a compact, locally connected metric space, points
closer than some `δ` are joined by a path within `2ε` of the first point. -/
theorem exists_path_ball {X : Type*} [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : X, dist a b < δ → ∃ γ : Path a b, ∀ t, dist a (γ t) < 2 * ε := by
  have hpos : ∀ n : ℕ, 0 < ε / 2 / 2 ^ n := fun n => by positivity
  choose δ' hδ' hconn using fun n => ulc_of_compact (X := X) (hpos n)
  let P : ULCData X :=
    { ε := fun n => ε / 2 / 2 ^ n
      δ := fun n => min (δ' n) (ε / 2 / 2 ^ n)
      δpos := fun n => lt_min (hδ' n) (hpos n)
      δle := fun n => min_le_right _ _
      conn := fun n a b h => hconn n a b (lt_of_lt_of_le h (min_le_left _ _)) }
  exact ⟨P.δ 0, P.δpos 0, fun a b hab => exists_path_near P a b hε (fun n => rfl) hab⟩

theorem locallyPathConnectedSpace_of_compact_metric {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_isOpen_pathComponentIn]
  intro x U hU
  rw [Metric.isOpen_iff]
  intro y hy
  have hyU : y ∈ U := pathComponentIn_subset hy
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hyU
  obtain ⟨δ, hδ, hpath⟩ := exists_path_ball (X := X) (half_pos hr)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  rw [mem_ball, dist_comm] at hz
  obtain ⟨γ, hγ⟩ := hpath y z hz
  have hyz : z ∈ pathComponentIn U y :=
    ⟨γ, fun t => hrU (by rw [mem_ball, dist_comm]; linarith [hγ t])⟩
  rwa [pathComponentIn_congr hy] at hyz

/-- **Compact, locally connected metrizable spaces are locally path connected.** -/
theorem locallyPathConnectedSpace_of_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetrizableSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by
  let := TopologicalSpace.metrizableSpaceMetric X
  exact locallyPathConnectedSpace_of_compact_metric

end MosaicSpaces.Peano

namespace MosaicSpaces

variable {X : Type*} [TopologicalSpace X]

/-- Every quasi-Peano subspace (compact, metrizable, locally connected) is locally path
connected. -/
theorem IsQuasiPeano.locallyPathConnectedSpace {K : Set X} (h : IsQuasiPeano K) :
    LocallyPathConnectedSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 h.1
  have := h.2.1
  have := h.2.2
  exact Peano.locallyPathConnectedSpace_of_compact

/-- Every Peano continuum is locally path connected. -/
theorem IsPeanoContinuum.locallyPathConnectedSpace {K : Set X} (h : IsPeanoContinuum K) :
    LocallyPathConnectedSpace K :=
  h.isQuasiPeano.locallyPathConnectedSpace

end MosaicSpaces
