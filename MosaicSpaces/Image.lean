module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Images of compact metrizable spaces (article: Lemma 2.4, Remark 2.5)

The article works with spaces that are sequential and in which convergent sequences have unique
limits; such spaces need not be Hausdorff. This file proves that in such a space the continuous
image of a compact metrizable space is closed, compact and metrizable (Lemma 2.4, `lem:image`),
and the Hausdorff variant (Remark 2.5, `rem:hausimage`).

No separation axiom beyond what is stated is assumed.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- Convergent sequences in `X` have unique limits ("unique sequential limits"). This is weaker
than the Hausdorff property. -/
def UniqueSeqLimits (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃a b : X⦄, Tendsto x atTop (𝓝 a) → Tendsto x atTop (𝓝 b) → a = b

/-- A Hausdorff space has unique sequential limits. -/
theorem uniqueSeqLimits_of_t2 [T2Space X] : UniqueSeqLimits X :=
  fun _ _ _ ha hb => tendsto_nhds_unique ha hb

/-- A sequential space with unique sequential limits is `T₁` (article: proof of Proposition 2.7,
"singletons contain the limits of their sequences"). -/
theorem UniqueSeqLimits.t1Space [SequentialSpace X] (h : UniqueSeqLimits X) : T1Space X := by
  refine ⟨fun a => IsSeqClosed.isClosed ?_⟩
  intro x p hx hp
  have hx' : x = fun _ => a := funext fun n => hx n
  rw [hx'] at hp
  exact (h tendsto_const_nhds hp).symm

/-- First paragraph of the proof of Lemma 2.4: a continuous map from a compact first countable
space into a sequential space with unique sequential limits is a closed map. -/
theorem isClosedMap_of_compact [SequentialSpace X] (hX : UniqueSeqLimits X)
    {C : Type v} [TopologicalSpace C] [CompactSpace C] [FirstCountableTopology C]
    {f : C → X} (hf : Continuous f) : IsClosedMap f := by
  intro B hB
  refine IsSeqClosed.isClosed ?_
  intro x p hx hp
  choose c hcB hc using hx
  obtain ⟨a, haB, φ, hφ, hlim⟩ := hB.isCompact.tendsto_subseq hcB
  have h1 : Tendsto (x ∘ φ) atTop (𝓝 (f a)) := by
    have h := (hf.tendsto a).comp hlim
    have e : f ∘ c ∘ φ = x ∘ φ := funext fun n => hc (φ n)
    rw [← e]
    exact h
  have h2 : Tendsto (x ∘ φ) atTop (𝓝 p) := hp.comp hφ.tendsto_atTop
  exact ⟨a, haB, hX h1 h2⟩

/-- Second and third paragraphs of the proof of Lemma 2.4: a `T₁` space which is the image of a
compact metrizable space under a closed continuous surjection is compact and metrizable. -/
theorem compact_metrizable_of_isClosedMap_surjective {C : Type v} {Y : Type u}
    [TopologicalSpace C] [CompactSpace C] [MetrizableSpace C] [TopologicalSpace Y] [T1Space Y]
    {g : C → Y} (hg : Continuous g) (hcl : IsClosedMap g) (hs : Function.Surjective g) :
    CompactSpace Y ∧ MetrizableSpace Y := by
  have hcomp : CompactSpace Y := ⟨by simpa [hs.range_eq] using isCompact_range hg⟩
  have hopen : ∀ U : Set C, IsOpen U → IsOpen (g '' Uᶜ)ᶜ :=
    fun U hU => (hcl _ hU.isClosed_compl).isOpen_compl
  have hmem : ∀ (U : Set C) (y : Y), g ⁻¹' {y} ⊆ U → y ∈ (g '' Uᶜ)ᶜ := by
    rintro U y hy ⟨c, hc, rfl⟩
    exact hc (hy rfl)
  have hsub : ∀ (U : Set C) (c : C), g c ∈ (g '' Uᶜ)ᶜ → c ∈ U := by
    intro U c hc
    by_contra h
    exact hc ⟨c, h, rfl⟩
  -- `Y` is Hausdorff.
  have ht2 : T2Space Y := by
    refine ⟨fun y y' hne => ?_⟩
    have hd : Disjoint (g ⁻¹' {y}) (g ⁻¹' {y'}) := by
      rw [Set.disjoint_left]
      intro c hc hc'
      have e1 : g c = y := hc
      have e2 : g c = y' := hc'
      exact hne (e1.symm.trans e2)
    obtain ⟨U, V, hU, hV, hyU, hyV, hUV⟩ :=
      normal_separation (isClosed_singleton.preimage hg) (isClosed_singleton.preimage hg) hd
    refine ⟨_, _, hopen U hU, hopen V hV, hmem U y hyU, hmem V y' hyV, ?_⟩
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨c, rfl⟩ := hs z
    exact Set.disjoint_left.1 hUV (hsub U c hz) (hsub V c hz')
  -- `Y` is second countable.
  have hsc : SecondCountableTopology Y := by
    letI : MetricSpace C := metrizableSpaceMetric C
    haveI : SecondCountableTopology C := inferInstance
    haveI : Countable (countableBasis C) := (countable_countableBasis C).to_subtype
    let S : Set (Set Y) :=
      range fun s : Finset (countableBasis C) => (g '' (⋃ B ∈ s, (B : Set C))ᶜ)ᶜ
    have hSc : S.Countable := countable_range _
    have hbasis : IsTopologicalBasis S := by
      refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
      · rintro _ ⟨s, rfl⟩
        exact hopen _ (isOpen_biUnion fun B _ => isOpen_of_mem_countableBasis B.2)
      · intro y W hyW hW
        have hK : IsCompact (g ⁻¹' {y}) := (isClosed_singleton.preimage hg).isCompact
        have hcov : g ⁻¹' {y} ⊆
            ⋃ i : {B : countableBasis C // (B : Set C) ⊆ g ⁻¹' W}, (i.1 : Set C) := by
          intro c hc
          have e : g c = y := hc
          have hcW : c ∈ g ⁻¹' W := by
            show g c ∈ W
            rw [e]
            exact hyW
          obtain ⟨B, hB, hcB, hBW⟩ :=
            (isBasis_countableBasis C).exists_subset_of_mem_open hcW (hW.preimage hg)
          exact mem_iUnion.2 ⟨⟨⟨B, hB⟩, hBW⟩, hcB⟩
        obtain ⟨t, ht⟩ :=
          hK.elim_finite_subcover _ (fun i => isOpen_of_mem_countableBasis i.1.2) hcov
        refine ⟨_, ⟨t.image Subtype.val, rfl⟩, hmem _ y ?_, ?_⟩
        · intro c hc
          obtain ⟨i, hi, hci⟩ := mem_iUnion₂.1 (ht hc)
          exact mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, hci⟩
        · intro z hz
          obtain ⟨c, rfl⟩ := hs z
          obtain ⟨B, hB, hcB⟩ := mem_iUnion₂.1 (hsub _ c hz)
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hB
          exact i.2 hcB
    exact hbasis.secondCountableTopology hSc
  exact ⟨hcomp, inferInstance⟩

/-- The corestriction of a closed map to its range is a closed map. -/
theorem isClosedMap_rangeFactorization {C : Type v} [TopologicalSpace C] {f : C → X}
    (hcl : IsClosedMap f) : IsClosedMap (rangeFactorization f) := by
  intro B hB
  have e : rangeFactorization f '' B = Subtype.val ⁻¹' (f '' B) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, congrArg Subtype.val h⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, Subtype.ext h⟩
  rw [e]
  exact (hcl B hB).preimage continuous_subtype_val

/-- **Lemma 2.4** (`lem:image`). Let `X` be a sequential space with unique sequential limits, `C`
a compact metrizable space and `f : C → X` continuous. Then `f(C)` is closed in `X` and is, as a
subspace, compact and metrizable. `X` is not assumed Hausdorff. -/
theorem range_closed_compact_metrizable [SequentialSpace X] (hX : UniqueSeqLimits X)
    {C : Type v} [TopologicalSpace C] [CompactSpace C] [MetrizableSpace C]
    {f : C → X} (hf : Continuous f) :
    IsClosed (range f) ∧ IsCompact (range f) ∧ MetrizableSpace (range f) := by
  have hcl : IsClosedMap f := isClosedMap_of_compact hX hf
  haveI : T1Space X := hX.t1Space
  refine ⟨hcl.isClosed_range, isCompact_range hf, ?_⟩
  exact (compact_metrizable_of_isClosedMap_surjective hf.rangeFactorization
    (isClosedMap_rangeFactorization hcl) rangeFactorization_surjective).2

/-- **Remark 2.5** (`rem:hausimage`). In an arbitrary Hausdorff space, the continuous image of a
compact metrizable space is compact and metrizable. -/
theorem range_compact_metrizable_of_t2 [T2Space X]
    {C : Type v} [TopologicalSpace C] [CompactSpace C] [MetrizableSpace C]
    {f : C → X} (hf : Continuous f) :
    IsClosed (range f) ∧ IsCompact (range f) ∧ MetrizableSpace (range f) := by
  have hcl : IsClosedMap f := hf.isClosedMap
  refine ⟨hcl.isClosed_range, isCompact_range hf, ?_⟩
  exact (compact_metrizable_of_isClosedMap_surjective hf.rangeFactorization
    (isClosedMap_rangeFactorization hcl) rangeFactorization_surjective).2

/-! ### The one-point compactification of `ℕ` is metrizable -/

/-- The map `OnePoint ℕ → ℝ`, `n ↦ 1/(n+1)`, `∞ ↦ 0`. (The same map is used in Mathlib's
`LightProfinite.natUnionInftyEmbedding`; it is reproduced here to avoid importing category
theory.) -/
noncomputable def natInftyToReal : OnePoint ℕ → ℝ := fun c => c.elim 0 fun n => 1 / ((n : ℝ) + 1)

theorem continuous_natInftyToReal : Continuous natInftyToReal :=
  (OnePoint.continuous_iff_from_nat _).2 tendsto_one_div_add_atTop_nhds_zero_nat

theorem injective_natInftyToReal : Function.Injective natInftyToReal := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  rintro (_ | n) (_ | m) h
  · rfl
  · exact absurd h.symm (hpos m).ne'
  · exact absurd h (hpos n).ne'
  · have h' : 1 / ((n : ℝ) + 1) = 1 / ((m : ℝ) + 1) := h
    rw [one_div, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h'
    rw [h']

instance : MetrizableSpace (OnePoint ℕ) :=
  (continuous_natInftyToReal.isClosedEmbedding injective_natInftyToReal).metrizableSpace

end MosaicSpaces
