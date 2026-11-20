module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Zorn
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The arc theorem, part 1: a minimal set of parameters

For a continuous `g : ℝ → X` into a Hausdorff space, call a closed set `K ⊆ [0,1]` containing `0`
and `1` *admissible* if `g` takes equal values at the two end points of every gap of `K`
(`Adm`). Zorn's lemma gives a minimal admissible set (`exists_minimal_adm`); for it, any two
points of `K` with equal `g`-values bound a gap (`Minimal.gap_of_eq`).

This is the first half of the classical proof that two distinct points joined by a path in a
Hausdorff space are joined by an arc (EXT-ARC in `docs/MATHLIB_GAPS.md`).
-/

@[expose] public section

open Set Filter Topology

namespace MosaicSpaces.Arc

variable {X : Type*} [TopologicalSpace X]

/-- An admissible set of parameters for `g`. -/
def Adm (g : ℝ → X) (K : Set ℝ) : Prop :=
  IsClosed K ∧ K ⊆ Icc 0 1 ∧ (0 : ℝ) ∈ K ∧ (1 : ℝ) ∈ K ∧
    ∀ a ∈ K, ∀ b ∈ K, a < b → Ioo a b ∩ K = ∅ → g a = g b

theorem adm_Icc (g : ℝ → X) : Adm g (Icc 0 1) := by
  refine ⟨isClosed_Icc, subset_rfl, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩, ?_⟩
  intro a ha b hb hab h
  have hm : (a + b) / 2 ∈ Ioo a b ∩ Icc (0 : ℝ) 1 :=
    ⟨⟨by linarith, by linarith⟩, by linarith [ha.1], by linarith [hb.2]⟩
  rw [h] at hm
  exact absurd hm (Set.notMem_empty _)

/-- The intersection of a chain of admissible sets is admissible. -/
theorem adm_sInter [T2Space X] {g : ℝ → X} (hg : Continuous g) {c : Set (Set ℝ)}
    (hc : c ⊆ {K | Adm g K}) (hch : IsChain (· ⊆ ·) c) : Adm g (Icc 0 1 ∩ ⋂₀ c) := by
  set L := Icc (0 : ℝ) 1 ∩ ⋂₀ c
  have hLK : ∀ K ∈ c, L ⊆ K := fun K hK => fun x hx => hx.2 K hK
  refine ⟨isClosed_Icc.inter (isClosed_sInter fun K hK => (hc hK).1),
    inter_subset_left, ⟨⟨le_rfl, zero_le_one⟩, fun K hK => (hc hK).2.2.1⟩,
    ⟨⟨zero_le_one, le_rfl⟩, fun K hK => (hc hK).2.2.2.1⟩, ?_⟩
  intro a ha b hb hab hgap
  have hcne : c.Nonempty := by
    by_contra hce
    rw [not_nonempty_iff_eq_empty] at hce
    have hm : (a + b) / 2 ∈ Ioo a b ∩ L := by
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith [ha.1.1], by linarith [hb.1.2]⟩, ?_⟩
      rw [hce]; exact fun K hK => absurd hK (Set.notMem_empty K)
    rw [hgap] at hm
    exact absurd hm (Set.notMem_empty _)
  haveI : Nonempty c := hcne.to_subtype
  -- for each small `ε`, a gap of some member of the chain, with end points within `ε`
  have key : ∀ ε : ℝ, 0 < ε → 2 * ε < b - a →
      ∃ a' b', a ≤ a' ∧ a' ≤ a + ε ∧ b - ε ≤ b' ∧ b' ≤ b ∧ g a' = g b' := by
    intro ε hε hεab
    obtain ⟨⟨K, hKc⟩, hK⟩ := (isCompact_Icc (a := a + ε) (b := b - ε)).elim_directed_family_closed
      (fun K : c => (K : Set ℝ)) (fun K => (hc K.2).1) (by
        rw [Set.disjoint_left]
        intro x hx hxK
        have hxL : x ∈ L := ⟨⟨by linarith [ha.1.1, hx.1], by linarith [hb.1.2, hx.2]⟩, by
          intro K hK; exact mem_iInter.1 hxK ⟨K, hK⟩⟩
        have : x ∈ Ioo a b ∩ L := ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hxL⟩
        rw [hgap] at this
        exact this)
      (by
        intro K₁ K₂
        rcases hch.total K₁.2 K₂.2 with h | h
        · exact ⟨K₁, subset_rfl, h⟩
        · exact ⟨K₂, h, subset_rfl⟩)
    have hKa : Adm g K := hc hKc
    have haK : a ∈ K := hLK K hKc ha
    have hbK : b ∈ K := hLK K hKc hb
    set A := K ∩ Icc a (a + ε)
    set B := K ∩ Icc (b - ε) b
    have hA : IsClosed A := hKa.1.inter isClosed_Icc
    have hB : IsClosed B := hKa.1.inter isClosed_Icc
    have hAne : A.Nonempty := ⟨a, haK, le_rfl, by linarith⟩
    have hBne : B.Nonempty := ⟨b, hbK, by linarith, le_rfl⟩
    have hAbdd : BddAbove A := ⟨a + ε, fun x hx => hx.2.2⟩
    have hBbdd : BddBelow B := ⟨b - ε, fun x hx => hx.2.1⟩
    set a' := sSup A
    set b' := sInf B
    have ha'A : a' ∈ A := hA.csSup_mem hAne hAbdd
    have hb'B : b' ∈ B := hB.csInf_mem hBne hBbdd
    refine ⟨a', b', ha'A.2.1, ha'A.2.2, hb'B.2.1, hb'B.2.2,
      hKa.2.2.2.2 a' ha'A.1 b' hb'B.1 (by linarith [ha'A.2.2, hb'B.2.1]) ?_⟩
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    obtain ⟨⟨hu1, hu2⟩, huK⟩ := hu
    by_cases h1 : u ≤ a + ε
    · have : u ≤ a' := le_csSup hAbdd ⟨huK, by linarith [ha'A.2.1], h1⟩
      linarith
    by_cases h2 : b - ε ≤ u
    · have : b' ≤ u := csInf_le hBbdd ⟨huK, h2, by linarith [hb'B.2.2]⟩
      linarith
    · exact hK.ne_of_mem ⟨by linarith, by linarith⟩ huK rfl
  -- pass to the limit
  let ε : ℕ → ℝ := fun n => (b - a) / (n + 3)
  have hε : ∀ n, 0 < ε n := fun n => div_pos (by linarith) (by positivity)
  have hε2 : ∀ n, 2 * ε n < b - a := fun n => by
    have h3 : (2 : ℝ) < n + 3 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    calc 2 * ε n = 2 * (b - a) / (n + 3) := by simp only [ε]; ring
      _ < (n + 3) * (b - a) / (n + 3) := by
          apply div_lt_div_of_pos_right _ (by positivity); nlinarith
      _ = b - a := by field_simp
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp (tendsto_add_atTop_nat 3)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, ε]
    push_cast
    rfl
  choose a' b' ha1 ha2 hb1 hb2 hgab using fun n => key (ε n) (hε n) (hε2 n)
  have ta : Tendsto a' atTop (𝓝 a) := by
    have h1 : Tendsto (fun n => a + ε n) atTop (𝓝 a) := by simpa using tendsto_const_nhds.add hεt
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 ha1 ha2
  have tb : Tendsto b' atTop (𝓝 b) := by
    have h1 : Tendsto (fun n => b - ε n) atTop (𝓝 b) := by simpa using tendsto_const_nhds.sub hεt
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hb1 hb2
  have h1 := (hg.tendsto a).comp ta
  have h2 := (hg.tendsto b).comp tb
  have h3 : (g ∘ a') = (g ∘ b') := funext hgab
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- A minimal admissible set exists. -/
theorem exists_minimal_adm [T2Space X] {g : ℝ → X} (hg : Continuous g) :
    ∃ K, Minimal (Adm g) K := by
  obtain ⟨K, hK⟩ := zorn_superset {K | Adm g K} fun c hc hch =>
    ⟨Icc 0 1 ∩ ⋂₀ c, adm_sInter hg hc hch, fun K hK x hx => hx.2 K hK⟩
  exact ⟨K, hK⟩

/-- In a minimal admissible set, two points with equal `g`-values bound a gap. -/
theorem Minimal.gap_of_eq {g : ℝ → X} {K : Set ℝ} (hK : Minimal (Adm g) K) {s t : ℝ}
    (hs : s ∈ K) (ht : t ∈ K) (hst : s < t) (heq : g s = g t) : Ioo s t ∩ K = ∅ := by
  have hA := hK.prop
  set K' := K \ Ioo s t
  have hs01 := hA.2.1 hs
  have ht01 := hA.2.1 ht
  have hK' : Adm g K' := by
    refine ⟨hA.1.inter isOpen_Ioo.isClosed_compl, diff_subset.trans hA.2.1,
      ⟨hA.2.2.1, fun h => by linarith [h.1, hs01.1]⟩,
      ⟨hA.2.2.2.1, fun h => by linarith [h.2, ht01.2]⟩, ?_⟩
    intro a ha b hb hab hgap
    by_cases hK0 : Ioo a b ∩ K = ∅
    · exact hA.2.2.2.2 a ha.1 b hb.1 hab hK0
    · obtain ⟨u, hu, huK⟩ := nonempty_iff_ne_empty.2 hK0
      have huI : u ∈ Ioo s t := by
        by_contra h
        have : u ∈ Ioo a b ∩ K' := ⟨hu, huK, h⟩
        rw [hgap] at this; exact this
      have has : a ≤ s := by
        by_contra h
        exact ha.2 ⟨lt_of_not_ge h, by linarith [hu.1, huI.2]⟩
      have htb : t ≤ b := by
        by_contra h
        exact hb.2 ⟨by linarith [hu.2, huI.1], lt_of_not_ge h⟩
      have hsa : a = s := by
        by_contra h
        have : s ∈ Ioo a b ∩ K' :=
          ⟨⟨lt_of_le_of_ne has h, by linarith⟩, hs, fun h' => lt_irrefl s h'.1⟩
        rw [hgap] at this; exact this
      have htb' : b = t := by
        by_contra h
        have : t ∈ Ioo a b ∩ K' :=
          ⟨⟨by linarith, lt_of_le_of_ne htb (Ne.symm h)⟩, ht, fun h' => lt_irrefl t h'.2⟩
        rw [hgap] at this; exact this
      rw [hsa, htb']
      exact heq
  have hsub : K ⊆ K' := hK.2 hK' diff_subset
  ext u
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hu huK
  exact (hsub huK).2 hu

end MosaicSpaces.Arc
