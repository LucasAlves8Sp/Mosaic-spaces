module

public import MosaicSpaces.Fan
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The metric `φ` of a null fan (Section 4.2)

The article defines `Fan(I) = {o} ∪ I × (0,1]` with the metric
`φ((i,t),(j,s)) = |t - s|/ν(i)` if `i = j` and `t/ν(i) + s/ν(j)` if `i ≠ j`, for an injection
`ν : I → ℕ = {1,2,…}`. In the formalization `Fan J` is a subspace of `J → ℝ` with the product
topology (`MosaicSpaces.Fan`), the point `(j,t)` being `t·δ_j`. Here:

* `phi ν f g = ∑' j, |f j - g j| / (ν j + 1)` (the article's `ν` is `ν + 1`, valued in
  `{1,2,…}`), which is the article's formula (`phi_spine_same`, `phi_spine_ne`);
* `phi` is a metric (`phi_comm`, `phi_triangle`, `phi_eq_zero_iff`);
* **the product topology of `Fan J` is the topology of `φ`** (`isOpen_iff_phi`), for every
  injection `ν`. In particular the fan topology does not depend on `ν` (F1);
* **(F1)**, the neighbourhoods of the centre (`mem_nhds_centre_iff`);
* **(F4)**, `Fan(J')` for `J' ⊆ J` is a closed subspace of `Fan(J)` (`isClosedEmbedding_extend`).
-/

@[expose] public section

open Set Filter Topology Function

namespace MosaicSpaces.Fan

universe u

variable {J : Type u}

/-- The article's metric `φ` on `Fan(J)` for an injection `ν` (the article's `ν` is `ν + 1`). -/
noncomputable def phi (ν : J → ℕ) (f g : Fan J) : ℝ :=
  ∑' j, |(f : J → ℝ) j - (g : J → ℝ) j| / ((ν j : ℝ) + 1)

variable (ν : J → ℕ)

theorem support_subsingleton (f : Fan J) : {j | (f : J → ℝ) j ≠ 0}.Subsingleton :=
  fun j hj j' hj' => by
    by_contra h
    exact hj' (eq_zero_of_ne h hj)

theorem phi_term_nonneg (f g : Fan J) (j : J) :
    0 ≤ |(f : J → ℝ) j - (g : J → ℝ) j| / ((ν j : ℝ) + 1) := by positivity

theorem summable_phi (f g : Fan J) :
    Summable fun j => |(f : J → ℝ) j - (g : J → ℝ) j| / ((ν j : ℝ) + 1) := by
  refine summable_of_hasFiniteSupport
    (((support_subsingleton f).finite.union (support_subsingleton g).finite).subset ?_)
  intro j hj
  by_contra h
  simp only [mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  exact hj (by simp [h.1, h.2])

theorem term_le_phi (f g : Fan J) (j : J) :
    |(f : J → ℝ) j - (g : J → ℝ) j| / ((ν j : ℝ) + 1) ≤ phi ν f g :=
  (summable_phi ν f g).le_tsum j fun k _ => phi_term_nonneg ν f g k

theorem phi_nonneg (f g : Fan J) : 0 ≤ phi ν f g :=
  tsum_nonneg fun j => phi_term_nonneg ν f g j

theorem phi_comm (f g : Fan J) : phi ν f g = phi ν g f := by
  unfold phi; congr 1; ext j; rw [abs_sub_comm]

theorem phi_triangle (f g h : Fan J) : phi ν f h ≤ phi ν f g + phi ν g h := by
  unfold phi
  rw [← (summable_phi ν f g).tsum_add (summable_phi ν g h)]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_phi ν f h)
    ((summable_phi ν f g).add (summable_phi ν g h))
  rw [← add_div]
  gcongr
  exact abs_sub_le _ _ _

theorem phi_eq_zero_iff (f g : Fan J) : phi ν f g = 0 ↔ f = g := by
  constructor
  · intro h
    refine Subtype.ext (funext fun j => ?_)
    have h1 := term_le_phi ν f g j
    rw [h] at h1
    have h2 : |(f : J → ℝ) j - (g : J → ℝ) j| / ((ν j : ℝ) + 1) = 0 :=
      le_antisymm h1 (phi_term_nonneg ν f g j)
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · exact sub_eq_zero.1 (abs_eq_zero.1 h2)
    · exact absurd h2 (by positivity)
  · rintro rfl
    simp [phi]

/-- The article's formula on one spine. -/
theorem phi_spine_same (i : J) (t s : unitInterval) :
    phi ν (spine i t) (spine i s) = |(t : ℝ) - s| / ((ν i : ℝ) + 1) := by
  unfold phi
  rw [tsum_eq_single i fun j hj => by simp [spine_apply_ne hj]]
  simp [spine_apply_self]

/-- The article's formula on two distinct spines. -/
theorem phi_spine_ne {i j : J} (hij : i ≠ j) (t s : unitInterval) :
    phi ν (spine i t) (spine j s) = (t : ℝ) / ((ν i : ℝ) + 1) + (s : ℝ) / ((ν j : ℝ) + 1) := by
  classical
  unfold phi
  rw [tsum_eq_sum (s := {i, j}) fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [spine_apply_ne hk.1, spine_apply_ne hk.2]]
  rw [Finset.sum_pair hij]
  simp [spine_apply_self, spine_apply_ne hij, spine_apply_ne (Ne.symm hij), abs_of_nonneg t.2.1,
    abs_of_nonneg s.2.1]

/-- **The fan topology is the topology of the metric `φ`** (for every injection `ν`). -/
theorem isOpen_iff_phi (hν : Injective ν) {s : Set (Fan J)} :
    IsOpen s ↔ ∀ f ∈ s, ∃ ε > 0, ∀ g, phi ν f g < ε → g ∈ s := by
  classical
  constructor
  · intro hs f hf
    obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hs
    obtain ⟨I, u, hu, hIW⟩ := isOpen_pi_iff.1 hW (f : J → ℝ) hf
    have hη : ∀ a ∈ I, ∃ η > 0, Metric.ball ((f : J → ℝ) a) η ⊆ u a := fun a ha =>
      Metric.isOpen_iff.1 (hu a ha).1 _ (hu a ha).2
    choose η hηpos hηu using hη
    let w : J → ℝ := fun a => if h : a ∈ I then η a h / ((ν a : ℝ) + 1) else 1
    have hw : ∀ a, 0 < w a := fun a => by
      by_cases h : a ∈ I
      · simp only [w, h, ↓reduceDIte]; exact div_pos (hηpos a h) (by positivity)
      · simp only [w, h, ↓reduceDIte]; exact one_pos
    obtain ⟨ε, hε, hεw⟩ : ∃ ε > 0, ∀ a ∈ I, ε ≤ w a := by
      rcases I.eq_empty_or_nonempty with hI | hI
      · exact ⟨1, one_pos, by simp [hI]⟩
      · refine ⟨I.inf' hI w, (Finset.lt_inf'_iff hI).2 fun a _ => hw a, fun a ha =>
          Finset.inf'_le _ ha⟩
    refine ⟨ε, hε, fun g hg => hIW fun a (ha : a ∈ I) => hηu a ha ?_⟩
    have h1 := (term_le_phi ν f g a).trans_lt (hg.trans_le (hεw a ha))
    have hwa : w a = η a ha / ((ν a : ℝ) + 1) := by simp only [w, ha, ↓reduceDIte]
    rw [hwa] at h1
    rw [div_lt_div_iff_of_pos_right (by positivity)] at h1
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]; exact h1
  · intro h
    refine isOpen_iff_mem_nhds.2 fun f hf => ?_
    obtain ⟨ε, hε, hεs⟩ := h f hf
    refine Filter.mem_of_superset ?_ fun g hg => hεs g hg
    rcases eq_centre_or_spine f with rfl | ⟨i, hi⟩
    · -- the centre: finitely many spines are short, the others are uniformly small
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
      let F : Set J := ν ⁻¹' {n | n < N}
      have hF : F.Finite := (Set.finite_lt_nat N).preimage hν.injOn
      have hev : ∀ᶠ g : Fan J in 𝓝 centre, ∀ j ∈ F, (g : J → ℝ) j < ε / 2 := by
        refine (hF.eventually_all).2 fun j _ => ?_
        have hc : Continuous fun g : Fan J => (g : J → ℝ) j :=
          (continuous_apply j).comp continuous_subtype_val
        have h0 : ((centre : Fan J) : J → ℝ) j < ε / 2 := by simpa using half_pos hε
        exact (hc.tendsto centre).eventually (Iio_mem_nhds h0)
      filter_upwards [hev] with g hg
      show phi ν centre g < ε
      rcases eq_centre_or_spine g with rfl | ⟨k, hk⟩
      · rw [(phi_eq_zero_iff ν _ _).2 rfl]; exact hε
      have hphi : phi ν centre g = (g : J → ℝ) k / ((ν k : ℝ) + 1) := by
        unfold phi
        rw [tsum_eq_single k fun j hj => by simp [eq_zero_of_ne (Ne.symm hj) hk]]
        simp [abs_of_nonneg (coe_mem_Icc g k).1]
      rw [hphi]
      have hgk := coe_mem_Icc g k
      by_cases hkF : k ∈ F
      · have := hg k hkF
        calc (g : J → ℝ) k / ((ν k : ℝ) + 1) ≤ (g : J → ℝ) k :=
              div_le_self hgk.1 (by linarith [(Nat.cast_nonneg (ν k) : (0 : ℝ) ≤ ν k)])
          _ < ε := by linarith
      · have hNk : (N : ℝ) ≤ ν k := by exact_mod_cast not_lt.1 hkF
        have hpos : (0 : ℝ) < (ν k : ℝ) + 1 := by positivity
        rw [div_lt_iff₀ hpos]
        have : 2 < ε * N := by rwa [div_lt_iff₀ hε, mul_comm] at hN
        nlinarith [hgk.2]
    · -- a point `t·δ_i` with `t > 0`: nearby points lie on the same spine
      set t := (f : J → ℝ) i
      have ht : 0 < t := lt_of_le_of_ne (coe_mem_Icc f i).1 (Ne.symm hi)
      set δ := min t (ε * ((ν i : ℝ) + 1))
      have hδ : 0 < δ := lt_min ht (by positivity)
      have hc : Continuous fun g : Fan J => (g : J → ℝ) i :=
        (continuous_apply i).comp continuous_subtype_val
      have hev : ∀ᶠ g : Fan J in 𝓝 f, |(g : J → ℝ) i - t| < δ := by
        have := (hc.tendsto f).eventually (Metric.ball_mem_nhds t hδ)
        filter_upwards [this] with g hg
        simpa [Real.dist_eq] using hg
      filter_upwards [hev] with g hg
      show phi ν f g < ε
      have hgi : (g : J → ℝ) i ≠ 0 := by
        intro h0
        rw [h0, zero_sub, abs_neg, abs_of_pos ht] at hg
        exact absurd (hg.trans_le (min_le_left _ _)) (lt_irrefl t)
      have hphi : phi ν f g = |t - (g : J → ℝ) i| / ((ν i : ℝ) + 1) := by
        unfold phi
        refine tsum_eq_single i fun j hj => ?_
        simp [eq_zero_of_ne (Ne.symm hj) hi, eq_zero_of_ne (Ne.symm hj) hgi]
      rw [hphi, div_lt_iff₀ (by positivity), abs_sub_comm]
      exact hg.trans_le (min_le_right _ _)


/-- **(F1)**: a set containing the centre is a neighbourhood of the centre iff it contains all but
finitely many spines and an initial segment of each remaining spine. -/
theorem mem_nhds_centre_iff {N : Set (Fan J)} (hN : centre ∈ N) :
    N ∈ 𝓝 (centre : Fan J) ↔ ∃ F : Set J, F.Finite ∧ (∀ j ∉ F, ∀ t, spine j t ∈ N) ∧
      ∀ j ∈ F, ∃ η > 0, ∀ t : unitInterval, (t : ℝ) < η → spine j t ∈ N := by
  classical
  constructor
  · intro h
    rw [nhds_subtype, Filter.mem_comap] at h
    obtain ⟨W, hW, hWN⟩ := h
    obtain ⟨I, u, hu, hIW⟩ := isOpen_pi_iff.1 (isOpen_interior) _ (mem_interior_iff_mem_nhds.2 hW)
    have hη : ∀ a ∈ I, ∃ η > 0, Metric.ball (0 : ℝ) η ⊆ u a := fun a ha =>
      Metric.isOpen_iff.1 (hu a ha).1 _ (hu a ha).2
    choose η hηpos hηu using hη
    have key : ∀ g : Fan J, (∀ a ∈ I, (g : J → ℝ) a ∈ u a) → g ∈ N := fun g hg =>
      hWN (show (g : J → ℝ) ∈ W from interior_subset (hIW fun a (ha : a ∈ I) => hg a ha))
    refine ⟨I, I.finite_toSet, fun j hj t => key _ fun a ha => ?_,
      fun j (hj : j ∈ I) => ⟨η j hj, hηpos j hj, fun t ht => key _ fun a ha => hηu a ha ?_⟩⟩
    · have hne : a ≠ j := fun e => hj (e ▸ ha)
      rw [coe_spine, Pi.single_eq_of_ne hne]
      exact (hu a ha).2
    · by_cases hja : a = j
      · subst hja
        rw [coe_spine, Pi.single_eq_same, Metric.mem_ball, Real.dist_eq, sub_zero,
          abs_of_nonneg t.2.1]
        exact ht
      · rw [coe_spine, Pi.single_eq_of_ne hja]; exact Metric.mem_ball_self (hηpos a ha)
  · rintro ⟨F, hF, hout, hin⟩
    choose! η hηpos hη using hin
    have hev : ∀ᶠ g : Fan J in 𝓝 centre, ∀ j ∈ F, (g : J → ℝ) j < η j := by
      refine (hF.eventually_all).2 fun j hj => ?_
      have hc : Continuous fun g : Fan J => (g : J → ℝ) j :=
        (continuous_apply j).comp continuous_subtype_val
      have h0 : ((centre : Fan J) : J → ℝ) j < η j := by simpa using hηpos j hj
      exact (hc.tendsto centre).eventually (Iio_mem_nhds h0)
    filter_upwards [hev] with g hg
    rcases centre_or_spine g with rfl | ⟨j, t, -, rfl⟩
    · exact hN
    · by_cases hj : j ∈ F
      · refine hη j hj t ?_
        have := hg j hj
        rwa [spine_apply_self] at this
      · exact hout j hj t

open Classical in
/-- Extension by zero from `Fan J'` (`J' ⊆ J`) to `Fan J`. -/
noncomputable def extend (J' : Set J) (f : Fan J') : Fan J :=
  ⟨fun j => if h : j ∈ J' then (f : J' → ℝ) ⟨j, h⟩ else 0, fun j => by
    by_cases h : j ∈ J'
    · simp only [h, dite_true]; exact coe_mem_Icc f _
    · simp only [h, dite_false]; exact ⟨le_rfl, zero_le_one⟩, fun j j' hjj' => by
    by_cases h : j ∈ J'
    · by_cases h' : j' ∈ J'
      · simp only [h, h', dite_true]
        exact f.2.2 _ _ fun e => hjj' (congrArg Subtype.val e)
      · simp [h']
    · simp [h]⟩

/-- **(F4)**: for `J' ⊆ J`, `Fan(J')` with its own topology is a closed subspace of `Fan(J)`. -/
theorem isClosedEmbedding_extend (J' : Set J) : IsClosedEmbedding (extend J') := by
  classical
  have hc : Continuous (extend J') := by
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    by_cases h : j ∈ J'
    · simp only [h, dite_true]
      exact (continuous_apply (⟨j, h⟩ : J')).comp continuous_subtype_val
    · simp only [h, dite_false]; exact continuous_const
  have hinj : Injective (extend J') := by
    intro f g hfg
    refine Subtype.ext (funext fun j => ?_)
    have := congrArg (fun f : Fan J => (f : J → ℝ) j) hfg
    simpa [extend, j.2] using this
  have : T2Space (Fan J) := inferInstance
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap hc hinj hc.isClosedMap


/-- **(F2)**, spines: each spine is an arc (a closed embedding of `[0,1]`), and a spine minus the
centre is open. -/
theorem spine_arc (j : J) :
    IsClosedEmbedding (spine j : unitInterval → Fan J) ∧
      IsOpen (spine j '' {t | (t : ℝ) ≠ 0}) := by
  classical
  refine ⟨IsClosedEmbedding.of_continuous_injective_isClosedMap (continuous_spine j)
    (spine_injective_right j) (continuous_spine j).isClosedMap, ?_⟩
  have e : spine j '' {t | (t : ℝ) ≠ 0} = {g : Fan J | (g : J → ℝ) j ≠ 0} := by
    ext g
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [spine_apply_self] using ht
    · intro hg
      exact ⟨⟨(g : J → ℝ) j, coe_mem_Icc g j⟩, hg, (eq_spine hg).symm⟩
  rw [e]
  exact isOpen_ne_fun ((continuous_apply j).comp continuous_subtype_val) continuous_const

end MosaicSpaces.Fan
