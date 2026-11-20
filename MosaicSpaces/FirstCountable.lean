module

public import MosaicSpaces.Local
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Order.ProjIcc

/-!
# First countable spaces (article: Propositions 7.1 and 7.2)

* `MosaicSpaces.exists_metricContinuum_tail` is **Proposition 7.1**, and
  `MosaicSpaces.isMContinuumSpace_of_isOpen_of_firstCountable` its consequence.
* `MosaicSpaces.exists_path_through_tail` is **Proposition 7.2**, and
  `MosaicSpaces.isQuasiCurveSpace_of_firstCountable` its consequence.

The hypothesis "`x` has a countable neighbourhood base" is `(𝓝 x).IsCountablyGenerated`. Neither
proof uses that the ambient space is Hausdorff; Proposition 7.2's path construction does not even
use that the space is a mosaic space, and the Lean statement omits that hypothesis.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ### A nested sequence of good neighbourhoods -/

/-- Under a countable neighbourhood base at `x`, if every open set containing `x` contains an
open set containing `x` with property `Q`, then there are nested open sets `W k ⊆ U` with
property `Q`, containing `x`, forming a neighbourhood base at `x`. (The nesting is the choice made
in the proof of Proposition 7.2: `W (k+1) ⊆ W k ∩ V (k+1)`.) -/
theorem exists_nested_basis {x : X} [(𝓝 x).IsCountablyGenerated] {U : Set X} (hU : IsOpen U)
    (hxU : x ∈ U) {Q : Set X → Prop}
    (hloc : ∀ O : Set X, IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ Q W) :
    ∃ W : ℕ → Set X, (∀ k, IsOpen (W k) ∧ x ∈ W k ∧ W k ⊆ U ∧ Q (W k)) ∧ Antitone W ∧
      ∀ O ∈ 𝓝 x, ∃ k, W k ⊆ O := by
  obtain ⟨B, hB⟩ := (𝓝 x).exists_antitone_basis
  choose! S hSo hxS hSsub hSQ using hloc
  let W : ℕ → Set X := fun k => Nat.rec (S (interior (B 0) ∩ U))
    (fun k Wk => S (Wk ∩ interior (B (k + 1)))) k
  have hxB : ∀ k, x ∈ interior (B k) := fun k => mem_interior_iff_mem_nhds.2 (hB.mem k)
  have key : ∀ k, IsOpen (W k) ∧ x ∈ W k ∧ W k ⊆ U ∧ W k ⊆ B k := by
    intro k
    induction k with
    | zero =>
      have ho : IsOpen (interior (B 0) ∩ U) := isOpen_interior.inter hU
      have hx : x ∈ interior (B 0) ∩ U := ⟨hxB 0, hxU⟩
      exact ⟨hSo _ ho hx, hxS _ ho hx, (hSsub _ ho hx).trans inter_subset_right,
        (hSsub _ ho hx).trans (inter_subset_left.trans interior_subset)⟩
    | succ k ih =>
      have ho : IsOpen (W k ∩ interior (B (k + 1))) := ih.1.inter isOpen_interior
      have hx : x ∈ W k ∩ interior (B (k + 1)) := ⟨ih.2.1, hxB (k + 1)⟩
      exact ⟨hSo _ ho hx, hxS _ ho hx, (hSsub _ ho hx).trans (inter_subset_left.trans ih.2.2.1),
        (hSsub _ ho hx).trans (inter_subset_right.trans interior_subset)⟩
  have hsucc : ∀ k, W (k + 1) ⊆ W k := by
    intro k
    have ho : IsOpen (W k ∩ interior (B (k + 1))) := (key k).1.inter isOpen_interior
    have hx : x ∈ W k ∩ interior (B (k + 1)) := ⟨(key k).2.1, hxB (k + 1)⟩
    exact (hSsub _ ho hx).trans inter_subset_left
  have hQ : ∀ k, Q (W k) := by
    intro k
    cases k with
    | zero =>
      exact hSQ _ (isOpen_interior.inter hU) ⟨hxB 0, hxU⟩
    | succ k =>
      exact hSQ _ ((key k).1.inter isOpen_interior) ⟨(key k).2.1, hxB (k + 1)⟩
  refine ⟨W, fun k => ⟨(key k).1, (key k).2.1, (key k).2.2.1, hQ k⟩,
    antitone_nat_of_succ_le hsucc, fun O hO => ?_⟩
  obtain ⟨k, -, hk⟩ := hB.toHasBasis.mem_iff.1 hO
  exact ⟨k, (key k).2.2.2.trans hk⟩

/-- The index bookkeeping of Propositions 7.1 and 7.2: given `u → x` and neighbourhoods
`W k ∋ x`, there are `N₀` and a nondecreasing `κ : ℕ → ℕ`, tending to infinity, with
`u n ∈ W (κ n)` for `n ≥ N₀`. -/
theorem exists_index {u : ℕ → X} {x : X} (hu : Tendsto u atTop (𝓝 x)) {W : ℕ → Set X}
    (hW : ∀ k, W k ∈ 𝓝 x) :
    ∃ (N₀ : ℕ) (κ : ℕ → ℕ), (∀ n ≥ N₀, u n ∈ W (κ n)) ∧ (∀ n n', N₀ ≤ n → n ≤ n' → κ n ≤ κ n')
      ∧ ∀ k₀, ∃ M, ∀ n ≥ M, k₀ ≤ κ n := by
  have hev : ∀ k, ∃ M, ∀ n ≥ M, u n ∈ ⋂ i ∈ Finset.range (k + 1), W i := fun k =>
    eventually_atTop.1 (hu.eventually ((biInter_finset_mem _).2 fun i _ => hW i))
  choose M hM using hev
  let N : ℕ → ℕ := fun k => M k + k
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hspec : ∀ n, N 0 ≤ n → N (κ n) ≤ n := fun n hn =>
    Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn
  refine ⟨N 0, κ, fun n hn => ?_, fun n n' hn hnn' => ?_, fun k₀ => ⟨N k₀, fun n hn => ?_⟩⟩
  · have h1 : M (κ n) ≤ n := le_trans (Nat.le_add_right _ _) (hspec n hn)
    exact mem_iInter₂.1 (hM (κ n) n h1) (κ n) (Finset.mem_range.2 (Nat.lt_succ_self _))
  · exact Nat.le_findGreatest ((Nat.findGreatest_le n).trans hnn') ((hspec n hn).trans hnn')
  · exact Nat.le_findGreatest ((Nat.le_add_left k₀ (M k₀)).trans hn) hn

/-! ### Proposition 7.1 -/

/-- **Proposition 7.1**. Let `X` be a mosaic space, `U ⊆ X` open and `x ∈ U`. Suppose `x` has a
countable neighbourhood base and every open set containing `x` contains an open m-strongly
connected set containing `x`. Then for every sequence in `U` converging to `x` there are `N` and a
metric continuum `L ⊆ U` containing `x` and the terms with index `≥ N`. -/
theorem exists_metricContinuum_tail (hX : IsMosaicSpace X) {U : Set X} (hU : IsOpen U) {x : X}
    (hxU : x ∈ U) [(𝓝 x).IsCountablyGenerated]
    (hloc : ∀ O : Set X, IsOpen O → x ∈ O →
      ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ MStronglyConnected W)
    {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x)) :
    ∃ N, ∃ L ⊆ U, IsMetricContinuum L ∧ x ∈ L ∧ ∀ n ≥ N, u n ∈ L := by
  haveI := hX.sequentialSpace
  obtain ⟨W, hW, hWanti, hWbasis⟩ := exists_nested_basis hU hxU hloc
  obtain ⟨N₀, κ, hκ, -, hκtop⟩ := exists_index hu fun k => (hW k).1.mem_nhds (hW k).2.1
  have hex : ∀ m, ∃ K ⊆ W (κ (m + N₀)), IsMetricContinuum K ∧ x ∈ K ∧ u (m + N₀) ∈ K :=
    fun m => (hW _).2.2.2 x (hW _).2.1 _ (hκ _ (Nat.le_add_left _ _))
  choose K hKW hK hxK huK using hex
  have hnull : ∀ O : Set X, IsOpen O → x ∈ O → ∀ᶠ m in atTop, K m ⊆ O := by
    intro O hO hxO
    obtain ⟨k₀, hk₀⟩ := hWbasis O (hO.mem_nhds hxO)
    obtain ⟨M, hM⟩ := hκtop k₀
    filter_upwards [eventually_ge_atTop M] with m hm
    exact (hKW m).trans ((hWanti (hM _ (le_trans hm (Nat.le_add_right _ _)))).trans hk₀)
  refine ⟨N₀, ⋃ m, K m, iUnion_subset fun m => (hKW m).trans (hW _).2.2.1,
    isMetricContinuum_iUnion_of_null hX.uniqueSeqLimits hK hxK hnull,
    mem_iUnion.2 ⟨0, hxK 0⟩, fun n hn => mem_iUnion.2 ⟨n - N₀, ?_⟩⟩
  have e : n - N₀ + N₀ = n := Nat.sub_add_cancel hn
  have := huK (n - N₀)
  rwa [e] at this

/-- **Proposition 7.1**, consequence: in a first countable, locally m-strongly connected mosaic
space every open subspace is an m-continuum space. -/
theorem isMContinuumSpace_of_isOpen_of_firstCountable [FirstCountableTopology X]
    (hX : IsMosaicSpace X) (hloc : LocallyMStronglyConnected X) {U : Set X} (hU : IsOpen U) :
    IsMContinuumSpace U := by
  rw [isMContinuumSpace_iff_captures (hX.of_isOpen hU)]
  intro v b hv
  have hv' : Tendsto (fun n => (v n : X)) atTop (𝓝 (b : X)) := tendsto_subtype_rng.1 hv
  obtain ⟨N, L, hLU, hL, hbL, hvL⟩ :=
    exists_metricContinuum_tail hX hU b.2 (hloc b) hv'
  refine ⟨(Subtype.val ⁻¹' L : Set U), hL.preimage_val hLU, mem_preimage.2 hbL, fun n => n + N,
    fun i j hij => Nat.add_lt_add_right hij N, fun n => hvL _ (Nat.le_add_left _ _)⟩

/-! ### Concatenating a null sequence of paths -/

/-- The point `1 - 1/(j+1)` of `[0,1]`. -/
noncomputable def tailPt (j : ℕ) : unitInterval :=
  ⟨1 - 1 / ((j : ℝ) + 1), by
    constructor
    · have : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      linarith
    · have : 0 < 1 / ((j : ℝ) + 1) := by positivity
      linarith⟩

/-- A sequence of paths `p j`, each ending where the next begins, whose images converge to `x`,
can be concatenated into one path on `[0,1]` which runs along `p j` on
`[1 - 1/(j+1), 1 - 1/(j+2)]` and ends at `x`. -/
theorem exists_concat_path (p : ℕ → C(unitInterval, X)) (hp : ∀ j, p j 1 = p (j + 1) 0) (x : X)
    (hx : ∀ O : Set X, IsOpen O → x ∈ O → ∀ᶠ j in atTop, range (p j) ⊆ O) :
    ∃ γ : C(unitInterval, X), γ 1 = x ∧ ∀ j, γ (tailPt j) = p j 0 := by
  let pr : ℝ → unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one
  have hpr : Continuous pr := continuous_projIcc
  let g : ℝ → X := fun s => p ⌊s⌋₊ (pr (s - ⌊s⌋₊))
  have hpr0 : pr 0 = 0 := by
    show Set.projIcc (0 : ℝ) 1 zero_le_one 0 = ⟨0, _⟩
    exact Set.projIcc_left _
  have hpr1 : pr 1 = 1 := by
    show Set.projIcc (0 : ℝ) 1 zero_le_one 1 = ⟨1, _⟩
    exact Set.projIcc_right _
  -- on `[j, j+1]` the function `g` is the reparametrised path `p j`
  have hpiece : ∀ j : ℕ, EqOn g (fun s => p j (pr (s - j))) (Icc (j : ℝ) (j + 1)) := by
    intro j s ⟨hs1, hs2⟩
    rcases hs2.lt_or_eq with hlt | heq
    · have hfl : ⌊s⌋₊ = j := (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans hs1)).2 ⟨hs1, hlt⟩
      simp only [g, hfl]
    · have hfl : ⌊s⌋₊ = j + 1 := by
        rw [heq]
        exact_mod_cast Nat.floor_natCast (R := ℝ) (j + 1)
      subst heq
      show p ⌊(j : ℝ) + 1⌋₊ (pr ((j : ℝ) + 1 - ⌊(j : ℝ) + 1⌋₊)) = p j (pr ((j : ℝ) + 1 - j))
      rw [hfl]
      push_cast
      rw [sub_self, add_sub_cancel_left, hpr0, hpr1, hp]
  have hcont : ContinuousOn g (Ici 0) := by
    have hlf : LocallyFinite fun j : ℕ => Icc (j : ℝ) (j + 1) := by
      intro s
      refine ⟨Ioo (s - 1) (s + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      refine (finite_lt_nat ⌈s + 1⌉₊).subset ?_
      rintro j ⟨y, ⟨hy1, -⟩, -, hy4⟩
      exact Nat.lt_ceil.2 (lt_of_le_of_lt hy1 hy4)
    have hcov : (⋃ j : ℕ, Icc (j : ℝ) (j + 1)) = Ici 0 := by
      apply Subset.antisymm
      · exact iUnion_subset fun j s hs => (Nat.cast_nonneg j).trans hs.1
      · intro s hs
        exact mem_iUnion.2 ⟨⌊s⌋₊, Nat.floor_le hs, (Nat.lt_floor_add_one s).le⟩
    rw [← hcov]
    refine hlf.continuousOn_iUnion (fun j => isClosed_Icc) fun j => ?_
    exact ((p j).continuous.comp (hpr.comp (continuous_id.sub continuous_const))).continuousOn.congr
      (hpiece j)
  let G : ℝ → X := fun s => g (max s 0)
  have hG : Continuous G :=
    hcont.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hGrange : ∀ s : ℝ, 0 ≤ s → G s ∈ range (p ⌊s⌋₊) := fun s hs => by
    simp only [G, max_eq_left hs, g]
    exact mem_range_self _
  let σ : unitInterval → ℝ := fun t => (t : ℝ) / (1 - t)
  let f : unitInterval → X := fun t => if (t : ℝ) < 1 then G (σ t) else x
  have hf : Continuous f := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    by_cases ht : (t : ℝ) < 1
    · have hopen : IsOpen {t : unitInterval | (t : ℝ) < 1} :=
        isOpen_lt continuous_subtype_val continuous_const
      have hev : f =ᶠ[𝓝 t] fun t => G (σ t) :=
        Filter.eventually_of_mem (hopen.mem_nhds ht) fun t' ht' => if_pos ht'
      refine ContinuousAt.congr ?_ hev.symm
      refine hG.continuousAt.comp ?_
      exact (continuous_subtype_val.continuousAt).div
        (continuous_const.sub continuous_subtype_val).continuousAt (by linarith)
    · have ht1 : (t : ℝ) = 1 := le_antisymm t.2.2 (not_lt.1 ht)
      have htt : t = 1 := Subtype.ext ht1
      subst htt
      have hf1 : f 1 = x := if_neg (lt_irrefl _)
      show Tendsto f (𝓝 1) (𝓝 (f 1))
      rw [hf1]
      refine (nhds_basis_opens x).tendsto_right_iff.2 fun O ⟨hxO, hO⟩ => ?_
      obtain ⟨J, hJ⟩ := eventually_atTop.1 (hx O hO hxO)
      have hopen : IsOpen {t : unitInterval | (J : ℝ) / (J + 1) < t} :=
        isOpen_lt continuous_const continuous_subtype_val
      have h1 : (1 : unitInterval) ∈ {t : unitInterval | (J : ℝ) / (J + 1) < t} := by
        show (J : ℝ) / (J + 1) < 1
        rw [div_lt_one (by positivity)]
        linarith
      filter_upwards [hopen.mem_nhds h1] with t ht
      by_cases ht' : (t : ℝ) < 1
      · have hpos : 0 < 1 - (t : ℝ) := by linarith
        have hσ : (J : ℝ) ≤ σ t := by
          show (J : ℝ) ≤ (t : ℝ) / (1 - t)
          rw [le_div_iff₀ hpos]
          have h2 : (J : ℝ) < t * (J + 1) := by
            have := (div_lt_iff₀ (by positivity : (0 : ℝ) < J + 1)).1 ht
            linarith
          nlinarith
        have hσ0 : 0 ≤ σ t := le_trans (Nat.cast_nonneg J) hσ
        have hmem := hGrange (σ t) hσ0
        have hfl : J ≤ ⌊σ t⌋₊ := Nat.le_floor hσ
        show f t ∈ O
        simp only [f, if_pos ht']
        exact hJ _ hfl hmem
      · show f t ∈ O
        simp only [f, if_neg ht']
        exact hxO
  refine ⟨⟨f, hf⟩, if_neg (lt_irrefl _), fun j => ?_⟩
  have hlt : ((tailPt j : unitInterval) : ℝ) < 1 := by
    show 1 - 1 / ((j : ℝ) + 1) < 1
    have : 0 < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hσj : σ (tailPt j) = j := by
    show (1 - 1 / ((j : ℝ) + 1)) / (1 - (1 - 1 / ((j : ℝ) + 1))) = j
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  show f (tailPt j) = p j 0
  simp only [f, if_pos hlt, hσj, G, max_eq_left (Nat.cast_nonneg j), g, Nat.floor_natCast,
    sub_self, hpr0]

/-! ### Proposition 7.2 -/

/-- **Proposition 7.2**. Let `x` be a point with a countable neighbourhood base such that every
open set containing `x` contains an open path connected set containing `x`. Then for every
sequence `u → x` there are `N` and a path `f` with `f 1 = x` and `f (1 - 1/(j+1)) = u (N + j)`
for all `j ≥ 0` (the article writes `f(1 - 1/j) = x_{N+j-1}` for `j ≥ 1`). The ambient space is
not assumed to be a mosaic space or Hausdorff. -/
theorem exists_path_through_tail {x : X} [(𝓝 x).IsCountablyGenerated]
    (hloc : ∀ O : Set X, IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPathConnected W)
    {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x)) :
    ∃ N, ∃ f : C(unitInterval, X), f 1 = x ∧ ∀ j, f (tailPt j) = u (N + j) := by
  obtain ⟨W, hW, hWanti, hWbasis⟩ := exists_nested_basis isOpen_univ (mem_univ x) hloc
  obtain ⟨N₀, κ, hκ, hκmono, hκtop⟩ := exists_index hu fun k => (hW k).1.mem_nhds (hW k).2.1
  have hjoin : ∀ j, JoinedIn (W (κ (N₀ + j))) (u (N₀ + j)) (u (N₀ + j + 1)) := by
    intro j
    have h1 : u (N₀ + j) ∈ W (κ (N₀ + j)) := hκ _ (Nat.le_add_right _ _)
    have h2 : u (N₀ + j + 1) ∈ W (κ (N₀ + j)) :=
      hWanti (hκmono _ _ (Nat.le_add_right _ _) (Nat.le_succ _)) (hκ _ (by omega))
    exact (hW _).2.2.2.joinedIn _ h1 _ h2
  let p : ℕ → C(unitInterval, X) := fun j => (hjoin j).somePath.toContinuousMap
  have hp0 : ∀ j, p j 0 = u (N₀ + j) := fun j => (hjoin j).somePath.source
  have hp1 : ∀ j, p j 1 = u (N₀ + j + 1) := fun j => (hjoin j).somePath.target
  have hpnull : ∀ O : Set X, IsOpen O → x ∈ O → ∀ᶠ j in atTop, range (p j) ⊆ O := by
    intro O hO hxO
    obtain ⟨k₀, hk₀⟩ := hWbasis O (hO.mem_nhds hxO)
    obtain ⟨M, hM⟩ := hκtop k₀
    filter_upwards [eventually_ge_atTop M] with j hj
    rintro _ ⟨t, rfl⟩
    exact hk₀ (hWanti (hM _ (le_trans hj (Nat.le_add_left _ _))) ((hjoin j).somePath_mem t))
  obtain ⟨f, hf1, hfj⟩ := exists_concat_path p (fun j => by rw [hp1, hp0]; rfl) x hpnull
  exact ⟨N₀, f, hf1, fun j => (hfj j).trans (hp0 j)⟩

/-- **Proposition 7.2**, consequence: every first countable, locally arcwise connected mosaic
space is a quasi-curve space (indeed a curve space). Only local path connectedness is used. -/
theorem isCurveSpace_of_firstCountable [FirstCountableTopology X] (hX : IsMosaicSpace X)
    (hloc : LocallyPathConnectedOpen X) : IsCurveSpace X := by
  refine isCurveSpace_of_capturesPath hX fun u a hu => ?_
  obtain ⟨N, f, hf1, hfj⟩ := exists_path_through_tail (hloc a) hu
  let γ : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  refine ⟨range γ, ⟨_, _, γ, rfl⟩, ⟨1, hf1⟩, fun n => N + n,
    fun i j hij => Nat.add_lt_add_left hij N, fun n => ⟨tailPt n, hfj n⟩⟩

theorem isQuasiCurveSpace_of_firstCountable [FirstCountableTopology X] (hX : IsMosaicSpace X)
    (hloc : LocallyArcwiseConnected X) : IsQuasiCurveSpace X :=
  (isCurveSpace_of_firstCountable hX hloc.locallyPathConnectedOpen).isQuasiCurveSpace

end MosaicSpaces
