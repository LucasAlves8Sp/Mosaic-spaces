module

public import MosaicSpaces.G.Basic
public import Mathlib.Order.Interval.Set.Infinite

/-!
# `G` is a mosaic space; closed sets; routes; local path connectedness

Article: Lemma 4.2 (`isMosaicFamily_pieces`, `isMosaicSpace`), Lemma 4.3 (`finite_xpt_mem`,
`finite_arc_mem`, `finite_spoke_mem`, `exists_row_nmem`), Lemma 4.6 (`routes`), Proposition 4.7 in
its path-connected form (`isOpen_pathComponentIn`, `locallyPathConnectedSpace`).

Proposition 4.7 is stated in the article with "arcwise connected"; that form follows from the
arc theorem (`MosaicSpaces.Arc`, `IsMosaicSpace.arcwiseConnected_pathComponentIn`) and is
`MosaicSpaces.G_arcwise`.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval Function

namespace MosaicSpaces

section general

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

theorem isCompactMetrizable_range [CompactSpace P] [MetrizableSpace P] {f : P → X}
    (hf : IsEmbedding f) : IsCompactMetrizable (range f) := by
  refine ⟨isCompact_range hf.continuous, ?_⟩
  have h := (metrizableSpace_image_iff hf univ).2 inferInstance
  rwa [image_univ] at h

theorem locallyPathConnectedSpace_range [LocallyPathConnectedSpace P] {f : P → X}
    (hf : Continuous f) (hcl : IsClosedMap f) : LocallyPathConnectedSpace (range f) :=
  ((isClosedMap_rangeFactorization hcl).isQuotientMap hf.rangeFactorization
    rangeFactorization_surjective).locallyPathConnectedSpace

end general

namespace GSpace

variable {𝒟 : Set (Set (ℕ × ℕ))}

theorem arcMap_coe (D : 𝒟) (s : Ioo (0 : ℝ) 1) :
    arcMap D ⟨s, Ioo_subset_Icc_self s.2⟩ = arc D s := by
  rw [arcMap_of_ne D (t := ⟨s, Ioo_subset_Icc_self s.2⟩) s.2.1.ne' s.2.2.ne]
  rfl

theorem spokeMap_coe (D : 𝒟) (m : (D : Set (ℕ × ℕ))) (s : Ioo (0 : ℝ) 1) :
    spokeMap D m ⟨s, Ioo_subset_Icc_self s.2⟩ = spoke D m s := by
  rw [spokeMap_of_ne D m (t := ⟨s, Ioo_subset_Icc_self s.2⟩) s.2.1.ne' s.2.2.ne]
  rfl

/-- The pieces of the mosaic `𝔐_G`: the ranges of the piece maps. -/
def pieces (𝒟 : Set (Set (ℕ × ℕ))) : Set (Set (GSpace 𝒟)) :=
  {K | (∃ n, K = range (rowMap n)) ∨ K = range sigMap ∨ (∃ D, K = range (phiMap D)) ∨
    ∃ S : CS 𝒟, K = range (lamMap S.1)}

section mosaic

variable (h𝒟 : IsMADFamily 𝒟)
include h𝒟

theorem isClosedEmbedding_rowMap (n : ℕ) : IsClosedEmbedding (rowMap n : I → GSpace 𝒟) :=
  .of_continuous_injective_isClosedMap (continuous_rowMap n) (rowMap_injective n)
    (isClosedMap_rowMap h𝒟 n)

theorem isClosedEmbedding_sigMap : IsClosedEmbedding (sigMap : OnePoint ℕ → GSpace 𝒟) :=
  .of_continuous_injective_isClosedMap continuous_sigMap sigMap_injective (isClosedMap_sigMap h𝒟)

theorem isClosedEmbedding_phiMap (D : 𝒟) : IsClosedEmbedding (phiMap D) :=
  .of_continuous_injective_isClosedMap (continuous_phiMap D) (phiMap_injective D)
    (isClosedMap_phiMap h𝒟 D)

theorem isClosedEmbedding_lamMap (S : CS 𝒟) : IsClosedEmbedding (lamMap S.1) :=
  .of_continuous_injective_isClosedMap (continuous_lamMap S) (lamMap_injective S.1)
    (isClosedMap_lamMap h𝒟 S.1)

/-- **Lemma 4.2**: the pieces form a mosaic family on `G`. -/
theorem isMosaicFamily_pieces : IsMosaicFamily (pieces 𝒟) where
  cover g := by
    cases g with
    | infty => exact ⟨_, Or.inr (Or.inl rfl), OnePoint.infty, rfl⟩
    | pnt D => exact ⟨_, Or.inr (Or.inr (Or.inl ⟨D, rfl⟩)), Fan.centre, phiMap_centre D⟩
    | row n t => exact ⟨_, Or.inl ⟨n, rfl⟩, t, rfl⟩
    | arc D s =>
      refine ⟨_, Or.inr (Or.inr (Or.inr ⟨⟨{D}, countable_singleton D⟩, rfl⟩)),
        Fan.spine (⟨D, mem_singleton D⟩ : ({D} : Set 𝒟)) ⟨s, Ioo_subset_Icc_self s.2⟩, ?_⟩
      rw [lamMap_spine]
      exact arcMap_coe D s
    | spoke D m s =>
      refine ⟨_, Or.inr (Or.inr (Or.inl ⟨D, rfl⟩)), Fan.spine m ⟨s, Ioo_subset_Icc_self s.2⟩, ?_⟩
      rw [phiMap_spine]
      exact spokeMap_coe D m s
  isClosed := by
    rintro K (⟨n, rfl⟩ | rfl | ⟨D, rfl⟩ | ⟨S, rfl⟩)
    · exact (isClosedMap_rowMap h𝒟 n).isClosed_range
    · exact (isClosedMap_sigMap h𝒟).isClosed_range
    · exact (isClosedMap_phiMap h𝒟 D).isClosed_range
    · exact (isClosedMap_lamMap h𝒟 S.1).isClosed_range
  coherent M hM := by
    refine isClosed_iff.2 ⟨fun n => ?_, ?_, fun D => ?_, fun S => ?_⟩
    · have := (hM _ (Or.inl ⟨n, rfl⟩)).preimage (continuous_rowMap n)
      rwa [preimage_inter, preimage_range, inter_univ] at this
    · have := (hM _ (Or.inr (Or.inl rfl))).preimage (continuous_sigMap (𝒟 := 𝒟))
      rwa [preimage_inter, preimage_range, inter_univ] at this
    · have := (hM _ (Or.inr (Or.inr (Or.inl ⟨D, rfl⟩)))).preimage (continuous_phiMap D)
      rwa [preimage_inter, preimage_range, inter_univ] at this
    · have := (hM _ (Or.inr (Or.inr (Or.inr ⟨S, rfl⟩)))).preimage (continuous_lamMap S)
      rwa [preimage_inter, preimage_range, inter_univ] at this

theorem isCompactMetrizable_pieces : ∀ K ∈ pieces 𝒟, IsCompactMetrizable K := by
  rintro K (⟨n, rfl⟩ | rfl | ⟨D, rfl⟩ | ⟨S, rfl⟩)
  · exact isCompactMetrizable_range (isClosedEmbedding_rowMap h𝒟 n).isEmbedding
  · exact isCompactMetrizable_range (isClosedEmbedding_sigMap h𝒟).isEmbedding
  · exact isCompactMetrizable_range (isClosedEmbedding_phiMap h𝒟 D).isEmbedding
  · haveI : Countable S.1 := S.2.to_subtype
    exact isCompactMetrizable_range (isClosedEmbedding_lamMap h𝒟 S).isEmbedding

/-- **Lemma 4.2**: `G` is a mosaic space. -/
theorem isMosaicSpace : IsMosaicSpace (GSpace 𝒟) :=
  ⟨pieces 𝒟, isMosaicFamily_pieces h𝒟, isCompactMetrizable_pieces h𝒟⟩

theorem sequentialSpace : SequentialSpace (GSpace 𝒟) := (isMosaicSpace h𝒟).sequentialSpace

theorem t1Space : T1Space (GSpace 𝒟) := (isMosaicSpace h𝒟).t1Space

end mosaic

/-! ### Lemma 4.3: how closed sets meet the pieces -/


/-- **Lemma 4.3(1)**, first part. -/
theorem finite_xpt_mem {F : Set (GSpace 𝒟)} (hF : IsClosed F) (hinf : infty ∉ F) :
    {n | xpt n ∈ F}.Finite := by
  have hC : IsClosed (sigMap ⁻¹' F) := (isClosed_iff.1 hF).2.1
  have hO : IsOpen (sigMap ⁻¹' F)ᶜ := hC.isOpen_compl
  have hmem : (OnePoint.infty : OnePoint ℕ) ∈ (sigMap ⁻¹' F)ᶜ := hinf
  have h := ((OnePoint.isOpen_iff_of_mem hmem).1 hO).2
  rw [preimage_compl, compl_compl] at h
  exact h.finite_of_discrete

/-- **Lemma 4.3(1)**, second part: only finitely many arcs `A_D` meet a closed set missing `∞`. -/
theorem finite_arc_mem {F : Set (GSpace 𝒟)} (hF : IsClosed F) (hinf : infty ∉ F) :
    {D : 𝒟 | ∃ t, arcMap D t ∈ F}.Finite := by
  by_contra hinfin
  let e := Set.Infinite.natEmbedding _ hinfin
  let S : Set 𝒟 := range fun k => (e k : 𝒟)
  have hS : S.Countable := countable_range _
  have hC : IsClosed (lamMap S ⁻¹' F) := (isClosed_iff.1 hF).2.2.2 ⟨S, hS⟩
  have hc : (Fan.centre : Fan S) ∉ lamMap S ⁻¹' F := by
    simp only [mem_preimage, lamMap_centre]
    exact hinf
  have hfin := Fan.finite_spines_of_isClosed hC hc
  let j : ℕ → S := fun k => ⟨e k, k, rfl⟩
  have hj : Injective j := fun k k' h => by
    have h' := congrArg (fun x : S => (x : 𝒟)) h
    exact e.injective (Subtype.ext h')
  refine Set.infinite_range_of_injective hj (hfin.subset ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨t, ht⟩ := (e k).2
  have ht0 : (t : ℝ) ≠ 0 := by
    intro h0
    rw [show t = 0 from Subtype.ext h0, arcMap_zero] at ht
    exact hinf ht
  refine ⟨Fan.spine (j k) t, ?_, ?_⟩
  · show lamMap S (Fan.spine (j k) t) ∈ F
    rw [lamMap_spine]
    exact ht
  · rw [Fan.spine_apply_self]
    exact ht0

/-- **Lemma 4.3(2)**: a closed set missing `p_D` meets only finitely many spokes of `Φ_D`. -/
theorem finite_spoke_mem {F : Set (GSpace 𝒟)} (hF : IsClosed F) {D : 𝒟} (hD : pnt D ∉ F) :
    {m : (D : Set (ℕ × ℕ)) | ∃ t, spokeMap D m t ∈ F}.Finite := by
  have hC : IsClosed (phiMap D ⁻¹' F) := (isClosed_iff.1 hF).2.2.1 D
  have hc : (Fan.centre : Fan (D : Set (ℕ × ℕ))) ∉ phiMap D ⁻¹' F := by
    simp only [mem_preimage, phiMap_centre]
    exact hD
  refine (Fan.finite_spines_of_isClosed hC hc).subset ?_
  rintro m ⟨t, ht⟩
  have ht0 : (t : ℝ) ≠ 0 := by
    intro h0
    rw [show t = 0 from Subtype.ext h0, spokeMap_zero] at ht
    exact hD ht
  refine ⟨Fan.spine m t, ?_, ?_⟩
  · show phiMap D (Fan.spine m t) ∈ F
    rw [phiMap_spine]
    exact ht
  · rw [Fan.spine_apply_self]
    exact ht0

/-- **Lemma 4.3(2)**, "in particular". -/
theorem finite_wit_mem {F : Set (GSpace 𝒟)} (hF : IsClosed F) {D : 𝒟} (hD : pnt D ∉ F) :
    {m | m ∈ (D : Set (ℕ × ℕ)) ∧ wit m ∈ F}.Finite := by
  refine ((finite_spoke_mem hF hD).image Subtype.val).subset ?_
  rintro m ⟨hm, hmF⟩
  refine ⟨⟨m, hm⟩, ⟨1, ?_⟩, rfl⟩
  rw [spokeMap_one]
  exact hmF

/-- **Lemma 4.3(3)**. -/
theorem exists_row_nmem {F : Set (GSpace 𝒟)} (hF : IsClosed F) {n : ℕ} (hn : xpt n ∉ F) :
    ∃ ε > 0, ∀ t : I, (t : ℝ) < ε → row n t ∉ F := by
  have hO : IsOpen (rowMap n ⁻¹' F)ᶜ := ((isClosed_iff.1 hF).1 n).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 0 hn
  refine ⟨ε, hε, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, sub_zero,
    abs_of_nonneg t.2.1]
  exact ht

/-- Finitely many members of `𝒟` have a union with finite sections. -/
theorem finite_section_biUnion (h𝒟 : IsMADFamily 𝒟) {𝒜 : Set 𝒟} (h𝒜 : 𝒜.Finite) (n : ℕ) :
    {i | (n, i) ∈ ⋃ D ∈ 𝒜, (D : Set (ℕ × ℕ))}.Finite := by
  refine (h𝒜.biUnion fun D _ => (h𝒟.mem D D.2).2 n).subset ?_
  intro i hi
  simp only [mem_setOf_eq, mem_iUnion] at hi ⊢
  obtain ⟨D, hD, h⟩ := hi
  exact ⟨D, hD, h⟩

/-! ### Paths in `G` -/

/-- The initial segment of the row `n`, from `x_n` to `R_n(a)`. -/
def rowPath (n : ℕ) (a : I) : Path (xpt n : GSpace 𝒟) (row n a) where
  toFun s := row n ⟨(s : ℝ) * a, unitInterval.mul_mem s.2 a.2⟩
  continuous_toFun := (continuous_rowMap n).comp
    (Continuous.subtype_mk (continuous_subtype_val.mul continuous_const) _)
  source' := by
    show row n _ = row n 0
    congr 1
    exact Subtype.ext (show ((0 : I) : ℝ) * a = ((0 : I) : ℝ) by simp)
  target' := by
    show row n _ = row n a
    congr 1
    exact Subtype.ext (show ((1 : I) : ℝ) * a = a by simp)

theorem rowPath_apply_le (n : ℕ) (a s : I) :
    ∃ t : I, (rowPath n a s : GSpace 𝒟) = row n t ∧ (t : ℝ) ≤ a := by
  refine ⟨⟨(s : ℝ) * a, unitInterval.mul_mem s.2 a.2⟩, rfl, ?_⟩
  exact mul_le_of_le_one_left a.2.1 s.2.2

/-- The arc `A_D` as a path from `∞` to `p_D`. -/
noncomputable def arcPath (D : 𝒟) : Path (infty : GSpace 𝒟) (pnt D) where
  toFun := arcMap D
  continuous_toFun := continuous_arcMap D
  source' := arcMap_zero D
  target' := arcMap_one D

/-- The spoke `E_{D,m}` as a path from `p_D` to the witness `m`. -/
noncomputable def spokePath (D : 𝒟) (m : (D : Set (ℕ × ℕ))) :
    Path (pnt D : GSpace 𝒟) (wit m) where
  toFun := spokeMap D m
  continuous_toFun := continuous_spokeMap D m
  source' := spokeMap_zero D m
  target' := spokeMap_one D m

/-! ### Lemma 4.6: routes -/

/-- **Lemma 4.6 (Routes)**: if `F` is closed and `∞ ∉ F`, then all but finitely many `x_n` are
joined to `∞` by a path missing `F`. -/
theorem routes (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F) (hinf : infty ∉ F) :
    {n | ¬ JoinedIn Fᶜ (xpt n) infty}.Finite := by
  set N₁ := {n | xpt n ∈ F}
  have hN₁ : N₁.Finite := finite_xpt_mem hF hinf
  set 𝒟F := {D : 𝒟 | ∃ t, arcMap D t ∈ F}
  have h𝒟F : 𝒟F.Finite := finite_arc_mem hF hinf
  let good : ℕ → Prop := fun n => ∃ (i : ℕ) (D : 𝒟) (hm : (n, i) ∈ (D : Set (ℕ × ℕ))),
    D ∉ 𝒟F ∧ (∀ t : I, (t : ℝ) ≤ witT i → row n t ∉ F) ∧ ∀ t, spokeMap D ⟨(n, i), hm⟩ t ∉ F
  have hgood : ∀ n, good n → JoinedIn Fᶜ (xpt n) infty := by
    rintro n ⟨i, D, hm, hD, hrow, hspoke⟩
    have j1 : JoinedIn Fᶜ (xpt n) (row n (witT i) : GSpace 𝒟) := by
      refine ⟨rowPath n (witT i), fun s => ?_⟩
      obtain ⟨t, ht, hle⟩ := rowPath_apply_le (𝒟 := 𝒟) n (witT i) s
      have := hrow t hle
      rw [← ht] at this
      exact this
    have j2 : JoinedIn Fᶜ (wit (n, i) : GSpace 𝒟) (pnt D) :=
      (show JoinedIn Fᶜ (pnt D) (wit ((⟨(n, i), hm⟩ : (D : Set (ℕ × ℕ))) : ℕ × ℕ)) from
        ⟨spokePath D ⟨(n, i), hm⟩, fun s => hspoke s⟩).symm
    have j3 : JoinedIn Fᶜ (pnt D) (infty : GSpace 𝒟) :=
      (show JoinedIn Fᶜ infty (pnt D) from
        ⟨arcPath D, fun s hs => hD ⟨s, hs⟩⟩).symm
    exact (j1.trans j2).trans j3
  set N₂ := {n | n ∉ N₁ ∧ ¬ good n}
  have hN₂ : N₂.Finite := by
    by_contra hinfin
    set B := ⋃ D ∈ 𝒟F, (D : Set (ℕ × ℕ))
    have hex : ∀ n ∈ N₂, ∃ i, (∀ t : I, (t : ℝ) ≤ witT i → row n t ∉ F) ∧ (n, i) ∉ B := by
      intro n hn
      obtain ⟨ε, hε, hrow⟩ := exists_row_nmem hF hn.1
      obtain ⟨i₀, hi₀⟩ := exists_witT_lt hε
      obtain ⟨i, hi, hiB⟩ :=
        ((Set.Ici_infinite i₀).diff (finite_section_biUnion h𝒟 h𝒟F n)).nonempty
      exact ⟨i, fun t ht => hrow t (lt_of_le_of_lt ht (hi₀ i hi)), hiB⟩
    choose! ι hι using hex
    set Y : Set (ℕ × ℕ) := (fun n => (n, ι n)) '' N₂
    have hY : IsC Y := by
      refine ⟨(show N₂.Infinite from hinfin).image fun a _ b _ h => (Prod.mk.inj h).1, fun n => ?_⟩
      refine (finite_singleton (ι n)).subset ?_
      rintro j ⟨n', -, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    obtain ⟨D, hD𝒟, hDY⟩ := h𝒟.maximal Y hY
    let D' : 𝒟 := ⟨D, hD𝒟⟩
    have hD'F : D' ∉ 𝒟F := by
      intro hD'
      obtain ⟨m, hmD, hmY⟩ := hDY.nonempty
      obtain ⟨n, hn, rfl⟩ := hmY
      exact (hι n hn).2 (mem_biUnion hD' hmD)
    have hpD : pnt D' ∉ F := by
      intro h
      exact hD'F ⟨1, by rw [arcMap_one]; exact h⟩
    have hT := (finite_spoke_mem hF hpD).image Subtype.val
    obtain ⟨m, ⟨hmD, hmY⟩, hmT⟩ := (hDY.diff hT).nonempty
    obtain ⟨n, hn, rfl⟩ := hmY
    refine hn.2 ⟨ι n, D', hmD, hD'F, (hι n hn).1, fun t ht => hmT ⟨⟨_, hmD⟩, ⟨t, ht⟩, rfl⟩⟩
  refine (hN₁.union hN₂).subset fun n hn => ?_
  by_cases h1 : n ∈ N₁
  · exact Or.inl h1
  · exact Or.inr ⟨h1, fun hg => hn (hgood n hg)⟩

/-! ### Proposition 4.7 (path-connected form) -/

/-- The condition of Lemma 2.14 for the piece `Σ`, from Lemma 4.6. -/
theorem sigma_condition (h𝒟 : IsMADFamily 𝒟) (O : Set (GSpace 𝒟)) (hO : IsOpen O) :
    ∀ z ∈ O ∩ range sigMap, ∀ v : ℕ → GSpace 𝒟, (∀ n, v n ∈ range sigMap) →
      Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z := by
  rintro z ⟨hzO, c, rfl⟩ v hv hvz
  choose w hw using hv
  have hwv : v = sigMap ∘ w := funext fun n => (hw n).symm
  have hwc : Tendsto w atTop (𝓝 c) := by
    rw [(isClosedEmbedding_sigMap h𝒟).isInducing.tendsto_nhds_iff, ← hwv]
    exact hvz
  induction c using OnePoint.rec with
  | infty =>
    have hbad := routes h𝒟 hO.isClosed_compl (fun h => h hzO)
    rw [compl_compl] at hbad
    have hQ : IsClosed (((↑) : ℕ → OnePoint ℕ) '' {n | ¬ JoinedIn O (xpt n) infty}) :=
      (hbad.image _).isClosed
    have hmem : (OnePoint.infty : OnePoint ℕ) ∈
        (((↑) : ℕ → OnePoint ℕ) '' {n | ¬ JoinedIn O (xpt n) infty})ᶜ := by
      rintro ⟨n, -, h⟩
      exact OnePoint.coe_ne_infty n h
    filter_upwards [hwc.eventually (hQ.isOpen_compl.mem_nhds hmem)] with k hk
    rw [hwv]
    induction h : w k using OnePoint.rec with
    | infty =>
      simp only [comp_apply, h]
      exact mem_pathComponentIn_self hzO
    | coe n =>
      simp only [comp_apply, h]
      have hj : JoinedIn O (xpt n) infty := by
        by_contra hn
        exact hk ⟨n, hn, h.symm⟩
      exact hj.symm
  | coe n =>
    have hopen : IsOpen ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
      rw [← image_singleton]
      exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete _)
    filter_upwards [hwc.eventually (hopen.mem_nhds rfl)] with k hk
    rw [hwv, comp_apply, mem_singleton_iff.1 hk]
    exact mem_pathComponentIn_self hzO

theorem pieces_condition (h𝒟 : IsMADFamily 𝒟) :
    ∀ K ∈ pieces 𝒟, LocallyPathConnectedSpace K ∨
      ∀ (O : Set (GSpace 𝒟)), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → GSpace 𝒟, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z := by
  rintro K (⟨n, rfl⟩ | rfl | ⟨D, rfl⟩ | ⟨S, rfl⟩)
  · exact Or.inl (locallyPathConnectedSpace_range (continuous_rowMap n) (isClosedMap_rowMap h𝒟 n))
  · exact Or.inr fun O hO => sigma_condition h𝒟 O hO
  · haveI := Fan.locallyPathConnectedSpace (J := (D : Set (ℕ × ℕ)))
    exact Or.inl (locallyPathConnectedSpace_range (continuous_phiMap D) (isClosedMap_phiMap h𝒟 D))
  · haveI := Fan.locallyPathConnectedSpace (J := S.1)
    exact Or.inl (locallyPathConnectedSpace_range (continuous_lamMap S)
      (isClosedMap_lamMap h𝒟 S.1))

/-- **Proposition 4.7**, path-connected form: the path components of every open subset of `G` are
open. -/
theorem isOpen_pathComponentIn (h𝒟 : IsMADFamily 𝒟) {O : Set (GSpace 𝒟)} (hO : IsOpen O)
    (x : GSpace 𝒟) : IsOpen (pathComponentIn O x) :=
  (isMosaicFamily_pieces h𝒟).isOpen_pathComponentIn (isCompactMetrizable_pieces h𝒟)
    (pieces_condition h𝒟) hO x

/-- **Proposition 4.7**, path-connected form: `G` is locally path connected. -/
theorem locallyPathConnectedSpace (h𝒟 : IsMADFamily 𝒟) : LocallyPathConnectedSpace (GSpace 𝒟) :=
  (isMosaicFamily_pieces h𝒟).locallyPathConnectedSpace (isCompactMetrizable_pieces h𝒟)
    (pieces_condition h𝒟)

end GSpace

end MosaicSpaces
