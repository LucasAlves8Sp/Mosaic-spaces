module

public import MosaicSpaces.G.Mosaic

/-!
# The obstruction for continua in `G` (article: Lemma 4.8, Proposition 4.9, Theorem 4.11(3),(4))

* `isClosed_otherPnts`, `exists_isolating_nhd`: every `p_D` has an open neighbourhood containing no
  other `p_{D'}` (the last assertion of Theorem 4.5, proved here directly; the Tychonoff property
  is `GSpace.t35Space`, `MosaicSpaces.G.Tychonoff`).
* `pnt_mem_of_infinite`: an infinite set of witnesses of `D` lying in a closed set forces `p_D`
  into it (from Lemma 4.2).
* `infinite_wit_of_isPreconnected` (Lemma 4.8, the cut lemma).
* `finite_xpt_of_isMetricContinuum` (Proposition 4.9, for metric continua: the "in particular").
  The general form for closed connected sets of countable spread is not stated.
* `not_isMContinuumSpace`, `not_isQuasiCurveSpace`, `finite_xpt_of_path` (Theorem 4.11(4)).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval Function

namespace MosaicSpaces

namespace GSpace

variable {𝒟 : Set (Set (ℕ × ℕ))}

instance : Nonempty (GSpace 𝒟) := ⟨infty⟩

theorem arcMap_eq_pnt_iff {D D' : 𝒟} {t : I} (h0 : (t : ℝ) ≠ 0) :
    arcMap D t = pnt D' ↔ D = D' ∧ t = 1 := by
  constructor
  · intro h
    by_cases h1 : (t : ℝ) = 1
    · rw [eq_one_of_coe h1, arcMap_one, pnt.injEq] at h
      exact ⟨h, eq_one_of_coe h1⟩
    · rw [arcMap_of_ne D h0 h1] at h
      simp at h
  · rintro ⟨rfl, rfl⟩
    exact arcMap_one D

/-- Classification of the points of `Φ_D` lying on rows: they are free ends, i.e. witnesses. -/
theorem phiMap_eq_row {D : 𝒟} {f : Fan (D : Set (ℕ × ℕ))} {n : ℕ} {t : I}
    (h : phiMap D f = row n t) :
    ∃ m : (D : Set (ℕ × ℕ)), f = Fan.spine m 1 ∧ (m : ℕ × ℕ).1 = n ∧ t = witT (m : ℕ × ℕ).2 := by
  rcases Fan.centre_or_spine f with rfl | ⟨m, s, hs, rfl⟩
  · rw [phiMap_centre] at h
    simp at h
  · rw [phiMap_spine] at h
    rcases spokeMap_cases D m hs with ⟨h', rfl⟩ | ⟨s', h', -⟩ <;> rw [h'] at h
    · simp only [wit, row.injEq] at h
      exact ⟨m, rfl, h.1, h.2.symm⟩
    · simp at h

/-! ### The points `p_D` are relatively discrete -/

/-- The set `{∞} ∪ {p_{D'} : D' ≠ D}`. -/
def otherPnts (D : 𝒟) : Set (GSpace 𝒟) := {g | g = infty ∨ ∃ D', D' ≠ D ∧ g = pnt D'}

theorem isClosed_otherPnts (D : 𝒟) : IsClosed (otherPnts D) := by
  refine isClosed_iff.2 ⟨fun n => ?_, ?_, fun D'' => ?_, fun S => ?_⟩
  · convert isClosed_empty
    ext t
    simp [otherPnts, rowMap]
  · refine ((finite_singleton (OnePoint.infty : OnePoint ℕ)).subset ?_).isClosed
    intro c hc
    induction c using OnePoint.rec with
    | infty => rfl
    | coe n =>
      rcases hc with h | ⟨D', -, h⟩ <;> simp [sigMap_coe, xpt] at h
  · refine ((finite_singleton (Fan.centre : Fan (D'' : Set (ℕ × ℕ)))).subset ?_).isClosed
    intro f hf
    rcases Fan.centre_or_spine f with rfl | ⟨m, s, hs, rfl⟩
    · rfl
    · exfalso
      simp only [mem_preimage, phiMap_spine] at hf
      rcases spokeMap_cases D'' m hs with ⟨h', -⟩ | ⟨s', h', -⟩ <;> rw [h'] at hf <;>
        rcases hf with h | ⟨D', -, h⟩ <;> simp [wit] at h
  · let R1 : Set (Fan S.1) :=
      ⋂ j, {h | (h : S.1 → ℝ) j = 0 ∨ (h : S.1 → ℝ) j = 1}
    let R2 : Set (Fan S.1) := ⋂ j : S.1, ⋂ (_ : (j : 𝒟) = D), {h | (h : S.1 → ℝ) j = 0}
    let R := R1 ∩ R2
    have hR : IsClosed R := by
      refine IsClosed.inter ?_ ?_
      · exact isClosed_iInter fun j =>
          (isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const).union
          (isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const)
      · exact isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const
    convert hR using 1
    ext h
    rcases Fan.centre_or_spine h with rfl | ⟨j, t, ht, rfl⟩
    · simp [R, R1, R2, otherPnts, lamMap_centre]
    · simp only [mem_preimage, lamMap_spine]
      constructor
      · rintro (h | ⟨D', hD', h⟩)
        · exact absurd h (arcMap_ne_infty _ ht)
        · obtain ⟨hj, rfl⟩ := (arcMap_eq_pnt_iff ht).1 h
          refine ⟨mem_iInter.2 fun j' => ?_, mem_iInter₂.2 fun j' hj' => ?_⟩
          · by_cases e : j' = j
            · subst e
              right
              rw [Fan.spine_apply_self]
              rfl
            · left
              exact Fan.spine_apply_ne e _
          · have e : j' ≠ j := by
              rintro rfl
              exact hD' (hj.symm.trans hj')
            exact Fan.spine_apply_ne e _
      · rintro ⟨h1, h2⟩
        have ht1 : t = 1 := by
          rcases mem_iInter.1 h1 j with h | h <;> rw [Fan.spine_apply_self] at h
          · exact absurd h ht
          · exact Subtype.ext h
        subst ht1
        refine Or.inr ⟨j, fun hj => ?_, arcMap_one _⟩
        have := mem_iInter₂.1 h2 j hj
        rw [mem_setOf_eq, Fan.spine_apply_self] at this
        simp at this

/-- Last assertion of Theorem 4.5: `p_D` has an open neighbourhood containing no other `p_{D'}`. -/
theorem exists_isolating_nhd (D : 𝒟) :
    ∃ U : Set (GSpace 𝒟), IsOpen U ∧ pnt D ∈ U ∧ ∀ D', pnt D' ∈ U → D' = D := by
  refine ⟨(otherPnts D)ᶜ, (isClosed_otherPnts D).isOpen_compl, ?_, fun D' hD' => ?_⟩
  · rintro (h | ⟨D', hD', h⟩)
    · simp at h
    · exact hD' (pnt.inj h).symm
  · by_contra hne
    exact hD' (Or.inr ⟨D', hne, rfl⟩)

/-! ### Witnesses accumulate at `p_D` -/

/-- An injective sequence of points of `D` converges to `p_D` (Lemma 4.2), in the form: if
infinitely many witnesses of `D` lie in a closed set, so does `p_D`. -/
theorem pnt_mem_of_infinite {K : Set (GSpace 𝒟)} (hK : IsClosed K) {D : 𝒟}
    (h : ((D : Set (ℕ × ℕ)) ∩ {m | wit m ∈ K}).Infinite) : pnt D ∈ K := by
  set T : Set (D : Set (ℕ × ℕ)) := {m | wit (m : ℕ × ℕ) ∈ K}
  have hT : T.Infinite := by
    refine Set.Infinite.of_image Subtype.val (h.mono ?_)
    rintro m ⟨hm, hmK⟩
    exact ⟨⟨m, hm⟩, hmK, rfl⟩
  let e := hT.natEmbedding
  let f : ℕ → Fan (D : Set (ℕ × ℕ)) := fun k => Fan.spine (e k : (D : Set (ℕ × ℕ))) 1
  have hf : Tendsto f atTop (𝓝 Fan.centre) := by
    refine Fan.tendsto_centre fun j => Set.Subsingleton.finite fun k hk k' hk' => ?_
    have h1 : (e k : (D : Set (ℕ × ℕ))) = j := by
      by_contra hne
      exact hk (Fan.spine_apply_ne (Ne.symm hne) _)
    have h2 : (e k' : (D : Set (ℕ × ℕ))) = j := by
      by_contra hne
      exact hk' (Fan.spine_apply_ne (Ne.symm hne) _)
    exact e.injective (Subtype.ext (h1.trans h2.symm))
  have hlim := ((continuous_phiMap D).tendsto _).comp hf
  rw [phiMap_centre] at hlim
  refine hK.mem_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  show phiMap D (Fan.spine _ 1) ∈ K
  rw [phiMap_spine, spokeMap_one]
  exact (e k).2

/-! ### Lemma 4.8: the cut lemma -/

/-- **Lemma 4.8**: a closed connected set containing `∞` and `x_n` contains infinitely many
witnesses of the row `n`. (Only closedness and preconnectedness are used.) -/
theorem infinite_wit_of_isPreconnected (h𝒟 : IsMADFamily 𝒟) {K : Set (GSpace 𝒟)}
    (hK : IsClosed K) (hconn : IsPreconnected K) (hinf : infty ∈ K) {n : ℕ} (hx : xpt n ∈ K) :
    {i | wit (n, i) ∈ K}.Infinite := by
  intro hfin
  obtain ⟨b, hb⟩ := hfin.bddAbove
  set i₀ := b + 1
  have hi₀ : ∀ i, i₀ ≤ i → wit (n, i) ∉ K := fun i hi hiK => by
    have := hb hiK
    omega
  set ε := witT i₀
  let R : Set (GSpace 𝒟) := rowMap n '' {t | (t : ℝ) < ε}
  let Rbar : Set (GSpace 𝒟) := rowMap n '' {t | (t : ℝ) ≤ ε}
  have hRbar : IsClosed Rbar :=
    isClosedMap_rowMap h𝒟 n _ (isClosed_le continuous_subtype_val continuous_const)
  have hRsub : R ⊆ Rbar := image_mono fun t (ht : (t : ℝ) < ε) => show (t : ℝ) ≤ ε from le_of_lt ht
  -- no point of `Φ_D` in `K` lies in `R`
  have hphi : ∀ (D : 𝒟) (f : Fan (D : Set (ℕ × ℕ))), phiMap D f ∈ K → phiMap D f ∉ R := by
    rintro D f hfK ⟨t, ht, he⟩
    obtain ⟨m, rfl, hm1, rfl⟩ := phiMap_eq_row he.symm
    rw [phiMap_spine, spokeMap_one] at hfK
    have hlt : i₀ < (m : ℕ × ℕ).2 := witT_lt_iff.1 ht
    have : wit (n, (m : ℕ × ℕ).2) ∉ K := hi₀ _ hlt.le
    rw [← hm1] at this
    exact this hfK
  have hcl : IsClosed (K ∩ Rᶜ) := by
    refine isClosed_iff.2 ⟨fun n' => ?_, ?_, fun D => ?_, fun S => ?_⟩
    · rw [preimage_inter, preimage_compl]
      refine ((isClosed_iff.1 hK).1 n').inter (IsOpen.isClosed_compl ?_)
      by_cases h : n' = n
      · subst h
        rw [(rowMap_injective n').preimage_image]
        exact isOpen_lt continuous_subtype_val continuous_const
      · convert isOpen_empty
        ext t
        simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and,
          R, rowMap]
        intro t' _ e
        simp only [row.injEq] at e
        exact h e.1.symm
    · rw [preimage_inter, preimage_compl]
      refine ((isClosed_iff.1 hK).2.1).inter (IsOpen.isClosed_compl ?_)
      have e : sigMap ⁻¹' R = {(n : OnePoint ℕ)} := by
        ext c
        induction c using OnePoint.rec with
        | infty =>
          simp only [mem_preimage, sigMap_infty, mem_singleton_iff, R, mem_image]
          constructor
          · rintro ⟨t, -, h⟩
            simp [rowMap] at h
          · intro h
            exact absurd h.symm (OnePoint.coe_ne_infty n)
        | coe k =>
          simp only [mem_preimage, sigMap_coe, mem_singleton_iff, R, mem_image, rowMap, xpt,
            row.injEq, OnePoint.coe_eq_coe]
          constructor
          · rintro ⟨t, -, h, -⟩
            exact h.symm
          · rintro rfl
            refine ⟨0, ?_, rfl, rfl⟩
            show ((0 : I) : ℝ) < ε
            simpa using lt_of_le_of_ne (witT i₀).2.1 (witT_ne_zero i₀).symm
      rw [e, ← image_singleton]
      exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete _)
    · have e : phiMap D ⁻¹' (K ∩ Rᶜ) = phiMap D ⁻¹' K := by
        ext f
        exact ⟨fun h => h.1, fun h => ⟨h, hphi D f h⟩⟩
      rw [e]
      exact (isClosed_iff.1 hK).2.2.1 D
    · have e : lamMap S.1 ⁻¹' (K ∩ Rᶜ) = lamMap S.1 ⁻¹' K := by
        ext f
        refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
        rintro ⟨t, -, he⟩
        have hmem := range_lamMap_subset S.1 ⟨f, rfl⟩
        rw [← he] at hmem
        rcases hmem with h' | ⟨D, -, h'⟩ | ⟨D, -, s, h'⟩ <;> simp [rowMap] at h'
      rw [e]
      exact (isClosed_iff.1 hK).2.2.2 S
  obtain ⟨g, hgK, hgR, -, hgnR⟩ := isPreconnected_closed_iff.1 hconn Rbar (K ∩ Rᶜ) hRbar hcl
    (fun g hg => by
      by_cases h : g ∈ R
      · exact Or.inl (hRsub h)
      · exact Or.inr ⟨hg, h⟩)
    ⟨xpt n, hx, 0, (witT i₀).2.1, rfl⟩
    ⟨infty, hinf, hinf, by rintro ⟨t, -, h⟩; simp [rowMap] at h⟩
  obtain ⟨t, ht, rfl⟩ := hgR
  have hte : t = ε := by
    refine Subtype.ext (le_antisymm ht (not_lt.1 fun h => hgnR ⟨t, h, rfl⟩))
  rw [hte] at hgK
  exact hi₀ i₀ le_rfl hgK

/-! ### Proposition 4.9 for metric continua -/

/-- The core of Proposition 4.9: a closed preconnected `K ∋ ∞` for which the set of `D` meeting
`K` in infinitely many witnesses is countable contains only finitely many `x_n`. -/
theorem finite_xpt_core (h𝒟 : IsMADFamily 𝒟) {K : Set (GSpace 𝒟)} (hKc : IsClosed K)
    (hconn : IsPreconnected K) (hinf : infty ∈ K)
    (hcount : {D : 𝒟 | ((D : Set (ℕ × ℕ)) ∩ {m | wit m ∈ K}).Infinite}.Countable) :
    {n | xpt n ∈ K}.Finite := by
  set W : Set (ℕ × ℕ) := {m | wit m ∈ K}
  set 𝒟K : Set 𝒟 := {D | ((D : Set (ℕ × ℕ)) ∩ W).Infinite}
  obtain ⟨e, he⟩ := countable_iff_exists_subset_range.1 (hcount.image fun D : 𝒟 => (D : Set (ℕ × ℕ)))
  -- the finite families `𝒜 k = {e j : j < k}` exhaust `𝒟K`
  let 𝒜 : ℕ → Set 𝒟 := fun k => {D | ∃ j < k, (D : Set (ℕ × ℕ)) = e j}
  have h𝒜 : ∀ k, (𝒜 k).Finite := fun k => by
    refine (((finite_Iio k).image e).preimage Subtype.val_injective.injOn).subset ?_
    rintro D ⟨j, hj, hD⟩
    exact ⟨j, hj, hD.symm⟩
  by_contra hinfin
  let ν := Set.Infinite.natEmbedding _ hinfin
  have hcut : ∀ k, ∃ i, wit ((ν k : ℕ), i) ∈ K ∧
      ((ν k : ℕ), i) ∉ ⋃ D ∈ 𝒜 k, (D : Set (ℕ × ℕ)) := by
    intro k
    obtain ⟨i, hiK, hiB⟩ := ((infinite_wit_of_isPreconnected h𝒟 hKc hconn hinf
      (ν k).2).diff (finite_section_biUnion h𝒟 (h𝒜 k) (ν k))).nonempty
    exact ⟨i, hiK, hiB⟩
  choose ι hιK hιB using hcut
  let w : ℕ → ℕ × ℕ := fun k => ((ν k : ℕ), ι k)
  have hw : Injective w := fun k k' h => ν.injective (Subtype.ext (Prod.mk.inj h).1)
  have hY : IsC (range w) := by
    refine ⟨infinite_range_of_injective hw, fun n => Set.Subsingleton.finite ?_⟩
    rintro i ⟨k, hk⟩ i' ⟨k', hk'⟩
    obtain ⟨h1, rfl⟩ := Prod.mk.inj hk
    obtain ⟨h1', rfl⟩ := Prod.mk.inj hk'
    have : k = k' := ν.injective (Subtype.ext (h1.trans h1'.symm))
    rw [this]
  obtain ⟨D, hD𝒟, hDY⟩ := h𝒟.maximal _ hY
  have hDK : (⟨D, hD𝒟⟩ : 𝒟) ∈ 𝒟K := hDY.mono fun m hm' => by
    obtain ⟨k, hk⟩ := hm'.2
    refine ⟨hm'.1, ?_⟩
    rw [← hk]
    exact hιK k
  obtain ⟨j, hj⟩ := he ⟨_, hDK, rfl⟩
  refine hDY (((finite_Iic j).image w).subset ?_)
  rintro m ⟨hmD, k, rfl⟩
  refine ⟨k, ?_, rfl⟩
  by_contra hk
  exact hιB k (mem_biUnion (x := ⟨D, hD𝒟⟩) ⟨j, not_le.1 hk, hj.symm⟩ hmD)

/-- **Proposition 4.9**: let `K ⊆ G` be closed and connected with `∞ ∈ K`, and suppose every
discrete subspace of `K` is countable (`K` has countable spread). Then `x_n ∈ K` for only finitely
many `n`. "Discrete subspace" is rendered literally: every point of `A` has an open neighbourhood
meeting `A` only in that point. -/
theorem finite_xpt_of_spread (h𝒟 : IsMADFamily 𝒟) {K : Set (GSpace 𝒟)} (hKc : IsClosed K)
    (hconn : IsPreconnected K) (hinf : infty ∈ K)
    (hspread : ∀ A ⊆ K, (∀ a ∈ A, ∃ U : Set (GSpace 𝒟), IsOpen U ∧ U ∩ A = {a}) → A.Countable) :
    {n | xpt n ∈ K}.Finite := by
  refine finite_xpt_core h𝒟 hKc hconn hinf ?_
  set 𝒟K := {D : 𝒟 | ((D : Set (ℕ × ℕ)) ∩ {m | wit m ∈ K}).Infinite}
  have hA : (pnt '' 𝒟K : Set (GSpace 𝒟)).Countable := by
    refine hspread _ (by rintro _ ⟨D, hD, rfl⟩; exact pnt_mem_of_infinite hKc hD) ?_
    rintro _ ⟨D, hD, rfl⟩
    obtain ⟨U, hU, hDU, hUD⟩ := exists_isolating_nhd D
    refine ⟨U, hU, ?_⟩
    ext c
    constructor
    · rintro ⟨hcU, D', -, rfl⟩
      rw [hUD D' hcU]; rfl
    · rintro rfl
      exact ⟨hDU, D, hD, rfl⟩
  exact MapsTo.countable_of_injOn (fun D hD => mem_image_of_mem pnt hD)
    (fun D _ D' _ h => pnt.inj h) hA

/-- **Proposition 4.9** ("in particular"): no metric continuum in `G` contains `∞` and infinitely
many of the points `x_n`. -/
theorem finite_xpt_of_isMetricContinuum (h𝒟 : IsMADFamily 𝒟) {K : Set (GSpace 𝒟)}
    (hK : IsMetricContinuum K) (hinf : infty ∈ K) : {n | xpt n ∈ K}.Finite := by
  have hX := isMosaicSpace h𝒟
  haveI := hX.sequentialSpace
  have hKc : IsClosed K := hK.isCompactMetrizable.isClosed hX.uniqueSeqLimits
  refine finite_xpt_core h𝒟 hKc hK.2.1.isPreconnected hinf ?_
  set W : Set (ℕ × ℕ) := {m | wit m ∈ K}
  set 𝒟K : Set 𝒟 := {D | ((D : Set (ℕ × ℕ)) ∩ W).Infinite}
  show 𝒟K.Countable
  have hcount : 𝒟K.Countable := by
    haveI : MetrizableSpace K := hK.2.2
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
    letI := metrizableSpaceMetric K
    obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis K
    have hex : ∀ D (hD : D ∈ 𝒟K), ∃ b ∈ B, (⟨pnt D, pnt_mem_of_infinite hKc hD⟩ : K) ∈ b ∧
        ∀ D' (h : pnt D' ∈ K), (⟨pnt D', h⟩ : K) ∈ b → D' = D := by
      intro D hD
      obtain ⟨U, hU, hDU, hUD⟩ := exists_isolating_nhd D
      obtain ⟨b, hbB, hDb, hbU⟩ := hB.exists_subset_of_mem_open (a := ⟨pnt D, _⟩)
        (u := (Subtype.val ⁻¹' U : Set K)) hDU (hU.preimage continuous_subtype_val)
      exact ⟨b, hbB, hDb, fun D' h hb => hUD D' (hbU hb)⟩
    choose! β hβB hβmem hβinj using hex
    refine MapsTo.countable_of_injOn (f := β) (t := B) (fun D hD => hβB D hD) ?_ hBc
    intro D hD D' hD' e
    exact (hβinj D hD D' (pnt_mem_of_infinite hKc hD') (e ▸ hβmem D' hD')).symm
  exact hcount

/-! ### Theorem 4.11(3),(4) -/

/-- **Theorem 4.11(4)**: `G` is not an m-continuum space. -/
theorem not_isMContinuumSpace (h𝒟 : IsMADFamily 𝒟) : ¬ IsMContinuumSpace (GSpace 𝒟) := by
  intro h
  obtain ⟨K, hK, hinf, φ, hφ, hφK⟩ :=
    (isMContinuumSpace_iff_captures (isMosaicSpace h𝒟)).1 h xpt infty tendsto_xpt
  refine infinite_range_of_injective hφ.injective
    ((finite_xpt_of_isMetricContinuum h𝒟 hK hinf).subset ?_)
  rintro _ ⟨k, rfl⟩
  exact hφK k

/-- **Theorem 4.11(4)**: `G` is not a quasi-curve space. -/
theorem not_isQuasiCurveSpace (h𝒟 : IsMADFamily 𝒟) : ¬ IsQuasiCurveSpace (GSpace 𝒟) :=
  fun h => not_isMContinuumSpace h𝒟 h.isMContinuumSpace

/-- **Theorem 4.11(4)**: no path in `G` passes through infinitely many of the points `x_n`. -/
theorem finite_xpt_of_path (h𝒟 : IsMADFamily 𝒟) {a b : GSpace 𝒟} (γ : Path a b) :
    {n | xpt n ∈ range γ}.Finite := by
  have hX := isMosaicSpace h𝒟
  haveI := hX.sequentialSpace
  have hK := isMetricContinuum_range_path hX.uniqueSeqLimits γ
  have hKc : IsClosed (range γ) := hK.isCompactMetrizable.isClosed hX.uniqueSeqLimits
  by_contra hinfin
  let ν := Set.Infinite.natEmbedding _ hinfin
  have hmono : Tendsto (fun k => (ν k : ℕ)) atTop atTop :=
    (Injective.nat_tendsto_atTop (fun k k' h => ν.injective (Subtype.ext h)))
  have hinf : infty ∈ range γ :=
    hKc.mem_of_tendsto (tendsto_xpt.comp hmono) (Eventually.of_forall fun k => (ν k).2)
  exact hinfin (finite_xpt_of_isMetricContinuum h𝒟 hK hinf)

end GSpace

end MosaicSpaces
