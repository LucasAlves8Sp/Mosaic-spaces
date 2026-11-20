module

public import MosaicSpaces.Cone
public import MosaicSpaces.Local

/-!
# Theorem 6.3(4): open subspaces of the cone

`Cone.allOpenMContinuum_iff`: for a nonempty mosaic space `Y`, every nonempty open subspace of
`𝖼 Y` is an m-continuum space iff every nonempty open subspace of `Y` is.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- An open subspace of a mosaic space is an m-continuum space if every sequence converging in it
is captured, together with its limit, by a metric continuum of the ambient space contained in
it. -/
theorem isMContinuumSpace_of_captures_open (hX : IsMosaicSpace X) {O : Set X} (hO : IsOpen O)
    (h : ∀ (u : ℕ → X) (z : X), z ∈ O → Tendsto u atTop (𝓝 z) →
      ∃ L ⊆ O, IsMetricContinuum L ∧ z ∈ L ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ L) :
    IsMContinuumSpace O := by
  rw [isMContinuumSpace_iff_captures (hX.of_isOpen hO)]
  intro v z hv
  obtain ⟨L, hLO, hL, hzL, φ, hφ, hφL⟩ :=
    h (fun n => (v n : X)) z z.2 (tendsto_subtype_rng.1 hv)
  exact ⟨(↑) ⁻¹' L, hL.preimage_val hLO, mem_preimage.2 hzL, φ, hφ, fun n => mem_preimage.2 (hφL n)⟩

/-- The condition (H) of Theorem 7.4 for a space: every nonempty open subspace is an m-continuum
space. -/
def AllOpenMCont (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → IsMContinuumSpace U

namespace Cone

variable {Y : Type u} [TopologicalSpace Y]

/-- A continuous left inverse of `κ` on the complement of the vertex, extended arbitrarily. -/
noncomputable def proj (y₀ : Y) : Cone Y → Y := by
  classical
  exact fun c => if h : c ∈ range (punctured : Y × Ilt → Cone Y) then
    ((isOpenEmbedding_punctured (Y := Y)).isEmbedding.toHomeomorph.symm ⟨c, h⟩).1 else y₀

theorem proj_punctured (y₀ : Y) (p : Y × Ilt) : proj y₀ (punctured p) = p.1 := by
  classical
  have h : punctured p ∈ range (punctured : Y × Ilt → Cone Y) := mem_range_self p
  simp only [proj, dif_pos h]
  have : (⟨punctured p, h⟩ : range (punctured : Y × Ilt → Cone Y)) =
      (isOpenEmbedding_punctured (Y := Y)).isEmbedding.toHomeomorph p := rfl
  rw [this, Homeomorph.symm_apply_apply]

theorem continuousOn_proj (y₀ : Y) :
    ContinuousOn (proj y₀) (range (punctured : Y × Ilt → Cone Y)) := by
  classical
  refine continuousOn_iff_continuous_restrict.2 ?_
  convert continuous_fst.comp
    (isOpenEmbedding_punctured (Y := Y)).isEmbedding.toHomeomorph.symm.continuous using 1
  funext c
  show proj y₀ c = _
  simp only [proj, dif_pos c.2, Function.comp_apply]

theorem eq_mk_proj (y₀ : Y) {p : Y × Ilt} : punctured p = mk (proj y₀ (punctured p), p.2.1) := by
  rw [proj_punctured]; rfl

/-- **Theorem 6.3(4)**, first direction. -/
theorem allOpenMCont_of_cone (hY : IsMosaicSpace Y) (h : AllOpenMCont (Cone Y)) :
    AllOpenMCont Y := by
  intro V hV ⟨y₀, hy₀⟩
  haveI := hY.sequentialSpace
  have hU := hY.uniqueSeqLimits
  have hcY := isMosaicSpace hY
  have h0 : (0 : I) ∈ Ilt := by show ((0 : I) : ℝ) < 1; simp
  let O : Set (Cone Y) := punctured '' (V ×ˢ univ)
  have hO : IsOpen O := isOpenEmbedding_punctured.isOpenMap _ (hV.prod isOpen_univ)
  have hOne : O.Nonempty := ⟨_, ⟨(y₀, ⟨0, h0⟩), ⟨hy₀, trivial⟩, rfl⟩⟩
  have hm := h O hO hOne
  have hOr : O ⊆ range (punctured : Y × Ilt → Cone Y) := image_subset_range _ _
  refine isMContinuumSpace_of_captures_open hY hV fun u y hyV hu => ?_
  let z : Y → Cone Y := fun y => punctured (y, ⟨0, h0⟩)
  have hz : Continuous z :=
    isOpenEmbedding_punctured.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨L, hLO, hL, hyL, φ, hφ, hφL⟩ :=
    captures_in_open hcY hO hm (u := fun n => z (u n)) (z := z y) ⟨_, ⟨hyV, trivial⟩, rfl⟩
      ((hz.tendsto y).comp hu)
  -- project `L` back to `Y`
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL.1
  haveI := hL.2.2
  have hπ : Continuous fun c : L => proj y₀ (c : Cone Y) :=
    (continuousOn_proj y₀).comp_continuous continuous_subtype_val fun c => hOr (hLO c.2)
  have himg := range_closed_compact_metrizable hU hπ
  have hconn : IsConnected (range fun c : L => proj y₀ (c : Cone Y)) := by
    haveI : ConnectedSpace L := isConnected_iff_connectedSpace.1 hL.2.1
    exact isConnected_range hπ
  refine ⟨range fun c : L => proj y₀ (c : Cone Y), ?_, ⟨himg.2.1, hconn, himg.2.2⟩,
    ⟨⟨z y, hyL⟩, proj_punctured _ _⟩, φ, hφ, fun n => ⟨⟨z (u (φ n)), hφL n⟩, proj_punctured _ _⟩⟩
  rintro _ ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨⟨y', t'⟩, ⟨hy'V, -⟩, rfl⟩ := hLO hc
  simp only [proj_punctured]
  exact hy'V

/-- **Theorem 6.3(4)**, second direction. -/
theorem allOpenMCont_cone (hY : IsMosaicSpace Y) [Nonempty Y] (h : AllOpenMCont Y) :
    AllOpenMCont (Cone Y) := by
  intro O hO ⟨c₀, hc₀⟩
  haveI := hY.sequentialSpace
  have hU := hY.uniqueSeqLimits
  have hcY := isMosaicSpace hY
  haveI := hcY.sequentialSpace
  have hcU := hcY.uniqueSeqLimits
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  refine isMContinuumSpace_of_captures_open hcY hO fun u z hzO hu => ?_
  by_cases hzv : z = vertex
  · -- the vertex
    subst hzv
    by_cases hfreq : ∃ᶠ n in atTop, u n = vertex
    · obtain ⟨φ, hφ, hφv⟩ := extraction_of_frequently_atTop hfreq
      exact ⟨{vertex}, singleton_subset_iff.2 hzO, isMetricContinuum_singleton hcU _, rfl, φ, hφ,
        fun n => hφv n⟩
    obtain ⟨𝒦, h𝒦, hcm⟩ := hY
    obtain ⟨P, hP, hvP, ψ, hψ, hψP⟩ :=
      (isMosaicFamily_pieces h𝒦).exists_piece_subseq
        (fun P hP => by
          obtain ⟨K, ⟨hK, hKne⟩, rfl⟩ := hP
          exact (isMetricContinuum_piece (h𝒦.isClosed K hK) (hcm K hK) hKne).isCompactMetrizable)
        hu
    obtain ⟨K, ⟨hK, hKne⟩, rfl⟩ := hP
    have hKcl := h𝒦.isClosed K hK
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 (hcm K hK).1
    -- a tube `K × (1-η, 1]` inside `O`
    let F : K × I → Cone Y := fun p => mk ((p.1 : Y), p.2)
    have hF : Continuous F := continuous_mk.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hC : IsClosed (Prod.snd '' (F ⁻¹' Oᶜ)) :=
      isClosedMap_snd_of_compactSpace _ (hO.isClosed_compl.preimage hF)
    have h1 : (1 : I) ∉ Prod.snd '' (F ⁻¹' Oᶜ) := by
      rintro ⟨⟨k, s⟩, hks, rfl⟩
      exact hks (by simpa [F, mk_one_eq_vertex] using hzO)
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl 1 h1
    have htube : ∀ k ∈ K, ∀ s : I, 1 - η < (s : ℝ) → mk (k, s) ∈ O := by
      intro k hk s hs
      by_contra hns
      refine hball ?_ ⟨(⟨k, hk⟩, s), hns, rfl⟩
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, Icc.coe_one, abs_sub_lt_iff]
      constructor <;> linarith [s.2.2]
    -- the heights tend to `1`
    have hht : Tendsto (fun n => (height (u n) : ℝ)) atTop (𝓝 1) := by
      have := (continuous_subtype_val.comp continuous_height).tendsto (vertex : Cone Y)
      simpa [Function.comp_def, vertex, height_mk] using this.comp hu
    have hev : ∀ᶠ n in atTop, 1 - η / 2 < (height (u (ψ n)) : ℝ) :=
      (hht.comp hψ.tendsto_atTop).eventually (lt_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    let J : Set I := {s | 1 - η / 2 ≤ (s : ℝ)}
    let T : Set (Cone Y) := mk '' (K ×ˢ J)
    have hTP : T ⊆ piece K := image_mono (prod_mono subset_rfl (subset_univ _))
    have hT : IsMetricContinuum T := by
      refine ⟨((hcm K hK).1.prod (isClosed_le continuous_const
        continuous_subtype_val).isCompact).image continuous_mk, ?_, ?_⟩
      · obtain ⟨k₀, hk₀⟩ := hKne
        refine ⟨⟨mk (k₀, 1), ⟨(k₀, 1), ⟨hk₀, by simp [J]; linarith⟩, rfl⟩⟩, ?_⟩
        refine isPreconnected_of_forall (mk (k₀, 1)) fun c hc => ?_
        obtain ⟨⟨k, s⟩, ⟨hk, hs⟩, rfl⟩ := hc
        refine ⟨mk '' ({k} ×ˢ J), image_mono (prod_mono (singleton_subset_iff.2 hk) subset_rfl),
          ⟨(k, 1), ⟨rfl, by simp [J]; linarith⟩, mk_one _ _⟩, ⟨(k, s), ⟨rfl, hs⟩, rfl⟩, ?_⟩
        refine (isPreconnected_singleton.prod ?_).image _ continuous_mk.continuousOn
        have hJeq : J = Ici (⟨max (1 - η / 2) 0, le_max_right _ _,
            max_le (by linarith) zero_le_one⟩ : I) := by
          ext s
          simp only [J, mem_setOf_eq, mem_Ici]
          constructor
          · intro hs; exact show max (1 - η / 2) 0 ≤ (s : ℝ) from max_le hs s.2.1
          · intro hs
            have hs' : max (1 - η / 2) 0 ≤ (s : ℝ) := hs
            exact le_trans (le_max_left _ _) hs'
        rw [hJeq]; exact isPreconnected_Ici
      · have hPm := (isMetricContinuum_piece hKcl (hcm K hK) hKne).2.2
        exact (IsEmbedding.inclusion hTP).metrizableSpace
    obtain ⟨k₀, hk₀⟩ := hKne
    refine ⟨T, ?_, hT, ⟨(k₀, 1), ?_, ?_⟩,
      fun n => ψ (n + N), hψ.comp (strictMono_id.add_const N), fun n => ?_⟩
    · rintro _ ⟨⟨k, s⟩, ⟨hk, hs⟩, rfl⟩
      exact htube k hk s (by simp only [J, mem_setOf_eq] at hs; linarith)
    · exact ⟨hk₀, by simp [J]; linarith⟩
    · exact mk_one_eq_vertex _
    · obtain ⟨⟨k, s⟩, ⟨hk, -⟩, he⟩ := hψP (n + N)
      refine ⟨(k, s), ⟨hk, ?_⟩, he⟩
      have := hN (n + N) (Nat.le_add_left N n)
      rw [← he, height_mk] at this
      exact this.le
  · -- a point of `Y × [0,1)`
    have hzr : z ∈ range (punctured : Y × Ilt → Cone Y) := by
      rw [range_punctured]; exact hzv
    obtain ⟨⟨y, t⟩, rfl⟩ := hzr
    have ht1 : (t : ℝ) < 1 := t.2
    obtain ⟨W, hWo, hyt, hWO⟩ : ∃ W : Set (Y × Ilt), IsOpen W ∧ (y, t) ∈ W ∧
        punctured '' W ⊆ O :=
      ⟨punctured ⁻¹' O, hO.preimage isOpenEmbedding_punctured.continuous, hzO,
        image_preimage_subset _ _⟩
    obtain ⟨V, N', hV, hN', hyV, htN', hVN⟩ := isOpen_prod_iff.1 hWo y t hyt
    obtain ⟨δ, hδ, hδN⟩ := Metric.isOpen_iff.1 hN' t htN'
    set δ' := min (δ / 2) ((1 - t) / 2)
    have hδ' : 0 < δ' := lt_min (by linarith) (by linarith)
    -- the compact interval `J ∋ t` inside `[0,1)` and inside `N'`
    let J : Set I := {s | |(s : ℝ) - t| ≤ δ'}
    have hJN : ∀ s ∈ J, ∃ hs : s ∈ Ilt, (⟨s, hs⟩ : Ilt) ∈ N' := by
      intro s hs
      have hs1 : (s : ℝ) < 1 := by
        have := (abs_le.1 (show |(s : ℝ) - t| ≤ δ' from hs)).2
        have := min_le_right (δ / 2) ((1 - (t : ℝ)) / 2)
        linarith
      refine ⟨hs1, hδN ?_⟩
      rw [Metric.mem_ball, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq]
      exact lt_of_le_of_lt hs (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hJc : IsCompact J :=
      (isClosed_le (continuous_abs.comp (continuous_subtype_val.sub continuous_const))
        continuous_const).isCompact
    have hJconn : IsConnected J := by
      refine ⟨⟨t, by simp [J, hδ'.le]⟩, ?_⟩
      have e : J = Icc (⟨max ((t : ℝ) - δ') 0, by
          constructor
          · exact le_max_right _ _
          · exact max_le (by linarith [t.1.2.2]) zero_le_one⟩ : I)
          ⟨min ((t : ℝ) + δ') 1, by
          constructor
          · exact le_min (by linarith [t.1.2.1]) zero_le_one
          · exact min_le_right _ _⟩ := by
        ext s
        simp only [J, mem_setOf_eq, mem_Icc, abs_le]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨show max _ _ ≤ (s : ℝ) from max_le (by linarith) s.2.1,
            show (s : ℝ) ≤ min _ _ from le_min (by linarith) s.2.2⟩
        · rintro ⟨h1, h2⟩
          have h1' : max ((t : ℝ) - δ') 0 ≤ s := h1
          have h2' : (s : ℝ) ≤ min ((t : ℝ) + δ') 1 := h2
          exact ⟨by linarith [le_max_left ((t : ℝ) - δ') 0],
            by linarith [min_le_left ((t : ℝ) + δ') 1]⟩
      rw [e]; exact isPreconnected_Icc
    -- project the sequence to `Y`
    have hπc : ContinuousAt (proj y₀) (punctured (y, t)) :=
      (continuousOn_proj y₀).continuousAt
        (isOpenEmbedding_punctured.isOpen_range.mem_nhds (mem_range_self _))
    have hπu : Tendsto (fun n => proj y₀ (u n)) atTop (𝓝 y) := by
      have := hπc.tendsto.comp hu
      rwa [proj_punctured] at this
    have hVne : V.Nonempty := ⟨y, hyV⟩
    obtain ⟨L, hLV, hL, hyL, φ, hφ, hφL⟩ := captures_in_open hY hV (h V hV hVne) hyV hπu
    -- eventually the sequence lies over `V × (t - δ', t + δ')`
    let B : Set Ilt := {s | |((s : I) : ℝ) - t| < δ'}
    have hB : IsOpen B := isOpen_lt
      (continuous_abs.comp ((continuous_subtype_val.comp continuous_subtype_val).sub
        continuous_const)) continuous_const
    have hev : ∀ᶠ n in atTop, u n ∈ punctured '' (V ×ˢ B) :=
      hu.eventually ((isOpenEmbedding_punctured.isOpenMap _ (hV.prod hB)).mem_nhds
        ⟨(y, t), ⟨hyV, by simp [B, hδ']⟩, rfl⟩)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    let T : Set (Cone Y) := mk '' (L ×ˢ J)
    have hLcl : IsClosed L := hL.isCompactMetrizable.isClosed hU
    have hTP : T ⊆ piece L := image_mono (prod_mono subset_rfl (subset_univ _))
    have hT : IsMetricContinuum T := by
      refine ⟨(hL.1.prod hJc).image continuous_mk, (hL.2.1.prod hJconn).image _
        continuous_mk.continuousOn, ?_⟩
      have := (isMetricContinuum_piece hLcl hL.isCompactMetrizable ⟨y, hyL⟩).2.2
      exact (IsEmbedding.inclusion hTP).metrizableSpace
    refine ⟨T, ?_, hT, ⟨(y, t), ⟨hyL, by simp [J, hδ'.le]⟩, rfl⟩,
      fun n => φ (n + M), hφ.comp (strictMono_id.add_const M), fun n => ?_⟩
    · rintro _ ⟨⟨l, s⟩, ⟨hl, hs⟩, rfl⟩
      obtain ⟨hsI, hsN⟩ := hJN s hs
      exact hWO ⟨(l, ⟨s, hsI⟩), hVN ⟨hLV hl, hsN⟩, rfl⟩
    · have hk : M ≤ φ (n + M) := le_trans (Nat.le_add_left M n) (hφ.id_le _)
      obtain ⟨⟨y', t'⟩, ⟨-, ht'⟩, he⟩ := hM _ hk
      have hy'L : y' ∈ L := by
        have := hφL (n + M)
        rw [← he, proj_punctured] at this
        exact this
      rw [← he]
      exact ⟨(y', t'.1), ⟨hy'L, show |((t' : I) : ℝ) - t| ≤ δ' from le_of_lt ht'⟩, rfl⟩

end Cone

end MosaicSpaces
