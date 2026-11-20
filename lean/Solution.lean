module

public import MosaicSpaces

public section

/-!
# Proved solution

Every theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`; the proofs are in the library `MosaicSpaces`. The definitions used in the
statements are those of the library, which `Challenge.lean` copies verbatim.
-/

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

namespace Paper

variable {X : Type u} [TopologicalSpace X]

theorem prop_2_3_t1 (hX : IsMosaicSpace X) : T1Space X := hX.t1Space

theorem lemma_2_4 [SequentialSpace X] (hX : UniqueSeqLimits X) {C : Type u} [TopologicalSpace C]
    [CompactSpace C] [MetrizableSpace C] {f : C → X} (hf : Continuous f) :
    IsClosed (range f) ∧ IsCompact (range f) ∧ MetrizableSpace (range f) :=
  range_closed_compact_metrizable hX hf

theorem cor_2_6_union [SequentialSpace X] (hX : UniqueSeqLimits X) {K L : Set X}
    (hK : IsMetricContinuum K) (hL : IsMetricContinuum L) (hKL : (K ∩ L).Nonempty) :
    IsMetricContinuum (K ∪ L) :=
  hK.union hX hL hKL

theorem prop_2_7 : IsMosaicSpace X ↔ SequentialSpace X ∧ UniqueSeqLimits X := isMosaicSpace_iff

theorem prop_2_7_t2 [T2Space X] [SequentialSpace X] : IsMosaicSpace X := isMosaicSpace_of_t2

theorem prop_2_7_open (hX : IsMosaicSpace X) {U : Set X} (hU : IsOpen U) : IsMosaicSpace U :=
  hX.of_isOpen hU

theorem lemma_2_8 (hX : IsMosaicSpace X) {𝒦 : Set (Set X)}
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) (hcover : ∀ x : X, ∃ K ∈ 𝒦, x ∈ K) :
    IsMosaicFamily 𝒦 ↔ Captures X (· ∈ 𝒦) :=
  isMosaicFamily_iff_captures hX hcm hcover

theorem cor_2_9_1 (hX : IsMosaicSpace X) :
    IsMContinuumSpace X ↔ Captures X IsMetricContinuum :=
  isMContinuumSpace_iff_captures hX

theorem cor_2_9_2 (hX : IsMosaicSpace X) :
    [IsQuasiCurveSpace X, IsCurveSpace X, Captures X IsPeanoContinuum].TFAE :=
  isQuasiCurveSpace_tfae hX

theorem cor_2_9_2_path (hX : IsMosaicSpace X) (h : Captures X IsPathImage) : IsCurveSpace X :=
  isCurveSpace_of_capturesPath hX h

theorem cor_2_9_qc (h : IsQuasiCurveSpace X) : IsMContinuumSpace X := h.isMContinuumSpace

theorem display_2_1 (hX : IsMosaicSpace X) :
    (LocallyArcwiseConnected X → LocallyPathConnectedSpace X) ∧
    (LocallyPathConnectedSpace X → LocallyMStronglyConnected X) ∧
    (LocallyMStronglyConnected X → LocallyConnectedSpace X) :=
  ⟨fun h => locallyPathConnectedOpen_iff.1 h.locallyPathConnectedOpen,
    fun h => (locallyPathConnectedOpen_iff.2 h).locallyMStronglyConnected hX,
    fun h => h.locallyConnectedSpace⟩

theorem arc_theorem [T2Space X] {x y : X} (γ : Path x y) (hxy : x ≠ y) :
    ∃ f : unitInterval → X, IsEmbedding f ∧ f 0 = x ∧ f 1 = y ∧ range f ⊆ range γ :=
  Arc.exists_arc γ hxy

theorem cor_2_6_2_arc [SequentialSpace X] (hX : UniqueSeqLimits X) {s : Set X} {x y : X}
    (h : JoinedIn s x y) (hxy : x ≠ y) : IsArcBetween s x y :=
  isArcBetween_of_joinedIn hX h hxy

theorem display_2_1_iff (hX : IsMosaicSpace X) :
    LocallyArcwiseConnected X ↔ LocallyPathConnectedSpace X :=
  hX.locallyArcwiseConnected_iff

theorem prop_2_12 (hX : IsMosaicSpace X)
    (h : ∀ U : Set X, IsOpen U → U.Nonempty → IsMContinuumSpace U) :
    LocallyMStronglyConnected X :=
  locallyMStronglyConnected_of_forall_isOpen hX h

theorem prop_2_13 (h : IsQuasiCurveSpace X) {U : Set X} (hU : IsOpen U) : IsMContinuumSpace U :=
  h.isMContinuumSpace_of_isOpen hU

theorem lemma_2_14 {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    (hK : ∀ K ∈ 𝒦, LocallyPathConnectedSpace K ∨
      ∀ (O : Set X), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → X, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z) :
    (∀ O : Set X, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected X :=
  h𝒦.lemma_2_14 hcm hK

theorem exists_madFamily : ∃ 𝒟 : Set (Set (ℕ × ℕ)), IsMADFamily 𝒟 := exists_isMADFamily

theorem theorem_4_11 :
    ∃ (G : Type) (_ : TopologicalSpace G) (x : G) (u : ℕ → G) (W : Set G) (ι : Type) (p : ι → G),
      IsMosaicSpace G ∧ T35Space G ∧ LocallyPathConnectedSpace G ∧ LocallyArcwiseConnected G ∧
      (∀ O : Set G, IsOpen O → ∀ y ∈ O,
        IsOpen (pathComponentIn O y) ∧ ArcwiseConnected (pathComponentIn O y)) ∧
      LocallyMStronglyConnected G ∧
      Tendsto u atTop (𝓝 x) ∧
      (∀ K : Set G, IsMetricContinuum K → x ∈ K → {n | u n ∈ K}.Finite) ∧
      (∀ (a b : G) (γ : Path a b), {n | u n ∈ range γ}.Finite) ∧
      ¬ IsMContinuumSpace G ∧ ¬ IsQuasiCurveSpace G ∧ ¬ (𝓝 x).IsCountablyGenerated ∧
      Function.Injective p ∧ (∀ i, ∃ U : Set G, IsOpen U ∧ p i ∈ U ∧ ∀ j, p j ∈ U → j = i) ∧
      (∀ K : Set G, IsClosed K → IsPreconnected K → x ∈ K →
        (∀ A ⊆ K, (∀ a ∈ A, ∃ U : Set G, IsOpen U ∧ U ∩ A = {a}) → A.Countable) →
        {n | u n ∈ K}.Finite) ∧
      (∃ K : Set G, IsClosed K ∧ IsConnected K ∧ SeparableSpace K ∧ x ∈ K ∧
        {n | u n ∈ K}.Infinite ∧ ¬ {i | p i ∈ K}.Countable) ∧
      (∀ n, u n ∈ closure W) ∧ x ∈ closure W ∧
      (∀ v : ℕ → G, (∀ n, v n ∈ W) → ¬ Tendsto v atTop (𝓝 x)) ∧ ¬ FrechetUrysohnSpace G := by
  obtain ⟨h1, -, -, -, h5, h6, -, h8, h9, h10, h11, h12⟩ := G_properties
  exact ⟨G, inferInstance, GSpace.infty, GSpace.xpt, range GSpace.wit, madFamily, GSpace.pnt,
    h1, G_t35, h5, G_arcwise.2, G_arcwise.1, h6, h8, h9, h12, h10, h11,
    G_not_isCountablyGenerated_nhds_infty, fun D D' h => GSpace.pnt.inj h,
    GSpace.exists_isolating_nhd, G_spread_frechet.1, G_remark_4_10,
    GSpace.xpt_mem_closure_wit, G_spread_frechet.2.1, G_spread_frechet.2.2.1,
    G_spread_frechet.2.2.2⟩

theorem answer_Q3 :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMosaicSpace X ∧ T35Space X ∧
      LocallyArcwiseConnected X ∧
      (∀ O : Set X, IsOpen O → ∀ x ∈ O,
        IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
      ¬ IsQuasiCurveSpace X ∧ ¬ IsMContinuumSpace X ∧ ¬ IsPathDetermined X :=
  ⟨G, inferInstance, G_properties.1, G_t35, G_arcwise.2, G_arcwise.1,
    G_properties.2.2.2.2.2.2.2.2.2.2.1, G_properties.2.2.2.2.2.2.2.2.2.1, G_not_isPathDetermined⟩

theorem lemma_6_1 {A B L : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace L] [LocallyCompactSpace L] {q : A → B} (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map q (id : L → L)) :=
  isQuotientMap_prodMap_id hq

theorem theorem_6_3_1 {Y : Type u} [TopologicalSpace Y] (hY : IsMosaicSpace Y) :
    IsMContinuumSpace (Cone Y) ∧ (Nonempty Y → ContractibleSpace (Cone Y)) :=
  ⟨Cone.isMContinuumSpace hY, fun _ => Cone.contractibleSpace⟩

theorem theorem_6_3_2 {Y : Type u} [TopologicalSpace Y] [LocallyPathConnectedSpace Y]
    (hY : IsMosaicSpace Y) :
    LocallyPathConnectedSpace (Cone Y) ∧ LocallyArcwiseConnected (Cone Y) ∧
      LocallyMStronglyConnected (Cone Y) :=
  ⟨Cone.locallyPathConnectedSpace,
    (Cone.isMosaicSpace hY).locallyArcwiseConnected_iff.2 Cone.locallyPathConnectedSpace,
    Cone.locallyMStronglyConnected hY⟩

theorem theorem_6_3_3 {Y : Type u} [TopologicalSpace Y] [Nonempty Y] (hY : IsMosaicSpace Y)
    (hnot : ¬ IsMContinuumSpace Y) :
    IsOpen ({Cone.vertex}ᶜ : Set (Cone Y)) ∧ ¬ IsMContinuumSpace ({Cone.vertex}ᶜ : Set (Cone Y)) :=
  ⟨Cone.isOpen_compl_vertex, Cone.not_isMContinuumSpace_punctured hY hnot⟩

theorem theorem_6_3_5 {Y : Type u} [TopologicalSpace Y]
    (hsep : ∀ y y' : Y, y ≠ y' → ∃ f : Y → ℝ, Continuous f ∧ f y ≠ f y') :
    T2Space (Cone Y) :=
  Cone.t2Space hsep

theorem answer_Q2 :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ T2Space X ∧
      ContractibleSpace X ∧ LocallyArcwiseConnected X ∧ LocallyMStronglyConnected X ∧
      (∃ U : Set X, IsOpen U ∧ ¬ IsMContinuumSpace U) ∧ ¬ IsQuasiCurveSpace X :=
  MosaicSpaces.answer_Q2_full

theorem answer_Q1b :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ T2Space X ∧
      LocallyArcwiseConnected X ∧ LocallyMStronglyConnected X ∧ ¬ IsQuasiCurveSpace X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_t2, cone_G_locallyArcwiseConnected,
    cone_G_properties.2.2.2.1, cone_G_properties.2.2.2.2.2.2.2⟩

theorem answer_Q1a :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ T2Space X ∧
      LocallyConnectedSpace X ∧ ¬ IsQuasiCurveSpace X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_t2, cone_G_properties.2.2.2.2.1,
    cone_G_properties.2.2.2.2.2.2.2⟩

theorem prop_7_1 [FirstCountableTopology X] (hX : IsMosaicSpace X)
    (hloc : LocallyMStronglyConnected X) {U : Set X} (hU : IsOpen U) : IsMContinuumSpace U :=
  isMContinuumSpace_of_isOpen_of_firstCountable hX hloc hU

theorem prop_7_2_path [FirstCountableTopology X] (hX : IsMosaicSpace X)
    [LocallyPathConnectedSpace X] : IsCurveSpace X :=
  isCurveSpace_of_firstCountable hX (locallyPathConnectedOpen_iff.2 inferInstance)

theorem prop_7_2 [FirstCountableTopology X] (hX : IsMosaicSpace X)
    (hloc : LocallyArcwiseConnected X) : IsQuasiCurveSpace X :=
  isQuasiCurveSpace_of_firstCountable hX hloc

theorem theorem_7_4_impl (hX : IsMosaicSpace X) :
    (IsQuasiCurveSpace X → AllOpenMContinuum X) ∧
    (AllOpenMContinuum X → LocallyMStronglyConnected X) ∧
    (LocallyMStronglyConnected X → LocallyConnectedSpace X) :=
  chain_implications hX

theorem theorem_7_4_strict_H_LmS :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyMStronglyConnected X ∧
      ¬ AllOpenMContinuum X :=
  chain_strict_H_LmS

theorem theorem_7_4_firstCountable [FirstCountableTopology X] (hX : IsMosaicSpace X) :
    AllOpenMContinuum X ↔ LocallyMStronglyConnected X :=
  firstCountable_H_iff_LmS hX

theorem def_2_1_mosaic : IsMosaicSpace X ↔ IsAbstractMosaicSpaceWith (fun _ _ => True) X :=
  isMosaicSpace_iff_abstract

theorem def_2_1_mContinuum :
    IsMContinuumSpace X ↔ IsAbstractMosaicSpaceWith (fun Z t => @ConnectedSpace Z t) X :=
  isMContinuumSpace_iff_abstract

theorem def_2_1_quasiCurve :
    IsQuasiCurveSpace X ↔ IsAbstractMosaicSpaceWith (fun Z t => @LocallyConnectedSpace Z t) X :=
  isQuasiCurveSpace_iff_abstract

theorem def_2_1_curve :
    IsCurveSpace X ↔ IsAbstractMosaicSpaceWith
      (fun Z t => @ConnectedSpace Z t ∧ @LocallyConnectedSpace Z t) X :=
  isCurveSpace_iff_abstract

theorem lemma_2_2 {Z A : Type u} {S : A → Set Z} {τ : ∀ α, TopologicalSpace (S α)}
    (hcover : ∀ x : Z, ∃ α, x ∈ S α)
    (hcl : ∀ α β, IsClosed[τ α] {y : S α | (y : Z) ∈ S β})
    (hhom : ∀ α β, @Continuous {y : S α | (y : Z) ∈ S β} {y : S β | (y : Z) ∈ S α}
      (@instTopologicalSpaceSubtype _ _ (τ α)) (@instTopologicalSpaceSubtype _ _ (τ β))
      fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩) :
    IsAbstractMosaic S τ :=
  isAbstractMosaic_of_compatible hcover hcl hhom

theorem prop_2_3_1 {Z A : Type u} {S : A → Set Z} {τ : ∀ α, TopologicalSpace (S α)}
    (hM : IsAbstractMosaic S τ) (α : A) :
    @IsClosedEmbedding (S α) Z (τ α) (mosaicTopology S τ) Subtype.val :=
  isClosedEmbedding_val hM α

theorem cor_2_9_2_full (hX : IsMosaicSpace X) :
    [IsQuasiCurveSpace X, IsCurveSpace X, Captures X IsPeanoContinuum,
      Captures X IsPathImage].TFAE :=
  cor_2_9_2_tfae hX

theorem prop_2_10 [T2Space X] :
    [IsPathDetermined X, ClosedTestedByPaths X, IsQuotientOfIntervals X, IsCurveSpace X,
      IsQuasiCurveSpace X].TFAE :=
  prop_2_10_tfae

theorem lemma_2_14_article {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    (hK : ∀ K ∈ 𝒦, ¬ LocallyConnectedSpace K →
      ∀ (O : Set X), IsOpen O → ∀ z ∈ O ∩ K, ∀ v : ℕ → X, (∀ n, v n ∈ K) →
        Tendsto v atTop (𝓝 z) → ∀ᶠ n in atTop, v n ∈ pathComponentIn O z) :
    (∀ O : Set X, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected X :=
  h𝒦.lemma_2_14_lc hcm hK

theorem cor_2_15 (h : IsQuasiCurveSpace X) :
    (∀ O : Set X, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected X ∧ LocallyMStronglyConnected X :=
  h.cor_2_15

theorem compact_locallyConnected_lpc {Z : Type u} [TopologicalSpace Z] [CompactSpace Z]
    [MetrizableSpace Z] [LocallyConnectedSpace Z] : LocallyPathConnectedSpace Z :=
  Peano.locallyPathConnectedSpace_of_compact

theorem peano_classical {K : Set X} (h : IsPeanoContinuum K) :
    IsPathConnected K ∧ ArcwiseConnected K ∧ LocallyPathConnectedSpace K ∧
      LocallyArcwiseConnected K ∧ ∀ x ∈ K, ∀ y ∈ K, x ≠ y → ∃ A ⊆ K, IsArc A :=
  ⟨h.isPathConnected, h.arcwiseConnected, h.locallyPathConnectedSpace,
    h.locallyArcwiseConnected, fun _ hx _ hy hxy => h.exists_isArc hx hy hxy⟩

theorem quasiPeano_components {K : Set X} (h : IsQuasiPeano K) :
    (range fun a : K => connectedComponent a).Finite ∧
    ∀ a : K, IsOpen (connectedComponent a) ∧
      IsPeanoContinuum ((↑) '' connectedComponent a : Set X) :=
  h.components

theorem remark_3_7 [FirstCountableTopology X] (hX : IsMosaicSpace X)
    (hloc : LocallyMStronglyConnected X) (hnot : ¬ LocallyPathConnectedSpace X) :
    IsMContinuumSpace X ∧ ¬ IsQuasiCurveSpace X :=
  mContinuum_not_quasiCurve_of_firstCountable hX hloc hnot

theorem lemma_5_2 {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ConnectedSpace K] {U : Set K} (hU : IsOpen U) (hUne : U ≠ univ) {x : K}
    (hx : x ∈ closure U) :
    (connectedComponentIn (closure U) x ∩ (closure U \ U)).Nonempty :=
  boundary_bumping hU hUne hx

theorem theorem_6_3_4 {Y : Type u} [TopologicalSpace Y] [Nonempty Y] (hY : IsMosaicSpace Y) :
    AllOpenMContinuum (Cone Y) ↔ AllOpenMContinuum Y :=
  cone_allOpenMContinuum_iff hY

theorem theorem_7_4_lac (hX : IsMosaicSpace X) :
    (IsQuasiCurveSpace X → LocallyArcwiseConnected X) ∧
    (LocallyArcwiseConnected X → LocallyMStronglyConnected X) :=
  chain_lac hX

theorem theorem_7_4_firstCountable_lac [FirstCountableTopology X] (hX : IsMosaicSpace X) :
    IsQuasiCurveSpace X ↔ LocallyArcwiseConnected X :=
  firstCountable_QC_iff_LAC hX

theorem lemma_2_2_closed {Z A : Type u} [TopologicalSpace Z] {Y : Set Z} {S : A → Set Y}
    (hcover : ∀ y : Y, ∃ α, y ∈ S α) (hcl : ∀ α, IsClosed ((Subtype.val '' S α : Set Z))) :
    IsAbstractMosaic S fun _ => inferInstance :=
  isAbstractMosaic_of_isClosed hcover hcl

theorem lemma_2_2_finite {Z A : Type u} {S : A → Set Z} {τ : ∀ α, TopologicalSpace (S α)}
    (hcover : ∀ x : Z, ∃ α, x ∈ S α) (hT1 : ∀ α, @T1Space _ (τ α))
    (hfin : ∀ α β, α ≠ β → (S α ∩ S β).Finite) : IsAbstractMosaic S τ :=
  isAbstractMosaic_of_finite_inter hcover hT1 hfin

theorem prop_2_3_3 {Z : Type*} [TopologicalSpace Z] {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦) :
    IsQuotientMap (fun p : Σ K : 𝒦, (K : Set X) => (p.2 : X)) ∧
      ∀ f : X → Z, Continuous f ↔ ∀ K ∈ 𝒦, Continuous fun y : K => f y :=
  ⟨h𝒦.isQuotientMap_sigma, fun _ => h𝒦.continuous_iff⟩

theorem prop_2_3_456 {𝒦 : Set (Set X)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) :
    (∀ (u : ℕ → X) (a : X), Tendsto u atTop (𝓝 a) →
      ∃ K ∈ 𝒦, a ∈ K ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n, u (ψ n) ∈ K) ∧
    UniqueSeqLimits X ∧ SequentialSpace X :=
  ⟨fun _ _ hu => h𝒦.exists_piece_subseq hcm hu, h𝒦.uniqueSeqLimits hcm,
    IsMosaicSpace.sequentialSpace ⟨𝒦, h𝒦, hcm⟩⟩

theorem remark_2_5 [T2Space X] {C : Type*} [TopologicalSpace C] [CompactSpace C]
    [MetrizableSpace C] {f : C → X} (hf : Continuous f) :
    IsClosed (range f) ∧ IsCompact (range f) ∧ MetrizableSpace (range f) :=
  range_compact_metrizable_of_t2 hf

theorem cor_2_6_2 [SequentialSpace X] (hX : UniqueSeqLimits X) :
    (∀ {a b : X} (γ : Path a b), IsPeanoContinuum (range γ)) ∧
    ∀ {s : Set X}, IsPathConnected s → ∀ {a b : X}, a ∈ s → b ∈ s →
      ∃ L ⊆ s, IsMetricContinuum L ∧ a ∈ L ∧ b ∈ L :=
  ⟨fun γ => isPeanoContinuum_range_path hX γ,
    fun hs _ _ ha hb => MosaicSpaces.IsPathConnected.exists_metricContinuum hX hs ha hb⟩

theorem cor_2_6_3 [SequentialSpace X] (hX : UniqueSeqLimits X) {x : X}
    {K : ℕ → Set X} (hK : ∀ n, IsMetricContinuum (K n)) (hx : ∀ n, x ∈ K n)
    (hnull : ∀ O : Set X, IsOpen O → x ∈ O → ∀ᶠ n in atTop, K n ⊆ O) :
    IsMetricContinuum (⋃ n, K n) :=
  isMetricContinuum_iUnion_of_null hX hK hx hnull

theorem prop_2_10_quotient {ι : Type*} {q : (Σ _ : ι, unitInterval) → X} (hq : IsQuotientMap q) :
    ClosedTestedByPaths X :=
  ClosedTestedByPaths.of_isQuotientMap hq

theorem fan_metric {J : Type u} (ν : J → ℕ) (hν : Function.Injective ν) :
    (∀ f g h : Fan J, Fan.phi ν f h ≤ Fan.phi ν f g + Fan.phi ν g h) ∧
    (∀ f g : Fan J, Fan.phi ν f g = Fan.phi ν g f) ∧
    (∀ f g : Fan J, Fan.phi ν f g = 0 ↔ f = g) ∧
    ∀ s : Set (Fan J), IsOpen s ↔ ∀ f ∈ s, ∃ ε > 0, ∀ g, Fan.phi ν f g < ε → g ∈ s :=
  ⟨Fan.phi_triangle ν, Fan.phi_comm ν, Fan.phi_eq_zero_iff ν, fun _ => Fan.isOpen_iff_phi ν hν⟩

theorem prop_6_2_1 {Y : Type u} [TopologicalSpace Y] [Nonempty Y] :
    IsOpenEmbedding (fun p : Y × {t : unitInterval | (t : ℝ) < 1} => Cone.mk (p.1, p.2.1)) ∧
    range (fun p : Y × {t : unitInterval | (t : ℝ) < 1} => Cone.mk (p.1, p.2.1)) =
      ({Cone.vertex}ᶜ : Set (Cone Y)) :=
  ⟨Cone.isOpenEmbedding_punctured, Cone.range_punctured⟩

theorem prop_6_2_2 {Y : Type u} [TopologicalSpace Y] {K : Set Y} (hK : IsClosed K) :
    ∃ e : Cone K → Cone Y, IsClosedEmbedding e ∧ (∀ p : K × unitInterval,
      e (Cone.mk p) = Cone.mk ((p.1 : Y), p.2)) ∧ range e = Cone.mk '' (K ×ˢ univ) ∧
      (IsCompactMetrizable K → K.Nonempty → IsMetricContinuum (Cone.mk '' (K ×ˢ univ))) :=
  ⟨Cone.pieceMap K, Cone.isClosedEmbedding_pieceMap hK, fun _ => rfl, Cone.range_pieceMap,
    fun hKc hne => Cone.isMetricContinuum_piece hK hKc hne⟩

theorem prop_6_2_3 {Y : Type u} [TopologicalSpace Y] {𝒦 : Set (Set Y)} (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) :
    IsMosaicFamily ((fun K => Cone.mk '' (K ×ˢ univ)) '' {K | K ∈ 𝒦 ∧ K.Nonempty}) ∧
    ∀ P ∈ (fun K => Cone.mk '' (K ×ˢ univ)) '' {K | K ∈ 𝒦 ∧ K.Nonempty}, IsMetricContinuum P :=
  ⟨Cone.isMosaicFamily_pieces h𝒦, by
    rintro _ ⟨K, ⟨hK, hne⟩, rfl⟩
    exact Cone.isMetricContinuum_piece (h𝒦.isClosed K hK) (hcm K hK) hne⟩

theorem theorem_6_3_5_sep {Y : Type u} [TopologicalSpace Y]
    (hsep : ∀ y y' : Y, y ≠ y' → ∃ f : Y → ℝ, Continuous f ∧ f y ≠ f y') :
    ∀ c c' : Cone Y, c ≠ c' → ∃ f : Cone Y → ℝ, Continuous f ∧ f c ≠ f c' :=
  Cone.separatesPoints hsep

theorem prop_7_1_tail (hX : IsMosaicSpace X) {U : Set X} (hU : IsOpen U) {x : X}
    (hxU : x ∈ U) [(𝓝 x).IsCountablyGenerated]
    (hloc : ∀ O : Set X, IsOpen O → x ∈ O →
      ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ MStronglyConnected W)
    {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x)) :
    ∃ N, ∃ L ⊆ U, IsMetricContinuum L ∧ x ∈ L ∧ ∀ n ≥ N, u n ∈ L :=
  exists_metricContinuum_tail hX hU hxU hloc hu

theorem prop_7_2_tail {x : X} [(𝓝 x).IsCountablyGenerated]
    (hloc : ∀ O : Set X, IsOpen O → x ∈ O → ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPathConnected W)
    {u : ℕ → X} (hu : Tendsto u atTop (𝓝 x)) :
    ∃ N, ∃ f : C(unitInterval, X), f 1 = x ∧
      ∀ j : ℕ, ∃ t : unitInterval, (t : ℝ) = 1 - 1 / ((j : ℝ) + 1) ∧ f t = u (N + j) :=
  let ⟨N, f, hf1, hfj⟩ := exists_path_through_tail hloc hu
  ⟨N, f, hf1, fun j => ⟨tailPt j, rfl, hfj j⟩⟩

theorem theorem_7_4_strict_LAC_H :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyArcwiseConnected X ∧
      ¬ AllOpenMContinuum X :=
  chain_LAC_not_H

theorem sec_5_1_translation [T2Space X] [SequentialSpace X] [LocallyPathConnectedSpace X]
    (h : ¬ IsPathDetermined X) :
    IsMosaicSpace X ∧ LocallyArcwiseConnected X ∧ ¬ IsQuasiCurveSpace X :=
  ⟨isMosaicSpace_of_t2, isMosaicSpace_of_t2.locallyArcwiseConnected_iff.2 inferInstance,
    fun hq => h ((prop_2_10_tfae.out 1 5).2 hq)⟩

end Paper

end MosaicSpaces
