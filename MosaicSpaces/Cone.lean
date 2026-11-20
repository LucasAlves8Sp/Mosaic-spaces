module

public import MosaicSpaces.FirstCountable
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Cones (article: Lemma 6.1, Proposition 6.2, Theorem 6.3)

For a space `Y`, `Cone Y` is the quotient of `Y × [0,1]` collapsing `Y × {1}` to one point.

* `MosaicSpaces.isQuotientMap_prodMap_id` is **Lemma 6.1** (Whitehead).
* `MosaicSpaces.Cone.isOpenEmbedding_punctured` and `range_punctured` are
  **Proposition 6.2(1)**; `Cone.isMetricContinuum_piece` and `Cone.isClosedEmbedding_piece` are
  **Proposition 6.2(2)**; `Cone.isMosaicFamily_pieces` and `Cone.isMContinuumSpace` are
  **Proposition 6.2(3)**.
* **Theorem 6.3**: parts (1) `Cone.isMContinuumSpace`, `Cone.contractibleSpace`; (2)
  `Cone.locallyPathConnectedSpace`, `Cone.locallyMStronglyConnected`; (3)
  `Cone.not_isMContinuumSpace_punctured`; (5) `Cone.separatesPoints`, `Cone.t2Space`.
  Part (4) is `Cone.allOpenMCont_of_cone`, `Cone.allOpenMCont_cone` (`MosaicSpaces.Cone4`). In
  part (2), "locally arcwise connected" follows from local path connectedness by the arc theorem
  (`IsMosaicSpace.locallyArcwiseConnected_iff`, `MosaicSpaces.ArcConsequences`).

The cone over a compact metrizable space is shown to be compact and metrizable by a continuous
injection `[(y,t)] ↦ (t, (1-t)·e(y))` into `ℝ × ℓ^∞`, where `e` is Urysohn's embedding.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval
open scoped BoundedContinuousFunction

namespace MosaicSpaces

universe u

/-! ### Lemma 6.1 -/

/-- **Lemma 6.1** (Whitehead). If `q` is a quotient map and `L` is locally compact, then
`q × id_L` is a quotient map. (The article also assumes `L` Hausdorff; Mathlib's lifting lemma
does not need it.) -/
theorem isQuotientMap_prodMap_id {A B L : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace L] [LocallyCompactSpace L] {q : A → B} (hq : IsQuotientMap q) :
    IsQuotientMap (Prod.map q (id : L → L)) := by
  refine isQuotientMap_iff_isClosed.2 ⟨hq.surjective.prodMap Function.surjective_id,
    fun W => ⟨fun hW => hW.preimage (hq.continuous.prodMap continuous_id), fun hW => ?_⟩⟩
  have h : Continuous fun p : B × L => p ∈ Wᶜ := by
    refine hq.continuous_lift_prod_left (Z := Prop) (g := fun p : B × L => p ∈ Wᶜ) ?_
    exact continuous_Prop.2 hW.isOpen_compl
  exact isOpen_compl_iff.1 (continuous_Prop.1 h)

/-! ### Mosaic families give quotient maps (Proposition 2.3(3)) -/

variable {Y : Type u} [TopologicalSpace Y]

/-- **Proposition 2.3(3)**: for a mosaic family, the natural map from the topological sum of the
pieces is a quotient map. -/
theorem IsMosaicFamily.isQuotientMap_sigma {𝒦 : Set (Set Y)} (h𝒦 : IsMosaicFamily 𝒦) :
    IsQuotientMap (fun p : Σ K : 𝒦, (K : Set Y) => (p.2 : Y)) := by
  refine isQuotientMap_iff_isClosed.2 ⟨fun y => ?_, fun M => ⟨fun hM => ?_, fun hM => ?_⟩⟩
  · obtain ⟨K, hK, hyK⟩ := h𝒦.cover y
    exact ⟨⟨⟨K, hK⟩, ⟨y, hyK⟩⟩, rfl⟩
  · exact hM.preimage (continuous_sigma fun _ => continuous_subtype_val)
  · refine h𝒦.coherent M fun K hK => ?_
    have h1 : IsClosed (Sigma.mk ⟨K, hK⟩ ⁻¹' ((fun p : Σ K : 𝒦, (K : Set Y) => (p.2 : Y)) ⁻¹' M)) :=
      (isClosed_sigma_iff.1 hM) ⟨K, hK⟩
    exact isClosed_inter_of_preimage (h𝒦.isClosed K hK) h1

/-- **Proposition 2.3(3)**: a map out of a space with a mosaic family is continuous if its
restrictions to the pieces are. -/
theorem IsMosaicFamily.continuous_iff {Z : Type*} [TopologicalSpace Z] {𝒦 : Set (Set Y)}
    (h𝒦 : IsMosaicFamily 𝒦) {f : Y → Z} :
    Continuous f ↔ ∀ K ∈ 𝒦, Continuous fun y : K => f y := by
  rw [h𝒦.isQuotientMap_sigma.continuous_iff]
  constructor
  · intro h K hK
    exact continuous_sigma_iff.1 h ⟨K, hK⟩
  · intro h
    exact continuous_sigma fun K => h K.1 K.2

/-- Closed sets of `Y × [0,1]` are tested on the products of the pieces with `[0,1]`; this is
where Lemma 6.1 is used in the proof of Proposition 6.2. -/
theorem IsMosaicFamily.isClosed_of_prod {𝒦 : Set (Set Y)} (h𝒦 : IsMosaicFamily 𝒦)
    {N : Set (Y × I)} (hN : ∀ K ∈ 𝒦, IsClosed (N ∩ K ×ˢ univ)) : IsClosed N := by
  let q := fun p : Σ K : 𝒦, (K : Set Y) => (p.2 : Y)
  have hQ : IsQuotientMap (Prod.map q (id : I → I)) :=
    isQuotientMap_prodMap_id h𝒦.isQuotientMap_sigma
  rw [← hQ.isCoinducing.isClosed_preimage]
  rw [← (Homeomorph.sigmaProdDistrib (X := fun K : 𝒦 => (K : Set Y)) (Y := I)).symm.isClosed_preimage]
  refine isClosed_sigma_iff.2 fun K => ?_
  have hK := hN K.1 K.2
  have hc : Continuous fun p : (K.1 : Set Y) × I => ((p.1 : Y), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have e : Sigma.mk K ⁻¹' ((Homeomorph.sigmaProdDistrib (X := fun K : 𝒦 => (K : Set Y))
      (Y := I)).symm ⁻¹' (Prod.map q id ⁻¹' N)) =
      (fun p : (K.1 : Set Y) × I => ((p.1 : Y), p.2)) ⁻¹' (N ∩ (K.1 : Set Y) ×ˢ univ) := by
    ext ⟨a, t⟩
    simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
    constructor
    · intro h
      exact ⟨h, a.2⟩
    · intro h
      exact h.1
  rw [e]
  exact hK.preimage hc

/-! ### The cone -/

/-- The relation collapsing `Y × {1}`. -/
def coneSetoid (Y : Type u) : Setoid (Y × I) where
  r p q := p = q ∨ (p.2 = 1 ∧ q.2 = 1)
  iseqv := ⟨fun p => Or.inl rfl,
    fun h => h.elim (fun e => Or.inl e.symm) fun h => Or.inr ⟨h.2, h.1⟩,
    fun h h' => by
      rcases h with rfl | ⟨h1, h2⟩
      · exact h'
      · rcases h' with rfl | ⟨h3, h4⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h4⟩⟩

/-- The cone `𝖼 Y`: the quotient of `Y × [0,1]` collapsing `Y × {1}` to a point. -/
def Cone (Y : Type u) [TopologicalSpace Y] : Type u := Quotient (coneSetoid Y)

instance : TopologicalSpace (Cone Y) := inferInstanceAs (TopologicalSpace (Quotient _))

namespace Cone

/-- The quotient map `κ : Y × [0,1] → 𝖼 Y`. -/
def mk : Y × I → Cone Y := Quotient.mk _

theorem isQuotientMap_mk : IsQuotientMap (mk : Y × I → Cone Y) := isQuotientMap_quotient_mk'

theorem continuous_mk : Continuous (mk : Y × I → Cone Y) := isQuotientMap_mk.continuous

theorem mk_surjective : Function.Surjective (mk : Y × I → Cone Y) := Quotient.mk_surjective

theorem mk_eq_mk {p q : Y × I} : mk p = mk q ↔ p = q ∨ (p.2 = 1 ∧ q.2 = 1) := Quotient.eq

theorem mk_one (y y' : Y) : mk (y, 1) = mk (y', (1 : I)) := mk_eq_mk.2 (Or.inr ⟨rfl, rfl⟩)

/-- The vertex of the cone over a nonempty space. -/
noncomputable def vertex [Nonempty Y] : Cone Y := mk (Classical.arbitrary Y, 1)

theorem mk_one_eq_vertex [Nonempty Y] (y : Y) : mk (y, 1) = (vertex : Cone Y) := mk_one _ _

theorem mk_eq_vertex_iff [Nonempty Y] {p : Y × I} : mk p = (vertex : Cone Y) ↔ p.2 = 1 := by
  rw [vertex, mk_eq_mk]
  constructor
  · rintro (rfl | ⟨h, -⟩)
    · rfl
    · exact h
  · intro h
    exact Or.inr ⟨h, rfl⟩

/-- The height function `𝖼 Y → [0,1]`. -/
def height : Cone Y → I :=
  Quotient.lift (fun p : Y × I => p.2) fun p q h =>
    h.elim (fun e => e ▸ rfl) fun h => h.1.trans h.2.symm

theorem height_mk (p : Y × I) : height (mk p) = p.2 := rfl

theorem continuous_height : Continuous (height : Cone Y → I) :=
  isQuotientMap_mk.continuous_iff.2 continuous_snd

theorem connectedSpace [Nonempty Y] : ConnectedSpace (Cone Y) := by
  have hseg : ∀ y : Y, IsConnected (range fun t : I => (mk (y, t) : Cone Y)) := fun y =>
    isConnected_range (continuous_mk.comp (continuous_const.prodMk continuous_id))
  have hcov : (⋃ y : Y, range fun t : I => (mk (y, t) : Cone Y)) = univ := by
    refine eq_univ_of_forall fun c => ?_
    obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
    exact mem_iUnion.2 ⟨y, t, rfl⟩
  refine { isPreconnected_univ := ?_, toNonempty := ⟨vertex⟩ }
  rw [← hcov]
  exact isPreconnected_iUnion ⟨vertex, mem_iInter.2 fun y => ⟨1, mk_one_eq_vertex y⟩⟩
    fun y => (hseg y).2

/-! ### The cone over a compact metrizable space -/

theorem compactSpace [CompactSpace Y] : CompactSpace (Cone Y) :=
  Quotient.compactSpace

/-- The cone over a compact metrizable space is metrizable (article, before Proposition 6.2). -/
theorem metrizableSpace [CompactSpace Y] [MetrizableSpace Y] : MetrizableSpace (Cone Y) := by
  haveI := compactSpace (Y := Y)
  obtain ⟨e, he⟩ := exists_embedding_l_infty (X := Y)
  let F₀ : Y × I → ℝ × (ℕ →ᵇ ℝ) := fun p => ((p.2 : ℝ), (1 - (p.2 : ℝ)) • e p.1)
  have hF₀ : ∀ p q : Y × I, (coneSetoid Y) p q → F₀ p = F₀ q := by
    rintro p q (rfl | ⟨h1, h2⟩)
    · rfl
    · simp only [F₀, h1, h2, Icc.coe_one, sub_self, zero_smul]
  let F : Cone Y → ℝ × (ℕ →ᵇ ℝ) := Quotient.lift F₀ hF₀
  have hF : Continuous F := by
    refine isQuotientMap_mk.continuous_iff.2 ?_
    exact (continuous_subtype_val.comp continuous_snd).prodMk
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (he.continuous.comp continuous_fst))
  have hinj : Function.Injective F := by
    intro c c'
    obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
    obtain ⟨⟨y', t'⟩, rfl⟩ := mk_surjective c'
    intro h
    have h1 : (t : ℝ) = t' := congrArg Prod.fst h
    have htt : t = t' := Subtype.ext h1
    subst htt
    have h2 : (1 - (t : ℝ)) • e y = (1 - (t : ℝ)) • e y' := congrArg Prod.snd h
    by_cases ht : t = 1
    · subst ht
      exact mk_one y y'
    · have hne : (1 - (t : ℝ)) ≠ 0 := by
        intro h0
        apply ht
        exact Subtype.ext (by simp only [Icc.coe_one]; linarith)
      have := he.injective (smul_right_injective _ hne h2)
      rw [this]
  exact (hF.isClosedEmbedding hinj).metrizableSpace

/-- The cone over a nonempty compact metrizable space is a metric continuum. -/
theorem isMetricContinuum_univ [Nonempty Y] [CompactSpace Y] [MetrizableSpace Y] :
    IsMetricContinuum (univ : Set (Cone Y)) := by
  haveI := compactSpace (Y := Y)
  haveI := metrizableSpace (Y := Y)
  haveI := connectedSpace (Y := Y)
  exact ⟨isCompact_univ, isConnected_univ, inferInstance⟩

/-! ### Proposition 6.2(1): the punctured cone -/

/-- The open subset `[0,1)` of `[0,1]`. -/
def Ilt : Set I := {t | (t : ℝ) < 1}

theorem isOpen_Ilt : IsOpen Ilt := isOpen_lt continuous_subtype_val continuous_const

theorem ne_one_of_mem_Ilt {t : I} (ht : t ∈ Ilt) : t ≠ 1 := fun h => by
  rw [h] at ht
  have h1 : ((1 : I) : ℝ) < 1 := ht
  simp at h1

theorem mem_Ilt_iff {t : I} : t ∈ Ilt ↔ t ≠ 1 :=
  ⟨ne_one_of_mem_Ilt, fun h => lt_of_le_of_ne t.2.2 fun h' => h (Subtype.ext h')⟩

/-- The map `Y × [0,1) → 𝖼 Y`. -/
def punctured : Y × Ilt → Cone Y := fun p => mk (p.1, p.2.1)

/-- **Proposition 6.2(1)**: `κ` restricts to an open embedding of `Y × [0,1)` (product
topology) into the cone. -/
theorem isOpenEmbedding_punctured : IsOpenEmbedding (punctured : Y × Ilt → Cone Y) := by
  have hinj : Function.Injective (punctured : Y × Ilt → Cone Y) := by
    rintro ⟨y, t⟩ ⟨y', t'⟩ h
    rcases mk_eq_mk.1 h with h | ⟨h1, -⟩
    · simp only [Prod.mk.injEq] at h
      rw [h.1, Subtype.ext h.2]
    · exact absurd h1 (ne_one_of_mem_Ilt t.2)
  have hcont : Continuous (punctured : Y × Ilt → Cone Y) :=
    continuous_mk.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hemb : IsOpenEmbedding (Prod.map (id : Y → Y) (Subtype.val : Ilt → I)) :=
    IsOpenEmbedding.id.prodMap (isOpen_Ilt.isOpenEmbedding_subtypeVal)
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj fun V hV => ?_
  rw [← isQuotientMap_mk.isOpen_preimage]
  have e : mk ⁻¹' (punctured '' V) = Prod.map id Subtype.val '' V := by
    ext ⟨y, t⟩
    constructor
    · rintro ⟨⟨y', t'⟩, hV', h⟩
      rcases mk_eq_mk.1 h with h | ⟨h1, -⟩
      · exact ⟨⟨y', t'⟩, hV', h⟩
      · exact absurd h1 (ne_one_of_mem_Ilt t'.2)
    · rintro ⟨⟨y', t'⟩, hV', h⟩
      exact ⟨⟨y', t'⟩, hV', congrArg mk h⟩
  rw [e]
  exact hemb.isOpenMap V hV

/-- **Proposition 6.2(1)**: the image of `Y × [0,1)` is the complement of the vertex. -/
theorem range_punctured [Nonempty Y] : range (punctured : Y × Ilt → Cone Y) = {vertex}ᶜ := by
  ext c
  obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
  simp only [mem_range, mem_compl_iff, mem_singleton_iff, mk_eq_vertex_iff]
  constructor
  · rintro ⟨⟨y', t'⟩, h⟩ ht
    rcases mk_eq_mk.1 h with h | ⟨h1, -⟩
    · simp only [Prod.mk.injEq] at h
      rw [← h.2] at ht
      exact ne_one_of_mem_Ilt t'.2 ht
    · exact ne_one_of_mem_Ilt t'.2 h1
  · intro ht
    exact ⟨⟨y, ⟨t, mem_Ilt_iff.2 ht⟩⟩, rfl⟩

theorem isOpen_compl_vertex [Nonempty Y] : IsOpen ({vertex}ᶜ : Set (Cone Y)) :=
  range_punctured (Y := Y) ▸ isOpenEmbedding_punctured.isOpen_range

/-! ### Proposition 6.2(2): the cones over the pieces -/

variable {K : Set Y}

/-- The map `𝖼 K → 𝖼 Y` induced by the inclusion `K ⊆ Y`. -/
def pieceMap (K : Set Y) : Cone K → Cone Y :=
  Quotient.lift (fun p : K × I => mk ((p.1 : Y), p.2)) fun p q h => by
    rcases h with rfl | ⟨h1, h2⟩
    · rfl
    · exact mk_eq_mk.2 (Or.inr ⟨h1, h2⟩)

theorem pieceMap_mk (p : K × I) : pieceMap K (mk p) = mk ((p.1 : Y), p.2) := rfl

theorem continuous_pieceMap : Continuous (pieceMap K) :=
  isQuotientMap_mk.continuous_iff.2
    (continuous_mk.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

theorem injective_pieceMap : Function.Injective (pieceMap K) := by
  intro c c'
  obtain ⟨⟨a, t⟩, rfl⟩ := mk_surjective c
  obtain ⟨⟨a', t'⟩, rfl⟩ := mk_surjective c'
  intro h
  rcases mk_eq_mk.1 h with h | ⟨h1, h2⟩
  · simp only [Prod.mk.injEq] at h
    rw [Subtype.ext h.1, h.2]
  · exact mk_eq_mk.2 (Or.inr ⟨h1, h2⟩)

/-- The image of `𝖼 K` in `𝖼 Y`: the set `P_α = κ(X_α × [0,1])`. -/
def piece (K : Set Y) : Set (Cone Y) := mk '' (K ×ˢ univ)

theorem range_pieceMap : range (pieceMap K) = piece K := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨⟨a, t⟩, rfl⟩ := mk_surjective d
    exact ⟨((a : Y), t), ⟨a.2, mem_univ _⟩, rfl⟩
  · rintro ⟨⟨y, t⟩, ⟨hy, -⟩, rfl⟩
    exact ⟨mk (⟨y, hy⟩, t), rfl⟩

/-- If `K` is closed, the induced map `𝖼 K → 𝖼 Y` is a closed map (proof of Proposition 6.2(2)).
-/
theorem isClosedMap_pieceMap (hK : IsClosed K) : IsClosedMap (pieceMap K) := by
  intro C hC
  rw [← isQuotientMap_mk.isCoinducing.isClosed_preimage]
  let C' : Set (K × I) := mk ⁻¹' C
  have hC' : IsClosed C' := hC.preimage continuous_mk
  have hemb : IsClosedEmbedding (Prod.map (Subtype.val : K → Y) (id : I → I)) :=
    hK.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
  have e : mk ⁻¹' (pieceMap K '' C) =
      Prod.map Subtype.val id '' C' ∪ {p : Y × I | p.2 = 1 ∧ ∃ c ∈ C, height c = 1} := by
    ext ⟨y, t⟩
    constructor
    · rintro ⟨d, hd, h⟩
      obtain ⟨⟨a, s⟩, rfl⟩ := mk_surjective d
      rcases mk_eq_mk.1 h with h | ⟨h1, h2⟩
      · simp only [Prod.mk.injEq] at h
        refine Or.inl ⟨(a, s), hd, ?_⟩
        simp only [Prod.map, h.1, h.2, id]
      · exact Or.inr ⟨h2, mk (a, s), hd, h1⟩
    · rintro (⟨⟨a, s⟩, hd, h⟩ | ⟨ht, c, hc, hc1⟩)
      · simp only [Prod.map, id, Prod.mk.injEq] at h
        exact ⟨mk (a, s), hd, by rw [pieceMap_mk, h.1, h.2]⟩
      · obtain ⟨⟨a, s⟩, rfl⟩ := mk_surjective c
        refine ⟨mk (a, s), hc, ?_⟩
        rw [pieceMap_mk]
        exact mk_eq_mk.2 (Or.inr ⟨hc1, ht⟩)
  rw [e]
  refine (hemb.isClosedMap _ hC').union ?_
  by_cases h : ∃ c ∈ C, height c = 1
  · have : {p : Y × I | p.2 = 1 ∧ ∃ c ∈ C, height c = 1} = Prod.snd ⁻¹' {1} := by
      ext p
      simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, and_iff_left h]
    rw [this]
    exact isClosed_singleton.preimage continuous_snd
  · have : {p : Y × I | p.2 = 1 ∧ ∃ c ∈ C, height c = 1} = ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ => h
    rw [this]
    exact isClosed_empty

/-- **Proposition 6.2(2)**: for a closed `K ⊆ Y`, the map `𝖼 K → 𝖼 Y` is a closed embedding onto
`P = κ(K × [0,1])`. -/
theorem isClosedEmbedding_pieceMap (hK : IsClosed K) : IsClosedEmbedding (pieceMap K) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_pieceMap injective_pieceMap
    (isClosedMap_pieceMap hK)

theorem isClosed_piece (hK : IsClosed K) : IsClosed (piece K) :=
  range_pieceMap (K := K) ▸ (isClosedEmbedding_pieceMap hK).isClosed_range

/-- **Proposition 6.2(2)**: for a nonempty, closed, compact, metrizable `K ⊆ Y`, the set
`P = κ(K × [0,1])` is a metric continuum. -/
theorem isMetricContinuum_piece (hK : IsClosed K) (hKc : IsCompactMetrizable K)
    (hne : K.Nonempty) : IsMetricContinuum (piece K) := by
  haveI : Nonempty K := hne.to_subtype
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc.1
  haveI := hKc.2
  have h := (isMetricContinuum_image_iff (isClosedEmbedding_pieceMap hK).isEmbedding).2
    (isMetricContinuum_univ (Y := K))
  rwa [image_univ, range_pieceMap] at h

/-! ### Proposition 6.2(3) -/

variable {𝒦 : Set (Set Y)}

/-- The family of the sets `P_α` for the nonempty pieces. -/
def pieces (𝒦 : Set (Set Y)) : Set (Set (Cone Y)) :=
  (fun K => piece K) '' {K | K ∈ 𝒦 ∧ K.Nonempty}

/-- **Proposition 6.2(3)**: the cones over the (nonempty) pieces of a mosaic family form a mosaic
family of the cone. -/
theorem isMosaicFamily_pieces (h𝒦 : IsMosaicFamily 𝒦) : IsMosaicFamily (pieces 𝒦) := by
  refine ⟨fun c => ?_, ?_, fun M hM => ?_⟩
  · obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
    obtain ⟨K, hK, hyK⟩ := h𝒦.cover y
    exact ⟨piece K, ⟨K, ⟨hK, y, hyK⟩, rfl⟩, ⟨(y, t), ⟨hyK, mem_univ _⟩, rfl⟩⟩
  · rintro _ ⟨K, ⟨hK, -⟩, rfl⟩
    exact isClosed_piece (h𝒦.isClosed K hK)
  · rw [← isQuotientMap_mk.isCoinducing.isClosed_preimage]
    refine h𝒦.isClosed_of_prod fun K hK => ?_
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · rw [hKe, empty_prod, inter_empty]
      exact isClosed_empty
    · have h1 : IsClosed (M ∩ piece K) := hM _ ⟨K, ⟨hK, hKne⟩, rfl⟩
      have e : mk ⁻¹' M ∩ K ×ˢ univ = mk ⁻¹' (M ∩ piece K) ∩ K ×ˢ univ := by
        ext p
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨h, hp⟩
          exact ⟨⟨h, p, hp, rfl⟩, hp⟩
        · rintro ⟨⟨h, -⟩, hp⟩
          exact ⟨h, hp⟩
      rw [e]
      exact (h1.preimage continuous_mk).inter
        ((h𝒦.isClosed K hK).prod isClosed_univ)

/-- **Proposition 6.2(3)** and **Theorem 6.3(1)**, first part: the cone over a mosaic space is an
m-continuum space. -/
theorem isMContinuumSpace (hY : IsMosaicSpace Y) : IsMContinuumSpace (Cone Y) := by
  haveI := hY.sequentialSpace
  obtain ⟨𝒦, h𝒦, hcm⟩ := hY
  refine ⟨pieces 𝒦, isMosaicFamily_pieces h𝒦, ?_⟩
  rintro _ ⟨K, ⟨hK, hKne⟩, rfl⟩
  exact isMetricContinuum_piece (h𝒦.isClosed K hK) (hcm K hK) hKne

theorem isMosaicSpace (hY : IsMosaicSpace Y) : IsMosaicSpace (Cone Y) :=
  (isMContinuumSpace hY).isMosaicSpace

/-! ### Theorem 6.3(1): contractibility -/

/-- The point `t + (1 - t) r` of `[0,1]`. -/
def lerpOne (t r : I) : I :=
  ⟨(t : ℝ) + (1 - t) * r, by
    have h1 := t.2.1
    have h2 := t.2.2
    have h3 := r.2.1
    have h4 := r.2.2
    constructor <;> nlinarith⟩

theorem continuous_lerpOne : Continuous fun p : I × I => lerpOne p.1 p.2 :=
  Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd))) _

theorem lerpOne_one_left (r : I) : lerpOne 1 r = 1 := Subtype.ext (by simp [lerpOne])

theorem lerpOne_zero_right (t : I) : lerpOne t 0 = t := Subtype.ext (by simp [lerpOne])

theorem lerpOne_one_right (t : I) : lerpOne t 1 = 1 := Subtype.ext (by simp [lerpOne])

/-- **Theorem 6.3(1)**, second part: the cone over a nonempty space is contractible. Joint
continuity of the contraction comes from Lemma 6.1 (`IsQuotientMap.continuous_lift_prod_right`).
-/
theorem contractibleSpace [Nonempty Y] : ContractibleSpace (Cone Y) := by
  let H₀ : I → Cone Y → Cone Y := fun r =>
    Quotient.lift (fun p : Y × I => mk (p.1, lerpOne p.2 r)) fun p q h => by
      rcases h with rfl | ⟨h1, h2⟩
      · rfl
      · show mk (p.1, lerpOne p.2 r) = mk (q.1, lerpOne q.2 r)
        rw [h1, h2, lerpOne_one_left]
        exact mk_one _ _
  have hH : Continuous fun p : I × Cone Y => H₀ p.1 p.2 := by
    refine isQuotientMap_mk.continuous_lift_prod_right (g := fun p : I × Cone Y => H₀ p.1 p.2) ?_
    exact continuous_mk.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_lerpOne.comp ((continuous_snd.comp continuous_snd).prodMk continuous_fst)))
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨vertex, ⟨⟨⟨fun p => H₀ p.1 p.2, hH⟩, fun c => ?_, fun c => ?_⟩⟩⟩
  · obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
    show mk (y, lerpOne t 0) = mk (y, t)
    rw [lerpOne_zero_right]
  · obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
    show mk (y, lerpOne t 1) = vertex
    rw [lerpOne_one_right]
    exact mk_one_eq_vertex y

/-! ### Theorem 6.3(2) -/

/-- **Theorem 6.3(2)**: if `Y` is locally path connected, so is its cone; equivalently, path
components of open subsets of the cone are open. -/
theorem locallyPathConnectedSpace [LocallyPathConnectedSpace Y] :
    LocallyPathConnectedSpace (Cone Y) :=
  isQuotientMap_mk.locallyPathConnectedSpace

/-- **Theorem 6.3(2)**: the cone over a locally path connected mosaic space is locally
m-strongly connected. ("Locally arcwise connected": `IsMosaicSpace.locallyArcwiseConnected_iff`.) -/
theorem locallyMStronglyConnected [LocallyPathConnectedSpace Y] (hY : IsMosaicSpace Y) :
    LocallyMStronglyConnected (Cone Y) :=
  (locallyPathConnectedOpen_iff.2 locallyPathConnectedSpace).locallyMStronglyConnected
    (isMosaicSpace hY)

/-! ### Theorem 6.3(3) -/

/-- **Theorem 6.3(3)**. If the mosaic space `Y` is not an m-continuum space, then the open
subspace `𝖼 Y ∖ {v}` of its cone is not an m-continuum space. -/
theorem not_isMContinuumSpace_punctured [Nonempty Y] (hY : IsMosaicSpace Y)
    (hnot : ¬ IsMContinuumSpace Y) :
    ¬ IsMContinuumSpace ({vertex}ᶜ : Set (Cone Y)) := by
  haveI := hY.sequentialSpace
  have hU := hY.uniqueSeqLimits
  intro hm
  apply hnot
  rw [isMContinuumSpace_iff_captures hY]
  intro u y hu
  have hcY := isMosaicSpace hY
  rw [isMContinuumSpace_iff_captures (hcY.of_isOpen isOpen_compl_vertex)] at hm
  -- the homeomorphism `Y × [0,1) ≃ 𝖼 Y ∖ {v}` and the projection `π`
  have hemb := (isOpenEmbedding_punctured (Y := Y)).isEmbedding
  let e : Y × Ilt ≃ₜ ({vertex}ᶜ : Set (Cone Y)) :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr range_punctured)
  let π : ({vertex}ᶜ : Set (Cone Y)) → Y := fun c => (e.symm c).1
  have hπ : Continuous π := continuous_fst.comp e.symm.continuous
  have h0 : (0 : I) ∈ Ilt := by
    show ((0 : I) : ℝ) < 1
    simp
  let z : Y → ({vertex}ᶜ : Set (Cone Y)) := fun y => e (y, ⟨0, h0⟩)
  have hz : Continuous z := e.continuous.comp (continuous_id.prodMk continuous_const)
  have hπz : ∀ y, π (z y) = y := fun y => by simp [π, z]
  obtain ⟨L, hL, hyL, φ, hφ, hφL⟩ :=
    hm (fun n => z (u n)) (z y) ((hz.tendsto y).comp hu)
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL.1
  haveI := hL.2.2
  have himg := range_closed_compact_metrizable hU
    (hπ.comp (continuous_subtype_val : Continuous (Subtype.val : L → _)))
  have hconn : IsConnected (range (π ∘ (Subtype.val : L → _))) := by
    haveI : ConnectedSpace L := isConnected_iff_connectedSpace.1 hL.2.1
    exact isConnected_range (hπ.comp continuous_subtype_val)
  refine ⟨range (π ∘ (Subtype.val : L → _)), ⟨himg.2.1, hconn, himg.2.2⟩,
    ⟨⟨z y, hyL⟩, hπz y⟩, φ, hφ, fun n => ⟨⟨z (u (φ n)), hφL n⟩, hπz _⟩⟩

/-! ### Theorem 6.3(5) -/

/-- **Theorem 6.3(5)**: if continuous real functions separate the points of `Y`, they separate
the points of the cone. -/
theorem separatesPoints
    (hsep : ∀ y y' : Y, y ≠ y' → ∃ f : Y → ℝ, Continuous f ∧ f y ≠ f y') :
    ∀ c c' : Cone Y, c ≠ c' → ∃ f : Cone Y → ℝ, Continuous f ∧ f c ≠ f c' := by
  intro c c' hcc'
  obtain ⟨⟨y, t⟩, rfl⟩ := mk_surjective c
  obtain ⟨⟨y', t'⟩, rfl⟩ := mk_surjective c'
  by_cases ht : t = t'
  · subst ht
    have hy : y ≠ y' := fun h => hcc' (by rw [h])
    have ht1 : t ≠ 1 := fun h => hcc' (by rw [h]; exact mk_one y y')
    obtain ⟨f, hf, hff⟩ := hsep y y' hy
    let g : Cone Y → ℝ :=
      Quotient.lift (fun p : Y × I => (1 - (p.2 : ℝ)) * f p.1) fun p q h => by
        rcases h with rfl | ⟨h1, h2⟩
        · rfl
        · show (1 - (p.2 : ℝ)) * f p.1 = (1 - (q.2 : ℝ)) * f q.1
          rw [h1, h2]
          simp
    refine ⟨g, isQuotientMap_mk.continuous_iff.2 ?_, ?_⟩
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        (hf.comp continuous_fst)
    · show (1 - (t : ℝ)) * f y ≠ (1 - (t : ℝ)) * f y'
      have hne : (1 - (t : ℝ)) ≠ 0 := by
        intro h0
        apply ht1
        exact Subtype.ext (by simp only [Icc.coe_one]; linarith)
      exact fun h => hff (mul_left_cancel₀ hne h)
  · refine ⟨fun c => (height c : ℝ), continuous_subtype_val.comp continuous_height, ?_⟩
    exact fun h => ht (Subtype.ext h)

/-- **Theorem 6.3(5)**: in that case the cone is Hausdorff. -/
theorem t2Space (hsep : ∀ y y' : Y, y ≠ y' → ∃ f : Y → ℝ, Continuous f ∧ f y ≠ f y') :
    T2Space (Cone Y) := by
  refine ⟨fun c c' h => ?_⟩
  obtain ⟨f, hf, hff⟩ := separatesPoints hsep c c' h
  obtain ⟨U, V, hU, hV, hcU, hcV, hUV⟩ := t2_separation hff
  exact ⟨f ⁻¹' U, f ⁻¹' V, hU.preimage hf, hV.preimage hf, hcU, hcV, hUV.preimage f⟩

end Cone

end MosaicSpaces
