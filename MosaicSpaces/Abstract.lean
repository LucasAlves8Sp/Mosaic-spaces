module

public import MosaicSpaces.Mosaic

/-!
# Definition 2.1 (abstract mosaics), Lemma 2.2 and Proposition 2.3(1)

The article defines mosaics abstractly: a family of topological spaces `(X_α, 𝒯_α)` whose
underlying sets cover a set `X`, such that for every `𝒯_α`-closed `M ⊆ X_α` the set `M ∩ X_β` is
`𝒯_β`-closed; the mosaic topology on `X` has as closed sets the `M` with every `M ∩ X_α`
`𝒯_α`-closed.

* `IsAbstractMosaic S τ`, `mosaicTopology S τ`: Definition 2.1, with the pieces given as subsets
  `S α ⊆ X` carrying their own topologies `τ α`.
* `isClosedEmbedding_val`: **Proposition 2.3(1)**: each piece is closed in the mosaic topology,
  which induces the piece topology on it.
* `isAbstractMosaic_of_compatible`: **Lemma 2.2**.
* `isMosaicSpaceWith_iff_abstract` and the four corollaries `isMosaicSpace_iff_abstract`,
  `isMContinuumSpace_iff_abstract`, `isQuasiCurveSpace_iff_abstract`,
  `isCurveSpace_iff_abstract`: the intrinsic definitions used throughout the formalization
  (`IsMosaicSpace` etc.) agree with Definition 2.1: a topological space is a mosaic space (an
  m-continuum, quasi-curve, curve space) in the intrinsic sense iff its topology is the mosaic
  topology of an abstract mosaic of compact metrizable spaces (of metric continua, quasi-Peano
  spaces, Peano continua).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u}

/-- **Definition 2.1**: a mosaic on the set `X`: pieces `S α ⊆ X` with topologies `τ α`, covering
`X`, such that the trace on `S β` of a `τ α`-closed subset of `S α` is `τ β`-closed. -/
structure IsAbstractMosaic {A : Type u} (S : A → Set X) (τ : ∀ α, TopologicalSpace (S α)) :
    Prop where
  cover : ∀ x : X, ∃ α, x ∈ S α
  compat : ∀ α β (M : Set (S α)), IsClosed[τ α] M →
    IsClosed[τ β] {y : S β | (y : X) ∈ (Subtype.val '' M : Set X)}

/-- **Definition 2.1**: the mosaic topology: `M` is closed iff every trace `M ∩ S α` is
`τ α`-closed (the final topology of the inclusions). -/
def mosaicTopology {A : Type u} (S : A → Set X) (τ : ∀ α, TopologicalSpace (S α)) :
    TopologicalSpace X :=
  ⨆ α, @TopologicalSpace.coinduced (S α) X Subtype.val (τ α)

section abstract

variable {A : Type u} {S : A → Set X} {τ : ∀ α, TopologicalSpace (S α)}

theorem isClosed_mosaicTopology_iff {M : Set X} :
    IsClosed[mosaicTopology S τ] M ↔ ∀ α, IsClosed[τ α] (Subtype.val ⁻¹' M : Set (S α)) := by
  letI := mosaicTopology S τ
  rw [← isOpen_compl_iff]
  unfold mosaicTopology
  refine isOpen_iSup_iff.trans (forall_congr' fun α => ?_)
  rw [isOpen_coinduced, preimage_compl]
  letI := τ α
  exact isOpen_compl_iff

/-- **Proposition 2.3(1)**: in the mosaic topology each piece is closed and carries its own
topology: the inclusion is a closed embedding. -/
theorem isClosedEmbedding_val (hM : IsAbstractMosaic S τ) (α : A) :
    @IsClosedEmbedding (S α) X (τ α) (mosaicTopology S τ) Subtype.val := by
  letI := τ α
  letI := mosaicTopology S τ
  have hc : Continuous (Subtype.val : S α → X) :=
    continuous_iff_coinduced_le.2 (le_iSup (fun β => @TopologicalSpace.coinduced (S β) X
      Subtype.val (τ β)) α)
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap hc Subtype.val_injective ?_
  intro M hMc
  exact isClosed_mosaicTopology_iff.2 fun β => hM.compat α β M hMc

/-- **Lemma 2.2**: pieces whose pairwise intersections are closed in both, with the same induced
topology, form a mosaic. -/
theorem isAbstractMosaic_of_compatible (hcover : ∀ x : X, ∃ α, x ∈ S α)
    (hcl : ∀ α β, IsClosed[τ α] {y : S α | (y : X) ∈ S β})
    (hhom : ∀ α β, @Continuous {y : S α | (y : X) ∈ S β} {y : S β | (y : X) ∈ S α}
      (@instTopologicalSpaceSubtype _ _ (τ α)) (@instTopologicalSpaceSubtype _ _ (τ β))
      fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩) :
    IsAbstractMosaic S τ := by
  refine ⟨hcover, fun α β M hMc => ?_⟩
  letI := τ α
  letI := τ β
  -- the trace is the image of `M ∩ (S α ∩ S β)` under the homeomorphism onto `S β ∩ S α`
  have hpre : IsClosed[@instTopologicalSpaceSubtype _ _ (τ β)]
      {z : {y : S β | (y : X) ∈ S α} | (⟨⟨z.1.1, z.2⟩, z.1.2⟩ : {y : S α | (y : X) ∈ S β}) ∈
        ((↑) ⁻¹' M : Set {y : S α | (y : X) ∈ S β})} :=
    (hMc.preimage continuous_subtype_val).preimage (hhom β α)
  have hJ : IsClosedEmbedding (Subtype.val : {y : S β | (y : X) ∈ S α} → S β) :=
    (hcl β α).isClosedEmbedding_subtypeVal
  convert hJ.isClosedMap _ hpre using 1
  ext y
  constructor
  · rintro ⟨x, hxM, hxy⟩
    have hyα : (y : X) ∈ S α := hxy ▸ x.2
    refine ⟨⟨y, hyα⟩, ?_, rfl⟩
    show (⟨⟨(y : X), hyα⟩, y.2⟩ : {y : S α | (y : X) ∈ S β}).1 ∈ M
    have : (⟨(y : X), hyα⟩ : S α) = x := Subtype.ext hxy.symm
    simp only [this]; exact hxM
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, rfl⟩


/-- **Lemma 2.2**, first special case: a family of closed subspaces of a space `Z` covering a set
`Y ⊆ Z` is a mosaic on `Y`. -/
theorem isAbstractMosaic_of_isClosed {Z : Type u} [TopologicalSpace Z] {Y : Set Z} {A : Type u}
    {S : A → Set Y} (hcover : ∀ y : Y, ∃ α, y ∈ S α)
    (hcl : ∀ α, IsClosed ((Subtype.val '' S α : Set Z))) :
    IsAbstractMosaic S fun _ => inferInstance := by
  refine isAbstractMosaic_of_compatible hcover (fun α β => ?_) (fun α β => ?_)
  · have e : {y : S α | (y : Y) ∈ S β} =
        (fun y : S α => ((y : Y) : Z)) ⁻¹' (Subtype.val '' S β : Set Z) := by
      ext y
      simp only [mem_setOf_eq, mem_preimage, mem_image]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨z, hz, hzy⟩ => Subtype.ext hzy ▸ hz⟩
    rw [e]
    exact (hcl β).preimage (continuous_subtype_val.comp continuous_subtype_val)
  · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- **Lemma 2.2**, second special case: a family of `T₁` spaces with finite pairwise intersections
is a mosaic. -/
theorem isAbstractMosaic_of_finite_inter {A : Type u} {S : A → Set X}
    {τ : ∀ α, TopologicalSpace (S α)} (hcover : ∀ x : X, ∃ α, x ∈ S α)
    (hT1 : ∀ α, @T1Space _ (τ α)) (hfin : ∀ α β, α ≠ β → (S α ∩ S β).Finite) :
    IsAbstractMosaic S τ := by
  classical
  refine isAbstractMosaic_of_compatible hcover (fun α β => ?_) (fun α β => ?_)
  · letI := τ α
    have := hT1 α
    by_cases h : α = β
    · subst h
      have e : {y : S α | (y : X) ∈ S α} = univ := eq_univ_of_forall fun y => y.2
      rw [e]; exact isClosed_univ
    · refine Set.Finite.isClosed ?_
      refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
      refine (hfin α β h).subset ?_
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  · letI := τ α
    letI := τ β
    have := hT1 α
    by_cases h : α = β
    · subst h
      exact continuous_id
    · have hf : Finite {y : S α | (y : X) ∈ S β} := by
        refine Set.Finite.to_subtype ?_
        refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
        refine (hfin α β h).subset ?_
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      exact continuous_of_discreteTopology

end abstract

/-! ### Agreement with the intrinsic definitions -/

/-- An intrinsic mosaic space whose pieces have, besides being compact metrizable, a property `P`
(of the piece as a topological space). -/
def IsMosaicSpaceWith (P : ∀ Z : Type u, TopologicalSpace Z → Prop) (X : Type u)
    [TopologicalSpace X] : Prop :=
  ∃ 𝒦 : Set (Set X), IsMosaicFamily 𝒦 ∧ ∀ K ∈ 𝒦, IsCompactMetrizable K ∧ P K inferInstance

/-- An abstract mosaic space (Definition 2.1) whose pieces are compact metrizable spaces with
property `P`, carrying the mosaic topology. -/
def IsAbstractMosaicSpaceWith (P : ∀ Z : Type u, TopologicalSpace Z → Prop) (X : Type u)
    [t : TopologicalSpace X] : Prop :=
  ∃ (A : Type u) (S : A → Set X) (τ : ∀ α, TopologicalSpace (S α)), IsAbstractMosaic S τ ∧
    (∀ α, @CompactSpace _ (τ α) ∧ @MetrizableSpace _ (τ α) ∧ P (S α) (τ α)) ∧
    t = mosaicTopology S τ

/-- **Definition 2.1 vs. the intrinsic definition**: a space is an intrinsic mosaic space with
`P`-pieces iff its topology is the mosaic topology of an abstract mosaic of compact metrizable
`P`-spaces. -/
theorem isMosaicSpaceWith_iff_abstract (P : ∀ Z : Type u, TopologicalSpace Z → Prop)
    [t : TopologicalSpace X] : IsMosaicSpaceWith P X ↔ IsAbstractMosaicSpaceWith P X := by
  constructor
  · rintro ⟨𝒦, h𝒦, hK⟩
    refine ⟨𝒦, fun K => K.1, fun K => inferInstance, ⟨fun x => ?_, fun K L M hM => ?_⟩,
      fun K => ⟨isCompact_iff_compactSpace.1 (hK K.1 K.2).1.1, (hK K.1 K.2).1.2,
        (hK K.1 K.2).2⟩, ?_⟩
    · obtain ⟨K, hK𝒦, hxK⟩ := h𝒦.cover x
      exact ⟨⟨K, hK𝒦⟩, hxK⟩
    · exact ((h𝒦.isClosed K.1 K.2).isClosedEmbedding_subtypeVal.isClosedMap M hM).preimage
        continuous_subtype_val
    · refine TopologicalSpace.ext_iff_isClosed.2 fun M => ?_
      rw [isClosed_mosaicTopology_iff]
      constructor
      · intro hMc K
        exact hMc.preimage continuous_subtype_val
      · intro h
        refine h𝒦.coherent M fun K hK𝒦 => ?_
        have := (h𝒦.isClosed K hK𝒦).isClosedEmbedding_subtypeVal.isClosedMap _ (h ⟨K, hK𝒦⟩)
        rwa [Subtype.image_preimage_coe, inter_comm] at this
  · rintro ⟨A, S, τ, hM, hpc, rfl⟩
    letI := mosaicTopology S τ
    have hemb := isClosedEmbedding_val hM
    -- the subspace topology on each piece is the piece topology
    have hinst : ∀ α, (instTopologicalSpaceSubtype : TopologicalSpace (S α)) = τ α :=
      fun α => (hemb α).eq_induced.symm
    refine ⟨range S, ⟨fun x => ?_, ?_, fun M hMc => ?_⟩, ?_⟩
    · obtain ⟨α, hα⟩ := hM.cover x
      exact ⟨S α, mem_range_self α, hα⟩
    · rintro _ ⟨α, rfl⟩
      have := (hemb α).isClosedMap univ (@isClosed_univ _ (τ α))
      rwa [image_univ, Subtype.range_coe] at this
    · refine isClosed_mosaicTopology_iff.2 fun α => ?_
      have h1 : IsClosed[τ α] (Subtype.val ⁻¹' (M ∩ S α) : Set (S α)) := by
        letI := τ α
        exact (hMc (S α) (mem_range_self α)).preimage (hemb α).continuous
      have h2 : (Subtype.val ⁻¹' (M ∩ S α) : Set (S α)) = Subtype.val ⁻¹' M := by
        ext y; simp [y.2]
      rwa [h2] at h1
    · rintro _ ⟨α, rfl⟩
      obtain ⟨hc, hm, hP⟩ := hpc α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := @isCompact_range _ _ (τ α) _ hc _ (hemb α).continuous
        rwa [Subtype.range_coe] at this
      · rw [hinst α]; exact hm
      · rw [hinst α]; exact hP

theorem isMetricContinuum_iff_space {K : Set X} [TopologicalSpace X] :
    IsMetricContinuum K ↔ IsCompactMetrizable K ∧ ConnectedSpace K := by
  unfold IsMetricContinuum IsCompactMetrizable
  rw [isConnected_iff_connectedSpace]
  tauto

/-- **Definition 2.1** agrees with `IsMosaicSpace`. -/
theorem isMosaicSpace_iff_abstract [TopologicalSpace X] :
    IsMosaicSpace X ↔ IsAbstractMosaicSpaceWith (fun _ _ => True) X := by
  rw [← isMosaicSpaceWith_iff_abstract]
  simp [IsMosaicSpace, IsMosaicSpaceWith]

/-- **Definition 2.1** agrees with `IsMContinuumSpace`: pieces are metric continua. -/
theorem isMContinuumSpace_iff_abstract [TopologicalSpace X] :
    IsMContinuumSpace X ↔ IsAbstractMosaicSpaceWith (fun Z t => @ConnectedSpace Z t) X := by
  rw [← isMosaicSpaceWith_iff_abstract]
  simp only [IsMContinuumSpace, IsMosaicSpaceWith, isMetricContinuum_iff_space]

/-- **Definition 2.1** agrees with `IsQuasiCurveSpace`: pieces are quasi-Peano spaces. -/
theorem isQuasiCurveSpace_iff_abstract [TopologicalSpace X] :
    IsQuasiCurveSpace X ↔
      IsAbstractMosaicSpaceWith (fun Z t => @LocallyConnectedSpace Z t) X := by
  rw [← isMosaicSpaceWith_iff_abstract]
  simp only [IsQuasiCurveSpace, IsMosaicSpaceWith, IsQuasiPeano, IsCompactMetrizable, and_assoc]

/-- **Definition 2.1** agrees with `IsCurveSpace`: pieces are Peano continua. -/
theorem isCurveSpace_iff_abstract [TopologicalSpace X] :
    IsCurveSpace X ↔ IsAbstractMosaicSpaceWith
      (fun Z t => @ConnectedSpace Z t ∧ @LocallyConnectedSpace Z t) X := by
  rw [← isMosaicSpaceWith_iff_abstract]
  simp only [IsCurveSpace, IsMosaicSpaceWith, IsPeanoContinuum, isMetricContinuum_iff_space,
    and_assoc]

end MosaicSpaces
