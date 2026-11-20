module

public import MosaicSpaces.Continua
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Recognising classes of mosaic spaces from sequences (article: Lemma 2.8, Corollary 2.9)

* `MosaicSpaces.isMosaicFamily_iff_captures` is **Lemma 2.8** (`lem:generate`).
* `MosaicSpaces.isMContinuumSpace_iff_captures` is **Corollary 2.9(1)** (Lavallee, Theorem 2.1).
* `MosaicSpaces.isQuasiCurveSpace_tfae` is **Corollary 2.9(2)**, equivalence of (a), (b), (c);
  `MosaicSpaces.capturesPeano_of_capturesPath` is the implication (d) ⇒ (c). The implication
  (c) ⇒ (d) is proved in `MosaicSpaces.Peano.Consequences` (`IsCurveSpace.capturesPath`,
  `cor_2_9_2_tfae`) without the Hahn–Mazurkiewicz theorem: a convergent sequence in a Peano
  continuum has a tail on one path (Peano continua are locally path connected, `Peano.LPC`).

Also: transfer of metric continua between a subspace and the ambient space.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ### Transfer between a subspace and the ambient space -/

/-- An embedding maps subspaces homeomorphically onto their images; in particular it preserves
metrizability of subspaces. -/
theorem metrizableSpace_image_iff {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsEmbedding f) (s : Set X) : MetrizableSpace (f '' s) ↔ MetrizableSpace s := by
  let e₀ : s ≃ f '' s := Equiv.Set.image f s hf.injective
  have hind : IsInducing e₀ := by
    refine IsInducing.of_comp ?_ continuous_subtype_val ?_
    · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _
    · exact hf.isInducing.comp IsInducing.subtypeVal
  let e : s ≃ₜ f '' s := e₀.toHomeomorphOfIsInducing hind
  constructor
  · intro h
    exact e.isEmbedding.metrizableSpace
  · intro h
    exact e.symm.isEmbedding.metrizableSpace

theorem isMetricContinuum_image_iff {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsEmbedding f) {s : Set X} : IsMetricContinuum (f '' s) ↔ IsMetricContinuum s := by
  unfold IsMetricContinuum
  rw [← hf.isCompact_iff, metrizableSpace_image_iff hf s]
  have hc : IsConnected (f '' s) ↔ IsConnected s := by
    unfold IsConnected
    rw [hf.isInducing.isPreconnected_image, image_nonempty]
  rw [hc]

/-- A metric continuum of the subspace `U` is a metric continuum of `X`, and conversely. -/
theorem isMetricContinuum_val_image {U : Set X} {L : Set U} :
    IsMetricContinuum ((↑) '' L : Set X) ↔ IsMetricContinuum L :=
  isMetricContinuum_image_iff IsEmbedding.subtypeVal

theorem IsMetricContinuum.preimage_val {U : Set X} {L : Set X} (hL : IsMetricContinuum L)
    (hLU : L ⊆ U) : IsMetricContinuum ((↑) ⁻¹' L : Set U) := by
  rw [← isMetricContinuum_val_image, Subtype.image_preimage_coe, inter_eq_right.2 hLU]
  exact hL

theorem IsPeanoContinuum.image_iff_aux {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsEmbedding f) {s : Set X} :
    LocallyConnectedSpace (f '' s) ↔ LocallyConnectedSpace s := by
  let e₀ : s ≃ f '' s := Equiv.Set.image f s hf.injective
  have hind : IsInducing e₀ := by
    refine IsInducing.of_comp ?_ continuous_subtype_val ?_
    · exact (hf.continuous.comp continuous_subtype_val).subtype_mk _
    · exact hf.isInducing.comp IsInducing.subtypeVal
  let e : s ≃ₜ f '' s := e₀.toHomeomorphOfIsInducing hind
  constructor
  · intro h
    exact e.isOpenEmbedding.locallyConnectedSpace
  · intro h
    exact e.symm.isOpenEmbedding.locallyConnectedSpace

theorem isPeanoContinuum_image_iff {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : IsEmbedding f) {s : Set X} : IsPeanoContinuum (f '' s) ↔ IsPeanoContinuum s := by
  unfold IsPeanoContinuum
  rw [isMetricContinuum_image_iff hf, IsPeanoContinuum.image_iff_aux hf]

/-! ### Compact metrizable subsets are closed -/

/-- In a sequential space with unique sequential limits, a compact metrizable subset is closed
(the last assertion of Lemma 2.4). -/
theorem IsCompactMetrizable.isClosed [SequentialSpace X] (hX : UniqueSeqLimits X) {K : Set X}
    (hK : IsCompactMetrizable K) : IsClosed K := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
  haveI := hK.2
  have h := (range_closed_compact_metrizable hX (continuous_subtype_val (p := (· ∈ K)))).1
  rwa [Subtype.range_coe] at h

/-! ### Capture of convergent sequences -/

/-- Every convergent sequence has a subsequence lying, together with its limit, in a set with
property `P`. -/
def Captures (X : Type u) [TopologicalSpace X] (P : Set X → Prop) : Prop :=
  ∀ (u : ℕ → X) (a : X), Tendsto u atTop (𝓝 a) →
    ∃ K, P K ∧ a ∈ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ K

theorem Captures.mono {P Q : Set X → Prop} (h : Captures X P) (hPQ : ∀ K, P K → Q K) :
    Captures X Q := fun u a hu =>
  let ⟨K, hK, haK, φ, hφ, hφK⟩ := h u a hu
  ⟨K, hPQ K hK, haK, φ, hφ, hφK⟩

/-- **Lemma 2.8** (`lem:generate`). Let `X` be a mosaic space and `𝒦` a family of compact
metrizable subspaces covering `X`. Then `𝒦` generates the topology of `X` (that is, it is a mosaic
family: its members are closed and the topology is coherent with them) if and only if every
convergent sequence has a subsequence lying, together with its limit, in a member of `𝒦`. -/
theorem isMosaicFamily_iff_captures (hX : IsMosaicSpace X) {𝒦 : Set (Set X)}
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) (hcover : ∀ x : X, ∃ K ∈ 𝒦, x ∈ K) :
    IsMosaicFamily 𝒦 ↔ Captures X (· ∈ 𝒦) := by
  haveI := hX.sequentialSpace
  constructor
  · intro h𝒦 u a hu
    exact h𝒦.exists_piece_subseq hcm hu
  · intro hcap
    refine ⟨hcover, fun K hK => (hcm K hK).isClosed hX.uniqueSeqLimits, fun M hM => ?_⟩
    refine IsSeqClosed.isClosed fun u a huM hu => ?_
    obtain ⟨K, hK, haK, φ, hφ, hφK⟩ := hcap u a hu
    exact ((hM K hK).mem_of_tendsto (hu.comp hφ.tendsto_atTop)
      (Eventually.of_forall fun n => ⟨huM (φ n), hφK n⟩)).1

/-- **Corollary 2.9(1)** (Lavallee, Theorem 2.1). A mosaic space is an m-continuum space if and
only if every convergent sequence has a subsequence which lies, together with its limit, in a
metric continuum contained in the space. -/
theorem isMContinuumSpace_iff_captures (hX : IsMosaicSpace X) :
    IsMContinuumSpace X ↔ Captures X IsMetricContinuum := by
  haveI := hX.sequentialSpace
  constructor
  · rintro ⟨𝒦, h𝒦, hK⟩ u a hu
    obtain ⟨K, hK𝒦, haK, φ, hφ, hφK⟩ :=
      h𝒦.exists_piece_subseq (fun K hK' => (hK K hK').isCompactMetrizable) hu
    exact ⟨K, hK K hK𝒦, haK, φ, hφ, hφK⟩
  · intro hcap
    refine ⟨{K | IsMetricContinuum K}, ?_, fun K hK => hK⟩
    refine (isMosaicFamily_iff_captures hX (fun K hK => IsMetricContinuum.isCompactMetrizable hK)
      fun x => ⟨{x}, isMetricContinuum_singleton hX.uniqueSeqLimits x, mem_singleton x⟩).2 hcap

/-! ### Corollary 2.9(2) -/

instance : LocallyPathConnectedSpace unitInterval :=
  (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace

/-- The image of a path in a sequential space with unique sequential limits is a Peano continuum
(the part of Corollary 2.6(2) that needs no Hahn–Mazurkiewicz theorem: a closed continuous image
of `[0,1]` is locally connected because it is a quotient of `[0,1]`). -/
theorem isPeanoContinuum_range_path [SequentialSpace X] (hX : UniqueSeqLimits X) {a b : X}
    (γ : Path a b) : IsPeanoContinuum (range γ) := by
  refine ⟨isMetricContinuum_range_path hX γ, ?_⟩
  have hcl : IsClosedMap (rangeFactorization γ) :=
    isClosedMap_rangeFactorization (isClosedMap_of_compact hX γ.continuous)
  have hq : IsQuotientMap (rangeFactorization γ) :=
    hcl.isQuotientMap γ.continuous.rangeFactorization rangeFactorization_surjective
  haveI : LocallyPathConnectedSpace (range γ) := hq.locallyPathConnectedSpace
  infer_instance

theorem isPeanoContinuum_singleton [SequentialSpace X] (hX : UniqueSeqLimits X) (x : X) :
    IsPeanoContinuum ({x} : Set X) := by
  have h := isPeanoContinuum_range_path hX (Path.refl x)
  have e : range (Path.refl x) = {x} := by
    ext y
    simp [eq_comm]
  rwa [e] at h

/-- (a) ⇒ (c) of **Corollary 2.9(2)**: in a quasi-curve space every convergent sequence has a
subsequence lying, together with its limit, in a Peano continuum. The component of the limit in a
quasi-Peano piece is open in the piece and is a Peano continuum. -/
theorem IsQuasiCurveSpace.capturesPeano (h : IsQuasiCurveSpace X) :
    Captures X IsPeanoContinuum := by
  obtain ⟨𝒦, h𝒦, hQ⟩ := h
  intro u a hu
  obtain ⟨Q, hQ𝒦, haQ, φ, hφ, hφQ⟩ :=
    h𝒦.exists_piece_subseq (fun K hK => (hQ K hK).isCompactMetrizable) hu
  obtain ⟨hQc, hQm, hQl⟩ := hQ Q hQ𝒦
  haveI := hQm
  haveI := hQl
  haveI : CompactSpace Q := isCompact_iff_compactSpace.1 hQc
  let C : Set Q := connectedComponent ⟨a, haQ⟩
  have hCo : IsOpen C := isOpen_connectedComponent
  have hCc : IsClosed C := isClosed_connectedComponent
  have hPeano : IsPeanoContinuum C := by
    refine ⟨⟨hCc.isCompact, isConnected_connectedComponent, inferInstance⟩, ?_⟩
    exact hCo.locallyConnectedSpace
  -- the subsequence converges to `a` in the piece
  have hconv : Tendsto (fun n => (⟨u (φ n), hφQ n⟩ : Q)) atTop (𝓝 ⟨a, haQ⟩) :=
    tendsto_subtype_rng.2 (hu.comp hφ.tendsto_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hconv.eventually (hCo.mem_nhds mem_connectedComponent))
  refine ⟨(↑) '' C, (isPeanoContinuum_image_iff IsEmbedding.subtypeVal).2 hPeano,
    ⟨_, mem_connectedComponent, rfl⟩, fun n => φ (n + N), fun i j hij => hφ (by omega),
    fun n => ⟨_, hN (n + N) (Nat.le_add_left N n), rfl⟩⟩

/-- (c) ⇒ (b) of **Corollary 2.9(2)**: in a mosaic space in which every convergent sequence is
captured by a Peano continuum, the Peano continua form a mosaic of Peano continua. -/
theorem isCurveSpace_of_capturesPeano (hX : IsMosaicSpace X) (h : Captures X IsPeanoContinuum) :
    IsCurveSpace X := by
  haveI := hX.sequentialSpace
  refine ⟨{K | IsPeanoContinuum K}, ?_, fun K hK => hK⟩
  exact (isMosaicFamily_iff_captures hX (fun K hK => IsPeanoContinuum.isCompactMetrizable hK)
    fun x => ⟨{x}, isPeanoContinuum_singleton hX.uniqueSeqLimits x, mem_singleton x⟩).2 h

/-- **Corollary 2.9(2)** (cf. Lavallee, Theorem 6.1), equivalence of (a), (b), (c): for a mosaic
space, being a quasi-curve space, being a curve space, and having every convergent sequence
captured by a Peano continuum are equivalent. -/
theorem isQuasiCurveSpace_tfae (hX : IsMosaicSpace X) :
    List.TFAE [IsQuasiCurveSpace X, IsCurveSpace X, Captures X IsPeanoContinuum] := by
  tfae_have 1 → 3 := IsQuasiCurveSpace.capturesPeano
  tfae_have 3 → 2 := isCurveSpace_of_capturesPeano hX
  tfae_have 2 → 1 := IsCurveSpace.isQuasiCurveSpace
  tfae_finish

/-- The sets that are images of paths. -/
def IsPathImage (L : Set X) : Prop := ∃ (a b : X) (γ : Path a b), range γ = L

/-- (d) ⇒ (c) of **Corollary 2.9(2)**: if every convergent sequence is captured by the image of a
path, it is captured by a Peano continuum. The converse (c) ⇒ (d) is
`IsCurveSpace.capturesPath` (`MosaicSpaces.Peano.Consequences`). -/
theorem capturesPeano_of_capturesPath [SequentialSpace X] (hX : UniqueSeqLimits X)
    (h : Captures X IsPathImage) : Captures X IsPeanoContinuum :=
  h.mono fun _ ⟨_, _, γ, hγ⟩ => hγ ▸ isPeanoContinuum_range_path hX γ

/-- A mosaic space in which every convergent sequence is captured by the image of a path is a
curve space (used for Proposition 7.2). -/
theorem isCurveSpace_of_capturesPath (hX : IsMosaicSpace X) (h : Captures X IsPathImage) :
    IsCurveSpace X :=
  haveI := hX.sequentialSpace
  isCurveSpace_of_capturesPeano hX (capturesPeano_of_capturesPath hX.uniqueSeqLimits h)

/-- Quasi-curve spaces are m-continuum spaces (Lavallee, Corollary 6.2). -/
theorem IsQuasiCurveSpace.isMContinuumSpace (h : IsQuasiCurveSpace X) : IsMContinuumSpace X :=
  IsCurveSpace.isMContinuumSpace (((isQuasiCurveSpace_tfae h.isMosaicSpace).out 1 2).1 h)

end MosaicSpaces
