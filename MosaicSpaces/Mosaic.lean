module

public import MosaicSpaces.Image

/-!
# Mosaic spaces (article: Definition 2.1, Proposition 2.3, Proposition 2.7)

A *mosaic family* on a topological space `X` is a family `𝒦` of closed subsets covering `X` such
that a set is closed as soon as it meets every member of `𝒦` in a closed set. By Proposition 2.3(1)
of the article, the pieces of a mosaic are closed subspaces of the mosaic space and the mosaic
topology is exactly the topology coherent with them, so a topological space is the mosaic space of
a mosaic of compact metric spaces if and only if it admits a mosaic family all of whose members are
compact and metrizable in the subspace topology. That intrinsic formulation is the definition
`IsMosaicSpace` used here.

Nothing in this file assumes that a mosaic space is Hausdorff, first countable or metrizable.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A subset which is compact and metrizable as a subspace ("compact metric" in the article, where
"metric" means metrizable). -/
def IsCompactMetrizable (K : Set X) : Prop :=
  IsCompact K ∧ MetrizableSpace K

/-- A *metric continuum* contained in `X`: a nonempty, compact, connected, metrizable subspace.
(`IsConnected` includes nonemptiness.) -/
def IsMetricContinuum (K : Set X) : Prop :=
  IsCompact K ∧ IsConnected K ∧ MetrizableSpace K

/-- A *quasi-Peano space* contained in `X`: a compact, locally connected, metrizable subspace. -/
def IsQuasiPeano (K : Set X) : Prop :=
  IsCompact K ∧ MetrizableSpace K ∧ LocallyConnectedSpace K

/-- A *Peano continuum* contained in `X`: a locally connected metric continuum. -/
def IsPeanoContinuum (K : Set X) : Prop :=
  IsMetricContinuum K ∧ LocallyConnectedSpace K

theorem IsMetricContinuum.isCompactMetrizable {K : Set X} (h : IsMetricContinuum K) :
    IsCompactMetrizable K := ⟨h.1, h.2.2⟩

theorem IsQuasiPeano.isCompactMetrizable {K : Set X} (h : IsQuasiPeano K) :
    IsCompactMetrizable K := ⟨h.1, h.2.1⟩

theorem IsPeanoContinuum.isCompactMetrizable {K : Set X} (h : IsPeanoContinuum K) :
    IsCompactMetrizable K := h.1.isCompactMetrizable

theorem IsPeanoContinuum.isQuasiPeano {K : Set X} (h : IsPeanoContinuum K) :
    IsQuasiPeano K := ⟨h.1.1, h.1.2.2, h.2⟩

/-- A family of closed subsets covering `X` with which the topology of `X` is coherent: a set is
closed if it meets every member in a closed set. -/
structure IsMosaicFamily (𝒦 : Set (Set X)) : Prop where
  /-- The members cover `X`. -/
  cover : ∀ x : X, ∃ K ∈ 𝒦, x ∈ K
  /-- Every member is closed. -/
  isClosed : ∀ K ∈ 𝒦, IsClosed K
  /-- A set meeting every member in a closed set is closed. -/
  coherent : ∀ M : Set X, (∀ K ∈ 𝒦, IsClosed (M ∩ K)) → IsClosed M

/-- `X` is a *mosaic space*: its topology is coherent with a covering family of closed subspaces
that are compact and metrizable. -/
def IsMosaicSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ 𝒦 : Set (Set X), IsMosaicFamily 𝒦 ∧ ∀ K ∈ 𝒦, IsCompactMetrizable K

/-- `X` is an *m-continuum space*: a mosaic space of a mosaic of metric continua. -/
def IsMContinuumSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ 𝒦 : Set (Set X), IsMosaicFamily 𝒦 ∧ ∀ K ∈ 𝒦, IsMetricContinuum K

/-- `X` is a *quasi-curve space*: a mosaic space of a mosaic of quasi-Peano spaces. -/
def IsQuasiCurveSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ 𝒦 : Set (Set X), IsMosaicFamily 𝒦 ∧ ∀ K ∈ 𝒦, IsQuasiPeano K

/-- `X` is a *curve space*: a mosaic space of a mosaic of Peano continua. -/
def IsCurveSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ 𝒦 : Set (Set X), IsMosaicFamily 𝒦 ∧ ∀ K ∈ 𝒦, IsPeanoContinuum K

theorem IsMContinuumSpace.isMosaicSpace (h : IsMContinuumSpace X) : IsMosaicSpace X :=
  let ⟨𝒦, h𝒦, hK⟩ := h
  ⟨𝒦, h𝒦, fun K hKm => (hK K hKm).isCompactMetrizable⟩

theorem IsQuasiCurveSpace.isMosaicSpace (h : IsQuasiCurveSpace X) : IsMosaicSpace X :=
  let ⟨𝒦, h𝒦, hK⟩ := h
  ⟨𝒦, h𝒦, fun K hKm => (hK K hKm).isCompactMetrizable⟩

/-- A curve space is a quasi-curve space (the trivial implication (b) ⇒ (a) of
Corollary 2.9(2)). -/
theorem IsCurveSpace.isQuasiCurveSpace (h : IsCurveSpace X) : IsQuasiCurveSpace X :=
  let ⟨𝒦, h𝒦, hK⟩ := h
  ⟨𝒦, h𝒦, fun K hKm => (hK K hKm).isQuasiPeano⟩

/-- A curve space is an m-continuum space. -/
theorem IsCurveSpace.isMContinuumSpace (h : IsCurveSpace X) : IsMContinuumSpace X :=
  let ⟨𝒦, h𝒦, hK⟩ := h
  ⟨𝒦, h𝒦, fun K hKm => (hK K hKm).1⟩

/-- If `K` is closed and the trace of `M` on the subspace `K` is closed in `K`, then `M ∩ K` is
closed. -/
theorem isClosed_inter_of_preimage {K M : Set X} (hK : IsClosed K)
    (h : IsClosed ((↑) ⁻¹' M : Set K)) : IsClosed (M ∩ K) := by
  have e : M ∩ K = ((↑) : K → X) '' ((↑) ⁻¹' M) := by
    rw [Subtype.image_preimage_coe, inter_comm]
  rw [e]
  exact hK.isClosedEmbedding_subtypeVal.isClosedMap _ h

namespace IsMosaicFamily

variable {𝒦 : Set (Set X)}

/-- **Proposition 2.3(2)**: a mosaic space is `T₁`. -/
theorem t1Space (h𝒦 : IsMosaicFamily 𝒦) (hT1 : ∀ K ∈ 𝒦, T1Space K) : T1Space X := by
  refine ⟨fun p => h𝒦.coherent _ fun K hK => ?_⟩
  haveI := hT1 K hK
  refine isClosed_inter_of_preimage (h𝒦.isClosed K hK) (Set.Subsingleton.isClosed ?_)
  intro a ha b hb
  have e1 : (a : X) = p := ha
  have e2 : (b : X) = p := hb
  exact Subtype.ext (e1.trans e2.symm)

/-- **Proposition 2.3(6)**: a mosaic space is sequential. -/
theorem sequentialSpace (h𝒦 : IsMosaicFamily 𝒦) (hseq : ∀ K ∈ 𝒦, SequentialSpace K) :
    SequentialSpace X := by
  refine ⟨fun M hM => h𝒦.coherent M fun K hK => ?_⟩
  haveI := hseq K hK
  exact isClosed_inter_of_preimage (h𝒦.isClosed K hK)
    (IsSeqClosed.isClosed (hM.preimage continuous_subtype_val.seqContinuous))

theorem t1Space_of_compactMetrizable (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) : T1Space X :=
  h𝒦.t1Space fun K hK => by
    haveI := (hcm K hK).2
    infer_instance

/-- Statement `(∗)` in the proof of **Proposition 2.3**, without the injectivity hypothesis: a
sequence converging to a point it never takes has a subsequence lying in one piece and converging
there to a point outside the range of the sequence. -/
theorem exists_subseq_tendsto_in_piece (h𝒦 : IsMosaicFamily 𝒦)
    (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) {u : ℕ → X} {a : X}
    (hu : Tendsto u atTop (𝓝 a)) (hne : ∀ n, u n ≠ a) :
    ∃ K ∈ 𝒦, ∃ z ∈ K, z ∉ range u ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ n, u (ψ n) ∈ K) ∧
      Tendsto (u ∘ ψ) atTop (𝓝 z) := by
  haveI : T1Space X := h𝒦.t1Space_of_compactMetrizable hcm
  have haS : a ∉ range u := by
    rintro ⟨n, hn⟩
    exact hne n hn
  have hnc : ¬ IsClosed (range u) := fun hc =>
    haS (hc.mem_of_tendsto hu (Eventually.of_forall fun n => mem_range_self n))
  obtain ⟨K, hK, hKnc⟩ : ∃ K ∈ 𝒦, ¬ IsClosed (range u ∩ K) := by
    by_contra hcon
    push_neg at hcon
    exact hnc (h𝒦.coherent _ hcon)
  obtain ⟨z, hzcl, hznot⟩ : ∃ z ∈ closure (range u ∩ K), z ∉ range u ∩ K := by
    by_contra hcon
    push_neg at hcon
    exact hKnc (closure_subset_iff_isClosed.1 hcon)
  have hKcl : IsClosed K := h𝒦.isClosed K hK
  have hzK : z ∈ K := hKcl.closure_subset (closure_mono inter_subset_right hzcl)
  have hzS : z ∉ range u := fun h => hznot ⟨h, hzK⟩
  haveI : MetrizableSpace K := (hcm K hK).2
  have hz' : (⟨z, hzK⟩ : K) ∈ closure ((↑) ⁻¹' range u : Set K) := by
    rw [closure_subtype, Subtype.image_preimage_coe, inter_comm]
    exact hzcl
  obtain ⟨w, hwS, hw⟩ := mem_closure_iff_seq_limit.1 hz'
  have hwS' : ∀ n, ∃ k, u k = (w n : X) := hwS
  choose m hm using hwS'
  have hwX : Tendsto (fun n => (w n : X)) atTop (𝓝 z) := tendsto_subtype_rng.1 hw
  have hmtop : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 fun N => ?_
    by_contra hcon
    rw [not_eventually] at hcon
    have hfin : (u '' Iio N).Finite := (finite_Iio N).image u
    have hz2 : z ∈ u '' Iio N := hfin.isClosed.mem_of_frequently_of_tendsto
      (hcon.mono fun n hn => ⟨m n, not_le.1 hn, hm n⟩) hwX
    exact hzS (image_subset_range _ _ hz2)
  obtain ⟨φ, hφ, hmφ⟩ := strictMono_subseq_of_tendsto_atTop hmtop
  refine ⟨K, hK, z, hzK, hzS, m ∘ φ, hmφ, fun n => ?_, ?_⟩
  · rw [Function.comp_apply, hm]
    exact (w (φ n)).2
  · have e : u ∘ (m ∘ φ) = (fun n => (w n : X)) ∘ φ := funext fun n => hm (φ n)
    rw [e]
    exact hwX.comp hφ.tendsto_atTop

/-- **Proposition 2.3(5)**: convergent sequences in a mosaic space have unique limits. -/
theorem uniqueSeqLimits (h𝒦 : IsMosaicFamily 𝒦) (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K) :
    UniqueSeqLimits X := by
  haveI : T1Space X := h𝒦.t1Space_of_compactMetrizable hcm
  intro u a b ha hb
  by_contra hab
  have ea : ∀ᶠ n in atTop, u n ≠ a :=
    hb.eventually (isOpen_compl_singleton.eventually_mem fun h => hab h.symm)
  have eb : ∀ᶠ n in atTop, u n ≠ b :=
    ha.eventually (isOpen_compl_singleton.eventually_mem hab)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ea.and eb)
  have hva : Tendsto (fun n => u (n + N)) atTop (𝓝 a) := ha.comp (tendsto_add_atTop_nat N)
  have hvb : Tendsto (fun n => u (n + N)) atTop (𝓝 b) := hb.comp (tendsto_add_atTop_nat N)
  have hv : ∀ n, u (n + N) ≠ a ∧ u (n + N) ≠ b := fun n => hN (n + N) (Nat.le_add_left N n)
  obtain ⟨K, hK, z, hzK, -, ψ, hψ, hψK, hψz⟩ :=
    h𝒦.exists_subseq_tendsto_in_piece hcm hva fun n => (hv n).1
  haveI : MetrizableSpace K := (hcm K hK).2
  have hw : Tendsto (fun n => (⟨u (ψ n + N), hψK n⟩ : K)) atTop (𝓝 ⟨z, hzK⟩) :=
    tendsto_subtype_rng.2 hψz
  have hCK : IsClosed (insert (⟨z, hzK⟩ : K) (range fun n => (⟨u (ψ n + N), hψK n⟩ : K))) :=
    hw.isCompact_insert_range.isClosed
  have hC : IsClosed (insert z (range fun n => u (ψ n + N))) := by
    have e : insert z (range fun n => u (ψ n + N)) =
        ((↑) : K → X) '' insert (⟨z, hzK⟩ : K) (range fun n => (⟨u (ψ n + N), hψK n⟩ : K)) := by
      rw [image_insert_eq, ← range_comp]
      rfl
    rw [e]
    exact (h𝒦.isClosed K hK).isClosedEmbedding_subtypeVal.isClosedMap _ hCK
  have key : ∀ c, Tendsto (fun n => u (n + N)) atTop (𝓝 c) → c = z ∨ ∃ n, u (n + N) = c := by
    intro c hc
    have hc' : Tendsto (fun n => u (ψ n + N)) atTop (𝓝 c) := hc.comp hψ.tendsto_atTop
    have hmem : c ∈ insert z (range fun n => u (ψ n + N)) :=
      hC.mem_of_tendsto hc' (Eventually.of_forall fun n => mem_insert_of_mem _ (mem_range_self n))
    rcases Set.mem_insert_iff.1 hmem with h | ⟨n, hn⟩
    · exact Or.inl h
    · exact Or.inr ⟨ψ n, hn⟩
  rcases key a hva with h | ⟨n, hn⟩
  · rcases key b hvb with h' | ⟨n', hn'⟩
    · exact hab (h.trans h'.symm)
    · exact (hv n').2 hn'
  · exact (hv n).1 hn

/-- **Proposition 2.3(4)**: if `u → a` in a mosaic space, some piece contains `a` and a
subsequence of `u`. -/
theorem exists_piece_subseq (h𝒦 : IsMosaicFamily 𝒦) (hcm : ∀ K ∈ 𝒦, IsCompactMetrizable K)
    {u : ℕ → X} {a : X} (hu : Tendsto u atTop (𝓝 a)) :
    ∃ K ∈ 𝒦, a ∈ K ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ n, u (ψ n) ∈ K := by
  by_cases hfreq : ∃ᶠ n in atTop, u n = a
  · obtain ⟨K, hK, haK⟩ := h𝒦.cover a
    obtain ⟨ψ, hψ, hψa⟩ := extraction_of_frequently_atTop hfreq
    refine ⟨K, hK, haK, ψ, hψ, fun n => ?_⟩
    rw [hψa n]
    exact haK
  · rw [not_frequently] at hfreq
    obtain ⟨N, hN⟩ := eventually_atTop.1 hfreq
    have hv : Tendsto (fun n => u (n + N)) atTop (𝓝 a) := hu.comp (tendsto_add_atTop_nat N)
    obtain ⟨K, hK, z, hzK, -, ψ, hψ, hψK, hψz⟩ :=
      h𝒦.exists_subseq_tendsto_in_piece hcm hv fun n => hN (n + N) (Nat.le_add_left N n)
    have hza : z = a := h𝒦.uniqueSeqLimits hcm hψz (hv.comp hψ.tendsto_atTop)
    refine ⟨K, hK, hza ▸ hzK, fun n => ψ n + N,
      fun i j hij => Nat.add_lt_add_right (hψ hij) N, hψK⟩

end IsMosaicFamily

/-- A convergent sequence together with its limit, in a sequential space with unique sequential
limits, is a closed, compact, metrizable subspace (used in the proof of Proposition 2.7; here it
is deduced from Lemma 2.4 applied to the one-point compactification of `ℕ`). -/
theorem insert_range_closed_compact_metrizable [SequentialSpace X] (hX : UniqueSeqLimits X)
    {u : ℕ → X} {a : X} (hu : Tendsto u atTop (𝓝 a)) :
    IsClosed (insert a (range u)) ∧ IsCompactMetrizable (insert a (range u)) := by
  let f : OnePoint ℕ → X := fun c => c.elim a u
  have hf : Continuous f := (OnePoint.continuous_iff_from_nat f).2 hu
  have e : range f = insert a (range u) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      induction c using OnePoint.rec with
      | infty => exact mem_insert _ _
      | coe n => exact mem_insert_of_mem _ ⟨n, rfl⟩
    · intro hx
      rcases Set.mem_insert_iff.1 hx with h | ⟨n, hn⟩
      · exact ⟨OnePoint.infty, h.symm⟩
      · exact ⟨(n : OnePoint ℕ), hn⟩
  have h := range_closed_compact_metrizable hX hf
  rw [e] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **Proposition 2.7** (Davison; `prop:char`): a topological space is a mosaic space if and only
if it is sequential and its convergent sequences have unique limits. -/
theorem isMosaicSpace_iff :
    IsMosaicSpace X ↔ SequentialSpace X ∧ UniqueSeqLimits X := by
  constructor
  · rintro ⟨𝒦, h𝒦, hcm⟩
    refine ⟨h𝒦.sequentialSpace fun K hK => ?_, h𝒦.uniqueSeqLimits hcm⟩
    haveI := (hcm K hK).2
    infer_instance
  · rintro ⟨hseq, hX⟩
    refine ⟨{S | ∃ (u : ℕ → X) (a : X), Tendsto u atTop (𝓝 a) ∧ S = insert a (range u)},
      ⟨?_, ?_, ?_⟩, ?_⟩
    · intro x
      exact ⟨_, ⟨fun _ => x, x, tendsto_const_nhds, rfl⟩, mem_insert _ _⟩
    · rintro _ ⟨u, a, hu, rfl⟩
      exact (insert_range_closed_compact_metrizable hX hu).1
    · intro M hM
      refine IsSeqClosed.isClosed fun u a hu ha => ?_
      have hc : IsClosed (M ∩ insert a (range u)) := hM _ ⟨u, a, ha, rfl⟩
      exact (hc.mem_of_tendsto ha (Eventually.of_forall fun n =>
        ⟨hu n, mem_insert_of_mem _ (mem_range_self n)⟩)).1
    · rintro _ ⟨u, a, hu, rfl⟩
      exact (insert_range_closed_compact_metrizable hX hu).2

theorem IsMosaicSpace.sequentialSpace (h : IsMosaicSpace X) : SequentialSpace X :=
  (isMosaicSpace_iff.1 h).1

theorem IsMosaicSpace.uniqueSeqLimits (h : IsMosaicSpace X) : UniqueSeqLimits X :=
  (isMosaicSpace_iff.1 h).2

theorem IsMosaicSpace.t1Space (h : IsMosaicSpace X) : T1Space X :=
  haveI := h.sequentialSpace
  h.uniqueSeqLimits.t1Space

/-- **Proposition 2.7**, first consequence: every Hausdorff sequential space is a mosaic space. -/
theorem isMosaicSpace_of_t2 [T2Space X] [SequentialSpace X] : IsMosaicSpace X :=
  isMosaicSpace_iff.2 ⟨inferInstance, uniqueSeqLimits_of_t2⟩

end MosaicSpaces
