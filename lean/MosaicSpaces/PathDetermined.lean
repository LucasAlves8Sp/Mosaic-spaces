module

public import MosaicSpaces.Peano.Consequences

/-!
# Spaces determined by paths (Proposition 2.10)

Following van Douwen, a family `Ps` of subsets of `X` *determines* `X` if a set `F` is closed
whenever `F ∩ P` is closed in `P` for every `P ∈ Ps`; `X` is *path-determined* if it is determined
by the images of paths.

**Proposition 2.10.** For a Hausdorff space `X` the following are equivalent:
(a) `X` is path-determined; (b) a set is closed whenever its preimage under every path is closed;
(c) `X` is a quotient of a topological sum of copies of `[0,1]`; (d) `X` is a curve space;
(e) `X` is a quasi-curve space.

The article's proof of (d) ⇒ (a) uses that Peano continua are images of paths
(Hahn–Mazurkiewicz). Here (d) ⇒ (b) is proved instead from Corollary 2.9(2)(d) (capture by images
of paths, `IsCurveSpace.capturesPath`), which only needs local path connectedness of Peano
continua.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

universe u

namespace MosaicSpaces

variable {X : Type u} [TopologicalSpace X]

/-- A family `Ps` *determines* `X`: a set meeting every member in a relatively closed set is
closed. -/
def Determines (Ps : Set (Set X)) : Prop :=
  ∀ F : Set X, (∀ P ∈ Ps, IsClosed ((Subtype.val : P → X) ⁻¹' F)) → IsClosed F

/-- `X` is *path-determined*: it is determined by the images of paths. -/
def IsPathDetermined (X : Type u) [TopologicalSpace X] : Prop :=
  Determines {P : Set X | IsPathImage P}

/-- Condition (b) of Proposition 2.10: closedness is tested by preimages under paths. -/
def ClosedTestedByPaths (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ F : Set X, (∀ γ : C(unitInterval, X), IsClosed (γ ⁻¹' F)) → IsClosed F

/-- Condition (c) of Proposition 2.10: `X` is a quotient of a topological sum of copies of
`[0,1]`. -/
def IsQuotientOfIntervals (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (ι : Type u) (q : (Σ _ : ι, unitInterval) → X), IsQuotientMap q

/-- For a path `γ` in a Hausdorff space, `F ∩ range γ` is closed in `range γ` iff `γ⁻¹ F` is
closed. -/
theorem isClosed_preimage_val_range_iff [T2Space X] (γ : C(unitInterval, X)) (F : Set X) :
    IsClosed ((Subtype.val : range γ → X) ⁻¹' F) ↔ IsClosed (γ ⁻¹' F) := by
  let g : unitInterval → range γ := rangeFactorization γ
  have hg : Continuous g := γ.continuous.rangeFactorization
  have hgs : Function.Surjective g := rangeFactorization_surjective
  have hcl : IsClosedMap g := hg.isClosedMap
  have hpre : γ ⁻¹' F = g ⁻¹' ((Subtype.val : range γ → X) ⁻¹' F) := rfl
  constructor
  · intro h; rw [hpre]; exact h.preimage hg
  · intro h
    rw [← hgs.image_preimage ((Subtype.val : range γ → X) ⁻¹' F), ← hpre]
    exact hcl _ h

theorem isPathDetermined_iff_closedTestedByPaths [T2Space X] :
    IsPathDetermined X ↔ ClosedTestedByPaths X := by
  constructor
  · intro ha F hF
    refine ha F fun P ⟨a, b, γ, hγ⟩ => ?_
    subst hγ
    exact (isClosed_preimage_val_range_iff γ.toContinuousMap F).2 (hF _)
  · intro hb F hF
    refine hb F fun γ => ?_
    exact (isClosed_preimage_val_range_iff γ F).1
      (hF _ ⟨γ 0, γ 1, ⟨γ, rfl, rfl⟩, rfl⟩)

/-- (c) ⇒ (b) for a topological sum of copies of `[0,1]` indexed by a type in any universe. -/
theorem ClosedTestedByPaths.of_isQuotientMap {ι : Type*} {q : (Σ _ : ι, unitInterval) → X}
    (hq : IsQuotientMap q) : ClosedTestedByPaths X := by
  intro F hF
  refine (hq.isClosed_preimage).1 (isClosed_sigma_iff.2 fun i => ?_)
  exact hF ⟨fun t => q ⟨i, t⟩, hq.continuous.comp continuous_sigmaMk⟩

theorem closedTestedByPaths_iff_isQuotientOfIntervals :
    ClosedTestedByPaths X ↔ IsQuotientOfIntervals X := by
  constructor
  · intro hb
    let q : (Σ _ : C(unitInterval, X), unitInterval) → X := fun p => p.1 p.2
    refine ⟨C(unitInterval, X), q, isQuotientMap_iff_isClosed.2 ⟨fun x =>
      ⟨⟨ContinuousMap.const _ x, 0⟩, rfl⟩, fun s => ⟨fun hs => ?_, fun hs => hb s fun γ => ?_⟩⟩⟩
    · exact hs.preimage (continuous_sigma fun γ => γ.continuous)
    · exact isClosed_sigma_iff.1 hs γ
  · rintro ⟨ι, q, hq⟩
    exact ClosedTestedByPaths.of_isQuotientMap hq

/-- Condition (b) implies that `X` is sequential. -/
theorem ClosedTestedByPaths.sequentialSpace (hb : ClosedTestedByPaths X) : SequentialSpace X := by
  refine ⟨fun s hs => hb s fun γ => ?_⟩
  refine IsSeqClosed.isClosed fun {u t} hu ht => ?_
  exact hs hu ((γ.continuous.tendsto t).comp ht)

/-- (a) ⇒ (d): the images of paths form a mosaic of Peano continua. -/
theorem IsPathDetermined.isCurveSpace [T2Space X] (ha : IsPathDetermined X) : IsCurveSpace X := by
  have := (isPathDetermined_iff_closedTestedByPaths.1 ha).sequentialSpace
  refine ⟨{P : Set X | IsPathImage P}, ⟨fun x => ⟨_, ⟨x, x, Path.refl x, rfl⟩, ⟨0, rfl⟩⟩, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨a, b, γ, rfl⟩
    exact (isCompact_range γ.continuous).isClosed
  · intro M hM
    refine ha M fun P hP => ?_
    have h := (hM P hP).preimage (continuous_subtype_val (p := (· ∈ P)))
    have e : (Subtype.val : P → X) ⁻¹' (M ∩ P) = (Subtype.val : P → X) ⁻¹' M := by
      ext x; simp
    rwa [e] at h
  · rintro _ ⟨a, b, γ, rfl⟩
    exact isPeanoContinuum_range_path uniqueSeqLimits_of_t2 γ

/-- (d) ⇒ (b), via capture by images of paths. -/
theorem IsCurveSpace.closedTestedByPaths [T2Space X] (hd : IsCurveSpace X) :
    ClosedTestedByPaths X := by
  have := hd.isQuasiCurveSpace.isMosaicSpace.sequentialSpace
  intro F hF
  refine IsSeqClosed.isClosed fun {u x} huF hu => ?_
  obtain ⟨L, ⟨a, b, γ, rfl⟩, ⟨s₀, hs₀⟩, φ, hφ, hφL⟩ := hd.capturesPath u x hu
  choose t ht using hφL
  obtain ⟨s, -, ψ, hψ, hts⟩ := isCompact_univ.tendsto_subseq (x := t) fun n => mem_univ _
  have h1 : Tendsto (γ ∘ t ∘ ψ) atTop (𝓝 (γ s)) := (γ.continuous.tendsto s).comp hts
  have h2 : Tendsto (γ ∘ t ∘ ψ) atTop (𝓝 x) := by
    have : γ ∘ t ∘ ψ = u ∘ φ ∘ ψ := funext fun n => ht (ψ n)
    rw [this]
    exact hu.comp (hφ.comp hψ).tendsto_atTop
  have hsx : γ s = x := tendsto_nhds_unique h1 h2
  have hcl : IsClosed (γ.toContinuousMap ⁻¹' F) := hF _
  have hmem : s ∈ γ.toContinuousMap ⁻¹' F :=
    hcl.mem_of_tendsto hts (Eventually.of_forall fun n => by
      show γ (t (ψ n)) ∈ F
      rw [ht]; exact huF _)
  rw [← hsx]; exact hmem

/-- **Proposition 2.10.** For a Hausdorff space: path-determined ⇔ closedness tested by paths ⇔
quotient of a sum of intervals ⇔ curve space ⇔ quasi-curve space. -/
theorem prop_2_10_tfae [T2Space X] :
    [IsPathDetermined X, ClosedTestedByPaths X, IsQuotientOfIntervals X, IsCurveSpace X,
      IsQuasiCurveSpace X].TFAE := by
  tfae_have 1 ↔ 2 := isPathDetermined_iff_closedTestedByPaths
  tfae_have 2 ↔ 3 := closedTestedByPaths_iff_isQuotientOfIntervals
  tfae_have 1 → 4 := IsPathDetermined.isCurveSpace
  tfae_have 4 → 2 := IsCurveSpace.closedTestedByPaths
  tfae_have 4 → 5 := IsCurveSpace.isQuasiCurveSpace
  tfae_have 5 → 4 := fun h => ((isQuasiCurveSpace_tfae h.isMosaicSpace).out 1 2).1 h
  tfae_finish

end MosaicSpaces
