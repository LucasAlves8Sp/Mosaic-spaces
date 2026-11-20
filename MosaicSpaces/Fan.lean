module

public import MosaicSpaces.PathComponents
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Null fans (article: Section 4.2, facts (F1)–(F4))

The article defines `Fan(I)` for a countable set `I` as `{o} ∪ I × (0,1]` with the metric
`φ`, which makes it isometric to a subset of `ℓ¹(I)`. Here `Fan J` is the subspace of `J → ℝ`
(product topology) of the functions with values in `[0,1]` and at most one nonzero value; the
point `t·δ_j` corresponds to the article's `(j, t)` and `0` to the centre `o`.

The two topologies agree: `Fan.isOpen_iff_phi` (`MosaicSpaces.FanMetric`) proves that for every
injection `ν` the product topology of `Fan J` is the topology of the article's metric `φ`. This
module proves what is used later:

* `Fan` is compact; it is metrizable when `J` is countable (F2).
* `Fan.tendsto_centre`: points on pairwise distinct spines converge to the centre (F3).
* `Fan.finite_spines_of_isClosed`: a closed set missing the centre meets only finitely many
  spines (used for Lemma 4.4).
* `Fan.locallyPathConnectedSpace`, `Fan.pathConnectedSpace` (F2).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval

namespace MosaicSpaces

universe u

/-- The underlying set of the null fan with spines indexed by `J`. -/
def fan (J : Type u) : Set (J → ℝ) :=
  {f | (∀ j, f j ∈ Icc (0 : ℝ) 1) ∧ ∀ j j', j ≠ j' → f j = 0 ∨ f j' = 0}

/-- The null fan `Fan(J)`. -/
abbrev Fan (J : Type u) := ↥(fan J)

namespace Fan

variable {J : Type u}

theorem isClosed_fan : IsClosed (fan J) := by
  have e : fan J = (⋂ j, (fun f : J → ℝ => f j) ⁻¹' Icc 0 1) ∩
      ⋂ j, ⋂ j', ⋂ (_ : j ≠ j'), ({f : J → ℝ | f j = 0} ∪ {f | f j' = 0}) := by
    ext f
    simp only [fan, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_union]
  rw [e]
  refine (isClosed_iInter fun j => isClosed_Icc.preimage (continuous_apply j)).inter
    (isClosed_iInter fun j => isClosed_iInter fun j' => isClosed_iInter fun _ => ?_)
  exact (isClosed_eq (continuous_apply j) continuous_const).union
    (isClosed_eq (continuous_apply j') continuous_const)

theorem isCompact_fan : IsCompact (fan J) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset isClosed_fan
    fun _ hf j _ => hf.1 j

instance : CompactSpace (Fan J) := isCompact_iff_compactSpace.1 isCompact_fan

instance [Countable J] : MetrizableSpace (Fan J) := inferInstance

theorem coe_mem_Icc (f : Fan J) (j : J) : (f : J → ℝ) j ∈ Icc (0 : ℝ) 1 := f.2.1 j

theorem eq_zero_of_ne {f : Fan J} {j j' : J} (h : j ≠ j') (hj : (f : J → ℝ) j ≠ 0) :
    (f : J → ℝ) j' = 0 :=
  (f.2.2 j j' h).resolve_left hj

/-- The centre `o`. -/
def centre : Fan J := ⟨0, fun _ => ⟨le_rfl, zero_le_one⟩, fun _ _ _ => Or.inl rfl⟩

@[simp] theorem coe_centre : ((centre : Fan J) : J → ℝ) = 0 := rfl

open Classical in
/-- The point at height `t` on the spine `j`. -/
noncomputable def spine (j : J) (t : I) : Fan J :=
  ⟨Pi.single j (t : ℝ), fun i => by
    by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same]
      exact t.2
    · simp only [Pi.single_eq_of_ne h]
      exact ⟨le_rfl, zero_le_one⟩, fun i i' hii' => by
    by_cases h : i = j
    · subst h
      exact Or.inr (Pi.single_eq_of_ne hii'.symm _)
    · exact Or.inl (Pi.single_eq_of_ne h _)⟩

open Classical in
theorem coe_spine (j : J) (t : I) : ((spine j t : Fan J) : J → ℝ) = Pi.single j (t : ℝ) := rfl

theorem spine_apply_self (j : J) (t : I) : ((spine j t : Fan J) : J → ℝ) j = t := by
  classical
  simp [coe_spine]

theorem spine_apply_ne {j i : J} (h : i ≠ j) (t : I) : ((spine j t : Fan J) : J → ℝ) i = 0 := by
  classical
  simp [coe_spine, h]

theorem spine_zero (j : J) : spine j 0 = (centre : Fan J) := by
  classical
  apply Subtype.ext
  funext i
  by_cases h : i = j
  · subst h
    simp [spine_apply_self]
  · simp [spine_apply_ne h]

/-- Every point other than the centre lies on a unique spine. -/
theorem eq_spine {f : Fan J} {j : J} (hj : (f : J → ℝ) j ≠ 0) :
    f = spine j ⟨(f : J → ℝ) j, coe_mem_Icc f j⟩ := by
  apply Subtype.ext
  funext i
  by_cases h : i = j
  · subst h
    rw [spine_apply_self]
  · rw [spine_apply_ne h, eq_zero_of_ne (Ne.symm h) hj]

theorem eq_of_apply_eq {g g' : Fan J} {j : J} (hj : (g : J → ℝ) j ≠ 0)
    (h : (g : J → ℝ) j = (g' : J → ℝ) j) : g = g' := by
  have hj' : (g' : J → ℝ) j ≠ 0 := h ▸ hj
  apply Subtype.ext
  funext i
  by_cases hi : i = j
  · subst hi
    exact h
  · rw [eq_zero_of_ne (Ne.symm hi) hj, eq_zero_of_ne (Ne.symm hi) hj']

theorem eq_centre_or_spine (f : Fan J) : f = centre ∨ ∃ j, (f : J → ℝ) j ≠ 0 := by
  by_cases h : ∃ j, (f : J → ℝ) j ≠ 0
  · exact Or.inr h
  · push_neg at h
    exact Or.inl (Subtype.ext (funext h))


theorem continuous_spine (j : J) : Continuous (spine j : I → Fan J) := by
  classical
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  by_cases h : i = j
  · subst h
    simp only [Pi.single_eq_same]
    exact continuous_subtype_val
  · simp only [Pi.single_eq_of_ne h]
    exact continuous_const

theorem spine_injective_right (j : J) : Function.Injective (spine j : I → Fan J) := by
  intro t t' h
  have := congrArg (fun f : Fan J => (f : J → ℝ) j) h
  simp only [spine_apply_self] at this
  exact Subtype.ext this

theorem centre_or_spine (f : Fan J) : f = centre ∨ ∃ j, ∃ t : I, (t : ℝ) ≠ 0 ∧ f = spine j t := by
  rcases eq_centre_or_spine f with h | ⟨j, hj⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, _, hj, eq_spine hj⟩

theorem spine_ne_centre {j : J} {t : I} (ht : (t : ℝ) ≠ 0) : spine j t ≠ centre := fun h => by
  have := congrArg (fun f : Fan J => (f : J → ℝ) j) h
  simp only [spine_apply_self, coe_centre, Pi.zero_apply] at this
  exact ht this

theorem spine_inj {j j' : J} {t t' : I} (ht : (t : ℝ) ≠ 0) (h : spine j t = spine j' t') :
    j = j' ∧ t = t' := by
  have hj : j = j' := by
    by_contra hne
    have := congrArg (fun f : Fan J => (f : J → ℝ) j) h
    simp only [spine_apply_self, spine_apply_ne hne] at this
    exact ht this
  subst hj
  exact ⟨rfl, spine_injective_right j h⟩

/-! ### Maps out of a fan defined spine by spine -/

open Classical in
/-- The map `Fan J → Y` which is `g j` on the spine `j` (all `g j` agree at `0`, with value
`c`). -/
noncomputable def fanLift {Y : Type*} (g : J → I → Y) (c : Y) (f : Fan J) : Y :=
  if h : ∃ j, (f : J → ℝ) j ≠ 0 then g h.choose ⟨(f : J → ℝ) h.choose, coe_mem_Icc f _⟩ else c

section fanLift

variable {Y : Type*} {g : J → I → Y} {c : Y}

theorem fanLift_centre : fanLift g c centre = c := by
  simp [fanLift]

theorem fanLift_spine (hg : ∀ j, g j 0 = c) (j : J) (t : I) : fanLift g c (spine j t) = g j t := by
  by_cases ht : (t : ℝ) = 0
  · have : t = 0 := Subtype.ext ht
    subst this
    rw [spine_zero, fanLift_centre, hg]
  · have h : ∃ j', ((spine j t : Fan J) : J → ℝ) j' ≠ 0 := ⟨j, by rw [spine_apply_self]; exact ht⟩
    have hj : h.choose = j := by
      by_contra hne
      exact h.choose_spec (spine_apply_ne hne t)
    rw [fanLift, dif_pos h]
    have key : ∀ j' (_ : j' = j) (pf : ((spine j t : Fan J) : J → ℝ) j' ∈ Icc (0 : ℝ) 1),
        g j' ⟨_, pf⟩ = g j t := by
      intro j' hj' pf
      subst hj'
      exact congrArg (g _) (Subtype.ext (spine_apply_self _ t))
    exact key _ hj _

theorem fanLift_injective (hg : ∀ j, g j 0 = c) (hc : ∀ j (t : I), (t : ℝ) ≠ 0 → g j t ≠ c)
    (hinj : ∀ j j' (t t' : I), (t : ℝ) ≠ 0 → (t' : ℝ) ≠ 0 → g j t = g j' t' → j = j' ∧ t = t') :
    Function.Injective (fanLift g c) := by
  intro f f' h
  rcases centre_or_spine f with rfl | ⟨j, t, ht, rfl⟩ <;>
    rcases centre_or_spine f' with rfl | ⟨j', t', ht', rfl⟩
  · rfl
  · rw [fanLift_centre, fanLift_spine hg] at h
    exact absurd h.symm (hc j' t' ht')
  · rw [fanLift_centre, fanLift_spine hg] at h
    exact absurd h (hc j t ht)
  · rw [fanLift_spine hg, fanLift_spine hg] at h
    obtain ⟨rfl, rfl⟩ := hinj j j' t t' ht ht' h
    rfl

end fanLift

/-- **(F3)**: points whose nonzero coordinates sit on pairwise distinct spines converge to the
centre. Stated as: every coordinate is nonzero for only finitely many terms. -/
theorem tendsto_centre {f : ℕ → Fan J} (hf : ∀ j, {k | ((f k : Fan J) : J → ℝ) j ≠ 0}.Finite) :
    Tendsto f atTop (𝓝 centre) := by
  refine tendsto_subtype_rng.2 (tendsto_pi_nhds.2 fun j => ?_)
  refine tendsto_const_nhds.congr' ?_
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [(hf j).eventually_cofinite_notMem] with k hk
  simp only [mem_setOf_eq, not_not] at hk
  exact hk.symm

/-- A closed set not containing the centre meets only finitely many spines (used for
Lemma 4.4(1),(2)). -/
theorem finite_spines_of_isClosed {C : Set (Fan J)} (hC : IsClosed C) (hc : centre ∉ C) :
    {j | ∃ f ∈ C, (f : J → ℝ) j ≠ 0}.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  have hex : ∀ k, ∃ f ∈ C, (f : J → ℝ) (e k).1 ≠ 0 := fun k => (e k).2
  choose f hfC hf using hex
  have hfin : ∀ j, {k | ((f k : Fan J) : J → ℝ) j ≠ 0}.Finite := by
    intro j
    refine Set.Subsingleton.finite fun k hk k' hk' => ?_
    have h1 : (e k).1 = j := by
      by_contra hne
      exact hk (eq_zero_of_ne hne (hf k))
    have h2 : (e k').1 = j := by
      by_contra hne
      exact hk' (eq_zero_of_ne hne (hf k'))
    exact e.injective (Subtype.ext (h1.trans h2.symm))
  exact hc (hC.mem_of_tendsto (tendsto_centre hfin) (Eventually.of_forall hfC))

/-! ### Scaling towards the centre, path connectedness, local path connectedness -/

/-- The point `s • f` (`s ∈ [0,1]`). -/
def smul (s : I) (f : Fan J) : Fan J :=
  ⟨(s : ℝ) • (f : J → ℝ), fun j => by
    have h1 := coe_mem_Icc f j
    have h2 := s.2
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2], fun j j' h => by
    rcases f.2.2 j j' h with h' | h'
    · exact Or.inl (by simp [h'])
    · exact Or.inr (by simp [h'])⟩

theorem continuous_smul : Continuous fun p : I × Fan J => smul p.1 p.2 :=
  Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)) _

theorem smul_one (f : Fan J) : smul 1 f = f := Subtype.ext (by simp [smul])

theorem smul_zero (f : Fan J) : smul 0 f = centre := Subtype.ext (by simp [smul])

theorem smul_smul (s t : I) (f : Fan J) : smul s (smul t f) = smul (s * t) f :=
  Subtype.ext (by simp [smul, mul_smul])

theorem smul_centre (s : I) : smul s (centre : Fan J) = centre := Subtype.ext (by simp [smul])

/-- The segment from `f` to the centre. -/
def segment (f : Fan J) : Path f centre where
  toFun s := smul (σ s) f
  continuous_toFun := continuous_smul.comp ((continuous_symm).prodMk continuous_const)
  source' := by simp [smul_one]
  target' := by simp [smul_zero]

theorem segment_apply (f : Fan J) (s : I) : segment f s = smul (σ s) f := rfl

/-- A set stable under scaling is path connected if it contains the centre. -/
theorem isPathConnected_of_smul_mem {W : Set (Fan J)} (h0 : centre ∈ W)
    (hW : ∀ f ∈ W, ∀ s : I, smul s f ∈ W) : IsPathConnected W := by
  refine ⟨centre, h0, fun {f} hf => ?_⟩
  exact (JoinedIn.symm ⟨segment f, fun s => hW f hf _⟩)

theorem pathConnectedSpace : PathConnectedSpace (Fan J) := by
  refine pathConnectedSpace_iff_univ.2 ?_
  exact isPathConnected_of_smul_mem (mem_univ _) fun _ _ _ => mem_univ _

/-- **(F2)**: the fan is locally path connected. -/
theorem locallyPathConnectedSpace : LocallyPathConnectedSpace (Fan J) := by
  rw [← locallyPathConnectedOpen_iff]
  intro f O hO hfO
  rcases eq_centre_or_spine f with rfl | ⟨j, hj⟩
  · -- near the centre: points whose segment to the centre stays in `O`
    let W : Set (Fan J) := {g | ∀ s : I, smul s g ∈ O}
    have hWc : IsClosed Wᶜ := by
      have e : Wᶜ = Prod.snd '' ((fun p : I × Fan J => smul p.1 p.2) ⁻¹' Oᶜ) := by
        ext g
        simp only [W, mem_compl_iff, mem_setOf_eq, not_forall, mem_image, mem_preimage,
          Prod.exists, exists_and_right, exists_eq_right]
      rw [e]
      exact isClosedMap_snd_of_compactSpace _ (hO.isClosed_compl.preimage continuous_smul)
    refine ⟨W, isClosed_compl_iff.1 hWc, fun s => by rw [smul_centre]; exact hfO,
      fun g hg => by simpa [smul_one] using hg 1, ?_⟩
    refine isPathConnected_of_smul_mem (fun s => by rw [smul_centre]; exact hfO) ?_
    intro g hg s t
    rw [smul_smul]
    exact hg _
  · -- on a spine, away from the centre
    have ht : 0 < (f : J → ℝ) j := lt_of_le_of_ne (coe_mem_Icc f j).1 (Ne.symm hj)
    let t : I := ⟨(f : J → ℝ) j, coe_mem_Icc f j⟩
    have hft : f = spine j t := eq_spine hj
    have hpre : IsOpen (spine j ⁻¹' O) := hO.preimage (continuous_spine j)
    have htO : t ∈ spine j ⁻¹' O := by
      show spine j t ∈ O
      rw [← hft]
      exact hfO
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hpre t htO
    let δ' : ℝ := min δ ((f : J → ℝ) j)
    have hδ' : 0 < δ' := lt_min hδ ht
    let W : Set (Fan J) := {g | |(g : J → ℝ) j - (f : J → ℝ) j| < δ'}
    have hWo : IsOpen W :=
      isOpen_lt (continuous_abs.comp (((continuous_apply j).comp continuous_subtype_val).sub
        continuous_const)) continuous_const
    have hpos : ∀ g ∈ W, 0 < (g : J → ℝ) j := by
      intro g hg
      have h1 : |(g : J → ℝ) j - (f : J → ℝ) j| < (f : J → ℝ) j :=
        lt_of_lt_of_le hg (min_le_right _ _)
      have := (abs_lt.1 h1).1
      linarith
    have hspW : ∀ g ∈ W, g = spine j ⟨(g : J → ℝ) j, coe_mem_Icc g j⟩ :=
      fun g hg => eq_spine (hpos g hg).ne'
    have hWO : W ⊆ O := by
      intro g hg
      rw [hspW g hg]
      refine hball ?_
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      exact lt_of_lt_of_le hg (min_le_left _ _)
    have hfW : f ∈ W := by simp [W, hδ']
    refine ⟨W, hWo, hfW, hWO, ?_⟩
    -- `W` is an interval of the spine
    refine ⟨f, hfW, fun {g} hg => ?_⟩
    let a := (f : J → ℝ) j
    let b := (g : J → ℝ) j
    let γ : ℝ → Fan J := fun s =>
      spine j (Set.projIcc (0 : ℝ) 1 zero_le_one ((1 - s) * a + s * b))
    have hγc : Continuous γ := (continuous_spine j).comp
      (continuous_projIcc.comp ((continuous_const.sub continuous_id).mul continuous_const |>.add
        (continuous_id.mul continuous_const)))
    have hab : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s) * a + s * b ∈ Icc (0 : ℝ) 1 := by
      intro s hs
      have ha := coe_mem_Icc f j
      have hb := coe_mem_Icc g j
      constructor <;> nlinarith [hs.1, hs.2, ha.1, ha.2, hb.1, hb.2]
    have hval : ∀ s ∈ Icc (0 : ℝ) 1, ((γ s : Fan J) : J → ℝ) j = (1 - s) * a + s * b := by
      intro s hs
      simp only [γ, spine_apply_self, Set.projIcc_of_mem _ (hab s hs)]
    refine JoinedIn.ofLine hγc.continuousOn ?_ ?_ ?_
    · have h0 := hval 0 ⟨le_rfl, zero_le_one⟩
      rw [show (1 - (0:ℝ)) * a + 0 * b = a by ring] at h0
      exact eq_of_apply_eq (h0 ▸ hj) h0
    · have h1 := hval 1 ⟨zero_le_one, le_rfl⟩
      rw [show (1 - (1:ℝ)) * a + 1 * b = b by ring] at h1
      exact eq_of_apply_eq (h1 ▸ (hpos g hg).ne') h1
    · rintro _ ⟨s, hs, rfl⟩
      show |((γ s : Fan J) : J → ℝ) j - a| < δ'
      rw [hval s hs]
      have hgb : |b - a| < δ' := hg
      have : (1 - s) * a + s * b - a = s * (b - a) := by ring
      rw [this, abs_mul, abs_of_nonneg hs.1]
      calc s * |b - a| ≤ 1 * |b - a| := by
            exact mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
        _ = |b - a| := one_mul _
        _ < δ' := hgb

end Fan

end MosaicSpaces
