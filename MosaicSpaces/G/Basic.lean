module

public import MosaicSpaces.Fan

/-!
# The space `G` (article: Construction 4.1 and Lemma 4.2)

* `IsC`: the family `𝒞` of infinite subsets of `M = ℕ × ℕ` with finite sections.
* `IsMADFamily 𝒟`: `𝒟 ⊆ 𝒞`, pairwise almost disjoint, and maximal in the form (4.1)
  ("every `Y ∈ 𝒞` meets some `D ∈ 𝒟` in an infinite set"). `exists_isMADFamily` constructs one
  by Zorn's lemma; it is not assumed.
* `GSpace 𝒟`: the underlying set of `G` as an inductive type, with the five kinds of points of the
  article: `∞`, the points `p_D`, the rows `ℕ × [0,1]`, the open arcs `𝒟 × (0,1)` and the open
  spokes `(D, m, t)`.
* The topology of `G` is the final topology of the piece maps `rowMap n` (P1), `sigMap` (P2),
  `phiMap D` (P3) and `lamMap S` for countable `S ⊆ 𝒟` (P4). This is the mosaic topology of the
  article. `isMosaicFamily_pieces` proves that the ranges of the piece maps form a mosaic family of
  compact metrizable subspaces, i.e. Lemma 4.2, and in particular `G` is a mosaic space.

Indexing conventions (differences from the article, which are only notational):
* the article's witness `(n, i)` with `i ≥ 1` sits at `R_n(1/i)`; here `i ∈ ℕ` starts at `0` and
  the witness `(n, i)` sits at `R_n(1/(i+1))` (`witT i`);
* the article's arc `a_D` runs from `p_D` to `∞`; `arcMap D` runs from `∞` (at `0`) to `p_D`
  (at `1`), which is the parametrisation used by the article for the spines of `Λ_S`;
* empty `S` is allowed in (P4); `Λ_∅ = {∞}`, which changes nothing.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval Function

namespace MosaicSpaces

/-! ### Almost disjoint families -/

/-- The family `𝒞` of the article: infinite subsets of `ℕ × ℕ` all of whose sections
`{i | (n, i) ∈ Y}` are finite. -/
def IsC (Y : Set (ℕ × ℕ)) : Prop :=
  Y.Infinite ∧ ∀ n, {i | (n, i) ∈ Y}.Finite

/-- A maximal almost disjoint subfamily of `𝒞`, in the form used by the article (display (4.1)). -/
structure IsMADFamily (𝒟 : Set (Set (ℕ × ℕ))) : Prop where
  mem : ∀ D ∈ 𝒟, IsC D
  almostDisjoint : 𝒟.Pairwise fun D D' => (D ∩ D').Finite
  maximal : ∀ Y, IsC Y → ∃ D ∈ 𝒟, (D ∩ Y).Infinite

/-- Existence of a maximal almost disjoint family (Zorn's lemma). -/
theorem exists_isMADFamily : ∃ 𝒟, IsMADFamily 𝒟 := by
  let S : Set (Set (Set (ℕ × ℕ))) :=
    {𝒜 | (∀ D ∈ 𝒜, IsC D) ∧ 𝒜.Pairwise fun D D' => (D ∩ D').Finite}
  obtain ⟨𝒟, h𝒟⟩ := zorn_subset S fun c hcS hc => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · rintro D ⟨𝒜, h𝒜, hD⟩
      exact (hcS h𝒜).1 D hD
    · rintro D ⟨𝒜, h𝒜, hD⟩ D' ⟨𝒜', h𝒜', hD'⟩ hne
      rcases hc.total h𝒜 h𝒜' with h | h
      · exact (hcS h𝒜').2 (h hD) hD' hne
      · exact (hcS h𝒜).2 hD (h hD') hne
  refine ⟨𝒟, h𝒟.prop.1, h𝒟.prop.2, fun Y hY => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hfin : ∀ D ∈ 𝒟, (D ∩ Y).Finite := fun D hD => hcon D hD
  have hins : insert Y 𝒟 ∈ S := by
    refine ⟨?_, ?_⟩
    · rintro D (rfl | hD)
      · exact hY
      · exact h𝒟.prop.1 D hD
    · refine h𝒟.prop.2.insert fun D hD _ => ⟨?_, hfin D hD⟩
      rw [inter_comm]
      exact hfin D hD
  have he := h𝒟.eq_of_subset hins (subset_insert _ _)
  have hY𝒟 : Y ∈ 𝒟 := by
    rw [he]
    exact mem_insert _ _
  have := hfin Y hY𝒟
  rw [inter_self] at this
  exact hY.1 this

theorem IsC.finite_fst {D : Set (ℕ × ℕ)} (hD : IsC D) (n : ℕ) : {m | m ∈ D ∧ m.1 = n}.Finite := by
  refine ((hD.2 n).image fun i => (n, i)).subset ?_
  rintro ⟨n', i⟩ ⟨h, rfl⟩
  exact ⟨i, h, rfl⟩

/-! ### A general closedness criterion -/

theorem isClosed_preimage_image_of_finite {X P Q : Type*} [TopologicalSpace P] [T1Space P]
    {f : P → X} {g : Q → X} (hf : Injective f) {A B : Set X} (hfA : range f ⊆ A)
    (hgB : range g ⊆ B) (hAB : (A ∩ B).Finite) (C : Set Q) : IsClosed (f ⁻¹' (g '' C)) := by
  refine ((hAB.preimage hf.injOn).subset ?_).isClosed
  rintro x ⟨c, -, hc⟩
  exact ⟨hfA ⟨x, rfl⟩, hc ▸ hgB ⟨c, rfl⟩⟩

/-! ### The underlying set -/

/-- The points of `G` (Construction 4.1). -/
inductive GSpace (𝒟 : Set (Set (ℕ × ℕ))) : Type
  /-- The point `∞`. -/
  | infty : GSpace 𝒟
  /-- The point `p_D`. -/
  | pnt (D : 𝒟) : GSpace 𝒟
  /-- The point `R_n(t)` of the row `n`. -/
  | row (n : ℕ) (t : I) : GSpace 𝒟
  /-- An interior point of the arc `A_D`. -/
  | arc (D : 𝒟) (t : Ioo (0 : ℝ) 1) : GSpace 𝒟
  /-- An interior point `(D, m, t)` of the spoke `E_{D,m}`. -/
  | spoke (D : 𝒟) (m : (D : Set (ℕ × ℕ))) (t : Ioo (0 : ℝ) 1) : GSpace 𝒟

namespace GSpace

variable {𝒟 : Set (Set (ℕ × ℕ))}

/-- The position `1/(i+1)` of the witness `(n, i)` on the row `n`. -/
noncomputable def witT (i : ℕ) : I :=
  ⟨1 / ((i : ℝ) + 1), by positivity, by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]⟩

theorem witT_coe (i : ℕ) : (witT i : ℝ) = 1 / ((i : ℝ) + 1) := rfl

theorem witT_ne_zero (i : ℕ) : (witT i : ℝ) ≠ 0 := by
  rw [witT_coe]
  positivity

theorem witT_lt_iff {i j : ℕ} : (witT i : ℝ) < witT j ↔ j < i := by
  rw [witT_coe, witT_coe, one_div_lt_one_div (by positivity) (by positivity)]
  simp

theorem witT_le_iff {i j : ℕ} : (witT i : ℝ) ≤ witT j ↔ j ≤ i := by
  rw [witT_coe, witT_coe, one_div_le_one_div (by positivity) (by positivity)]
  simp

theorem witT_injective : Injective witT := by
  intro i j h
  apply le_antisymm
  · exact witT_le_iff.1 (le_of_eq (congrArg Subtype.val h).symm)
  · exact witT_le_iff.1 (le_of_eq (congrArg Subtype.val h))

theorem exists_witT_lt {ε : ℝ} (hε : 0 < ε) : ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → (witT i : ℝ) < ε := by
  obtain ⟨i₀, hi₀⟩ := exists_nat_one_div_lt hε
  exact ⟨i₀, fun i hi => lt_of_le_of_lt (witT_le_iff.2 hi) hi₀⟩

/-- The witness `m = (n, i)`, the point `R_n(1/(i+1))`. -/
noncomputable def wit (m : ℕ × ℕ) : GSpace 𝒟 := row m.1 (witT m.2)

theorem wit_injective : Injective (wit : ℕ × ℕ → GSpace 𝒟) := by
  rintro ⟨n, i⟩ ⟨n', i'⟩ h
  simp only [wit, row.injEq] at h
  rw [h.1, witT_injective h.2]

/-- The point `x_n = R_n(0)`. -/
def xpt (n : ℕ) : GSpace 𝒟 := row n 0

theorem wit_ne_xpt (m : ℕ × ℕ) (n : ℕ) : (wit m : GSpace 𝒟) ≠ xpt n := by
  intro h
  simp only [wit, xpt, row.injEq] at h
  exact witT_ne_zero _ (congrArg Subtype.val h.2)

/-- An interior point of `[0,1]` as a point of `(0,1)`. -/
def toIoo (t : I) (h0 : (t : ℝ) ≠ 0) (h1 : (t : ℝ) ≠ 1) : Ioo (0 : ℝ) 1 :=
  ⟨t, lt_of_le_of_ne t.2.1 (Ne.symm h0), lt_of_le_of_ne t.2.2 h1⟩

/-! ### Parametrisations -/

open Classical in
/-- The arc `A_D`, from `∞` (at `0`) to `p_D` (at `1`). -/
noncomputable def arcMap (D : 𝒟) (t : I) : GSpace 𝒟 :=
  if h0 : (t : ℝ) = 0 then infty else if h1 : (t : ℝ) = 1 then pnt D else arc D (toIoo t h0 h1)

open Classical in
/-- The spoke `E_{D,m}`, from `p_D` (at `0`) to the witness `m` (at `1`). -/
noncomputable def spokeMap (D : 𝒟) (m : (D : Set (ℕ × ℕ))) (t : I) : GSpace 𝒟 :=
  if h0 : (t : ℝ) = 0 then pnt D else if h1 : (t : ℝ) = 1 then wit m else spoke D m (toIoo t h0 h1)

theorem arcMap_zero (D : 𝒟) : arcMap D 0 = infty := by simp [arcMap]

theorem arcMap_one (D : 𝒟) : arcMap D 1 = pnt D := by simp [arcMap]

theorem arcMap_of_ne (D : 𝒟) {t : I} (h0 : (t : ℝ) ≠ 0) (h1 : (t : ℝ) ≠ 1) :
    arcMap D t = arc D (toIoo t h0 h1) := by
  simp [arcMap, h0, h1]

theorem spokeMap_zero (D : 𝒟) (m : (D : Set (ℕ × ℕ))) : spokeMap D m 0 = pnt D := by
  simp [spokeMap]

theorem spokeMap_one (D : 𝒟) (m : (D : Set (ℕ × ℕ))) : spokeMap D m 1 = wit m := by
  simp [spokeMap]

theorem spokeMap_of_ne (D : 𝒟) (m : (D : Set (ℕ × ℕ))) {t : I} (h0 : (t : ℝ) ≠ 0)
    (h1 : (t : ℝ) ≠ 1) : spokeMap D m t = spoke D m (toIoo t h0 h1) := by
  simp [spokeMap, h0, h1]

theorem eq_one_of_coe {t : I} (h1 : (t : ℝ) = 1) : t = 1 := Subtype.ext h1

theorem arcMap_cases (D : 𝒟) {t : I} (h0 : (t : ℝ) ≠ 0) :
    arcMap D t = pnt D ∨ ∃ s, arcMap D t = arc D s := by
  by_cases h1 : (t : ℝ) = 1
  · left
    rw [eq_one_of_coe h1, arcMap_one]
  · exact Or.inr ⟨_, arcMap_of_ne D h0 h1⟩

theorem spokeMap_cases (D : 𝒟) (m : (D : Set (ℕ × ℕ))) {t : I} (h0 : (t : ℝ) ≠ 0) :
    (spokeMap D m t = wit m ∧ t = 1) ∨ ∃ s, spokeMap D m t = spoke D m s ∧ (s : ℝ) = t := by
  by_cases h1 : (t : ℝ) = 1
  · left
    rw [eq_one_of_coe h1, spokeMap_one]
    exact ⟨rfl, rfl⟩
  · exact Or.inr ⟨_, spokeMap_of_ne D m h0 h1, rfl⟩

theorem arcMap_ne_infty (D : 𝒟) {t : I} (h0 : (t : ℝ) ≠ 0) : arcMap D t ≠ infty := by
  rcases arcMap_cases D h0 with h | ⟨s, h⟩ <;> rw [h] <;> simp

theorem arcMap_inj {D D' : 𝒟} {t t' : I} (h0 : (t : ℝ) ≠ 0) (h0' : (t' : ℝ) ≠ 0)
    (h : arcMap D t = arcMap D' t') : D = D' ∧ t = t' := by
  by_cases h1 : (t : ℝ) = 1 <;> by_cases h1' : (t' : ℝ) = 1
  · rw [eq_one_of_coe h1, eq_one_of_coe h1', arcMap_one, arcMap_one, pnt.injEq] at h
    exact ⟨h, (eq_one_of_coe h1).trans (eq_one_of_coe h1').symm⟩
  · rw [eq_one_of_coe h1, arcMap_one, arcMap_of_ne D' h0' h1'] at h
    simp at h
  · rw [eq_one_of_coe h1', arcMap_one, arcMap_of_ne D h0 h1] at h
    simp at h
  · rw [arcMap_of_ne D h0 h1, arcMap_of_ne D' h0' h1', arc.injEq] at h
    have e := congrArg (fun s : Ioo (0 : ℝ) 1 => (s : ℝ)) h.2
    exact ⟨h.1, Subtype.ext e⟩

theorem spokeMap_inj {D : 𝒟} {m m' : (D : Set (ℕ × ℕ))} {t t' : I} (h0 : (t : ℝ) ≠ 0)
    (h0' : (t' : ℝ) ≠ 0) (h : spokeMap D m t = spokeMap D m' t') : m = m' ∧ t = t' := by
  by_cases h1 : (t : ℝ) = 1 <;> by_cases h1' : (t' : ℝ) = 1
  · rw [eq_one_of_coe h1, eq_one_of_coe h1', spokeMap_one, spokeMap_one] at h
    exact ⟨Subtype.ext (wit_injective h), (eq_one_of_coe h1).trans (eq_one_of_coe h1').symm⟩
  · rw [eq_one_of_coe h1, spokeMap_one, spokeMap_of_ne D m' h0' h1'] at h
    simp [wit] at h
  · rw [eq_one_of_coe h1', spokeMap_one, spokeMap_of_ne D m h0 h1] at h
    simp [wit] at h
  · rw [spokeMap_of_ne D m h0 h1, spokeMap_of_ne D m' h0' h1', spoke.injEq] at h
    have e := congrArg (fun s : Ioo (0 : ℝ) 1 => (s : ℝ)) h.2.2
    exact ⟨eq_of_heq h.2.1, Subtype.ext e⟩

/-! ### The piece maps -/

/-- (P1) The row `R_n`. -/
def rowMap (n : ℕ) : I → GSpace 𝒟 := row n

/-- (P2) The convergent sequence `Σ = {∞} ∪ {x_n}`, parametrised by `ℕ ∪ {∞}`. -/
def sigMap : OnePoint ℕ → GSpace 𝒟 := fun c => c.elim infty xpt

/-- (P3) The fan `Φ_D`. -/
noncomputable def phiMap (D : 𝒟) : Fan (D : Set (ℕ × ℕ)) → GSpace 𝒟 :=
  Fan.fanLift (spokeMap D) (pnt D)

/-- (P4) The fan `Λ_S` of the arcs `A_D`, `D ∈ S`. -/
noncomputable def lamMap (S : Set 𝒟) : Fan S → GSpace 𝒟 :=
  Fan.fanLift (fun D t => arcMap D.1 t) infty

/-- The index set of the pieces (P4): countable subfamilies of `𝒟`. -/
abbrev CS (𝒟 : Set (Set (ℕ × ℕ))) := {S : Set 𝒟 // S.Countable}

theorem sigMap_infty : (sigMap (OnePoint.infty) : GSpace 𝒟) = infty := rfl

theorem sigMap_coe (n : ℕ) : (sigMap (n : OnePoint ℕ) : GSpace 𝒟) = xpt n := rfl

theorem phiMap_centre (D : 𝒟) : phiMap D Fan.centre = pnt D := Fan.fanLift_centre

theorem phiMap_spine (D : 𝒟) (m : (D : Set (ℕ × ℕ))) (t : I) :
    phiMap D (Fan.spine m t) = spokeMap D m t :=
  Fan.fanLift_spine (fun m => spokeMap_zero D m) m t

theorem lamMap_centre (S : Set 𝒟) : lamMap S Fan.centre = infty := Fan.fanLift_centre

theorem lamMap_spine (S : Set 𝒟) (D : S) (t : I) : lamMap S (Fan.spine D t) = arcMap D.1 t :=
  Fan.fanLift_spine (g := fun (D : S) t => arcMap D.1 t) (fun D => arcMap_zero D.1) D t

theorem rowMap_injective (n : ℕ) : Injective (rowMap n : I → GSpace 𝒟) := fun _ _ h => by
  simpa [rowMap] using h

theorem sigMap_injective : Injective (sigMap : OnePoint ℕ → GSpace 𝒟) := by
  intro c c'
  induction c using OnePoint.rec <;> induction c' using OnePoint.rec <;>
    simp [sigMap, xpt]

theorem phiMap_injective (D : 𝒟) : Injective (phiMap D) := by
  refine Fan.fanLift_injective (fun m => spokeMap_zero D m) (fun m t ht => ?_)
    (fun m m' t t' ht ht' h => spokeMap_inj ht ht' h)
  rcases spokeMap_cases D m ht with ⟨h, -⟩ | ⟨s, h, -⟩ <;> rw [h] <;> simp [wit]

theorem lamMap_injective (S : Set 𝒟) : Injective (lamMap S) := by
  refine Fan.fanLift_injective (fun D => arcMap_zero D.1) (fun D t ht => arcMap_ne_infty D.1 ht)
    (fun D D' t t' ht ht' h => ?_)
  obtain ⟨h1, h2⟩ := arcMap_inj ht ht' h
  exact ⟨Subtype.ext h1, h2⟩

/-! ### The topology -/

/-- The mosaic topology of `G`: the final topology of the piece maps. -/
noncomputable def gTop (𝒟 : Set (Set (ℕ × ℕ))) : TopologicalSpace (GSpace 𝒟) :=
  ((⨆ n : ℕ, TopologicalSpace.coinduced (rowMap n : I → GSpace 𝒟) inferInstance) ⊔
      TopologicalSpace.coinduced (sigMap : OnePoint ℕ → GSpace 𝒟) inferInstance) ⊔
    ((⨆ D : 𝒟, TopologicalSpace.coinduced (phiMap D) inferInstance) ⊔
      ⨆ S : CS 𝒟, TopologicalSpace.coinduced (lamMap S.1) inferInstance)

noncomputable instance : TopologicalSpace (GSpace 𝒟) := gTop 𝒟

theorem isOpen_iff {U : Set (GSpace 𝒟)} :
    IsOpen U ↔ (∀ n, IsOpen (rowMap n ⁻¹' U)) ∧ IsOpen (sigMap ⁻¹' U) ∧
      (∀ D, IsOpen (phiMap D ⁻¹' U)) ∧ ∀ S : CS 𝒟, IsOpen (lamMap S.1 ⁻¹' U) := by
  change IsOpen[gTop 𝒟] U ↔ _
  unfold gTop
  refine isOpen_sup.trans ?_
  refine (and_congr isOpen_sup isOpen_sup).trans ?_
  refine (and_congr (and_congr isOpen_iSup_iff isOpen_coinduced)
    (and_congr isOpen_iSup_iff isOpen_iSup_iff)).trans ?_
  simp only [isOpen_coinduced, and_assoc]

theorem isClosed_iff {F : Set (GSpace 𝒟)} :
    IsClosed F ↔ (∀ n, IsClosed (rowMap n ⁻¹' F)) ∧ IsClosed (sigMap ⁻¹' F) ∧
      (∀ D, IsClosed (phiMap D ⁻¹' F)) ∧ ∀ S : CS 𝒟, IsClosed (lamMap S.1 ⁻¹' F) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

theorem continuous_rowMap (n : ℕ) : Continuous (rowMap n : I → GSpace 𝒟) :=
  continuous_def.2 fun _ hU => (isOpen_iff.1 hU).1 n

theorem continuous_sigMap : Continuous (sigMap : OnePoint ℕ → GSpace 𝒟) :=
  continuous_def.2 fun _ hU => (isOpen_iff.1 hU).2.1

theorem continuous_phiMap (D : 𝒟) : Continuous (phiMap D) :=
  continuous_def.2 fun _ hU => (isOpen_iff.1 hU).2.2.1 D

theorem continuous_lamMap (S : CS 𝒟) : Continuous (lamMap S.1) :=
  continuous_def.2 fun _ hU => (isOpen_iff.1 hU).2.2.2 S

theorem continuous_arcMap (D : 𝒟) : Continuous (arcMap D) := by
  have h := (continuous_lamMap ⟨{D}, countable_singleton D⟩).comp
    (Fan.continuous_spine (⟨D, mem_singleton D⟩ : ({D} : Set 𝒟)))
  refine h.congr fun t => ?_
  simp only [comp_apply]
  rw [lamMap_spine]

theorem continuous_spokeMap (D : 𝒟) (m : (D : Set (ℕ × ℕ))) : Continuous (spokeMap D m) := by
  refine ((continuous_phiMap D).comp (Fan.continuous_spine m)).congr fun t => ?_
  simp only [comp_apply]
  rw [phiMap_spine]

theorem tendsto_xpt : Tendsto (xpt : ℕ → GSpace 𝒟) atTop (𝓝 infty) := by
  have h := (continuous_sigMap (𝒟 := 𝒟)).tendsto (OnePoint.infty : OnePoint ℕ)
  have h2 : Tendsto (fun n : ℕ => (n : OnePoint ℕ)) atTop (𝓝 OnePoint.infty) := by
    rw [← Nat.cofinite_eq_atTop, ← Filter.cocompact_eq_cofinite,
      ← Filter.coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty
  exact h.comp h2

/-! ### Shapes of the pieces and their intersections -/

/-- A set containing the range of `rowMap n`. -/
def RowS (n : ℕ) : Set (GSpace 𝒟) := range (row n)

/-- A set containing the range of `sigMap`. -/
def SigS : Set (GSpace 𝒟) := {g | g = infty ∨ ∃ n, g = xpt n}

/-- A set containing the range of `phiMap D`. -/
def PhiS (D : 𝒟) : Set (GSpace 𝒟) :=
  {g | g = pnt D ∨ (∃ m ∈ (D : Set (ℕ × ℕ)), g = wit m) ∨ ∃ m s, g = spoke D m s}

/-- A set containing the range of `lamMap S`. -/
def LamS (S : Set 𝒟) : Set (GSpace 𝒟) :=
  {g | g = infty ∨ (∃ D ∈ S, g = pnt D) ∨ ∃ D ∈ S, ∃ s, g = arc D s}

theorem range_rowMap_subset (n : ℕ) : range (rowMap n : I → GSpace 𝒟) ⊆ RowS n := subset_rfl

theorem range_sigMap_subset : range (sigMap : OnePoint ℕ → GSpace 𝒟) ⊆ SigS := by
  rintro _ ⟨c, rfl⟩
  induction c using OnePoint.rec
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem spokeMap_mem (D : 𝒟) (m : (D : Set (ℕ × ℕ))) (t : I) : spokeMap D m t ∈ PhiS D := by
  by_cases h0 : (t : ℝ) = 0
  · rw [show t = 0 from Subtype.ext h0, spokeMap_zero]
    exact Or.inl rfl
  · rcases spokeMap_cases D m h0 with ⟨h, -⟩ | ⟨s, h, -⟩ <;> rw [h]
    · exact Or.inr (Or.inl ⟨m, m.2, rfl⟩)
    · exact Or.inr (Or.inr ⟨m, s, rfl⟩)

theorem range_phiMap_subset (D : 𝒟) : range (phiMap D) ⊆ PhiS D := by
  rintro _ ⟨f, rfl⟩
  rcases Fan.centre_or_spine f with rfl | ⟨m, t, -, rfl⟩
  · rw [phiMap_centre]
    exact Or.inl rfl
  · rw [phiMap_spine]
    exact spokeMap_mem D m t

theorem arcMap_mem {S : Set 𝒟} {D : 𝒟} (hD : D ∈ S) (t : I) : arcMap D t ∈ LamS S := by
  by_cases h0 : (t : ℝ) = 0
  · rw [show t = 0 from Subtype.ext h0, arcMap_zero]
    exact Or.inl rfl
  · rcases arcMap_cases D h0 with h | ⟨s, h⟩ <;> rw [h]
    · exact Or.inr (Or.inl ⟨D, hD, rfl⟩)
    · exact Or.inr (Or.inr ⟨D, hD, s, rfl⟩)

theorem range_lamMap_subset (S : Set 𝒟) : range (lamMap S) ⊆ LamS S := by
  rintro _ ⟨f, rfl⟩
  rcases Fan.centre_or_spine f with rfl | ⟨D, t, -, rfl⟩
  · rw [lamMap_centre]
    exact Or.inl rfl
  · rw [lamMap_spine]
    exact arcMap_mem D.2 t

theorem mem_of_arcMap_mem_lamS {S : Set 𝒟} {D : 𝒟} {t : I} (h0 : (t : ℝ) ≠ 0)
    (h : arcMap D t ∈ LamS S) : D ∈ S := by
  rcases arcMap_cases D h0 with he | ⟨s, he⟩ <;> rw [he] at h
  · rcases h with h | ⟨D', hD', h⟩ | ⟨D', -, s', h⟩
    · simp at h
    · rw [pnt.injEq] at h
      exact h ▸ hD'
    · simp at h
  · rcases h with h | ⟨D', -, h⟩ | ⟨D', hD', s', h⟩
    · simp at h
    · simp at h
    · rw [arc.injEq] at h
      exact h.1 ▸ hD'

theorem finite_rowS_rowS {n n' : ℕ} (h : n ≠ n') :
    ((RowS n : Set (GSpace 𝒟)) ∩ RowS n').Finite := by
  convert finite_empty
  ext g
  simp only [RowS, mem_inter_iff, mem_range, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨t, rfl⟩ ⟨t', h'⟩
  simp only [row.injEq] at h'
  exact h h'.1.symm

theorem finite_rowS_sigS (n : ℕ) : ((RowS n : Set (GSpace 𝒟)) ∩ SigS).Finite := by
  refine (finite_singleton (xpt n : GSpace 𝒟)).subset ?_
  rintro g ⟨⟨t, rfl⟩, h | ⟨n', h⟩⟩
  · simp at h
  · simp only [xpt, row.injEq] at h
    rw [h.1, h.2]
    rfl

theorem finite_rowS_phiS (h𝒟 : IsMADFamily 𝒟) (n : ℕ) (D : 𝒟) :
    ((RowS n : Set (GSpace 𝒟)) ∩ PhiS D).Finite := by
  refine (((h𝒟.mem D D.2).finite_fst n).image wit).subset ?_
  rintro g ⟨⟨t, rfl⟩, h | ⟨m, hm, h⟩ | ⟨m, s, h⟩⟩
  · simp at h
  · refine ⟨m, ⟨hm, ?_⟩, h.symm⟩
    simp only [wit, row.injEq] at h
    exact h.1.symm
  · simp at h

theorem finite_rowS_lamS (n : ℕ) (S : Set 𝒟) : ((RowS n : Set (GSpace 𝒟)) ∩ LamS S).Finite := by
  convert finite_empty
  ext g
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨t, rfl⟩ (h | ⟨D, -, h⟩ | ⟨D, -, s, h⟩) <;> simp at h

theorem finite_sigS_phiS (D : 𝒟) : ((SigS : Set (GSpace 𝒟)) ∩ PhiS D).Finite := by
  convert finite_empty
  ext g
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  rintro (rfl | ⟨n, rfl⟩) (h | ⟨m, -, h⟩ | ⟨m, s, h⟩)
  · simp at h
  · simp [wit] at h
  · simp at h
  · simp [xpt] at h
  · exact wit_ne_xpt m n h.symm
  · simp [xpt] at h

theorem finite_sigS_lamS (S : Set 𝒟) : ((SigS : Set (GSpace 𝒟)) ∩ LamS S).Finite := by
  refine (finite_singleton (infty : GSpace 𝒟)).subset ?_
  rintro g ⟨rfl | ⟨n, rfl⟩, h | ⟨D, -, h⟩ | ⟨D, -, s, h⟩⟩ <;> simp_all [xpt]

theorem finite_phiS_phiS (h𝒟 : IsMADFamily 𝒟) {D D' : 𝒟} (hne : D ≠ D') :
    ((PhiS D : Set (GSpace 𝒟)) ∩ PhiS D').Finite := by
  have hfin : ((D : Set (ℕ × ℕ)) ∩ D').Finite :=
    h𝒟.almostDisjoint D.2 D'.2 fun e => hne (Subtype.ext e)
  refine (hfin.image wit).subset ?_
  rintro g ⟨h | ⟨m, hm, h⟩ | ⟨m, s, h⟩, h' | ⟨m', hm', h'⟩ | ⟨m', s', h'⟩⟩ <;> subst h
  · exact absurd (pnt.inj h') hne
  · simp [wit] at h'
  · simp at h'
  · simp [wit] at h'
  · exact ⟨m, ⟨hm, wit_injective h' ▸ hm'⟩, rfl⟩
  · simp [wit] at h'
  · simp at h'
  · simp [wit] at h'
  · exact absurd (spoke.inj h').1 hne

theorem finite_phiS_lamS (D : 𝒟) (S : Set 𝒟) : ((PhiS D : Set (GSpace 𝒟)) ∩ LamS S).Finite := by
  refine (finite_singleton (pnt D : GSpace 𝒟)).subset ?_
  rintro g ⟨h | ⟨m, -, h⟩ | ⟨m, s, h⟩, h' | ⟨D', -, h'⟩ | ⟨D', -, s', h'⟩⟩ <;> subst h <;>
    simp_all [wit]

/-! ### The pieces are closed embeddings -/

open Classical in
/-- Restriction of the fan `Λ_{S'}` to the spines in `S` (extension by `0`). -/
noncomputable def restr (S S' : Set 𝒟) (h : Fan S') : Fan S :=
  ⟨fun D => if hD : (D : 𝒟) ∈ S' then (h : S' → ℝ) ⟨D, hD⟩ else 0, fun D => by
    by_cases hD : (D : 𝒟) ∈ S'
    · simp only [dif_pos hD]
      exact Fan.coe_mem_Icc h _
    · simp only [dif_neg hD]
      exact ⟨le_rfl, zero_le_one⟩, fun D D' hne => by
    by_cases hD : (D : 𝒟) ∈ S'
    · by_cases hD' : (D' : 𝒟) ∈ S'
      · simp only [dif_pos hD, dif_pos hD']
        refine h.2.2 _ _ fun e => hne ?_
        have e' := congrArg (fun x : S' => (x : 𝒟)) e
        exact Subtype.ext e'
      · simp only [dif_neg hD', or_true]
    · simp only [dif_neg hD, true_or]⟩

theorem continuous_restr (S S' : Set 𝒟) : Continuous (restr S S') := by
  refine Continuous.subtype_mk (continuous_pi fun D => ?_) _
  by_cases hD : (D : 𝒟) ∈ S'
  · simp only [dif_pos hD]
    exact (continuous_apply _).comp continuous_subtype_val
  · simp only [dif_neg hD]
    exact continuous_const

theorem restr_centre (S S' : Set 𝒟) : restr S S' Fan.centre = Fan.centre := by
  apply Subtype.ext
  funext D
  simp [restr]

theorem restr_spine {S S' : Set 𝒟} (D : S') (hD : (D : 𝒟) ∈ S) (t : I) :
    restr S S' (Fan.spine D t) = Fan.spine ⟨D, hD⟩ t := by
  classical
  apply Subtype.ext
  funext D'
  by_cases hD' : (D' : 𝒟) ∈ S'
  · simp only [restr, dif_pos hD']
    by_cases e : (D' : 𝒟) = D
    · have e1 : (⟨D', hD'⟩ : S') = D := Subtype.ext e
      have e2 : D' = ⟨D, hD⟩ := Subtype.ext e
      rw [e1, e2, Fan.spine_apply_self, Fan.spine_apply_self]
    · have e1 : (⟨D', hD'⟩ : S') ≠ D := fun h => e (congrArg Subtype.val h)
      have e2 : D' ≠ ⟨D, hD⟩ := fun h => e (congrArg Subtype.val h)
      rw [Fan.spine_apply_ne e1, Fan.spine_apply_ne e2]
  · simp only [restr, dif_neg hD']
    have e2 : D' ≠ ⟨D, hD⟩ := fun h => hD' (h ▸ D.2)
    rw [Fan.spine_apply_ne e2]

theorem isClosed_lam_lam (S S' : Set 𝒟) {C : Set (Fan S)} (hC : IsClosed C) :
    IsClosed (lamMap S' ⁻¹' (lamMap S '' C)) := by
  let A : Set (Fan S') := {h | ∀ D : S', (D : 𝒟) ∉ S → (h : S' → ℝ) D = 0}
  have hA : IsClosed A := by
    simp only [A, setOf_forall]
    exact isClosed_iInter fun D => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply D).comp continuous_subtype_val) continuous_const
  have h1 : ∀ h ∈ A, lamMap S (restr S S' h) = lamMap S' h := by
    intro h hh
    rcases Fan.centre_or_spine h with rfl | ⟨D, t, ht, rfl⟩
    · rw [restr_centre, lamMap_centre, lamMap_centre]
    · have hDS : (D : 𝒟) ∈ S := by
        by_contra hn
        have := hh D hn
        rw [Fan.spine_apply_self] at this
        exact ht this
      rw [restr_spine D hDS, lamMap_spine, lamMap_spine]
  have h2 : ∀ h, lamMap S' h ∈ range (lamMap S) → h ∈ A := by
    intro h hh
    rcases Fan.centre_or_spine h with rfl | ⟨D, t, ht, rfl⟩
    · intro D _
      rfl
    · intro D' hD'
      by_cases e : D' = D
      · subst e
        rw [lamMap_spine] at hh
        exact absurd (mem_of_arcMap_mem_lamS ht (range_lamMap_subset S hh)) hD'
      · exact Fan.spine_apply_ne e t
  have e : lamMap S' ⁻¹' (lamMap S '' C) = A ∩ restr S S' ⁻¹' C := by
    ext h
    constructor
    · rintro ⟨c, hc, hch⟩
      have hA' : h ∈ A := h2 h ⟨c, hch⟩
      refine ⟨hA', ?_⟩
      have : lamMap S (restr S S' h) = lamMap S c := by rw [h1 h hA', hch]
      rw [mem_preimage, lamMap_injective S this]
      exact hc
    · rintro ⟨hA', hC'⟩
      exact ⟨_, hC', h1 h hA'⟩
  rw [e]
  exact hA.inter (hC.preimage (continuous_restr S S'))

section closedMaps

variable (h𝒟 : IsMADFamily 𝒟)
include h𝒟

theorem isClosedMap_rowMap (n : ℕ) : IsClosedMap (rowMap n : I → GSpace 𝒟) := by
  intro C hC
  refine isClosed_iff.2 ⟨fun n' => ?_, ?_, fun D => ?_, fun S => ?_⟩
  · by_cases h : n' = n
    · subst h
      rw [(rowMap_injective n').preimage_image]
      exact hC
    · exact isClosed_preimage_image_of_finite (rowMap_injective n') (range_rowMap_subset n')
        (range_rowMap_subset n) (finite_rowS_rowS h) C
  · exact isClosed_preimage_image_of_finite sigMap_injective range_sigMap_subset
      (range_rowMap_subset n) (by rw [inter_comm]; exact finite_rowS_sigS n) C
  · exact isClosed_preimage_image_of_finite (phiMap_injective D) (range_phiMap_subset D)
      (range_rowMap_subset n) (by rw [inter_comm]; exact finite_rowS_phiS h𝒟 n D) C
  · exact isClosed_preimage_image_of_finite (lamMap_injective S.1) (range_lamMap_subset S.1)
      (range_rowMap_subset n) (by rw [inter_comm]; exact finite_rowS_lamS n S.1) C

theorem isClosedMap_sigMap : IsClosedMap (sigMap : OnePoint ℕ → GSpace 𝒟) := by
  intro C hC
  refine isClosed_iff.2 ⟨fun n => ?_, ?_, fun D => ?_, fun S => ?_⟩
  · exact isClosed_preimage_image_of_finite (rowMap_injective n) (range_rowMap_subset n)
      range_sigMap_subset (finite_rowS_sigS n) C
  · rw [sigMap_injective.preimage_image]
    exact hC
  · exact isClosed_preimage_image_of_finite (phiMap_injective D) (range_phiMap_subset D)
      range_sigMap_subset (by rw [inter_comm]; exact finite_sigS_phiS D) C
  · exact isClosed_preimage_image_of_finite (lamMap_injective S.1) (range_lamMap_subset S.1)
      range_sigMap_subset (by rw [inter_comm]; exact finite_sigS_lamS S.1) C

theorem isClosedMap_phiMap (D : 𝒟) : IsClosedMap (phiMap D) := by
  intro C hC
  refine isClosed_iff.2 ⟨fun n => ?_, ?_, fun D' => ?_, fun S => ?_⟩
  · exact isClosed_preimage_image_of_finite (rowMap_injective n) (range_rowMap_subset n)
      (range_phiMap_subset D) (finite_rowS_phiS h𝒟 n D) C
  · exact isClosed_preimage_image_of_finite sigMap_injective range_sigMap_subset
      (range_phiMap_subset D) (finite_sigS_phiS D) C
  · by_cases h : D' = D
    · subst h
      rw [(phiMap_injective D').preimage_image]
      exact hC
    · exact isClosed_preimage_image_of_finite (phiMap_injective D') (range_phiMap_subset D')
        (range_phiMap_subset D) (finite_phiS_phiS h𝒟 h) C
  · exact isClosed_preimage_image_of_finite (lamMap_injective S.1) (range_lamMap_subset S.1)
      (range_phiMap_subset D) (by rw [inter_comm]; exact finite_phiS_lamS D S.1) C

theorem isClosedMap_lamMap (S : Set 𝒟) : IsClosedMap (lamMap S) := by
  intro C hC
  refine isClosed_iff.2 ⟨fun n => ?_, ?_, fun D => ?_, fun S' => ?_⟩
  · exact isClosed_preimage_image_of_finite (rowMap_injective n) (range_rowMap_subset n)
      (range_lamMap_subset S) (finite_rowS_lamS n S) C
  · exact isClosed_preimage_image_of_finite sigMap_injective range_sigMap_subset
      (range_lamMap_subset S) (finite_sigS_lamS S) C
  · exact isClosed_preimage_image_of_finite (phiMap_injective D) (range_phiMap_subset D)
      (range_lamMap_subset S) (finite_phiS_lamS D S) C
  · exact isClosed_lam_lam S S'.1 hC

end closedMaps

end GSpace

end MosaicSpaces
