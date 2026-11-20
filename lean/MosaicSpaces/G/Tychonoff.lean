module

public import MosaicSpaces.G.Capture
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Complete regularity of `G` (article: Lemma 4.4 and Theorem 4.5)

* `EdgeData`: a real function on `G` given by its values `vinf`, `vp D` at `∞` and `p_D`, a
  function on each row, on each spoke and on each arc. `EdgeData.Valid` states the matching
  conditions at the end points, continuity on each edge, and the finiteness conditions that make
  the function continuous on the fans. `EdgeData.continuous_toFun` is the continuity statement
  behind Lemma 4.4.
* `exists_binary` is **Lemma 4.4** (binary extension). The extension over the edges is done with
  Urysohn's lemma on `[0,1]` (Mathlib's `exists_continuous_zero_one_of_isClosed`) instead of
  Tietze's theorem interval by interval; on a row a single Urysohn function handles all the
  elementary intervals at once.
* `completelyRegularSpace`, `t35Space`, `t2Space`: **Theorem 4.5**: `G` is Tychonoff (`T₁` and
  completely regular), in particular Hausdorff. The last assertion of Theorem 4.5 is
  `exists_isolating_nhd` in `G/Capture`.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace unitInterval Function

namespace MosaicSpaces

/-! ### Auxiliary facts about `[0,1]` -/

open Classical in
/-- The indicator value of a proposition. -/
noncomputable def ind (p : Prop) : ℝ := if p then 1 else 0

theorem ind_mem (p : Prop) : ind p ∈ Icc (0 : ℝ) 1 := by
  unfold ind; split_ifs <;> simp

theorem ind_true {p : Prop} (h : p) : ind p = 1 := by simp [ind, h]

theorem ind_false {p : Prop} (h : ¬ p) : ind p = 0 := by simp [ind, h]

theorem ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by rw [propext h]

/-- A Urysohn function on `[0,1]`. -/
theorem exists_urysohn_I {Z O : Set I} (hZ : IsClosed Z) (hO : IsClosed O) (hd : Disjoint Z O) :
    ∃ sg : I → ℝ, Continuous sg ∧ (∀ t, sg t ∈ Icc (0 : ℝ) 1) ∧ EqOn sg 0 Z ∧ EqOn sg 1 O := by
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed hZ hO hd
  exact ⟨f, f.continuous, hf, hf0, hf1⟩

/-- The function on an edge used in Lemma 4.4: prescribed values `ind a`, `ind b` at the end
points, zero on the closed set `C`, and constant when this is possible. -/
theorem exists_edgeFun {C : Set I} (hC : IsClosed C) (a b : Prop) (ha : a → (0 : I) ∉ C)
    (hb : b → (1 : I) ∉ C) :
    ∃ sg : I → ℝ, Continuous sg ∧ (∀ t, sg t ∈ Icc (0 : ℝ) 1) ∧ EqOn sg 0 C ∧ sg 0 = ind a ∧
      sg 1 = ind b ∧ ((a ↔ b) → (¬ a ∨ C = ∅) → sg = fun _ => ind a) := by
  by_cases hc : (a ↔ b) ∧ (¬ a ∨ C = ∅)
  · refine ⟨fun _ => ind a, continuous_const, fun _ => ind_mem a, fun t ht => ?_, rfl,
      ind_congr hc.1, fun _ _ => rfl⟩
    rcases hc.2 with h | h
    · exact ind_false h
    · rw [h] at ht; exact absurd ht (Set.notMem_empty t)
  · let Z : Set I := C ∪ {t | (t = 0 ∧ ¬ a) ∨ (t = 1 ∧ ¬ b)}
    let O : Set I := {t | (t = 0 ∧ a) ∨ (t = 1 ∧ b)}
    have hfin : ∀ p q : Prop, ({t : I | (t = 0 ∧ p) ∨ (t = 1 ∧ q)}).Finite := fun p q =>
      ((finite_singleton (0 : I)).union (finite_singleton (1 : I))).subset fun t ht => by
        rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
    have h01 : (0 : I) ≠ 1 := fun h => zero_ne_one (congrArg Subtype.val h)
    obtain ⟨sg, hsg, hsgm, hsgZ, hsgO⟩ := exists_urysohn_I (Z := Z) (O := O)
      (hC.union (hfin _ _).isClosed) (hfin _ _).isClosed (by
        rw [Set.disjoint_left]
        rintro t (htC | ⟨ht0, hna⟩ | ⟨ht1, hnb⟩) (⟨ht0', ha'⟩ | ⟨ht1', hb'⟩)
        · exact ha ha' (ht0' ▸ htC)
        · exact hb hb' (ht1' ▸ htC)
        · exact hna ha'
        · exact h01 (ht0.symm.trans ht1')
        · exact h01 (ht0'.symm.trans ht1)
        · exact hnb hb')
    refine ⟨sg, hsg, hsgm, fun t ht => hsgZ (Or.inl ht), ?_, ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
    · by_cases ha' : a
      · rw [ind_true ha']; exact hsgO (Or.inl ⟨rfl, ha'⟩)
      · rw [ind_false ha']; exact hsgZ (Or.inr (Or.inl ⟨rfl, ha'⟩))
    · by_cases hb' : b
      · rw [ind_true hb']; exact hsgO (Or.inr ⟨rfl, hb'⟩)
      · rw [ind_false hb']; exact hsgZ (Or.inr (Or.inr ⟨rfl, hb'⟩))

namespace GSpace

variable {𝒟 : Set (Set (ℕ × ℕ))}

/-- The map `ℕ ∪ {∞} → [0,1]`, `n ↦ 1/(n+1)`, `∞ ↦ 0`. -/
noncomputable def witTInf : OnePoint ℕ → I := fun c => c.elim 0 witT

theorem continuous_witTInf : Continuous witTInf := by
  refine (OnePoint.continuous_iff_from_nat _).2 ?_
  refine tendsto_subtype_rng.2 ?_
  show Tendsto (fun n : ℕ => ((witT n : I) : ℝ)) atTop (𝓝 0)
  simp only [witT_coe]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- `{0} ∪ {1/(i+1) : i ∈ A}` is closed in `[0,1]`. -/
theorem isClosed_insert_zero_witT (A : Set ℕ) : IsClosed (insert (0 : I) (witT '' A)) := by
  have hcl : IsClosed (insert (OnePoint.infty : OnePoint ℕ) (((↑) : ℕ → OnePoint ℕ) '' A)) := by
    rw [← isOpen_compl_iff]
    have e : (insert (OnePoint.infty : OnePoint ℕ) (((↑) : ℕ → OnePoint ℕ) '' A))ᶜ =
        ((↑) : ℕ → OnePoint ℕ) '' Aᶜ := by
      ext c
      induction c using OnePoint.rec with
      | infty => simp
      | coe n => simp [OnePoint.coe_ne_infty]
    rw [e]
    exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete _)
  have := continuous_witTInf.isClosedMap _ hcl
  rwa [image_insert_eq, image_image] at this

theorem finite_wit_mem_row {F : Set (GSpace 𝒟)} (hF : IsClosed F) {n : ℕ} (hn : xpt n ∉ F) :
    {i | wit (n, i) ∈ F}.Finite := by
  obtain ⟨ε, hε, hrow⟩ := exists_row_nmem hF hn
  obtain ⟨i₀, hi₀⟩ := exists_witT_lt hε
  refine (finite_Iio i₀).subset fun i hi => ?_
  by_contra h
  exact hrow _ (hi₀ i (not_lt.1 h)) hi

/-- The function on a row used in Lemma 4.4. -/
theorem exists_rowFun {C : Set I} (hC : IsClosed C) (a : Prop) (A : Set ℕ)
    (hfin : {i | ¬ (i ∈ A ↔ a)}.Finite) (ha : a → (0 : I) ∉ C) (hA : ∀ i ∈ A, witT i ∉ C) :
    ∃ sg : I → ℝ, Continuous sg ∧ (∀ t, sg t ∈ Icc (0 : ℝ) 1) ∧ EqOn sg 0 C ∧ sg 0 = ind a ∧
      ∀ i, sg (witT i) = ind (i ∈ A) := by
  let O : Set I := {t | (t = 0 ∧ a) ∨ ∃ i ∈ A, t = witT i}
  let Z' : Set I := {t | (t = 0 ∧ ¬ a) ∨ ∃ i ∉ A, t = witT i}
  have hO : IsClosed O := by
    by_cases h : a
    · convert isClosed_insert_zero_witT A using 1
      ext t; simp [O, h, eq_comm]
    · refine ((hfin.image witT).subset ?_).isClosed
      rintro t (⟨-, h'⟩ | ⟨i, hi, rfl⟩)
      · exact absurd h' h
      · exact ⟨i, by simp [hi, h], rfl⟩
  have hZ' : IsClosed Z' := by
    by_cases h : a
    · refine ((hfin.image witT).subset ?_).isClosed
      rintro t (⟨-, h'⟩ | ⟨i, hi, rfl⟩)
      · exact absurd h h'
      · exact ⟨i, by simp [hi, h], rfl⟩
    · convert isClosed_insert_zero_witT Aᶜ using 1
      ext t; simp [Z', h, eq_comm]
  have hne : ∀ i, witT i ≠ 0 := fun i h => witT_ne_zero i (congrArg Subtype.val h)
  obtain ⟨sg, hsg, hsgm, hsgZ, hsgO⟩ := exists_urysohn_I (Z := C ∪ Z') (O := O) (hC.union hZ') hO (by
    rw [Set.disjoint_left]
    rintro t (htC | ⟨ht0, hna⟩ | ⟨j, hj, htj⟩) (⟨ht0', ha'⟩ | ⟨i, hi, hti⟩)
    · exact ha ha' (ht0' ▸ htC)
    · exact hA i hi (hti ▸ htC)
    · exact hna ha'
    · exact hne i (hti.symm.trans ht0)
    · exact hne j (htj.symm.trans ht0')
    · exact hj (witT_injective (htj.symm.trans hti) ▸ hi))
  refine ⟨sg, hsg, hsgm, fun t ht => hsgZ (Or.inl ht), ?_, fun i => ?_⟩
  · by_cases h : a
    · rw [ind_true h]; exact hsgO (Or.inl ⟨rfl, h⟩)
    · rw [ind_false h]; exact hsgZ (Or.inr (Or.inl ⟨rfl, h⟩))
  · by_cases h : i ∈ A
    · rw [ind_true h]; exact hsgO (Or.inr ⟨i, h, rfl⟩)
    · rw [ind_false h]; exact hsgZ (Or.inr (Or.inr ⟨i, h, rfl⟩))

/-! ### Functions on `G` given edge by edge -/

/-- Continuity out of `G` is checked on the pieces (Prop. 2.3(3) for this mosaic). -/
theorem continuous_of_pieces {Y : Type*} [TopologicalSpace Y] {f : GSpace 𝒟 → Y}
    (h1 : ∀ n, Continuous (f ∘ rowMap n)) (h2 : Continuous (f ∘ sigMap))
    (h3 : ∀ D, Continuous (f ∘ phiMap D)) (h4 : ∀ S : CS 𝒟, Continuous (f ∘ lamMap S.1)) :
    Continuous f :=
  continuous_def.2 fun U hU => isOpen_iff.2 ⟨fun n => (h1 n).isOpen_preimage U hU,
    h2.isOpen_preimage U hU, fun D => (h3 D).isOpen_preimage U hU,
    fun S => (h4 S).isOpen_preimage U hU⟩

/-- A fan coordinate as a point of `[0,1]`. -/
def coordI {J : Type*} (h : Fan J) (j : J) : I := ⟨(h : J → ℝ) j, Fan.coe_mem_Icc h j⟩

theorem continuous_coordI {J : Type*} (j : J) : Continuous fun h : Fan J => coordI h j :=
  Continuous.subtype_mk ((continuous_apply j).comp continuous_subtype_val) _

theorem coordI_centre {J : Type*} (j : J) : coordI (Fan.centre : Fan J) j = 0 :=
  Subtype.ext rfl

theorem coordI_spine_self {J : Type*} (j : J) (t : I) : coordI (Fan.spine j t) j = t :=
  Subtype.ext (Fan.spine_apply_self j t)

theorem coordI_spine_ne {J : Type*} {j j' : J} (h : j' ≠ j) (t : I) :
    coordI (Fan.spine j t) j' = 0 :=
  Subtype.ext (Fan.spine_apply_ne h t)

theorem continuous_fanSum {J : Type*} (E : Finset J) (sg : J → I → ℝ) (c : ℝ)
    (hsg : ∀ j, Continuous (sg j)) :
    Continuous fun h : Fan J => c + ∑ j ∈ E, (sg j (coordI h j) - c) :=
  continuous_const.add (continuous_finset_sum _ fun j _ =>
    ((hsg j).comp (continuous_coordI j)).sub continuous_const)

theorem fanSum_centre {J : Type*} (E : Finset J) (sg : J → I → ℝ) (c : ℝ)
    (hsg0 : ∀ j, sg j 0 = c) :
    c + ∑ j ∈ E, (sg j (coordI (Fan.centre : Fan J) j) - c) = c := by
  simp [coordI_centre, hsg0]

theorem fanSum_spine {J : Type*} (E : Finset J) (sg : J → I → ℝ) (c : ℝ)
    (hsg0 : ∀ j, sg j 0 = c) (hE : ∀ j ∉ E, sg j = fun _ => c) (j : J) (t : I) :
    c + ∑ j' ∈ E, (sg j' (coordI (Fan.spine j t) j') - c) = sg j t := by
  by_cases hj : j ∈ E
  · rw [Finset.sum_eq_single j (fun j' _ hne => by rw [coordI_spine_ne hne, hsg0, sub_self])
      (fun h => absurd hj h), coordI_spine_self]
    ring
  · rw [Finset.sum_eq_zero fun j' hj' => by
      rw [coordI_spine_ne (fun e => hj (by rw [← e]; exact hj')), hsg0, sub_self], hE j hj]
    simp

/-- A function on `G`, given by its values at `∞` and at the `p_D` and by functions on the rows,
spokes and arcs. -/
structure EdgeData (𝒟 : Set (Set (ℕ × ℕ))) where
  vinf : ℝ
  vp : 𝒟 → ℝ
  row : ℕ → I → ℝ
  spk : (D : 𝒟) → ↥(D : Set (ℕ × ℕ)) → I → ℝ
  arcf : 𝒟 → I → ℝ

/-- The conditions under which an `EdgeData` defines a continuous function. -/
structure EdgeData.Valid (e : EdgeData 𝒟) : Prop where
  row_cont : ∀ n, Continuous (e.row n)
  spk_cont : ∀ (D : 𝒟) (m : (D : Set (ℕ × ℕ))), Continuous (e.spk D m)
  arc_cont : ∀ D, Continuous (e.arcf D)
  spk_zero : ∀ (D : 𝒟) (m : (D : Set (ℕ × ℕ))), e.spk D m 0 = e.vp D
  spk_one : ∀ (D : 𝒟) (m : (D : Set (ℕ × ℕ))), e.spk D m 1 = e.row (m : ℕ × ℕ).1 (witT (m : ℕ × ℕ).2)
  arc_zero : ∀ D, e.arcf D 0 = e.vinf
  arc_one : ∀ D, e.arcf D 1 = e.vp D
  fin_spk : ∀ D : 𝒟, {m : (D : Set (ℕ × ℕ)) | e.spk D m ≠ fun _ => e.vp D}.Finite
  fin_arc : {D | e.arcf D ≠ fun _ => e.vinf}.Finite
  fin_row : {n | e.row n 0 ≠ e.vinf}.Finite

/-- The function on `G` defined by an `EdgeData`. -/
def EdgeData.toFun (e : EdgeData 𝒟) : GSpace 𝒟 → ℝ
  | .infty => e.vinf
  | .pnt D => e.vp D
  | .row n t => e.row n t
  | .arc D s => e.arcf D ⟨s, Ioo_subset_Icc_self s.2⟩
  | .spoke D m s => e.spk D m ⟨s, Ioo_subset_Icc_self s.2⟩

namespace EdgeData

variable {e : EdgeData 𝒟}

theorem toFun_arcMap (hv : e.Valid) (D : 𝒟) (t : I) : e.toFun (arcMap D t) = e.arcf D t := by
  by_cases h0 : (t : ℝ) = 0
  · rw [show t = 0 from Subtype.ext h0, arcMap_zero, hv.arc_zero]; rfl
  by_cases h1 : (t : ℝ) = 1
  · rw [eq_one_of_coe h1, arcMap_one, hv.arc_one]; rfl
  rw [arcMap_of_ne D h0 h1]; rfl

theorem toFun_spokeMap (hv : e.Valid) (D : 𝒟) (m : (D : Set (ℕ × ℕ))) (t : I) :
    e.toFun (spokeMap D m t) = e.spk D m t := by
  by_cases h0 : (t : ℝ) = 0
  · rw [show t = 0 from Subtype.ext h0, spokeMap_zero, hv.spk_zero]; rfl
  by_cases h1 : (t : ℝ) = 1
  · rw [eq_one_of_coe h1, spokeMap_one, hv.spk_one]; rfl
  rw [spokeMap_of_ne D m h0 h1]; rfl

theorem toFun_phiMap (hv : e.Valid) (D : 𝒟) (E : Finset (D : Set (ℕ × ℕ)))
    (hE : ∀ m ∉ E, e.spk D m = fun _ => e.vp D) (h : Fan (D : Set (ℕ × ℕ))) :
    e.toFun (phiMap D h) = e.vp D + ∑ m ∈ E, (e.spk D m (coordI h m) - e.vp D) := by
  rcases Fan.centre_or_spine h with rfl | ⟨m, t, -, rfl⟩
  · rw [phiMap_centre, fanSum_centre _ _ _ (hv.spk_zero D)]; rfl
  · rw [phiMap_spine, toFun_spokeMap hv, fanSum_spine _ _ _ (hv.spk_zero D) hE]

theorem toFun_lamMap (hv : e.Valid) (S : Set 𝒟) (E : Finset S)
    (hE : ∀ D ∉ E, e.arcf D = fun _ => e.vinf) (h : Fan S) :
    e.toFun (lamMap S h) = e.vinf + ∑ D ∈ E, (e.arcf D (coordI h D) - e.vinf) := by
  rcases Fan.centre_or_spine h with rfl | ⟨D, t, -, rfl⟩
  · rw [lamMap_centre, fanSum_centre (sg := fun D : S => e.arcf D) _ _ (fun D => hv.arc_zero D)]
    rfl
  · rw [lamMap_spine, toFun_arcMap hv,
      fanSum_spine (sg := fun D : S => e.arcf D) _ _ (fun D => hv.arc_zero D) hE]

theorem continuous_toFun (hv : e.Valid) : Continuous e.toFun := by
  refine continuous_of_pieces (fun n => hv.row_cont n) ?_ (fun D => ?_) (fun S => ?_)
  · refine (OnePoint.continuous_iff_from_nat _).2 (tendsto_const_nhds.congr' ?_)
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hv.fin_row.eventually_cofinite_notMem] with n hn
    simp only [mem_setOf_eq, not_not] at hn
    exact hn.symm
  · exact (continuous_fanSum _ _ _ (hv.spk_cont D)).congr fun h =>
      (toFun_phiMap hv D (hv.fin_spk D).toFinset (fun m hm => by simpa using hm) h).symm
  · have hfin : {D : S.1 | e.arcf D ≠ fun _ => e.vinf}.Finite :=
      hv.fin_arc.preimage Subtype.val_injective.injOn
    exact (continuous_fanSum _ (fun D : S.1 => e.arcf D) _ (fun D => hv.arc_cont D)).congr
      fun h => (toFun_lamMap hv S.1 hfin.toFinset (fun D hD => by simpa using hD) h).symm

end EdgeData

/-! ### Lemma 4.4 -/

/-- **Lemma 4.4 (binary extension).** Prescribe values in `{0,1}` at the vertices (the value is
`1` exactly on `Hinf`, `Hp`, `Hx`, `Hw`), zero at the vertices in a closed set `F`, subject to
the finiteness conditions (i)–(iii). Then there is a continuous `f : G → [0,1]` with these vertex
values which vanishes on `F`. -/
theorem exists_binary (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F)
    (Hinf : Prop) (Hp : Set 𝒟) (Hx : Set ℕ) (Hw : Set (ℕ × ℕ))
    (h0inf : Hinf → infty ∉ F) (h0p : ∀ D ∈ Hp, pnt D ∉ F) (h0x : ∀ n ∈ Hx, xpt n ∉ F)
    (h0w : ∀ m ∈ Hw, wit m ∉ F)
    (hi : ∀ n, {i | ¬ ((n, i) ∈ Hw ↔ n ∈ Hx)}.Finite)
    (hii : ∀ D : 𝒟, {m | m ∈ (D : Set (ℕ × ℕ)) ∧ ¬ (m ∈ Hw ↔ D ∈ Hp)}.Finite)
    (hiii1 : {n | ¬ (n ∈ Hx ↔ Hinf)}.Finite) (hiii2 : {D | ¬ (D ∈ Hp ↔ Hinf)}.Finite) :
    ∃ f : GSpace 𝒟 → ℝ, Continuous f ∧ (∀ g, f g ∈ Icc (0 : ℝ) 1) ∧ EqOn f 0 F ∧
      f infty = ind Hinf ∧ (∀ D, f (pnt D) = ind (D ∈ Hp)) ∧ (∀ n, f (xpt n) = ind (n ∈ Hx)) ∧
      ∀ m, f (wit m) = ind (m ∈ Hw) := by
  -- rows
  have hrow : ∀ n, ∃ sg : I → ℝ, Continuous sg ∧ (∀ t, sg t ∈ Icc (0 : ℝ) 1) ∧
      EqOn sg 0 (rowMap n ⁻¹' F) ∧ sg 0 = ind (n ∈ Hx) ∧ ∀ i, sg (witT i) = ind ((n, i) ∈ Hw) :=
    fun n => exists_rowFun (((isClosed_iff.1 hF).1 n)) (n ∈ Hx) {i | (n, i) ∈ Hw} (hi n)
      (fun h => h0x n h) (fun i hi => h0w _ hi)
  choose g hg hgm hgF hg0 hgw using hrow
  -- spokes
  have hspk : ∀ (D : 𝒟) (m : (D : Set (ℕ × ℕ))), ∃ sg : I → ℝ, Continuous sg ∧
      (∀ t, sg t ∈ Icc (0 : ℝ) 1) ∧ EqOn sg 0 (spokeMap D m ⁻¹' F) ∧ sg 0 = ind (D ∈ Hp) ∧
      sg 1 = ind ((m : ℕ × ℕ) ∈ Hw) ∧ ((D ∈ Hp ↔ (m : ℕ × ℕ) ∈ Hw) →
        (¬ D ∈ Hp ∨ spokeMap D m ⁻¹' F = ∅) → sg = fun _ => ind (D ∈ Hp)) :=
    fun D m => exists_edgeFun (hF.preimage (continuous_spokeMap D m)) _ _
      (fun h h' => h0p D h (by simpa [spokeMap_zero] using h'))
      (fun h h' => h0w _ h (by simpa [spokeMap_one] using h'))
  choose sg hsg hsgm hsgF hsg0 hsg1 hsgc using hspk
  -- arcs
  have harc : ∀ D : 𝒟, ∃ α : I → ℝ, Continuous α ∧ (∀ t, α t ∈ Icc (0 : ℝ) 1) ∧
      EqOn α 0 (arcMap D ⁻¹' F) ∧ α 0 = ind Hinf ∧ α 1 = ind (D ∈ Hp) ∧
      ((Hinf ↔ D ∈ Hp) → (¬ Hinf ∨ arcMap D ⁻¹' F = ∅) → α = fun _ => ind Hinf) :=
    fun D => exists_edgeFun (hF.preimage (continuous_arcMap D)) _ _
      (fun h h' => h0inf h (by simpa [arcMap_zero] using h'))
      (fun h h' => h0p D h (by simpa [arcMap_one] using h'))
  choose α hα hαm hαF hα0 hα1 hαc using harc
  let e : EdgeData 𝒟 := ⟨ind Hinf, fun D => ind (D ∈ Hp), g, sg, α⟩
  have hv : e.Valid := by
    refine ⟨hg, hsg, hα, hsg0, fun D m => ?_, hα0, hα1, fun D => ?_, ?_, ?_⟩
    · show sg D m 1 = g _ _
      rw [hsg1, hgw]
    · -- spokes that are not constant
      refine (((hii D).preimage Subtype.val_injective.injOn).union
        (show {m : (D : Set (ℕ × ℕ)) | D ∈ Hp ∧ spokeMap D m ⁻¹' F ≠ ∅}.Finite from ?_)).subset ?_
      · by_cases hD : D ∈ Hp
        · refine (finite_spoke_mem hF (h0p D hD)).subset ?_
          rintro m ⟨-, hm⟩
          obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hm
          exact ⟨t, ht⟩
        · convert finite_empty
          ext m; simp [hD]
      · intro m hm
        by_contra hcon
        simp only [mem_union, mem_preimage, mem_setOf_eq, not_or, not_and, not_not] at hcon
        refine hm (hsgc D m (hcon.1 m.2).symm ?_)
        by_cases hD : D ∈ Hp
        · exact Or.inr (hcon.2 hD)
        · exact Or.inl hD
    · refine (hiii2.union (show {D : 𝒟 | Hinf ∧ arcMap D ⁻¹' F ≠ ∅}.Finite from ?_)).subset ?_
      · by_cases hI : Hinf
        · refine (finite_arc_mem hF (h0inf hI)).subset ?_
          rintro D ⟨-, hD⟩
          obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hD
          exact ⟨t, ht⟩
        · convert finite_empty
          ext D; simp [hI]
      · intro D hD
        by_contra hcon
        simp only [mem_union, mem_setOf_eq, not_or, not_and, not_not] at hcon
        refine hD (hαc D (Iff.symm hcon.1) ?_)
        by_cases hI : Hinf
        · exact Or.inr (hcon.2 hI)
        · exact Or.inl hI
    · refine hiii1.subset fun n hn => fun hiff => hn ?_
      show g n 0 = ind Hinf
      rw [hg0, ind_congr hiff]
  refine ⟨e.toFun, EdgeData.continuous_toFun hv, fun q => ?_, fun q hq => ?_, rfl, fun D => rfl,
    fun n => hg0 n, fun m => hgw m.1 m.2⟩
  · cases q with
    | infty => exact ind_mem _
    | pnt D => exact ind_mem _
    | row n t => exact hgm n t
    | arc D s => exact hαm D _
    | spoke D m s => exact hsgm D m _
  · cases q with
    | infty => exact ind_false fun h => h0inf h hq
    | pnt D => exact ind_false fun h => h0p D h hq
    | row n t => exact hgF n hq
    | arc D s =>
      refine hαF D ?_
      show arcMap D _ ∈ F
      rw [arcMap_coe]; exact hq
    | spoke D m s =>
      refine hsgF D m ?_
      show spokeMap D m _ ∈ F
      rw [spokeMap_coe]; exact hq

/-! ### Theorem 4.5 -/

/-- A continuous function on `G` with values in `[0,1]`, equal to `1` at `q` and to `0` on `F`. -/
def Separates (F : Set (GSpace 𝒟)) (q : GSpace 𝒟) : Prop :=
  ∃ f : GSpace 𝒟 → ℝ, Continuous f ∧ (∀ g, f g ∈ Icc (0 : ℝ) 1) ∧ EqOn f 0 F ∧ f q = 1

theorem separates_of_binary (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F)
    {q : GSpace 𝒟}
    (Hinf : Prop) (Hp : Set 𝒟) (Hx : Set ℕ) (Hw : Set (ℕ × ℕ))
    (h0inf : Hinf → infty ∉ F) (h0p : ∀ D ∈ Hp, pnt D ∉ F) (h0x : ∀ n ∈ Hx, xpt n ∉ F)
    (h0w : ∀ m ∈ Hw, wit m ∉ F)
    (hi : ∀ n, {i | ¬ ((n, i) ∈ Hw ↔ n ∈ Hx)}.Finite)
    (hii : ∀ D : 𝒟, {m | m ∈ (D : Set (ℕ × ℕ)) ∧ ¬ (m ∈ Hw ↔ D ∈ Hp)}.Finite)
    (hiii1 : {n | ¬ (n ∈ Hx ↔ Hinf)}.Finite) (hiii2 : {D | ¬ (D ∈ Hp ↔ Hinf)}.Finite)
    (hq : (q = infty ∧ Hinf) ∨ (∃ D ∈ Hp, q = pnt D) ∨ (∃ n ∈ Hx, q = xpt n) ∨
      ∃ m ∈ Hw, q = wit m) : Separates F q := by
  obtain ⟨f, hf, hfm, hfF, hfi, hfp, hfx, hfw⟩ :=
    exists_binary h𝒟 hF Hinf Hp Hx Hw h0inf h0p h0x h0w hi hii hiii1 hiii2
  refine ⟨f, hf, hfm, hfF, ?_⟩
  rcases hq with ⟨rfl, h⟩ | ⟨D, hD, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨m, hm, rfl⟩
  · rw [hfi, ind_true h]
  · rw [hfp, ind_true hD]
  · rw [hfx, ind_true hn]
  · rw [hfw, ind_true hm]

theorem finite_section (h𝒟 : IsMADFamily 𝒟) (D : 𝒟) (n : ℕ) :
    {i | (n, i) ∈ (D : Set (ℕ × ℕ))}.Finite := (h𝒟.mem D D.2).2 n

theorem separates_infty (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F)
    (hq : infty ∉ F) : Separates F infty := by
  set IF := {n | xpt n ∈ F}
  have hIF : IF.Finite := finite_xpt_mem hF hq
  set 𝒟F := {D : 𝒟 | ∃ t, arcMap D t ∈ F}
  have h𝒟F : 𝒟F.Finite := finite_arc_mem hF hq
  set B : Set (ℕ × ℕ) := {m | wit m ∈ F} ∪ {m | m.1 ∈ IF} ∪ ⋃ D ∈ 𝒟F, (D : Set (ℕ × ℕ))
  have hpD : ∀ D, D ∉ 𝒟F → pnt D ∉ F := fun D hD h => hD ⟨1, by rw [arcMap_one]; exact h⟩
  refine separates_of_binary h𝒟 hF True 𝒟Fᶜ IFᶜ Bᶜ (fun _ => hq) (fun D hD => hpD D hD)
    (fun n hn => hn) (fun m hm h => hm (Or.inl (Or.inl h))) (fun n => ?_) (fun D => ?_)
    (by simpa using hIF) (by simpa using h𝒟F) (Or.inl ⟨rfl, trivial⟩)
  · by_cases hn : n ∈ IF
    · refine finite_empty.subset fun i hiff => hiff ?_
      exact ⟨fun h => absurd (Or.inl (Or.inr hn)) h, fun h => absurd hn h⟩
    · refine (((finite_wit_mem_row hF hn).union
        (finite_section_biUnion h𝒟 h𝒟F n))).subset fun i hi => ?_
      simp only [mem_setOf_eq, mem_compl_iff, hn, not_false_eq_true, iff_true, not_not] at hi
      rcases hi with (h | h) | h
      · exact Or.inl h
      · exact absurd h hn
      · exact Or.inr h
  · by_cases hD : D ∈ 𝒟F
    · refine finite_empty.subset fun m ⟨hm, hiff⟩ => hiff ?_
      exact ⟨fun h => absurd (Or.inr (mem_biUnion hD hm)) h, fun h => absurd hD h⟩
    · have h1 := finite_wit_mem hF (hpD D hD)
      have h2 : {m | m ∈ (D : Set (ℕ × ℕ)) ∧ m.1 ∈ IF}.Finite :=
        (hIF.biUnion fun n _ => (h𝒟.mem D D.2).finite_fst n).subset fun m ⟨hm, hmI⟩ =>
          mem_biUnion hmI ⟨hm, rfl⟩
      have h3 : ((D : Set (ℕ × ℕ)) ∩ ⋃ D' ∈ 𝒟F, (D' : Set (ℕ × ℕ))).Finite := by
        rw [inter_iUnion₂]
        exact h𝒟F.biUnion fun D' hD' => h𝒟.almostDisjoint D.2 D'.2 fun e =>
          hD (Subtype.ext e ▸ hD')
      refine ((h1.union h2).union h3).subset fun m hm => ?_
      simp only [mem_setOf_eq, mem_compl_iff, hD, not_false_eq_true, iff_true, not_not] at hm
      rcases hm with ⟨hmD, (h | h) | h⟩
      · exact Or.inl (Or.inl ⟨hmD, h⟩)
      · exact Or.inl (Or.inr ⟨hmD, h⟩)
      · exact Or.inr ⟨hmD, h⟩

theorem separates_pnt (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F) {D₀ : 𝒟}
    (hq : pnt D₀ ∉ F) : Separates F (pnt D₀) := by
  refine separates_of_binary h𝒟 hF False {D₀} ∅ {m | m ∈ (D₀ : Set (ℕ × ℕ)) ∧ wit m ∉ F}
    (fun h => h.elim) (fun D hD => by rw [mem_singleton_iff.1 hD]; exact hq)
    (fun n hn => hn.elim) (fun m hm => hm.2) (fun n => ?_) (fun D => ?_) (by simp)
    ((finite_singleton D₀).subset fun D hD => by simpa using hD)
    (Or.inr (Or.inl ⟨D₀, rfl, rfl⟩))
  · refine (finite_section h𝒟 D₀ n).subset fun i hi => ?_
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not] at hi
    exact hi.1
  · by_cases hD : D = D₀
    · subst hD
      refine (finite_wit_mem hF hq).subset fun m hm => ?_
      simp only [mem_setOf_eq, mem_singleton_iff, iff_true, not_and, not_not] at hm
      exact ⟨hm.1, hm.2 hm.1⟩
    · refine (h𝒟.almostDisjoint D.2 D₀.2 fun e => hD (Subtype.ext e)).subset fun m hm => ?_
      simp only [mem_setOf_eq, mem_singleton_iff, hD, iff_false, not_not] at hm
      exact ⟨hm.1, hm.2.1⟩

theorem separates_xpt (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F) {n₀ : ℕ}
    (hq : xpt n₀ ∉ F) : Separates F (xpt n₀) := by
  refine separates_of_binary h𝒟 hF False ∅ {n₀} {m | m.1 = n₀ ∧ wit m ∉ F}
    (fun h => h.elim) (fun D hD => hD.elim) (fun n hn => by rw [mem_singleton_iff.1 hn]; exact hq)
    (fun m hm => hm.2) (fun n => ?_) (fun D => ?_)
    ((finite_singleton n₀).subset fun n hn => by simpa using hn) (by simp)
    (Or.inr (Or.inr (Or.inl ⟨n₀, rfl, rfl⟩)))
  · by_cases hn : n = n₀
    · subst hn
      refine (finite_wit_mem_row hF hq).subset fun i hi => ?_
      simp only [mem_setOf_eq, mem_singleton_iff, iff_true, true_and, not_not] at hi
      exact hi
    · convert finite_empty
      ext i
      simp [hn]
  · refine ((h𝒟.mem D D.2).finite_fst n₀).subset fun m hm => ?_
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not] at hm
    exact ⟨hm.1, hm.2.1⟩

theorem separates_wit (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F)
    {m₀ : ℕ × ℕ} (hq : wit m₀ ∉ F) : Separates F (wit m₀) := by
  refine separates_of_binary h𝒟 hF False ∅ ∅ {m₀}
    (fun h => h.elim) (fun D hD => hD.elim) (fun n hn => hn.elim)
    (fun m hm => by rw [mem_singleton_iff.1 hm]; exact hq) (fun n => ?_) (fun D => ?_) (by simp)
    (by simp) (Or.inr (Or.inr (Or.inr ⟨m₀, rfl, rfl⟩)))
  · refine (finite_singleton m₀.2).subset fun i hi => ?_
    simp only [mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, not_not] at hi
    simp [← hi]
  · refine (finite_singleton m₀).subset fun m hm => ?_
    simp only [mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, not_not] at hm
    exact hm.2

/-- A bump on `[0,1]`. -/
theorem exists_bump_I {Z : Set I} (hZ : IsClosed Z) {t : I} (ht : t ∉ Z) :
    ∃ sg : I → ℝ, Continuous sg ∧ (∀ s, sg s ∈ Icc (0 : ℝ) 1) ∧ EqOn sg 0 Z ∧ sg t = 1 := by
  obtain ⟨sg, hsg, hsgm, hsgZ, hsgO⟩ := exists_urysohn_I hZ isClosed_singleton
    (disjoint_singleton_right.2 ht)
  exact ⟨sg, hsg, hsgm, hsgZ, hsgO rfl⟩

theorem isClosed_endpoints {C : Set I} (hC : IsClosed C) : IsClosed (C ∪ {0, 1}) :=
  hC.union ((finite_singleton 1).insert 0).isClosed

theorem separates_arc {F : Set (GSpace 𝒟)} (hF : IsClosed F) {D₀ : 𝒟} {s : Ioo (0 : ℝ) 1}
    (hq : arc D₀ s ∉ F) : Separates F (arc D₀ s) := by
  classical
  have hs : (⟨s, Ioo_subset_Icc_self s.2⟩ : I) ∉ arcMap D₀ ⁻¹' F ∪ {0, 1} := by
    rintro (h | h | h)
    · exact hq (by simpa [arcMap_coe] using h)
    · exact s.2.1.ne' (congrArg Subtype.val h)
    · exact s.2.2.ne (congrArg Subtype.val h)
  obtain ⟨sg, hsg, hsgm, hsgZ, hsgt⟩ :=
    exists_bump_I (isClosed_endpoints (hF.preimage (continuous_arcMap D₀))) hs
  let e : EdgeData 𝒟 := ⟨0, fun _ => 0, fun _ _ => 0, fun _ _ _ => 0,
    fun D => if D = D₀ then sg else fun _ => 0⟩
  have hv : e.Valid := by
    refine ⟨fun _ => continuous_const, fun _ _ => continuous_const, fun D => ?_, fun _ _ => rfl,
      fun _ _ => rfl, fun D => ?_, fun D => ?_, fun _ => by simp [e], ?_, by simp [e]⟩
    · show Continuous (if D = D₀ then sg else fun _ => 0)
      split_ifs; exacts [hsg, continuous_const]
    · show (if D = D₀ then sg else fun _ => (0 : ℝ)) 0 = 0
      split_ifs; exacts [hsgZ (Or.inr (Or.inl rfl)), rfl]
    · show (if D = D₀ then sg else fun _ => (0 : ℝ)) 1 = 0
      split_ifs; exacts [hsgZ (Or.inr (Or.inr rfl)), rfl]
    · refine (finite_singleton D₀).subset fun D hD => ?_
      by_contra h
      exact hD (by simp [e, show D ≠ D₀ from h])
  refine ⟨e.toFun, EdgeData.continuous_toFun hv, fun q => ?_, fun q hq' => ?_, ?_⟩
  · cases q with
    | arc D s' =>
      show (if D = D₀ then sg else fun _ => (0 : ℝ)) _ ∈ _
      split_ifs; exacts [hsgm _, by simp]
    | _ => simp [EdgeData.toFun, e]
  · cases q with
    | arc D s' =>
      show (if D = D₀ then sg else fun _ => (0 : ℝ)) _ = 0
      split_ifs with h
      · subst h; exact hsgZ (Or.inl (by simpa [arcMap_coe] using hq'))
      · rfl
    | _ => simp [EdgeData.toFun, e]
  · show (if D₀ = D₀ then sg else fun _ => (0 : ℝ)) _ = 1
    rw [if_pos rfl]; exact hsgt

theorem separates_spoke {F : Set (GSpace 𝒟)} (hF : IsClosed F) {D₀ : 𝒟}
    {m₀ : (D₀ : Set (ℕ × ℕ))} {s : Ioo (0 : ℝ) 1} (hq : spoke D₀ m₀ s ∉ F) :
    Separates F (spoke D₀ m₀ s) := by
  classical
  have hs : (⟨s, Ioo_subset_Icc_self s.2⟩ : I) ∉ spokeMap D₀ m₀ ⁻¹' F ∪ {0, 1} := by
    rintro (h | h | h)
    · exact hq (by simpa [spokeMap_coe] using h)
    · exact s.2.1.ne' (congrArg Subtype.val h)
    · exact s.2.2.ne (congrArg Subtype.val h)
  obtain ⟨sg, hsg, hsgm, hsgZ, hsgt⟩ :=
    exists_bump_I (isClosed_endpoints (hF.preimage (continuous_spokeMap D₀ m₀))) hs
  let sel : (D : 𝒟) → ↥(D : Set (ℕ × ℕ)) → Prop := fun D m => D = D₀ ∧ (m : ℕ × ℕ) = (m₀ : ℕ × ℕ)
  let e : EdgeData 𝒟 := ⟨0, fun _ => 0, fun _ _ => 0,
    fun D m => if sel D m then sg else fun _ => 0, fun _ _ => 0⟩
  have hv : e.Valid := by
    refine ⟨fun _ => continuous_const, fun D m => ?_, fun _ => continuous_const, fun D m => ?_,
      fun D m => ?_, fun _ => rfl, fun _ => rfl, fun D => ?_, by simp [e], by simp [e]⟩
    · show Continuous (if sel D m then sg else fun _ => 0)
      split_ifs; exacts [hsg, continuous_const]
    · show (if sel D m then sg else fun _ => (0 : ℝ)) 0 = 0
      split_ifs; exacts [hsgZ (Or.inr (Or.inl rfl)), rfl]
    · show (if sel D m then sg else fun _ => (0 : ℝ)) 1 = 0
      split_ifs; exacts [hsgZ (Or.inr (Or.inr rfl)), rfl]
    · refine Set.Subsingleton.finite fun m hm m' hm' => ?_
      have h1 : sel D m := by by_contra h; exact hm (by simp [e, h])
      have h2 : sel D m' := by by_contra h; exact hm' (by simp [e, h])
      exact Subtype.ext (h1.2.trans h2.2.symm)
  refine ⟨e.toFun, EdgeData.continuous_toFun hv, fun q => ?_, fun q hq' => ?_, ?_⟩
  · cases q with
    | spoke D m s' =>
      show (if sel D m then sg else fun _ => (0 : ℝ)) _ ∈ _
      split_ifs; exacts [hsgm _, by simp]
    | _ => simp [EdgeData.toFun, e]
  · cases q with
    | spoke D m s' =>
      show (if sel D m then sg else fun _ => (0 : ℝ)) _ = 0
      split_ifs with h
      · obtain ⟨rfl, h2⟩ := h
        obtain rfl : m = m₀ := Subtype.ext h2
        exact hsgZ (Or.inl (by simpa [spokeMap_coe] using hq'))
      · rfl
    | _ => simp [EdgeData.toFun, e]
  · show (if sel D₀ m₀ then sg else fun _ => (0 : ℝ)) _ = 1
    rw [if_pos ⟨rfl, rfl⟩]; exact hsgt

theorem separates_row_interior {F : Set (GSpace 𝒟)} (hF : IsClosed F) {n₀ : ℕ} {t : I}
    (ht : t ∉ insert (0 : I) (witT '' univ)) (hq : row n₀ t ∉ F) : Separates F (row n₀ t) := by
  classical
  obtain ⟨sg, hsg, hsgm, hsgZ, hsgt⟩ := exists_bump_I
    (((isClosed_iff.1 hF).1 n₀).union (isClosed_insert_zero_witT univ))
    (show t ∉ rowMap n₀ ⁻¹' F ∪ insert (0 : I) (witT '' univ) from fun h => h.elim hq ht)
  let e : EdgeData 𝒟 := ⟨0, fun _ => 0, fun n => if n = n₀ then sg else fun _ => 0,
    fun _ _ _ => 0, fun _ _ => 0⟩
  have hv : e.Valid := by
    refine ⟨fun n => ?_, fun _ _ => continuous_const, fun _ => continuous_const, fun _ _ => rfl,
      fun D m => ?_, fun _ => rfl, fun _ => rfl, fun D => by simp [e], by simp [e], ?_⟩
    · show Continuous (if n = n₀ then sg else fun _ => 0)
      split_ifs; exacts [hsg, continuous_const]
    · show (0 : ℝ) = (if _ = n₀ then sg else fun _ => (0 : ℝ)) _
      split_ifs; exacts [(hsgZ (Or.inr (Or.inr ⟨_, mem_univ _, rfl⟩))).symm, rfl]
    · convert finite_empty
      ext n
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      show (if n = n₀ then sg else fun _ => (0 : ℝ)) 0 = 0
      split_ifs; exacts [hsgZ (Or.inr (Or.inl rfl)), rfl]
  refine ⟨e.toFun, EdgeData.continuous_toFun hv, fun q => ?_, fun q hq' => ?_, ?_⟩
  · cases q with
    | row n s =>
      show (if n = n₀ then sg else fun _ => (0 : ℝ)) _ ∈ _
      split_ifs; exacts [hsgm _, by simp]
    | _ => simp [EdgeData.toFun, e]
  · cases q with
    | row n s =>
      show (if n = n₀ then sg else fun _ => (0 : ℝ)) _ = 0
      split_ifs with h
      · subst h; exact hsgZ (Or.inl hq')
      · rfl
    | _ => simp [EdgeData.toFun, e]
  · show (if n₀ = n₀ then sg else fun _ => (0 : ℝ)) _ = 1
    rw [if_pos rfl]; exact hsgt

theorem separates (h𝒟 : IsMADFamily 𝒟) {F : Set (GSpace 𝒟)} (hF : IsClosed F) {q : GSpace 𝒟}
    (hq : q ∉ F) : Separates F q := by
  cases q with
  | infty => exact separates_infty h𝒟 hF hq
  | pnt D => exact separates_pnt h𝒟 hF hq
  | row n t =>
    by_cases h0 : t = 0
    · subst h0; exact separates_xpt h𝒟 hF hq
    by_cases hw : ∃ i, t = witT i
    · obtain ⟨i, rfl⟩ := hw
      exact separates_wit (m₀ := (n, i)) h𝒟 hF hq
    · refine separates_row_interior hF ?_ hq
      rintro (h | ⟨i, -, h⟩)
      · exact h0 h
      · exact hw ⟨i, h.symm⟩
  | arc D s => exact separates_arc hF hq
  | spoke D m s => exact separates_spoke hF hq

/-- **Theorem 4.5**: `G` is completely regular. -/
theorem completelyRegularSpace (h𝒟 : IsMADFamily 𝒟) : CompletelyRegularSpace (GSpace 𝒟) := by
  refine ⟨fun x K hK hx => ?_⟩
  obtain ⟨f, hf, hfm, hfK, hfx⟩ := separates h𝒟 hK hx
  refine ⟨fun g => ⟨1 - f g, by simp [(hfm g).1, (hfm g).2], by simp [(hfm g).1]⟩,
    Continuous.subtype_mk (continuous_const.sub hf) _, Subtype.ext ?_, fun g hg => Subtype.ext ?_⟩
  · simp [hfx]
  · simp [hfK hg]

/-- **Theorem 4.5**: `G` is a Tychonoff space (`T₁` and completely regular). -/
theorem t35Space (h𝒟 : IsMADFamily 𝒟) : T35Space (GSpace 𝒟) :=
  haveI := t1Space h𝒟
  haveI := completelyRegularSpace h𝒟
  { }

/-- **Theorem 4.5**: `G` is Hausdorff. -/
theorem t2Space (h𝒟 : IsMADFamily 𝒟) : T2Space (GSpace 𝒟) :=
  haveI := t35Space h𝒟
  inferInstance

/-- Continuous real functions separate the points of `G`. -/
theorem separatesPoints (h𝒟 : IsMADFamily 𝒟) (x y : GSpace 𝒟) (hxy : x ≠ y) :
    ∃ f : GSpace 𝒟 → ℝ, Continuous f ∧ f x ≠ f y := by
  haveI := t1Space h𝒟
  obtain ⟨f, hf, -, hfK, hfx⟩ := separates h𝒟 (isClosed_singleton (x := y))
    (fun h => hxy (mem_singleton_iff.1 h))
  exact ⟨f, hf, by rw [hfx, hfK rfl]; norm_num⟩

end GSpace

end MosaicSpaces
