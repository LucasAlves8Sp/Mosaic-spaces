module

public import MosaicSpaces.G.Capture
public import MosaicSpaces.G.Tychonoff
public import MosaicSpaces.ArcConsequences
public import MosaicSpaces.Cone
public import MosaicSpaces.Cone4
public import MosaicSpaces.G.Remarks
public import MosaicSpaces.PathDetermined
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Answers to Lavallee's questions

All three questions are answered here in the negative by constructed spaces. Nothing is assumed:
the maximal almost disjoint family is obtained from Zorn's lemma (`exists_isMADFamily`).

* **Q3** (Corollary 4.12) is answered as asked by `answer_Q3`: `G` is a Tychonoff, locally
  arcwise connected mosaic space which is not a quasi-curve space (Theorem 4.5, Proposition 4.7,
  Theorem 4.11). The earlier, weaker `answer_Q3_path` (locally *path* connected form) is kept;
  it is implied by `answer_Q3`.
* **Q2** (Corollary 6.4) is answered in full by `answer_Q2_full`: the cone over `G` is a
  contractible, Hausdorff, locally arcwise connected m-continuum space with an open subspace that
  is not an m-continuum space.
* **Q1a and Q1b** are answered by the same cone: `answer_Q1b`, `answer_Q1a`. The article remarks
  this after Corollary 6.4 ("`𝖼G` is at the same time a counterexample to Q1a, Q1b and Q3"). The
  article's own main route to Q1 (Theorem 3.4, the space `E(K)` over an arcless continuum) is
  **not** formalized.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MosaicSpaces

/-- A maximal almost disjoint family, fixed by choice (it exists by `exists_isMADFamily`). -/
noncomputable def madFamily : Set (Set (ℕ × ℕ)) := Classical.choose exists_isMADFamily

theorem isMADFamily_madFamily : IsMADFamily madFamily := Classical.choose_spec exists_isMADFamily

/-- The space `G` of Construction 4.1. -/
abbrev G : Type := GSpace madFamily

instance : LocallyPathConnectedSpace G := GSpace.locallyPathConnectedSpace isMADFamily_madFamily

/-- **Theorem 4.11**, the parts not involving separation axioms or arcs. The Tychonoff property
is `G_t35`, the arcwise forms are `G_arcwise`, and the countable-spread form of Proposition 4.9 is
`G_spread_frechet`. -/
theorem G_properties :
    IsMosaicSpace G ∧ SequentialSpace G ∧ T1Space G ∧
    (∀ O : Set G, IsOpen O → ∀ x, IsOpen (pathComponentIn O x)) ∧
    LocallyPathConnectedSpace G ∧ LocallyMStronglyConnected G ∧ LocallyConnectedSpace G ∧
    Tendsto GSpace.xpt atTop (𝓝 (GSpace.infty : G)) ∧
    (∀ K : Set G, IsMetricContinuum K → GSpace.infty ∈ K → {n | GSpace.xpt n ∈ K}.Finite) ∧
    ¬ IsMContinuumSpace G ∧ ¬ IsQuasiCurveSpace G ∧
    (∀ (a b : G) (γ : Path a b), {n | GSpace.xpt n ∈ range γ}.Finite) := by
  have h := isMADFamily_madFamily
  have hX := GSpace.isMosaicSpace h
  have hm : LocallyMStronglyConnected G :=
    (locallyPathConnectedOpen_iff.2 inferInstance).locallyMStronglyConnected hX
  exact ⟨hX, hX.sequentialSpace, hX.t1Space, fun O hO x => GSpace.isOpen_pathComponentIn h hO x,
    inferInstance, hm, hm.locallyConnectedSpace, GSpace.tendsto_xpt,
    fun K hK hinf => GSpace.finite_xpt_of_isMetricContinuum h hK hinf,
    GSpace.not_isMContinuumSpace h, GSpace.not_isQuasiCurveSpace h,
    fun a b γ => GSpace.finite_xpt_of_path h γ⟩

/-- **Corollary 4.12**, locally path connected form: a locally path connected mosaic space which
is not a quasi-curve space (and not even an m-continuum space). Superseded by `answer_Q3`. -/
theorem answer_Q3_path :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMosaicSpace X ∧ LocallyPathConnectedSpace X ∧
      (∀ O : Set X, IsOpen O → ∀ x, IsOpen (pathComponentIn O x)) ∧
      ¬ IsQuasiCurveSpace X ∧ ¬ IsMContinuumSpace X :=
  ⟨G, inferInstance, G_properties.1, inferInstance, G_properties.2.2.2.1,
    G_properties.2.2.2.2.2.2.2.2.2.2.1, G_properties.2.2.2.2.2.2.2.2.2.1⟩

/-- **Corollary 6.4**: the cone over `G`. -/
theorem cone_G_properties :
    IsMContinuumSpace (Cone G) ∧ ContractibleSpace (Cone G) ∧
    LocallyPathConnectedSpace (Cone G) ∧ LocallyMStronglyConnected (Cone G) ∧
    LocallyConnectedSpace (Cone G) ∧ IsOpen ({Cone.vertex}ᶜ : Set (Cone G)) ∧
    ¬ IsMContinuumSpace ({Cone.vertex}ᶜ : Set (Cone G)) ∧ ¬ IsQuasiCurveSpace (Cone G) := by
  have hX := GSpace.isMosaicSpace isMADFamily_madFamily
  have hnot := GSpace.not_isMContinuumSpace isMADFamily_madFamily
  have hm : LocallyMStronglyConnected (Cone G) := Cone.locallyMStronglyConnected hX
  have hU : ¬ IsMContinuumSpace ({Cone.vertex}ᶜ : Set (Cone G)) :=
    Cone.not_isMContinuumSpace_punctured hX hnot
  exact ⟨Cone.isMContinuumSpace hX, Cone.contractibleSpace, Cone.locallyPathConnectedSpace, hm,
    hm.locallyConnectedSpace, Cone.isOpen_compl_vertex, hU,
    fun hq => hU (hq.isMContinuumSpace_of_isOpen Cone.isOpen_compl_vertex)⟩

/-- **Answer to Q2** (Corollary 6.4): a locally m-strongly connected m-continuum space need not
have all its open subspaces m-continuum spaces; the converse of Lavallee's Theorem 5.2 fails. -/
theorem answer_Q2 :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyMStronglyConnected X ∧
      ∃ U : Set X, IsOpen U ∧ ¬ IsMContinuumSpace U :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_properties.2.2.2.1, _,
    cone_G_properties.2.2.2.2.2.1, cone_G_properties.2.2.2.2.2.2.1⟩

/-- **Answer to Q1b** (via the cone over `G`, as remarked after Corollary 6.4): a locally
m-strongly connected m-continuum space need not be a quasi-curve space. -/
theorem answer_Q1b :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyMStronglyConnected X ∧
      ¬ IsQuasiCurveSpace X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_properties.2.2.2.1,
    cone_G_properties.2.2.2.2.2.2.2⟩

/-- **Answer to Q1a** (via the cone over `G`): a locally connected m-continuum space need not be a
quasi-curve space. -/
theorem answer_Q1a :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyConnectedSpace X ∧
      ¬ IsQuasiCurveSpace X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_properties.2.2.2.2.1,
    cone_G_properties.2.2.2.2.2.2.2⟩

/-! ### Hausdorff and arcwise forms (Theorem 4.5, Proposition 4.7, Corollaries 4.12 and 6.4) -/

/-- **Theorem 4.5**: `G` is a Tychonoff space. -/
theorem G_t35 : T35Space G := GSpace.t35Space isMADFamily_madFamily

instance : T2Space G := GSpace.t2Space isMADFamily_madFamily

/-- **Proposition 4.7** as stated: the path components of every open subset of `G` are open and
arcwise connected; `G` is locally arcwise connected. -/
theorem G_arcwise :
    (∀ O : Set G, IsOpen O → ∀ x ∈ O,
      IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
    LocallyArcwiseConnected G := by
  have hX := GSpace.isMosaicSpace isMADFamily_madFamily
  exact ⟨fun O hO x hx => ⟨GSpace.isOpen_pathComponentIn isMADFamily_madFamily hO x,
    hX.arcwiseConnected_pathComponentIn hx⟩, hX.locallyArcwiseConnected_iff.2 inferInstance⟩

/-- The cone over `G` is Hausdorff (Theorem 6.3(5) with Theorem 4.5). -/
theorem cone_G_t2 : T2Space (Cone G) := Cone.t2Space (GSpace.separatesPoints isMADFamily_madFamily)

/-- The cone over `G` is locally arcwise connected (Theorem 6.3(2) with display (2.1)). -/
theorem cone_G_locallyArcwiseConnected : LocallyArcwiseConnected (Cone G) :=
  (Cone.isMosaicSpace (GSpace.isMosaicSpace isMADFamily_madFamily)).locallyArcwiseConnected_iff.2
    Cone.locallyPathConnectedSpace

/-- **Answer to Q3** (Corollary 4.12), as asked: a locally arcwise connected mosaic space (here
moreover Tychonoff) which is not a quasi-curve space. -/
theorem answer_Q3 :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMosaicSpace X ∧ T35Space X ∧
      LocallyArcwiseConnected X ∧
      (∀ O : Set X, IsOpen O → ∀ x ∈ O,
        IsOpen (pathComponentIn O x) ∧ ArcwiseConnected (pathComponentIn O x)) ∧
      ¬ IsQuasiCurveSpace X ∧ ¬ IsMContinuumSpace X :=
  ⟨G, inferInstance, G_properties.1, G_t35, G_arcwise.2, G_arcwise.1,
    G_properties.2.2.2.2.2.2.2.2.2.2.1, G_properties.2.2.2.2.2.2.2.2.2.1⟩

/-- **Corollary 6.4** in full: the cone over `G` is a contractible, Hausdorff m-continuum space,
locally arcwise connected and hence locally m-strongly connected, with an open subspace that is not
an m-continuum space; it is not a quasi-curve space. -/
theorem answer_Q2_full :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ T2Space X ∧
      ContractibleSpace X ∧ LocallyArcwiseConnected X ∧ LocallyMStronglyConnected X ∧
      (∃ U : Set X, IsOpen U ∧ ¬ IsMContinuumSpace U) ∧ ¬ IsQuasiCurveSpace X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_t2, cone_G_properties.2.1,
    cone_G_locallyArcwiseConnected, cone_G_properties.2.2.2.1,
    ⟨_, cone_G_properties.2.2.2.2.2.1, cone_G_properties.2.2.2.2.2.2.1⟩,
    cone_G_properties.2.2.2.2.2.2.2⟩

/-! ### Remark 4.13(1) and Theorem 7.4 -/

/-- **Remark 4.13(1)**: `G` is not first countable at `∞` (from Proposition 7.1 and
Theorem 4.11). -/
theorem G_not_isCountablyGenerated_nhds_infty :
    ¬ (𝓝 (GSpace.infty : G)).IsCountablyGenerated := by
  intro hc
  have hX := (G_properties).1
  have hm := (G_properties).2.2.2.2.2.1
  obtain ⟨N, L, -, hL, hinf, hxL⟩ :=
    exists_metricContinuum_tail hX isOpen_univ (mem_univ _) (hm GSpace.infty)
      (GSpace.tendsto_xpt (𝒟 := madFamily))
  refine (Set.Ici_infinite N) ((G_properties.2.2.2.2.2.2.2.2.1 L hL hinf).subset ?_)
  intro n hn
  exact hxL n hn

theorem G_not_firstCountable : ¬ FirstCountableTopology G := fun h =>
  G_not_isCountablyGenerated_nhds_infty inferInstance

/-- The condition (H) of Theorem 7.4: every nonempty open subspace is an m-continuum space. -/
def AllOpenMContinuum (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → IsMContinuumSpace U

/-- **Theorem 7.4**, the implications `(QC) ⇒ (H) ⇒ (LmS) ⇒ (LC)` (for mosaic spaces; the article
states them for m-continuum spaces). -/
theorem chain_implications {X : Type*} [TopologicalSpace X] (hX : IsMosaicSpace X) :
    (IsQuasiCurveSpace X → AllOpenMContinuum X) ∧
    (AllOpenMContinuum X → LocallyMStronglyConnected X) ∧
    (LocallyMStronglyConnected X → LocallyConnectedSpace X) :=
  ⟨fun h U hU _ => h.isMContinuumSpace_of_isOpen hU,
    fun h => locallyMStronglyConnected_of_forall_isOpen hX h,
    fun h => h.locallyConnectedSpace⟩

/-- **Theorem 7.4**, strictness of `(H) ⇒ (LmS)`, witnessed by `𝖼G`. (The strictness of the other
two implications uses `E(K)` and `𝖼Z`, which are not formalized.) -/
theorem chain_strict_H_LmS :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyMStronglyConnected X ∧
      ¬ AllOpenMContinuum X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_properties.2.2.2.1, fun h =>
    cone_G_properties.2.2.2.2.2.2.1 (h _ cone_G_properties.2.2.2.2.2.1 ⟨Cone.mk (GSpace.infty, 0),
      fun e => by
        have := Cone.mk_eq_vertex_iff.1 e
        exact zero_ne_one this⟩)⟩

/-- After Theorem 7.4: for first countable mosaic spaces (H) and (LmS) are equivalent
(Proposition 7.1). -/
theorem firstCountable_H_iff_LmS {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (hX : IsMosaicSpace X) : AllOpenMContinuum X ↔ LocallyMStronglyConnected X :=
  ⟨(chain_implications hX).2.1, fun h U hU _ => isMContinuumSpace_of_isOpen_of_firstCountable hX h hU⟩

/-! ### Theorem 6.3(4), Proposition 4.9 (countable spread) and Remark 4.13(2) -/

/-- **Theorem 6.3(4)**: for a nonempty mosaic space `Y`, every nonempty open subspace of `𝖼Y` is an
m-continuum space iff every nonempty open subspace of `Y` is. -/
theorem cone_allOpenMContinuum_iff {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    (hY : IsMosaicSpace Y) : AllOpenMContinuum (Cone Y) ↔ AllOpenMContinuum Y :=
  ⟨Cone.allOpenMCont_of_cone hY, Cone.allOpenMCont_cone hY⟩

/-- **Proposition 4.9** in its countable-spread form and **Remark 4.13(2)** for `G`. -/
theorem G_spread_frechet :
    (∀ K : Set G, IsClosed K → IsPreconnected K → GSpace.infty ∈ K →
      (∀ A ⊆ K, (∀ a ∈ A, ∃ U : Set G, IsOpen U ∧ U ∩ A = {a}) → A.Countable) →
      {n | GSpace.xpt n ∈ K}.Finite) ∧
    (GSpace.infty : G) ∈ closure (range GSpace.wit) ∧
    (∀ v : ℕ → G, (∀ n, v n ∈ range GSpace.wit) → ¬ Tendsto v atTop (𝓝 GSpace.infty)) ∧
    ¬ FrechetUrysohnSpace G :=
  ⟨fun _ hKc hconn hinf hspread =>
      GSpace.finite_xpt_of_spread isMADFamily_madFamily hKc hconn hinf hspread,
    GSpace.infty_mem_closure_wit, fun _ hv => GSpace.not_tendsto_wit isMADFamily_madFamily hv,
    GSpace.not_frechetUrysohnSpace isMADFamily_madFamily⟩


/-- The family `madFamily` is nonempty. -/
theorem madFamily_nonempty : (madFamily : Set (Set (ℕ × ℕ))).Nonempty := by
  have hY : IsC (range fun n : ℕ => (n, 0)) := by
    refine ⟨Set.infinite_range_of_injective fun a b h => by simpa using h, fun n => ?_⟩
    refine (Set.finite_singleton 0).subset ?_
    rintro i ⟨m, hm⟩
    simp only [Prod.mk.injEq] at hm
    exact hm.2.symm
  obtain ⟨D, hD, -⟩ := isMADFamily_madFamily.maximal _ hY
  exact ⟨D, hD⟩

/-- **Remark 4.10** for `G`. -/
theorem G_remark_4_10 :
    ∃ K : Set G, IsClosed K ∧ IsConnected K ∧ SeparableSpace K ∧ GSpace.infty ∈ K ∧
      {n | GSpace.xpt n ∈ K}.Infinite ∧
      ¬ ({D | GSpace.pnt D ∈ K} : Set madFamily).Countable :=
  let ⟨D, hD⟩ := madFamily_nonempty
  GSpace.remark_4_10 isMADFamily_madFamily ⟨D, hD⟩

/-- **Corollary 4.12**, second sentence: `G` is not path-determined. -/
theorem G_not_isPathDetermined : ¬ IsPathDetermined G := fun h =>
  G_properties.2.2.2.2.2.2.2.2.2.2.1
    ((prop_2_10_tfae (X := G)).out 1 5 |>.1 h)

/-- **Theorem 7.4**: local arcwise connectedness does not imply (H) (witness `𝖼G`). -/
theorem chain_LAC_not_H :
    ∃ (X : Type) (_ : TopologicalSpace X), IsMContinuumSpace X ∧ LocallyArcwiseConnected X ∧
      ¬ AllOpenMContinuum X :=
  ⟨Cone G, inferInstance, cone_G_properties.1, cone_G_locallyArcwiseConnected,
    fun h => cone_G_properties.2.2.2.2.2.2.1 (h _ cone_G_properties.2.2.2.2.2.1
      ⟨Cone.mk (GSpace.infty, 0), fun e => by
        have := Cone.mk_eq_vertex_iff.1 e
        exact zero_ne_one this⟩)⟩

end MosaicSpaces
