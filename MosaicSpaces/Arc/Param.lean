module

public import MosaicSpaces.Arc.Minimal
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Path
public import Mathlib.Topology.Bases
public import Mathlib.Topology.UnitInterval

/-!
# The arc theorem, part 2: collapsing the gaps

Let `K ⊆ [0,1]` be closed, contain `0` and `1`, and satisfy, for a continuous `g : ℝ → X`:
`g` takes equal values at the two end points of every gap of `K`, and two points of `K` with equal
`g`-values bound a gap. A monotone continuous `ψ : [0,1] → [0,1]` that is constant exactly on the
gaps is built from a countable order-dense subset `Q` of `K` and an order isomorphism `Q ≃o ℚ`
(Cantor's back-and-forth theorem, `Order.iso_of_countable_dense`). Then `g` factors as `f ∘ ψ`
on `K` with `f : [0,1] → X` continuous and injective (`exists_injective`).

Together with part 1 this proves the **arc theorem** (`exists_arc`): in a Hausdorff space, two
distinct points joined by a path are the end points of an arc contained in the image of the path.
-/

@[expose] public section

open Set Filter Topology Function

namespace MosaicSpaces.Arc

variable {X : Type*} [TopologicalSpace X] {g : ℝ → X} {K : Set ℝ}

/-- Right end points of gaps of `K`. -/
def Rt (K : Set ℝ) : Set ℝ := {u | u ∈ K ∧ ∃ a ∈ K, a < u ∧ Ioo a u ∩ K = ∅}

/-- Left end points of gaps of `K`. -/
def Lt (K : Set ℝ) : Set ℝ := {u | u ∈ K ∧ ∃ b ∈ K, u < b ∧ Ioo u b ∩ K = ∅}

theorem countable_Lt : (Lt K).Countable := by
  have h : ∀ u : Lt K, ∃ r : ℚ, (u : ℝ) < r ∧ ∀ v ∈ K, (u : ℝ) < v → (r : ℝ) < v := by
    rintro ⟨u, -, b, hbK, hub, hgap⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hub
    refine ⟨r, hr1, fun v hvK huv => lt_of_lt_of_le hr2 (not_lt.1 fun hvb => ?_)⟩
    have : v ∈ Ioo u b ∩ K := ⟨⟨huv, hvb⟩, hvK⟩
    rw [hgap] at this; exact this
  choose r hr1 hr2 using h
  have hinj : Injective r := by
    intro u u' he
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Subtype.ext h)) with h | h
    · have h1 := hr2 u u' u'.2.1 h
      have h2 := hr1 u'
      rw [he] at h1; linarith
    · have h1 := hr2 u' u u.2.1 h
      have h2 := hr1 u
      rw [← he] at h1; linarith
  exact Set.countable_coe_iff.1 hinj.countable

section main

variable (hA : Adm g K) (hsep : ∀ s ∈ K, ∀ t ∈ K, s < t → g s = g t → Ioo s t ∩ K = ∅)
include hA hsep

theorem not_Rt_of_Lt {u : ℝ} (hL : u ∈ Lt K) : u ∉ Rt K := by
  rintro ⟨huK, a, haK, hau, hga⟩
  obtain ⟨-, b, hbK, hub, hgb⟩ := hL
  have h1 := hA.2.2.2.2 a haK u huK hau hga
  have h2 := hA.2.2.2.2 u huK b hbK hub hgb
  have h3 := hsep a haK b hbK (hau.trans hub) (h1.trans h2)
  have : u ∈ Ioo a b ∩ K := ⟨⟨hau, hub⟩, huK⟩
  rw [h3] at this; exact this

end main

/-- A point of `K` that is not a right end point of a gap is approached by `K` from the left. -/
theorem nonempty_of_not_Rt {s q : ℝ} (hs : s ∈ K) (hq : q ∈ K) (hsq : s < q) (hR : q ∉ Rt K) :
    (Ioo s q ∩ K).Nonempty := by
  by_contra h
  exact hR ⟨hq, s, hs, hsq, not_nonempty_iff_eq_empty.1 h⟩

section param

variable [T2Space X] (hA : Adm g K)
  (hsep : ∀ s ∈ K, ∀ t ∈ K, s < t → g s = g t → Ioo s t ∩ K = ∅) (hne : g 0 ≠ g 1)
include hA hsep hne

/-- Existence of a continuous injective `f : [0,1] → X` with `f 0 = g 0`, `f 1 = g 1` and range
in `g '' K`. -/
theorem exists_injective (hg : Continuous g) :
    ∃ f : unitInterval → X, Continuous f ∧ Injective f ∧ f 0 = g 0 ∧ f 1 = g 1 ∧
      range f ⊆ g '' K := by
  have hK01 : ∀ {u}, u ∈ K → 0 ≤ u ∧ u ≤ 1 := fun hu => hA.2.1 hu
  -- a countable dense subset of `K`
  obtain ⟨Q₀', hQ₀c, hQ₀d⟩ := TopologicalSpace.exists_countable_dense K
  set Q₀ : Set ℝ := Subtype.val '' Q₀'
  have hQ₀K : Q₀ ⊆ K := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hQ₀ : ∀ s t, (Ioo s t ∩ K).Nonempty → (Ioo s t ∩ Q₀).Nonempty := by
    rintro s t ⟨u, hu, huK⟩
    obtain ⟨x, hxU, hxQ⟩ := hQ₀d.inter_open_nonempty {x : K | (x : ℝ) ∈ Ioo s t}
      (isOpen_Ioo.preimage continuous_subtype_val) ⟨⟨u, huK⟩, hu⟩
    exact ⟨x, hxU, x, hxQ, rfl⟩
  set Q' : Set ℝ := (Q₀ \ Rt K) ∪ Lt K
  have hQ'K : Q' ⊆ K := fun q hq => hq.elim (fun h => hQ₀K h.1) (fun h => h.1)
  have hQ'R : ∀ q ∈ Q', q ∉ Rt K := fun q hq =>
    hq.elim (fun h => h.2) (fun h => not_Rt_of_Lt hA hsep h)
  have hQ'c : Q'.Countable := ((hQ₀c.image _).mono diff_subset).union countable_Lt
  -- every nonempty open portion of `K` between two points of `K` meets `Q'`
  have hD : ∀ s ∈ K, ∀ t ∈ K, s < t → (Ioo s t ∩ K).Nonempty → (Ioo s t ∩ Q').Nonempty := by
    intro s hs t ht hst hne'
    obtain ⟨q₀, hq₀I, hq₀Q⟩ := hQ₀ s t hne'
    by_cases hR : q₀ ∈ Rt K
    · obtain ⟨hq₀K, c, hcK, hcq, hcgap⟩ := hR
      have hsc : s ≤ c := by
        by_contra h
        have : s ∈ Ioo c q₀ ∩ K := ⟨⟨lt_of_not_ge h, hq₀I.1⟩, hs⟩
        rw [hcgap] at this; exact this
      rcases hsc.lt_or_eq with hsc | rfl
      · exact ⟨c, ⟨hsc, hcq.trans hq₀I.2⟩, Or.inr ⟨hcK, q₀, hq₀K, hcq, hcgap⟩⟩
      · -- `q₀` is not a left end point, so `K` accumulates at `q₀` from the right
        have hnL : q₀ ∉ Lt K := fun h => not_Rt_of_Lt hA hsep h ⟨hq₀K, s, hcK, hcq, hcgap⟩
        have hne2 : (Ioo q₀ t ∩ K).Nonempty := by
          by_contra h
          exact hnL ⟨hq₀K, t, ht, hq₀I.2, not_nonempty_iff_eq_empty.1 h⟩
        obtain ⟨q₁, hq₁I, hq₁Q⟩ := hQ₀ q₀ t hne2
        by_cases hR1 : q₁ ∈ Rt K
        · obtain ⟨hq₁K, c₁, hc₁K, hc₁q, hc₁gap⟩ := hR1
          have hc₁ : q₀ < c₁ := by
            rcases lt_trichotomy q₀ c₁ with h | h | h
            · exact h
            · exact absurd ⟨hq₀K, q₁, hq₁K, hq₁I.1, h ▸ hc₁gap⟩ hnL
            · have : q₀ ∈ Ioo c₁ q₁ ∩ K := ⟨⟨h, hq₁I.1⟩, hq₀K⟩
              rw [hc₁gap] at this; exact this.elim
          exact ⟨c₁, ⟨hcq.trans hc₁, hc₁q.trans hq₁I.2⟩, Or.inr ⟨hc₁K, q₁, hq₁K, hc₁q, hc₁gap⟩⟩
        · exact ⟨q₁, ⟨hcq.trans hq₁I.1, hq₁I.2⟩, Or.inl ⟨hq₁Q, hR1⟩⟩
    · exact ⟨q₀, hq₀I, Or.inl ⟨hq₀Q, hR⟩⟩
  -- the countable dense order `Q`
  set Q : Set ℝ := {q | q ∈ Q' ∧ (Ioo 0 q ∩ K).Nonempty ∧ (Ioo q 1 ∩ K).Nonempty}
  have hQK : Q ⊆ K := fun q hq => hQ'K hq.1
  have hQpos : ∀ q ∈ Q, 0 < q := fun q hq => by
    obtain ⟨u, hu, -⟩ := hq.2.1; linarith [hu.1, hu.2]
  have hQlt1 : ∀ q ∈ Q, q < 1 := fun q hq => by
    obtain ⟨u, hu, -⟩ := hq.2.2; linarith [hu.1, hu.2]
  have hK0 : (0 : ℝ) ∈ K := hA.2.2.1
  have hK1 : (1 : ℝ) ∈ K := hA.2.2.2.1
  have two : ∀ s ∈ K, ∀ t ∈ K, s < t → (Ioo s t ∩ K).Nonempty →
      ∃ q₀ ∈ Q, ∃ q₁ ∈ Q, s < q₀ ∧ q₀ < q₁ ∧ q₁ < t := by
    intro s hs t ht hst hne'
    obtain ⟨q, hqI, hqQ⟩ := hD s hs t ht hst hne'
    have hqK := hQ'K hqQ
    obtain ⟨q₁, hq₁I, hq₁Q⟩ :=
      hD s hs q hqK hqI.1 (nonempty_of_not_Rt hs hqK hqI.1 (hQ'R q hqQ))
    have hq₁K := hQ'K hq₁Q
    obtain ⟨q₀, hq₀I, hq₀Q⟩ :=
      hD s hs q₁ hq₁K hq₁I.1 (nonempty_of_not_Rt hs hq₁K hq₁I.1 (hQ'R q₁ hq₁Q))
    have hq₀K := hQ'K hq₀Q
    have hs0 := (hK01 hs).1
    have ht1 := (hK01 ht).2
    have hA0 : (Ioo 0 q₀ ∩ K).Nonempty := by
      obtain ⟨u, hu, huK⟩ := nonempty_of_not_Rt hs hq₀K hq₀I.1 (hQ'R q₀ hq₀Q)
      exact ⟨u, ⟨by linarith [hu.1], hu.2⟩, huK⟩
    have hq₀Q' : q₀ ∈ Q := ⟨hq₀Q, hA0, ⟨q₁, ⟨hq₀I.2, by linarith [hq₁I.2, hqI.2]⟩, hq₁K⟩⟩
    have hq₁Q' : q₁ ∈ Q := ⟨hq₁Q, ⟨q₀, ⟨by linarith [hq₀I.1], hq₀I.2⟩, hq₀K⟩,
      ⟨q, ⟨hq₁I.2, by linarith [hqI.2]⟩, hqK⟩⟩
    exact ⟨q₀, hq₀Q', q₁, hq₁Q', hq₀I.1, hq₀I.2, hq₁I.2.trans hqI.2⟩
  have hgap01 : (Ioo 0 1 ∩ K).Nonempty := by
    by_contra h
    exact hne (hA.2.2.2.2 0 hK0 1 hK1 zero_lt_one (not_nonempty_iff_eq_empty.1 h))
  -- order-theoretic instances on `Q`
  haveI : Countable Q := (hQ'c.mono fun q hq => hq.1).to_subtype
  haveI : Nonempty Q := by
    obtain ⟨q₀, hq₀, -⟩ := two 0 hK0 1 hK1 zero_lt_one hgap01
    exact ⟨⟨q₀, hq₀⟩⟩
  haveI : DenselyOrdered Q := ⟨fun a b hab => by
    obtain ⟨q₀, hq₀, q₁, -, h1, h2, h3⟩ := two a (hQK a.2) b (hQK b.2) hab
      (nonempty_of_not_Rt (hQK a.2) (hQK b.2) hab (hQ'R b b.2.1))
    exact ⟨⟨q₀, hq₀⟩, h1, show q₀ < (b : ℝ) by linarith⟩⟩
  haveI : NoMaxOrder Q := ⟨fun a => by
    obtain ⟨q₀, hq₀, -, -, h1, -, -⟩ := two a (hQK a.2) 1 hK1 (hQlt1 a a.2) a.2.2.2
    exact ⟨⟨q₀, hq₀⟩, h1⟩⟩
  haveI : NoMinOrder Q := ⟨fun a => by
    obtain ⟨-, -, q₁, hq₁, -, -, h2⟩ := two 0 hK0 a (hQK a.2) (hQpos a a.2) a.2.2.1
    exact ⟨⟨q₁, hq₁⟩, h2⟩⟩
  obtain ⟨ι⟩ := Order.iso_of_countable_dense Q ℚ
  let e := orderIsoIooNegOneOne ℝ
  let ν : Q → ℝ := fun q => ((e (ι q : ℝ) : ℝ) + 1) / 2
  have hν : StrictMono ν := by
    intro a b hab
    have h1 : ((ι a : ℚ) : ℝ) < ι b := by exact_mod_cast ι.strictMono hab
    have h2 : (e (ι a : ℝ) : ℝ) < e (ι b : ℝ) := e.strictMono h1
    simp only [ν]; linarith
  have hν01 : ∀ q, 0 < ν q ∧ ν q < 1 := fun q => by
    have := (e (ι q : ℝ)).2
    simp only [ν]; constructor <;> linarith [this.1, this.2]
  have hνdense : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∃ q, u < ν q ∧ ν q < v := by
    intro u v hu huv hv
    set w₁ : ℝ := 2 * u - 1 + (v - u) / 2
    set w₂ : ℝ := 2 * u - 1 + (v - u)
    have hw₁ : w₁ ∈ Ioo (-1 : ℝ) 1 := ⟨by simp only [w₁]; linarith, by simp only [w₁]; linarith⟩
    have hw₂ : w₂ ∈ Ioo (-1 : ℝ) 1 := ⟨by simp only [w₂]; linarith, by simp only [w₂]; linarith⟩
    have hw : (⟨w₁, hw₁⟩ : Ioo (-1 : ℝ) 1) < ⟨w₂, hw₂⟩ := by
      show w₁ < w₂; simp only [w₁, w₂]; linarith
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (e.symm.strictMono hw)
    refine ⟨ι.symm r, ?_, ?_⟩
    · have : (⟨w₁, hw₁⟩ : Ioo (-1 : ℝ) 1) < e (r : ℝ) := by
        simpa using e.strictMono hr1
      have h' : w₁ < e (r : ℝ) := this
      simp only [ν, OrderIso.apply_symm_apply]; simp only [w₁] at h'; linarith
    · have : e (r : ℝ) < (⟨w₂, hw₂⟩ : Ioo (-1 : ℝ) 1) := by
        simpa using e.strictMono hr2
      have h' : (e (r : ℝ) : ℝ) < w₂ := this
      simp only [ν, OrderIso.apply_symm_apply]; simp only [w₂] at h'; linarith
  -- the collapsing function
  let S : ℝ → Set ℝ := fun x => insert 0 (ν '' {q : Q | (q : ℝ) ≤ x})
  let ψ : ℝ → ℝ := fun x => sSup (S x)
  have hSbdd : ∀ x, BddAbove (S x) := fun x => ⟨1, by
    rintro _ (rfl | ⟨q, -, rfl⟩)
    · exact zero_le_one
    · exact (hν01 q).2.le⟩
  have hSne : ∀ x, (S x).Nonempty := fun x => ⟨0, mem_insert _ _⟩
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => le_csSup (hSbdd x) (mem_insert _ _)
  have hψ1 : ∀ x, ψ x ≤ 1 := fun x => csSup_le (hSne x) (by
    rintro _ (rfl | ⟨q, -, rfl⟩)
    · exact zero_le_one
    · exact (hν01 q).2.le)
  have hψmono : Monotone ψ := fun x y hxy => csSup_le_csSup (hSbdd y) (hSne x) (by
    rintro _ (rfl | ⟨q, hq, rfl⟩)
    · exact mem_insert _ _
    · exact Or.inr ⟨q, le_trans hq hxy, rfl⟩)
  have hψq : ∀ q : Q, ψ q = ν q := fun q => le_antisymm (csSup_le (hSne _) (by
      rintro _ (rfl | ⟨q', hq', rfl⟩)
      · exact (hν01 q).1.le
      · exact hν.monotone hq')) (le_csSup (hSbdd _) (Or.inr ⟨q, show (q : ℝ) ≤ q from le_rfl, rfl⟩))
  have hψlt : ∀ s ∈ K, ∀ t ∈ K, s < t → (Ioo s t ∩ K).Nonempty → ψ s < ψ t := by
    intro s hs t ht hst hne'
    obtain ⟨q₀, hq₀, q₁, hq₁, h1, h2, h3⟩ := two s hs t ht hst hne'
    have : ψ s ≤ ν ⟨q₀, hq₀⟩ := csSup_le (hSne _) (by
      rintro _ (rfl | ⟨q, hq, rfl⟩)
      · exact (hν01 _).1.le
      · exact (hν (show q < (⟨q₀, hq₀⟩ : Q) from show (q : ℝ) < q₀ from lt_of_le_of_lt hq h1)).le)
    calc ψ s ≤ ν ⟨q₀, hq₀⟩ := this
      _ < ν ⟨q₁, hq₁⟩ := hν (show (⟨q₀, hq₀⟩ : Q) < ⟨q₁, hq₁⟩ from h2)
      _ = ψ q₁ := (hψq ⟨q₁, hq₁⟩).symm
      _ ≤ ψ t := hψmono h3.le
  have hψeq : ∀ s x : ℝ, s ≤ x → (∀ q : Q, s < (q : ℝ) → (q : ℝ) ≤ x → False) → ψ s = ψ x := by
    intro s x hsx h
    have : S s = S x := by
      ext v
      constructor
      · rintro (rfl | ⟨q, hq, rfl⟩)
        · exact mem_insert _ _
        · exact Or.inr ⟨q, hq.trans hsx, rfl⟩
      · rintro (rfl | ⟨q, hq, rfl⟩)
        · exact mem_insert _ _
        · exact Or.inr ⟨q, not_lt.1 fun h' => h q h' hq, rfl⟩
    simp only [ψ, this]
  have hψ00 : ψ 0 = 0 := by
    have : S 0 = {0} := by
      ext v
      constructor
      · rintro (rfl | ⟨q, hq, rfl⟩)
        · rfl
        · exact absurd hq (not_le.2 (hQpos q q.2))
      · rintro rfl; exact mem_insert _ _
    simp only [ψ, this, csSup_singleton]
  have hψ11 : ψ 1 = 1 := by
    refine le_antisymm (hψ1 1) (le_of_forall_lt fun v hv => ?_)
    obtain ⟨q, hq1, -⟩ := hνdense (max v 0) 1 (le_max_right _ _) (max_lt hv zero_lt_one) le_rfl
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hq1)
      (le_csSup (hSbdd 1) (Or.inr ⟨q, (hQlt1 q q.2).le, rfl⟩))
  -- continuity of `ψ` on `[0,1]`, via a monotone extension with dense range
  let Ψ : ℝ → ℝ := fun x => if x < 0 then x else if 1 < x then x else ψ x
  have hΨmono : Monotone Ψ := by
    intro x y hxy
    simp only [Ψ]
    split_ifs with h1 h2 h3 h4 h5 h6 <;> first
      | linarith | linarith [hψ0 y] | linarith [hψ1 x] | exact hψmono hxy
  have hΨ : Continuous Ψ := hΨmono.continuous_of_denseRange (dense_of_exists_between fun u v huv => by
    by_cases hu : u < 0
    · refine ⟨(u + min v 0) / 2, ⟨(u + min v 0) / 2, ?_⟩, ?_, ?_⟩
      · have : (u + min v 0) / 2 < 0 := by linarith [min_le_right v 0]
        simp [Ψ, this]
      · linarith [lt_min huv hu]
      · linarith [min_le_left v 0, lt_min huv hu]
    by_cases hv : 1 < v
    · refine ⟨(max u 1 + v) / 2, ⟨(max u 1 + v) / 2, ?_⟩, ?_, ?_⟩
      · have h1 : 1 < (max u 1 + v) / 2 := by linarith [le_max_right u 1]
        have h0 : ¬ (max u 1 + v) / 2 < 0 := by linarith
        simp [Ψ, h1, h0]
      · linarith [le_max_left u 1, max_lt huv hv]
      · linarith [max_lt huv hv]
    · obtain ⟨q, hq1, hq2⟩ := hνdense u v (not_lt.1 hu) huv (not_lt.1 hv)
      refine ⟨ν q, ⟨q, ?_⟩, hq1, hq2⟩
      have h0 : ¬ (q : ℝ) < 0 := not_lt.2 (hQpos q q.2).le
      have h1 : ¬ 1 < (q : ℝ) := not_lt.2 (hQlt1 q q.2).le
      simp only [Ψ, h0, h1, if_false]
      exact hψq q)
  have hΨψ : ∀ x, 0 ≤ x → x ≤ 1 → Ψ x = ψ x := fun x h0 h1 => by
    simp [Ψ, not_lt.2 h0, not_lt.2 h1]
  -- every value is attained on `K`
  have hsurj : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∃ s ∈ K, ψ s = u := by
    intro u hu0 hu1
    obtain ⟨x, hx, hxu⟩ := intermediate_value_Icc zero_le_one hΨ.continuousOn
      (show u ∈ Icc (Ψ 0) (Ψ 1) by
        rw [hΨψ 0 le_rfl zero_le_one, hΨψ 1 zero_le_one le_rfl, hψ00, hψ11]; exact ⟨hu0, hu1⟩)
    rw [hΨψ x hx.1 hx.2] at hxu
    set A := K ∩ Icc 0 x
    have hAne : A.Nonempty := ⟨0, hK0, le_rfl, hx.1⟩
    have hAbdd : BddAbove A := ⟨x, fun y hy => hy.2.2⟩
    have hsA : sSup A ∈ A := (hA.1.inter isClosed_Icc).csSup_mem hAne hAbdd
    refine ⟨sSup A, hsA.1, ?_⟩
    rw [← hxu]
    refine hψeq _ _ hsA.2.2 fun q hq1 hq2 => ?_
    have : (q : ℝ) ≤ sSup A := le_csSup hAbdd ⟨hQK q.2, (hQpos q q.2).le, hq2⟩
    linarith
  -- equal `ψ`-values give equal `g`-values, and conversely
  have hW : ∀ s ∈ K, ∀ t ∈ K, ψ s = ψ t → g s = g t := by
    have aux : ∀ s ∈ K, ∀ t ∈ K, s < t → ψ s = ψ t → g s = g t := by
      intro s hs t ht hst he
      by_cases h : (Ioo s t ∩ K).Nonempty
      · exact absurd he (hψlt s hs t ht hst h).ne
      · exact hA.2.2.2.2 s hs t ht hst (not_nonempty_iff_eq_empty.1 h)
    intro s hs t ht he
    rcases lt_trichotomy s t with h | rfl | h
    · exact aux s hs t ht h he
    · rfl
    · exact (aux t ht s hs h he.symm).symm
  have hV : ∀ s ∈ K, ∀ t ∈ K, g s = g t → ψ s = ψ t := by
    have aux : ∀ s ∈ K, ∀ t ∈ K, s < t → g s = g t → ψ s = ψ t := by
      intro s hs t ht hst he
      have hgap := hsep s hs t ht hst he
      refine hψeq s t hst.le fun q hq1 hq2 => ?_
      rcases hq2.lt_or_eq with hq2 | hq2
      · have : (q : ℝ) ∈ Ioo s t ∩ K := ⟨⟨hq1, hq2⟩, hQK q.2⟩
        rw [hgap] at this; exact this
      · exact hQ'R q q.2.1 (hq2 ▸ ⟨ht, s, hs, hst, hgap⟩)
    intro s hs t ht he
    rcases lt_trichotomy s t with h | rfl | h
    · exact aux s hs t ht h he
    · rfl
    · exact (aux t ht s hs h he.symm).symm
  -- the arc
  choose sel hselK hsel using fun u : unitInterval => hsurj u u.2.1 u.2.2
  let f : unitInterval → X := fun u => g (sel u)
  haveI : CompactSpace K :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.of_isClosed_subset hA.1 hA.2.1)
  let κ : K → unitInterval := fun s => ⟨ψ s, hψ0 s, hψ1 s⟩
  have hκ : Continuous κ := Continuous.subtype_mk ((hΨ.comp continuous_subtype_val).congr
    fun s => by simp only [Function.comp_apply]; exact hΨψ _ (hK01 s.2).1 (hK01 s.2).2) _
  have hκs : Surjective κ := fun u => ⟨⟨sel u, hselK u⟩, Subtype.ext (hsel u)⟩
  have hq : Topology.IsQuotientMap κ := hκ.isClosedMap.isQuotientMap hκ hκs
  have hfκ : f ∘ κ = g ∘ Subtype.val := funext fun s =>
    hW _ (hselK _) _ s.2 (by rw [hsel])
  refine ⟨f, hq.continuous_iff.2 (hfκ ▸ hg.comp continuous_subtype_val), ?_, ?_, ?_, ?_⟩
  · intro u v he
    exact Subtype.ext ((hsel u).symm.trans ((hV _ (hselK u) _ (hselK v) he).trans (hsel v)))
  · exact hW _ (hselK 0) 0 hK0 (by rw [hsel, hψ00]; rfl)
  · exact hW _ (hselK 1) 1 hK1 (by rw [hsel, hψ11]; rfl)
  · rintro _ ⟨u, rfl⟩
    exact ⟨sel u, hselK u, rfl⟩

end param

/-- **The arc theorem** (EXT-ARC): in a Hausdorff space, two distinct points joined by a path are
the end points of an arc (a topological embedding of `[0,1]`) contained in the image of the path. -/
theorem exists_arc [T2Space X] {x y : X} (γ : Path x y) (hxy : x ≠ y) :
    ∃ f : unitInterval → X, IsEmbedding f ∧ f 0 = x ∧ f 1 = y ∧ range f ⊆ range γ := by
  obtain ⟨K, hK⟩ := exists_minimal_adm γ.continuous_extend
  obtain ⟨f, hf, hinj, hf0, hf1, hfr⟩ := exists_injective hK.prop
    (fun s hs t ht hst he => Minimal.gap_of_eq hK hs ht hst he)
    (by rw [γ.extend_zero, γ.extend_one]; exact hxy) γ.continuous_extend
  refine ⟨f, (hf.isClosedEmbedding hinj).isEmbedding, by rw [hf0, γ.extend_zero],
    by rw [hf1, γ.extend_one], hfr.trans ?_⟩
  rw [← γ.extend_range]
  exact image_subset_range _ _

end MosaicSpaces.Arc
