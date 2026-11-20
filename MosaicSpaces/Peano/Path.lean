module

public import MosaicSpaces.Peano.Chain
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Path
public import Mathlib.Topology.UnitInterval
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Peano continua are locally path connected, part 2: paths as limits of chains

In a complete, uniformly locally connected metric space, points `a`, `b` closer than `δ₀` are
joined by a path staying within `2ε` of `a` (`exists_path_near`). The path is the limit of
refining chains: at stage `n` there are `2^{K_n}+1` points with consecutive points closer than
`δ_n`; each step is replaced by a `δ_{n+1}`-chain inside a preconnected set of radius `ε_n`,
padded to `2^k` steps. The path at `t` is the limit of the stage-`n` point with index
`⌊t·2^{K_n}⌋`.
-/

@[expose] public section

open Set Filter Topology Metric

namespace MosaicSpaces.Peano

variable {X : Type*} [MetricSpace X]

/-- The data for the construction: radii `ε n` and step bounds `δ n ≤ ε n`. -/
structure ULCData (X : Type*) [MetricSpace X] where
  ε : ℕ → ℝ
  δ : ℕ → ℝ
  δpos : ∀ n, 0 < δ n
  δle : ∀ n, δ n ≤ ε n
  conn : ∀ n (a b : X), dist a b < δ n →
    ∃ C : Set X, IsPreconnected C ∧ a ∈ C ∧ b ∈ C ∧ C ⊆ ball a (ε n)

variable (P : ULCData X) (a b : X)

/-- A stage of the construction. -/
structure StageP (n K : ℕ) (g : ℕ → X) : Prop where
  zero : g 0 = a
  top : g (2 ^ K) = b
  step : ∀ i < 2 ^ K, dist (g i) (g (i + 1)) < P.δ n

theorem refine_stage {n K : ℕ} {g : ℕ → X} (h : StageP P a b n K g) :
    ∃ k, ∃ g' : ℕ → X, StageP P a b (n + 1) (K + k) g' ∧ (∀ i ≤ 2 ^ K, g' (i * 2 ^ k) = g i) ∧
      ∀ i < 2 ^ K, ∀ j ≤ 2 ^ k, dist (g i) (g' (i * 2 ^ k + j)) < P.ε n := by
  classical
  have : Nonempty X := ⟨a⟩
  have hch : ∀ i, i < 2 ^ K → ∃ (C : Set X) (m : ℕ) (c : ℕ → X), C ⊆ ball (g i) (P.ε n) ∧
      g (i + 1) ∈ C ∧ c 0 = g i ∧ c m = g (i + 1) ∧ (∀ j ≤ m, c j ∈ C) ∧
      ∀ j < m, dist (c j) (c (j + 1)) < P.δ (n + 1) := by
    intro i hi
    obtain ⟨C, hC, hiC, hi1C, hCsub⟩ := P.conn n _ _ (h.step i hi)
    obtain ⟨m, c, h0, hm, hcC, hstep⟩ := exists_chain hC (P.δpos (n + 1)) hiC hi1C
    exact ⟨C, m, c, hCsub, hi1C, h0, hm, hcC, hstep⟩
  choose! C m c hCsub hi1C hc0 hcm hcC hcstep using hch
  set M := (Finset.range (2 ^ K)).sup m
  have hmM : ∀ i < 2 ^ K, m i ≤ M := fun i hi => Finset.le_sup (Finset.mem_range.2 hi)
  set k := M + 1
  set L := 2 ^ k
  have hL : 0 < L := by positivity
  have hML : M < L - 1 := by
    have := Nat.lt_two_pow_self (n := M)
    have h2 : L = 2 * 2 ^ M := by simp [L, k, pow_succ, mul_comm]
    omega
  let d : ℕ → ℕ → X := fun i j => if j ≤ m i then c i j else g (i + 1)
  let g' : ℕ → X := fun p => if p / L < 2 ^ K then d (p / L) (p % L) else b
  have hdiv : ∀ i j, j < L → (i * L + j) / L = i ∧ (i * L + j) % L = j := fun i j hj => by
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hj, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hg'eq : ∀ i < 2 ^ K, ∀ j < L, g' (i * L + j) = d i j := fun i hi j hj => by
    simp only [g', (hdiv i j hj).1, (hdiv i j hj).2, hi, ite_true]
  have hd0 : ∀ i < 2 ^ K, d i 0 = g i := fun i hi => by simp [d, hc0 i hi]
  have hdlast : ∀ i < 2 ^ K, ∀ j, m i ≤ j → d i j = g (i + 1) := fun i hi j hj => by
    by_cases h' : j ≤ m i
    · have : j = m i := le_antisymm h' hj
      simp [d, this, hcm i hi]
    · simp [d, h']
  have hdC : ∀ i < 2 ^ K, ∀ j, d i j ∈ C i := fun i hi j => by
    by_cases h' : j ≤ m i
    · simp only [d, h', ite_true]; exact hcC i hi j h'
    · simp only [d, h', ite_false]; exact hi1C i hi
  have hcorner : ∀ i ≤ 2 ^ K, g' (i * L) = g i := fun i hi => by
    rcases hi.lt_or_eq with hi | rfl
    · rw [show i * L = i * L + 0 from rfl, hg'eq i hi 0 hL, hd0 i hi]
    · simp [g', Nat.mul_div_cancel _ hL, h.top]
  refine ⟨k, g', ⟨?_, ?_, ?_⟩, hcorner, ?_⟩
  · have := hcorner 0 (Nat.zero_le _)
    simpa [h.zero] using this
  · rw [pow_add]; exact (hcorner (2 ^ K) le_rfl).trans h.top
  · intro p hp
    have hpL : p / L < 2 ^ K := by
      rw [pow_add] at hp
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hp)
    set i := p / L
    set j := p % L
    have hj : j < L := Nat.mod_lt _ hL
    have hp' : p = i * L + j := by rw [mul_comm]; exact (Nat.div_add_mod p L).symm
    rw [hp', hg'eq i hpL j hj]
    by_cases hj1 : j + 1 < L
    · rw [show i * L + j + 1 = i * L + (j + 1) by ring, hg'eq i hpL (j + 1) hj1]
      by_cases hjm : j < m i
      · have h1 : j ≤ m i := hjm.le
        have h2 : j + 1 ≤ m i := hjm
        simp only [d, h1, h2, ite_true]
        exact hcstep i hpL j hjm
      · rw [hdlast i hpL j (not_lt.1 hjm), hdlast i hpL (j + 1) (by omega), dist_self]
        exact P.δpos _
    · have hjL : j + 1 = L := by omega
      rw [show i * L + j + 1 = (i + 1) * L by rw [add_mul, one_mul, ← hjL]; ring,
        hcorner (i + 1) hpL, hdlast i hpL j (by have := hmM i hpL; omega), dist_self]
      exact P.δpos _
  · intro i hi j hj
    rcases hj.lt_or_eq with hj | rfl
    · rw [hg'eq i hi j hj, dist_comm]
      exact hCsub i hi (hdC i hi j)
    · rw [show i * L + L = (i + 1) * L by ring, hcorner (i + 1) hi, dist_comm]
      exact hCsub i hi (hi1C i hi)

/-- The refinement step packed with its properties. -/
noncomputable def nextStage (n : ℕ) (s : {p : ℕ × (ℕ → X) // StageP P a b n p.1 p.2}) :
    {q : ℕ × (ℕ → X) // ∃ k, q.1 = s.1.1 + k ∧ StageP P a b (n + 1) q.1 q.2 ∧
      (∀ i ≤ 2 ^ s.1.1, q.2 (i * 2 ^ k) = s.1.2 i) ∧
      ∀ i < 2 ^ s.1.1, ∀ j ≤ 2 ^ k, dist (s.1.2 i) (q.2 (i * 2 ^ k + j)) < P.ε n} :=
  let h := refine_stage P a b s.2
  ⟨(s.1.1 + h.choose, h.choose_spec.choose), h.choose, rfl, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2⟩

/-- The sequence of stages. -/
noncomputable def stage (h0 : StageP P a b 0 0 (fun i => if i = 0 then a else b)) :
    (n : ℕ) → {p : ℕ × (ℕ → X) // StageP P a b n p.1 p.2}
  | 0 => ⟨(0, fun i => if i = 0 then a else b), h0⟩
  | n + 1 => ⟨(nextStage P a b n (stage h0 n)).1, (nextStage P a b n (stage h0 n)).2.choose_spec.2.1⟩

/-- **Paths from chains.** In a complete metric space with uniform local connectedness data
`P` (`ε n = ε / 2^(n+1)`), points closer than `δ 0` are joined by a path within `2ε` of `a`. -/
theorem exists_path_near [CompleteSpace X] {ε : ℝ} (hε : 0 < ε)
    (hPε : ∀ n, P.ε n = ε / 2 / 2 ^ n) (hab : dist a b < P.δ 0) :
    ∃ γ : Path a b, ∀ t, dist a (γ t) < 2 * ε := by
  classical
  have : Nonempty X := ⟨a⟩
  have h0 : StageP P a b 0 0 (fun i => if i = 0 then a else b) :=
    ⟨by simp, by simp, fun i hi => by
      have : i = 0 := by simpa using hi
      subst this; simpa using hab⟩
  let S := stage P a b h0
  let K : ℕ → ℕ := fun n => (S n).1.1
  let g : ℕ → ℕ → X := fun n => (S n).1.2
  have hS : ∀ n, StageP P a b n (K n) (g n) := fun n => (S n).2
  -- the relation between consecutive stages
  have hrel : ∀ n, ∃ k, K (n + 1) = K n + k ∧ (∀ i ≤ 2 ^ K n, g (n + 1) (i * 2 ^ k) = g n i) ∧
      ∀ i < 2 ^ K n, ∀ j ≤ 2 ^ k, dist (g n i) (g (n + 1) (i * 2 ^ k + j)) < P.ε n :=
    fun n => by
      obtain ⟨k, h1, -, h3, h4⟩ := (nextStage P a b n (S n)).2
      exact ⟨k, h1, h3, h4⟩
  choose k hk hkcorner hkloc using hrel
  -- indices
  let idx : ℕ → ℝ → ℕ := fun n t => ⌊t * 2 ^ K n⌋₊
  have hidx : ∀ n (t : unitInterval), idx n t ≤ 2 ^ K n := fun n t => by
    refine Nat.floor_le_of_le ?_
    have := t.2.2
    push_cast
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (K n)]
  have hidxsucc : ∀ n (t : unitInterval), idx (n + 1) t = idx n t * 2 ^ k n + idx (n + 1) t % 2 ^ k n
      ∧ idx (n + 1) t % 2 ^ k n ≤ 2 ^ k n := fun n t => by
    refine ⟨?_, (Nat.mod_lt _ (by positivity)).le⟩
    have h1 : idx (n + 1) t / 2 ^ k n = idx n t := by
      simp only [idx]
      rw [hk n, ← Nat.floor_div_natCast]
      congr 1
      push_cast
      rw [pow_add]
      field_simp
    conv_lhs => rw [← Nat.div_add_mod (idx (n + 1) t) (2 ^ k n), h1]
    ring
  let s : unitInterval → ℕ → X := fun t n => g n (idx n t)
  have hs : ∀ t n, dist (s t n) (s t (n + 1)) ≤ ε / 2 / 2 ^ n := fun t n => by
    obtain ⟨he, hle⟩ := hidxsucc n t
    simp only [s]
    rw [he]
    rcases (hidx n t).lt_or_eq with hlt | heq
    · rw [← hPε n]; exact (hkloc n _ hlt _ hle).le
    · -- `t = 1`: the index is the last one
      have : idx (n + 1) t % 2 ^ k n = 0 := by
        have h2 := hidx (n + 1) t
        rw [he, heq, hk n, pow_add] at h2
        omega
      rw [this, add_zero, heq, hkcorner n _ le_rfl, dist_self]
      positivity
  have hcauchy : ∀ t, CauchySeq (s t) := fun t => cauchySeq_of_le_geometric_two (hs t)
  let γf : unitInterval → X := fun t => limUnder atTop (s t)
  have hlim : ∀ t, Tendsto (s t) atTop (𝓝 (γf t)) := fun t => (hcauchy t).tendsto_limUnder
  have hnear : ∀ t n, dist (s t n) (γf t) ≤ ε / 2 ^ n := fun t n =>
    dist_le_of_le_geometric_two_of_tendsto (hs t) (hlim t) n
  -- continuity
  have hcont : Continuous γf := by
    refine Metric.uniformContinuous_iff.2 (fun η hη => ?_) |>.continuous
    obtain ⟨n, hn⟩ := exists_nat_gt (3 * ε / η)
    have hn' : 3 * ε / 2 ^ n < η := by
      have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
      rw [div_lt_iff₀ hη] at hn
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hp : (0 : ℝ) < 2 ^ K n := by positivity
    have key : ∀ u v : unitInterval, dist u v < 1 / 2 ^ K n → idx n u ≤ idx n v + 1 := by
      intro u v huv
      rw [Subtype.dist_eq, Real.dist_eq, abs_lt] at huv
      refine Nat.le_of_lt_succ ((Nat.floor_lt' (by omega)).2 ?_)
      have e1 : ((u : ℝ)) * 2 ^ K n < (v : ℝ) * 2 ^ K n + 1 := by
        have := huv.2
        have : (u : ℝ) < v + 1 / 2 ^ K n := by linarith
        calc (u : ℝ) * 2 ^ K n < (v + 1 / 2 ^ K n) * 2 ^ K n := by gcongr
          _ = (v : ℝ) * 2 ^ K n + 1 := by field_simp
      have e2 := Nat.lt_floor_add_one ((v : ℝ) * 2 ^ K n)
      simp only [idx]
      push_cast
      linarith
    refine ⟨1 / 2 ^ K n, by positivity, fun {t t'} htt' => ?_⟩
    have hd : dist (s t n) (s t' n) ≤ ε / 2 ^ n := by
      have hdiff : idx n t ≤ idx n t' + 1 ∧ idx n t' ≤ idx n t + 1 :=
        ⟨key t t' htt', key t' t (by rwa [dist_comm])⟩
      have hstepb : ∀ i < 2 ^ K n, dist (g n i) (g n (i + 1)) ≤ ε / 2 ^ n := fun i hi => by
        have h1 := ((hS n).step i hi).le.trans (P.δle n)
        rw [hPε n] at h1
        refine h1.trans ?_
        rw [div_div]
        apply div_le_div_of_nonneg_left hε.le (by positivity)
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
      change dist (g n (idx n t)) (g n (idx n t')) ≤ ε / 2 ^ n
      rcases lt_trichotomy (idx n t) (idx n t') with h | h | h
      · have e : idx n t' = idx n t + 1 := by omega
        have := hidx n t'
        rw [e]; exact hstepb _ (by omega)
      · rw [h, dist_self]; positivity
      · have e : idx n t = idx n t' + 1 := by omega
        have := hidx n t
        rw [e, dist_comm]; exact hstepb _ (by omega)
    calc dist (γf t) (γf t') ≤ dist (γf t) (s t n) + dist (s t n) (s t' n) + dist (s t' n) (γf t') :=
          dist_triangle4 _ _ _ _
      _ ≤ ε / 2 ^ n + ε / 2 ^ n + ε / 2 ^ n := by
          gcongr
          · rw [dist_comm]; exact hnear t n
          · exact hnear t' n
      _ = 3 * ε / 2 ^ n := by ring
      _ < η := hn'
  have hγ0 : γf 0 = a := by
    refine tendsto_nhds_unique (hlim 0) (tendsto_const_nhds.congr fun n => ?_)
    simp only [s, idx, Set.Icc.coe_zero, zero_mul, Nat.floor_zero]
    exact ((hS n).zero).symm
  have hγ1 : γf 1 = b := by
    refine tendsto_nhds_unique (hlim 1) (tendsto_const_nhds.congr fun n => ?_)
    simp only [s, idx, Set.Icc.coe_one, one_mul]
    rw [show ⌊(2 : ℝ) ^ K n⌋₊ = 2 ^ K n by exact_mod_cast Nat.floor_natCast (2 ^ K n)]
    exact ((hS n).top).symm
  refine ⟨⟨⟨γf, hcont⟩, hγ0, hγ1⟩, fun t => ?_⟩
  have h1 := hnear t 0
  simp only [pow_zero, div_one] at h1
  have h2 : dist a (s t 0) < ε := by
    have hK0 : K 0 = 0 := rfl
    have hle : ⌊(t : ℝ) * 2 ^ K 0⌋₊ ≤ 2 ^ K 0 := hidx 0 t
    have htop : g 0 (2 ^ K 0) = b := (hS 0).top
    change dist a (g 0 ⌊(t : ℝ) * 2 ^ K 0⌋₊) < ε
    rw [hK0, pow_zero, mul_one] at hle ⊢
    rw [hK0, pow_zero] at htop
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with ht | ht
    · rw [ht, (hS 0).zero, dist_self]; exact hε
    · rw [ht, htop]
      refine lt_of_lt_of_le hab ((P.δle 0).trans ?_)
      rw [hPε 0]; simp only [pow_zero, div_one]; linarith
  calc dist a (γf t) ≤ dist a (s t 0) + dist (s t 0) (γf t) := dist_triangle _ _ _
    _ < ε + ε := by linarith
    _ = 2 * ε := by ring

end MosaicSpaces.Peano
