import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Find
import LongTails.Proofs.FiniteSumNondualLowerGeometry

open Finset

namespace LongTails.Proofs.StrongQuasarChainBlock

noncomputable def deadEnergy (θ t : ℝ) : ℝ := max (|t| - θ) 0 ^ 2 / 2

noncomputable def deadSlope (θ t : ℝ) : ℝ := t - max (-θ) (min θ t)

noncomputable def deadBreg (θ s d : ℝ) : ℝ :=
  deadEnergy θ s - deadEnergy θ d - deadSlope θ d * (s - d)

noncomputable def gain (v : ℝ) : ℝ := min 1 (max 0 (16 * |v| - 1))

noncomputable def linkTerm (θ q : ℝ) (X : ℕ → ℝ) (i : ℕ) : ℝ :=
  deadBreg θ (X i - X (i + 1)) (q ^ i - q ^ (i + 1))

noncomputable def coordTerm (μ γ q : ℝ) (X : ℕ → ℝ) (i : ℕ) : ℝ :=
  μ * (gain (X i / q ^ i) - γ) * (X i - q ^ i) ^ 2

structure Regime (m : ℕ) (q μ γ θ : ℝ) : Prop where
  hm : 16 ≤ m
  hq : q = 1 - 1 / (m : ℝ)
  hμ0 : 0 < μ
  hμ : μ ≤ 1 / 100
  hγ0 : 0 ≤ γ
  hγ : γ ≤ 1 / 256
  hc : (42 * γ * m) ^ 2 * μ ≤ 1
  hθ0 : 0 ≤ θ

lemma gain_nonneg (v : ℝ) : 0 ≤ gain v := le_min zero_le_one (le_max_left _ _)

lemma gain_le_one (v : ℝ) : gain v ≤ 1 := min_le_left _ _

lemma gain_eq_one {v : ℝ} (h : 1 / 8 ≤ |v|) : gain v = 1 := by
  unfold gain
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

lemma deadEnergy_of_ge {θ d : ℝ} (hθ : 0 ≤ θ) (hd : θ ≤ d) :
    deadEnergy θ d = (d - θ) ^ 2 / 2 := by
  unfold deadEnergy
  rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]

lemma deadSlope_of_ge {θ d : ℝ} (hθ : 0 ≤ θ) (hd : θ ≤ d) : deadSlope θ d = d - θ := by
  unfold deadSlope
  rw [min_eq_left hd, max_eq_right (by linarith)]

lemma deadBreg_ge (θ s d : ℝ) (hθ : 0 ≤ θ) (hd : θ ≤ d) :
    max (|s - d| - 2 * θ) 0 ^ 2 / 2 ≤ deadBreg θ s d := by
  unfold deadBreg
  rw [deadEnergy_of_ge hθ hd, deadSlope_of_ge hθ hd]
  rcases le_total θ s with hs | hs
  · rw [deadEnergy_of_ge hθ hs]
    have hm : max (|s - d| - 2 * θ) 0 ^ 2 ≤ (s - d) ^ 2 := by
      rcases le_total (|s - d| - 2 * θ) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (s - d)]
      · rw [max_eq_left h, ← sq_abs (s - d)]
        exact pow_le_pow_left₀ h (by linarith) 2
    nlinarith
  · rcases le_total s (-θ) with hs' | hs'
    · have he : deadEnergy θ s = (s + θ) ^ 2 / 2 := by
        unfold deadEnergy
        rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        ring
      rw [he, abs_of_nonpos (by linarith : s - d ≤ 0), max_eq_left (by linarith)]
      nlinarith
    · have hab : |s| ≤ θ := abs_le.mpr ⟨hs', hs⟩
      have he : deadEnergy θ s = 0 := by
        unfold deadEnergy
        rw [max_eq_right (by linarith)]
        norm_num
      rw [he, abs_of_nonpos (by linarith : s - d ≤ 0)]
      rcases le_total (-(s - d) - 2 * θ) 0 with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith

lemma deadBreg_nonneg (θ s d : ℝ) (hθ : 0 ≤ θ) (hd : θ ≤ d) : 0 ≤ deadBreg θ s d :=
  le_trans (by positivity) (deadBreg_ge θ s d hθ hd)

section regime

variable {m : ℕ} {q μ γ θ : ℝ}

lemma Regime.m_pos (R : Regime m q μ γ θ) : (16 : ℝ) ≤ m := by exact_mod_cast R.hm

lemma Regime.one_sub (R : Regime m q μ γ θ) : 1 - q = 1 / (m : ℝ) := by rw [R.hq]; ring

lemma Regime.q_pos (R : Regime m q μ γ θ) : 0 < q := by
  have hm := R.m_pos
  rw [R.hq]
  have : 1 / (m : ℝ) ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hm
  linarith

lemma Regime.q_lt_one (R : Regime m q μ γ θ) : q < 1 := by
  have hm := R.m_pos
  rw [R.hq]
  have : 0 < 1 / (m : ℝ) := by positivity
  linarith

lemma Regime.pow_lower (R : Regime m q μ γ θ) (n : ℕ) : 1 - n / (m : ℝ) ≤ q ^ n := by
  have hm := R.m_pos
  have h := one_add_mul_le_pow (a := -(1 / (m : ℝ))) (by
    have : 1 / (m : ℝ) ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hm
    linarith) n
  rw [R.hq]
  have he : (1 : ℝ) + -(1 / (m : ℝ)) = 1 - 1 / m := by ring
  rw [he] at h
  have he2 : (1 : ℝ) + n * -(1 / (m : ℝ)) = 1 - n / m := by ring
  linarith

lemma Regime.pow_anti (R : Regime m q μ γ θ) {i j : ℕ} (h : i ≤ j) : q ^ j ≤ q ^ i :=
  pow_le_pow_of_le_one R.q_pos.le R.q_lt_one.le h

lemma Regime.link_gap (R : Regime m q μ γ θ) (i : ℕ) : q ^ i - q ^ (i + 1) = q ^ i / m := by
  have h := R.one_sub
  rw [pow_succ]
  have : q ^ i - q ^ i * q = q ^ i * (1 - q) := by ring
  rw [this, h]
  ring

lemma Regime.link_nonneg (R : Regime m q μ γ θ) (X : ℕ → ℝ) (i : ℕ)
    (hθ : 4 * m * θ ≤ q ^ i) : 0 ≤ linkTerm θ q X i := by
  apply deadBreg_nonneg _ _ _ R.hθ0
  rw [R.link_gap]
  have hm := R.m_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith [R.hθ0]

lemma Regime.geom_tail (R : Regime m q μ γ θ) (i0 e : ℕ) (hi0 : 1 ≤ i0) :
    ∑ i ∈ Ioc (i0 - 1) e, (q ^ i) ^ 2 ≤ m * (q ^ i0) ^ 2 := by
  have hq0 := R.q_pos
  have hq1 := R.q_lt_one
  have hx0 : 0 ≤ q ^ 2 := by positivity
  have hx1 : q ^ 2 < 1 := by nlinarith
  have hI : Ioc (i0 - 1) e = Ico i0 (e + 1) := by
    ext i
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hI]
  have hs : ∑ i ∈ Ico i0 (e + 1), (q ^ i) ^ 2 = ∑ i ∈ Ico i0 (e + 1), (q ^ 2) ^ i := by
    apply sum_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hs]
  refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans ?_
  have hpow : (q ^ 2) ^ i0 = (q ^ i0) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hpow, div_le_iff₀ (by linarith)]
  have h1 := R.one_sub
  have hm := R.m_pos
  have hmq : (m : ℝ) * (1 - q) = 1 := by rw [h1]; field_simp
  have hq2 : (m : ℝ) * (1 - q ^ 2) ≥ 1 := by nlinarith
  have hp : 0 ≤ (q ^ i0) ^ 2 := by positivity
  nlinarith

lemma key_poly (R : Regime m q μ γ θ) (n : ℝ) (hn : 1 ≤ n) :
    13 / 10 * γ * μ * m ≤ 1 / (256 * n) + (n - 1) * μ / 8 := by
  have hμ0 := R.hμ0
  set s := Real.sqrt μ with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hs1 : s ≤ 1 / 10 := by
    rw [hs, show (1 : ℝ) / 10 = Real.sqrt (1 / 100) by
      rw [show (1 : ℝ) / 100 = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt R.hμ
  have hm := R.m_pos
  have hcs : 42 * γ * m * s ≤ 1 := by
    have h := R.hc
    rw [← hss, ← mul_pow] at h
    have h0 : 0 ≤ 42 * γ * m * s := by
      have := R.hγ0; positivity
    nlinarith
  have hn0 : 0 < n := by linarith
  set w := n * s with hw
  have hw0 : 0 ≤ w := by positivity
  have key : 0 ≤ 1 + 32 * w ^ 2 - (1112 / 100) * w := by
    nlinarith [sq_nonneg (w - 17381 / 100000)]
  have h1 : n * s ^ 2 ≤ w / 10 := by
    rw [hw]; nlinarith
  have h2 : 1300 / 1000 * γ * m * s ^ 2 * n ≤ (1300 / 42000) * w := by
    rw [hw]
    have := R.hγ0
    nlinarith [mul_nonneg hn0.le hs0]
  have key' : 0 ≤ 1 + 32 * w ^ 2 - (1113 / 100) * w := by
    nlinarith [sq_nonneg (w - 1113 / 6400)]
  have hw2 : w ^ 2 = n ^ 2 * s ^ 2 := by rw [hw]; ring
  rw [← hss]
  rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
  nlinarith [key', h1, h2, hw2]

lemma Regime.coord_eq (R : Regime m q μ γ θ) (X : ℕ → ℝ) (i : ℕ) :
    (X i - q ^ i) ^ 2 = (q ^ i) ^ 2 * (X i / q ^ i - 1) ^ 2 := by
  have h : q ^ i ≠ 0 := (pow_pos R.q_pos i).ne'
  field_simp

lemma Regime.coord_good_nonneg (R : Regime m q μ γ θ) (X : ℕ → ℝ) (i : ℕ)
    (h : 1 / 8 ≤ |X i / q ^ i|) : 0 ≤ coordTerm μ γ q X i := by
  unfold coordTerm
  rw [gain_eq_one h]
  have := R.hμ0
  have := R.hγ
  have : 0 ≤ 1 - γ := by linarith
  positivity

lemma Regime.coord_goodlow (R : Regime m q μ γ θ) (X : ℕ → ℝ) (i : ℕ)
    (h1 : 1 / 8 ≤ |X i / q ^ i|) (h2 : |X i / q ^ i| ≤ 1 / 2) :
    μ * (q ^ i) ^ 2 / 8 ≤ coordTerm μ γ q X i := by
  unfold coordTerm
  rw [gain_eq_one h1, R.coord_eq X i]
  set v := X i / q ^ i
  have hv : v ≤ 1 / 2 := (abs_le.mp h2).2
  have hv2 : 1 / 4 ≤ (v - 1) ^ 2 := by nlinarith
  have hμ := R.hμ0
  have hγ := R.hγ
  have hp : 0 ≤ (q ^ i) ^ 2 := by positivity
  have : 0 ≤ μ * (q ^ i) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hv2 this]

lemma Regime.coord_low (R : Regime m q μ γ θ) (X : ℕ → ℝ) (i : ℕ) :
    -(13 / 10) * γ * μ * (q ^ i) ^ 2 ≤ coordTerm μ γ q X i := by
  have hγ0 := R.hγ0
  have hμ := R.hμ0
  have hp : 0 ≤ (q ^ i) ^ 2 := by positivity
  by_cases h1 : 1 / 8 ≤ |X i / q ^ i|
  · have := R.coord_good_nonneg X i h1
    have : 0 ≤ γ * μ * (q ^ i) ^ 2 := by positivity
    linarith
  · push Not at h1
    unfold coordTerm
    rw [R.coord_eq X i]
    set v := X i / q ^ i
    have hv := abs_lt.mp h1
    have hv2 : (v - 1) ^ 2 ≤ 81 / 64 := by nlinarith
    have hg := gain_nonneg v
    have hA : 0 ≤ μ * (q ^ i) ^ 2 := by positivity
    have hB : μ * (gain v - γ) * ((q ^ i) ^ 2 * (v - 1) ^ 2) ≥
        μ * (-γ) * ((q ^ i) ^ 2 * (v - 1) ^ 2) := by
      have : 0 ≤ μ * ((q ^ i) ^ 2 * (v - 1) ^ 2) := by positivity
      nlinarith
    have hC : μ * (-γ) * ((q ^ i) ^ 2 * (v - 1) ^ 2) ≥ -(81 / 64) * γ * μ * (q ^ i) ^ 2 := by
      have : 0 ≤ γ * μ * (q ^ i) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hv2 this]
    have : 0 ≤ γ * μ * (q ^ i) ^ 2 := by positivity
    linarith

lemma tele (f : ℕ → ℝ) (p n : ℕ) :
    ∑ i ∈ Ico p (p + n), (f i - f (i + 1)) = f p - f (p + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
    ring

lemma Regime.drop (R : Regime m q μ γ θ) (X : ℕ → ℝ) (p n : ℕ) (hn : 8 * n ≤ m)
    (hp : 1 / 2 < |X p / q ^ p|) (hb : |X (p + n) / q ^ (p + n)| < 1 / 8) :
    q ^ p / 4 ≤ |(X p - q ^ p) - (X (p + n) - q ^ (p + n))| := by
  have hq0 := R.q_pos
  have hP : 0 < q ^ p := pow_pos hq0 p
  have hm := R.m_pos
  have hlow := R.pow_lower n
  have hnm : (n : ℝ) / m ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have : (8 * n : ℝ) ≤ m := by exact_mod_cast hn
    linarith
  have hqn : 7 / 8 ≤ q ^ n := by linarith
  have hqn1 : q ^ n ≤ 1 := pow_le_one₀ hq0.le R.q_lt_one.le
  set vp := X p / q ^ p
  set vb := X (p + n) / q ^ (p + n)
  have hXp : X p = q ^ p * vp := by simp only [vp]; field_simp
  have hQ : 0 < q ^ (p + n) := pow_pos hq0 _
  have hXb : X (p + n) = q ^ (p + n) * vb := by simp only [vb]; field_simp
  have hpow : q ^ (p + n) = q ^ p * q ^ n := pow_add q p n
  have hb' := abs_lt.mp hb
  rw [hXp, hXb, hpow]
  rcases lt_abs.mp hp with h | h
  · rw [abs_of_nonneg (by nlinarith [mul_pos hP (show (0:ℝ) < q ^ n by positivity)])]
    nlinarith [mul_pos hP (show (0:ℝ) < q ^ n by positivity)]
  · rw [abs_of_nonpos (by nlinarith [mul_pos hP (show (0:ℝ) < q ^ n by positivity)])]
    nlinarith [mul_pos hP (show (0:ℝ) < q ^ n by positivity)]

lemma Regime.block_nonneg (R : Regime m q μ γ θ) (X : ℕ → ℝ) (p e : ℕ) (hpe : p < e)
    (hθ : ∀ i < e, 4 * m * θ ≤ q ^ i)
    (hp : 1 / 2 < |X p / q ^ p|) (hlow : ∀ i, p < i → i ≤ e → |X i / q ^ i| ≤ 1 / 2) :
    0 ≤ (1 - γ) * ∑ i ∈ Ico p e, linkTerm θ q X i + ∑ i ∈ Ioc p e, coordTerm μ γ q X i := by
  classical
  have hγ0 := R.hγ0
  have hγ := R.hγ
  have hμ0 := R.hμ0
  have hq0 := R.q_pos
  have hm := R.m_pos
  have hθ0 := R.hθ0
  have hlink : ∀ i ∈ Ico p e, 0 ≤ linkTerm θ q X i := fun i hi =>
    R.link_nonneg X i (hθ i (mem_Ico.mp hi).2)
  have hL0 : 0 ≤ ∑ i ∈ Ico p e, linkTerm θ q X i := sum_nonneg hlink
  by_cases hbad : ∃ i, p < i ∧ i ≤ e ∧ |X i / q ^ i| < 1 / 8
  swap
  · push Not at hbad
    have h2 : 0 ≤ ∑ i ∈ Ioc p e, coordTerm μ γ q X i := sum_nonneg (fun i hi => by
      obtain ⟨a, b⟩ := mem_Ioc.mp hi
      exact R.coord_good_nonneg X i (hbad i a b))
    have : 0 ≤ 1 - γ := by linarith
    positivity
  obtain ⟨hpi0, hi0e, hi0bad⟩ := Nat.find_spec hbad
  set i0 := Nat.find hbad with hi0
  have hmin : ∀ i, p < i → i < i0 → 1 / 8 ≤ |X i / q ^ i| := by
    intro i hpi hii
    have h := Nat.find_min hbad hii
    push Not at h
    exact h hpi (by omega)
  have htail : -(13 / 10) * γ * μ * (m * (q ^ i0) ^ 2) ≤
      ∑ i ∈ Ioc (i0 - 1) e, coordTerm μ γ q X i := by
    have hs : ∑ i ∈ Ioc (i0 - 1) e, (-(13 / 10) * γ * μ * (q ^ i) ^ 2) ≤
        ∑ i ∈ Ioc (i0 - 1) e, coordTerm μ γ q X i :=
      sum_le_sum (fun i _ => R.coord_low X i)
    have hg := R.geom_tail i0 e (by omega)
    rw [← mul_sum] at hs
    have : 0 ≤ (13 / 10) * γ * μ := by positivity
    nlinarith
  have hsplit : ∑ i ∈ Ioc p e, coordTerm μ γ q X i =
      ∑ i ∈ Ioc p (i0 - 1), coordTerm μ γ q X i + ∑ i ∈ Ioc (i0 - 1) e, coordTerm μ γ q X i :=
    (sum_Ioc_consecutive _ (by omega) (by omega)).symm
  have hhead : ∀ i ∈ Ioc p (i0 - 1), μ * (q ^ i) ^ 2 / 8 ≤ coordTerm μ γ q X i := by
    intro i hi
    obtain ⟨a, b⟩ := mem_Ioc.mp hi
    exact R.coord_goodlow X i (hmin i a (by omega)) (hlow i a (by omega))
  have hhead0 : ∀ i ∈ Ioc p (i0 - 1), 0 ≤ coordTerm μ γ q X i := fun i hi =>
    le_trans (by positivity) (hhead i hi)
  have hQ : 0 ≤ (q ^ i0) ^ 2 := by positivity
  have hPQ : (q ^ i0) ^ 2 ≤ (q ^ p) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (R.pow_anti (by omega)) 2
  obtain ⟨n, hn⟩ : ∃ n, i0 = p + n := ⟨i0 - p, by omega⟩
  have hn1 : 1 ≤ n := by omega
  rw [hsplit]
  by_cases hA : 8 * n ≤ m
  · have hsub : ∑ i ∈ Ico p i0, linkTerm θ q X i ≤ ∑ i ∈ Ico p e, linkTerm θ q X i :=
      sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hi0e)
        (fun i hi _ => hlink i hi)
    let z := fun i => (X i - X (i + 1)) - (q ^ i - q ^ (i + 1))
    let y := fun i => max (|z i| - 2 * θ) 0
    have hly : ∀ i ∈ Ico p i0, y i ^ 2 / 2 ≤ linkTerm θ q X i := by
      intro i hi
      have hie : i < e := by have := (mem_Ico.mp hi).2; omega
      have hd : θ ≤ q ^ i - q ^ (i + 1) := by
        rw [R.link_gap, le_div_iff₀ (by positivity)]
        nlinarith [hθ i hie]
      exact deadBreg_ge θ _ _ hθ0 hd
    have htel : ∑ i ∈ Ico p i0, z i = (X p - q ^ p) - (X i0 - q ^ i0) := by
      rw [hn]
      have h := tele (fun i => X i - q ^ i) p n
      rw [← h]
      apply sum_congr rfl
      intro i _
      simp only [z]
      ring
    have hdrop := R.drop X p n hA hp (by rw [← hn]; exact hi0bad)
    rw [← hn, ← htel] at hdrop
    have habs : |∑ i ∈ Ico p i0, z i| ≤ ∑ i ∈ Ico p i0, |z i| := abs_sum_le_sum_abs _ _
    have hcard : ((Ico p i0).card : ℝ) = n := by
      rw [Nat.card_Ico]; push_cast [hn]; simp
    have hysum : ∑ i ∈ Ico p i0, |z i| - 2 * θ * n ≤ ∑ i ∈ Ico p i0, y i := by
      have h : ∑ i ∈ Ico p i0, (|z i| - 2 * θ) ≤ ∑ i ∈ Ico p i0, y i :=
        sum_le_sum (fun i _ => le_max_left _ _)
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard] at h
      linarith
    have hθp : 4 * m * θ ≤ q ^ p := hθ p hpe
    have hθn : 2 * θ * n ≤ q ^ p / 16 := by
      have h8 : (8 * n : ℝ) ≤ m := by exact_mod_cast hA
      nlinarith
    have hPpos : 0 < q ^ p := pow_pos hq0 p
    have hY : q ^ p / 8 ≤ ∑ i ∈ Ico p i0, y i := by linarith
    have hcs := sq_sum_le_card_mul_sum_sq (s := Ico p i0) (f := y)
    rw [hcard] at hcs
    have hY2 : (q ^ p / 8) ^ 2 ≤ (∑ i ∈ Ico p i0, y i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hY 2
    have hLy : ∑ i ∈ Ico p i0, (1 / 2) * y i ^ 2 ≤ ∑ i ∈ Ico p i0, linkTerm θ q X i :=
      sum_le_sum (fun i hi => by have := hly i hi; linarith)
    rw [← mul_sum] at hLy
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlinks : (q ^ p) ^ 2 / (128 * n) ≤ ∑ i ∈ Ico p e, linkTerm θ q X i := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hheadsum : (n - 1) * (μ * (q ^ i0) ^ 2 / 8) ≤ ∑ i ∈ Ioc p (i0 - 1), coordTerm μ γ q X i := by
      have h := sum_le_sum (fun i hi => (hhead i hi).trans' (by
        have : (q ^ i0) ^ 2 ≤ (q ^ i) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (R.pow_anti (by have := (mem_Ioc.mp hi).2; omega)) 2
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hμ0.le) (by norm_num)))
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul] at h
      have hc : ((i0 - 1 - p : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast [hn]; ring
      rw [hc] at h
      exact h
    have hkey := key_poly R (n : ℝ) hnR
    have hfin : 0 ≤ (q ^ i0) ^ 2 * (1 / (256 * n) + (n - 1) * μ / 8 - 13 / 10 * γ * μ * m) :=
      mul_nonneg hQ (by linarith)
    have hlinks' : (1 - γ) * ((q ^ i0) ^ 2 / (128 * n)) ≤
        (1 - γ) * ∑ i ∈ Ico p e, linkTerm θ q X i := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact (div_le_div_of_nonneg_right hPQ (by positivity)).trans hlinks
    have hhalf : (q ^ i0) ^ 2 / (256 * n) ≤ (1 - γ) * ((q ^ i0) ^ 2 / (128 * n)) := by
      have h0 : 0 ≤ (q ^ i0) ^ 2 / (128 * n) := by positivity
      have : (q ^ i0) ^ 2 / (256 * n) = (1 / 2) * ((q ^ i0) ^ 2 / (128 * n)) := by
        field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) h0
    have he : (q ^ i0) ^ 2 * (1 / (256 * n) + (n - 1) * μ / 8 - 13 / 10 * γ * μ * m) =
        (q ^ i0) ^ 2 / (256 * n) + (n - 1) * (μ * (q ^ i0) ^ 2 / 8) +
          -(13 / 10) * γ * μ * (m * (q ^ i0) ^ 2) := by
      field_simp; ring
    linarith
  · push Not at hA
    obtain ⟨M, hM⟩ : ∃ M, M = m / 8 := ⟨_, rfl⟩
    have hM8 : 8 * M ≤ m := by omega
    have hMn : M < n := by omega
    have hMR : (m : ℝ) / 16 ≤ M := by
      have : m ≤ 8 * M + 7 := by omega
      have h16 := R.hm
      have : (m : ℝ) ≤ 8 * M + 7 := by exact_mod_cast this
      have : (16 : ℝ) ≤ m := hm
      linarith
    have hsub : ∑ i ∈ Ioc p (p + M), coordTerm μ γ q X i ≤
        ∑ i ∈ Ioc p (i0 - 1), coordTerm μ γ q X i :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (by omega))
        (fun i hi _ => hhead0 i hi)
    have hqM : 7 / 8 ≤ q ^ M := by
      have h := R.pow_lower M
      have : (8 * M : ℝ) ≤ m := by exact_mod_cast hM8
      have : (M : ℝ) / m ≤ 1 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    have hfloor : ∀ i ∈ Ioc p (p + M), μ * (q ^ p) ^ 2 * (49 / 64) / 8 ≤ coordTerm μ γ q X i := by
      intro i hi
      obtain ⟨a, b⟩ := mem_Ioc.mp hi
      refine le_trans ?_ (hhead i (mem_Ioc.mpr ⟨a, by omega⟩))
      have hqi : q ^ (p + M) ≤ q ^ i := R.pow_anti b
      have hpm : q ^ (p + M) = q ^ p * q ^ M := pow_add q p M
      have hP : 0 < q ^ p := pow_pos hq0 p
      have h1 : q ^ p * (7 / 8) ≤ q ^ i := by nlinarith
      have h2 : (q ^ p) ^ 2 * (49 / 64) ≤ (q ^ i) ^ 2 := by nlinarith
      nlinarith
    have hs := sum_le_sum hfloor
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul] at hs
    have hc : ((p + M - p : ℕ) : ℝ) = M := by rw [Nat.add_sub_cancel_left]
    rw [hc] at hs
    have hfin : 13 / 10 * γ * μ * (m * (q ^ i0) ^ 2) ≤ M * (μ * (q ^ p) ^ 2 * (49 / 64) / 8) := by
      have h1 : 13 / 10 * γ * μ * (m * (q ^ i0) ^ 2) ≤ 13 / 10 * γ * μ * (m * (q ^ p) ^ 2) := by
        have h0 : 0 ≤ 13 / 10 * γ * μ * m := by positivity
        have := mul_le_mul_of_nonneg_left hPQ h0
        calc 13 / 10 * γ * μ * (m * (q ^ i0) ^ 2) = 13 / 10 * γ * μ * m * (q ^ i0) ^ 2 := by ring
          _ ≤ 13 / 10 * γ * μ * m * (q ^ p) ^ 2 := this
          _ = _ := by ring
      have hPp : 0 ≤ μ * (q ^ p) ^ 2 := by positivity
      have h2 : 13 / 10 * γ * μ * (m * (q ^ p) ^ 2) ≤ (m / 16) * (μ * (q ^ p) ^ 2 * (49 / 64) / 8) := by
        have h0 : 0 ≤ (m : ℝ) * (μ * (q ^ p) ^ 2) := by positivity
        have hγ' : 13 / 10 * γ ≤ 49 / 8192 := by linarith
        calc 13 / 10 * γ * μ * (m * (q ^ p) ^ 2) = (13 / 10 * γ) * ((m : ℝ) * (μ * (q ^ p) ^ 2)) := by ring
          _ ≤ (49 / 8192) * ((m : ℝ) * (μ * (q ^ p) ^ 2)) := mul_le_mul_of_nonneg_right hγ' h0
          _ = _ := by ring
      have h3 : (m / 16) * (μ * (q ^ p) ^ 2 * (49 / 64) / 8) ≤ M * (μ * (q ^ p) ^ 2 * (49 / 64) / 8) :=
        mul_le_mul_of_nonneg_right hMR (by positivity)
      linarith
    have : 0 ≤ 1 - γ := by linarith
    have hL := mul_nonneg this hL0
    linarith

lemma Regime.chain_nonneg (R : Regime m q μ γ θ) (X : ℕ → ℝ) (N : ℕ) (hX0 : X 0 = 1)
    (hθ : ∀ i < N, 4 * m * θ ≤ q ^ i) :
    0 ≤ (1 - γ) * ∑ i ∈ range N, linkTerm θ q X i + ∑ i ∈ Ioc 0 N, coordTerm μ γ q X i := by
  classical
  have hP0 : 1 / 2 < |X 0 / q ^ 0| := by rw [hX0]; norm_num
  suffices h : ∀ k, k ≤ N → 0 ≤ (1 - γ) * ∑ i ∈ range k, linkTerm θ q X i +
      ∑ i ∈ Ioc 0 k, coordTerm μ γ q X i from h N le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    let P := fun i => 1 / 2 < |X i / q ^ i|
    have hpP : P (Nat.findGreatest P k) := Nat.findGreatest_spec (Nat.zero_le k) hP0
    have hpk : Nat.findGreatest P k ≤ k := Nat.findGreatest_le k
    set p := Nat.findGreatest P k with hpdef
    rcases Nat.lt_or_ge p k with hlt | hge
    · have hS := ih p hlt (by omega)
      have hB := R.block_nonneg X p k hlt (fun i hi => hθ i (by omega)) hpP
        (fun i hi hik => by
          have h := Nat.findGreatest_is_greatest (P := P) hi hik
          simp only [P, not_lt] at h
          exact h)
      rw [← sum_range_add_sum_Ico _ hpk, ← sum_Ioc_consecutive _ (Nat.zero_le p) hpk]
      nlinarith
    · have hpk' : p = k := le_antisymm hpk hge
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        simp
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hS := ih j (by omega) (by omega)
        have hl := R.link_nonneg X j (hθ j (by omega))
        have hc : 0 ≤ coordTerm μ γ q X (j + 1) := R.coord_good_nonneg X (j + 1) (by
          have : P (j + 1) := hpk' ▸ hpP
          simp only [P] at this
          linarith)
        rw [sum_range_succ, sum_Ioc_succ_top (Nat.zero_le j)]
        have : 0 ≤ 1 - γ := by linarith [R.hγ]
        nlinarith

end regime

end LongTails.Proofs.StrongQuasarChainBlock
