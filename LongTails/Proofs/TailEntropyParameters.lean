import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.GeneralizedSmoothTransientParameters
import LongTails.Proofs.AdaptiveTransientParameters
import LongTails.Proofs.GeneralizedSmoothHardChainRadius
import LongTails.Proofs.TailEntropySmoothedChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.TailEntropyParameters

open LongTails.Setups.GeneralizedSmoothConvexFull
open AdaptiveTransientParameters TailEntropyHardChain

def Valid (p : Params) : Prop := spec.valid p ∧ 16777216 ≤ p.L1 * p.R

noncomputable def q (p : Params) : ℝ := p.L1 * p.R

noncomputable def links (p : Params) : ℕ := ⌊q p / 33554432⌋₊ + 1

noncomputable def ratio (m : ℕ) : ℝ := 1 / Real.sqrt m

noncomputable def degree (p : Params) : ℕ := ⌈16 * Real.sqrt (q p)⌉₊

noncomputable def width (p : Params) : ℝ := 131072 * p.R

lemma log_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr (by linarith)
  have hl := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt (by linarith)] at hl
  have hsq : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  linarith

lemma sqrt_m_pos (m : ℕ) (hm : 0 < m) : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)

lemma one_le_m (m : ℕ) (hm : 0 < m) : (1 : ℝ) ≤ m := by exact_mod_cast hm

lemma ratio_pos (m : ℕ) (hm : 0 < m) : 0 < ratio m := by
  have := sqrt_m_pos m hm
  unfold ratio; positivity

lemma ratio_le_one (m : ℕ) (hm : 0 < m) : ratio m ≤ 1 := by
  have h1 : 1 ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (one_le_m m hm)
  unfold ratio
  rw [div_le_one (by linarith)]
  exact h1

lemma exponent_le (m : ℕ) (hm : 0 < m) : ((m : ℝ) - 1) * ratio m ≤ Real.sqrt m := by
  have hs := sqrt_m_pos m hm
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  unfold ratio
  rw [mul_one_div, div_le_iff₀ hs]
  nlinarith

section

variable (p : Params) (hp : Valid p)

include hp

lemma L0_pos : 0 < p.L0 := hp.1.1
lemma R_pos : 0 < p.R := hp.1.2.2.1
lemma ε_pos : 0 < p.ε := hp.1.2.2.2.1
lemma q_ge : 16777216 ≤ q p := hp.2

lemma L1_pos : 0 < p.L1 := by
  have h1 := hp.1.2.1
  have hR := R_pos p hp
  have hq := q_ge p hp
  rcases h1.eq_or_lt with h0 | hlt
  · unfold q at hq; rw [← h0] at hq; simp at hq; linarith
  · exact hlt

lemma accuracy_le : 16 * p.ε ≤ p.L0 * p.R ^ 2 := by
  have := hp.1.2.2.2.2.1; linarith

lemma dim_ge : ⌈17592186044416 * (1 + q p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5⌉₊ ≤ p.d :=
  hp.1.2.2.2.2.2

lemma q_pos : 0 < q p := by have := q_ge p hp; linarith

lemma degree_valid : 2 ≤ degree p :=
  degree_ge_two _ (by have := q_ge p hp; linarith)

lemma width_pos : 0 < width p := by
  have := R_pos p hp
  unfold width
  positivity

lemma width_radius : p.R ≤ width p := by
  have := R_pos p hp
  unfold width
  linarith

lemma width_valid : 256 * ((degree p : ℝ) * (degree p + 1 : ℕ)) ≤ p.L1 * width p := by
  have hq : 1 ≤ q p := by have := q_ge p hp; linarith
  have hh := degree_product _ hq
  change (degree p : ℝ) * (degree p + 1 : ℕ) ≤ 306 * q p at hh
  unfold q at hh
  unfold width
  nlinarith only [hh, hq]

lemma scaled_coefficient : p.ε * p.L1 ^ 2 ≤ p.L0 * q p ^ 2 / 16 := by
  have hh := mul_le_mul_of_nonneg_right (accuracy_le p hp) (sq_nonneg p.L1)
  unfold q
  nlinarith

variable (m : ℕ) (hm : 0 < m) (hmM : m ≤ links p)

include hm hmM

omit hm in
lemma m_le : (m : ℝ) ≤ q p / 8388608 := by
  have hq := q_ge p hp
  have hl : (links p : ℝ) ≤ q p / 33554432 + 1 := by
    unfold links
    push_cast
    linarith [Nat.floor_le (show 0 ≤ q p / 33554432 by positivity)]
  have hm' : (m : ℝ) ≤ links p := by exact_mod_cast hmM
  linarith

omit hm in
lemma sqrt_m_le : Real.sqrt m ≤ Real.sqrt (q p) / 2896 := by
  have hm' := m_le p hp m hmM
  have hq := q_pos p hp
  rw [le_div_iff₀ (by norm_num), ← Real.sqrt_mul_self (show (0 : ℝ) ≤ 2896 by norm_num),
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  nlinarith

lemma peak_small :
    KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio m) * (1 / 2 : ℝ) ^ degree p * p.L1 ≤ p.L0 := by
  have hL0 := L0_pos p hp
  have hL1 := L1_pos p hp
  have hε := ε_pos p hp
  have hq1 : 1 ≤ q p := by have := q_ge p hp; linarith
  have hexp : Real.exp (((m : ℝ) - 1) * ratio m) ≤ Real.exp (Real.sqrt (q p)) := by
    apply Real.exp_le_exp.mpr
    have h1 := exponent_le m hm
    have h2 := sqrt_m_le p hp m hmM
    have h3 := Real.sqrt_nonneg (q p)
    linarith
  have hcoef : p.ε * p.L1 ^ 2 / 2 ≤ p.L0 * q p ^ 2 / 32 := by
    have := scaled_coefficient p hp; linarith
  have hsup := exponential_suppression (q p) hq1
  unfold KnownGapChainWeights.peak degree
  have he : 2 * p.ε * (p.L1 / 4) * Real.exp (((m : ℝ) - 1) * ratio m) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ * p.L1 =
      (p.ε * p.L1 ^ 2 / 2) * Real.exp (((m : ℝ) - 1) * ratio m) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by ring
  rw [he]
  have h1 : (p.ε * p.L1 ^ 2 / 2) * Real.exp (((m : ℝ) - 1) * ratio m) ≤
      p.L0 * q p ^ 2 / 32 * Real.exp (Real.sqrt (q p)) :=
    mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)
  have h2 : p.L0 * q p ^ 2 / 32 * Real.exp (Real.sqrt (q p)) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ ≤
      p.L0 / 32 := by
    have hh := mul_le_mul_of_nonneg_left hsup (show 0 ≤ p.L0 / 32 by positivity)
    have hinv : (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ = 1 / (2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by
      rw [one_div_pow]
    rw [hinv, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc (p.ε * p.L1 ^ 2 / 2) * Real.exp (((m : ℝ) - 1) * ratio m) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊
      ≤ p.L0 * q p ^ 2 / 32 * Real.exp (Real.sqrt (q p)) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by
        gcongr
    _ ≤ p.L0 / 32 := h2
    _ ≤ p.L0 := by linarith

omit hmM in
lemma level_bound :
    p.L1 / 4 * level m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m) ≤
      142 * Real.sqrt m + 28 * Real.log m + 4 * Real.log (1 + q p) := by
  have hL0 := L0_pos p hp
  have hL1 := L1_pos p hp
  have hε := ε_pos p hp
  have hq := q_pos p hp
  have hs := sqrt_m_pos m hm
  have hE := exponent_le m hm
  set E := Real.exp (((m : ℝ) - 1) * ratio m) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg (by linarith [one_le_m m hm])
    (ratio_pos m hm).le)
  have harg : p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio m) / (p.L0 / 4) =
      p.ε * p.L1 ^ 2 / (2 * p.L0) * E := by
    unfold KnownGapChainWeights.peak
    rw [← hEdef]
    field_simp
    ring
  have hcoef : p.ε * p.L1 ^ 2 / (2 * p.L0) ≤ q p ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := scaled_coefficient p hp
    nlinarith
  have hlog : Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio m) / (p.L0 / 4)) ≤
      2 * Real.log (1 + q p) + Real.sqrt m := by
    rw [harg]
    have hpos : 0 < 1 + p.ε * p.L1 ^ 2 / (2 * p.L0) * E := by positivity
    have h1 : 1 + p.ε * p.L1 ^ 2 / (2 * p.L0) * E ≤ (1 + q p) ^ 2 * E := by
      have : 0 ≤ p.ε * p.L1 ^ 2 / (2 * p.L0) := by positivity
      nlinarith
    have h2 := Real.log_le_log hpos h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hEdef, Real.log_exp] at h2
    push_cast at h2
    linarith
  unfold level ratio
  have hscale : p.L1 / 4 * (2 * (Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε
      (1 / Real.sqrt m) / (p.L0 / 4)) / (p.L1 / 4)) + 28 / (p.L1 / 4) * Real.log m +
      140 / (p.L1 / 4 * (1 / Real.sqrt m))) =
      2 * Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε
      (1 / Real.sqrt m) / (p.L0 / 4)) + 28 * Real.log m + 140 * Real.sqrt m := by
    field_simp
  rw [hscale]
  unfold ratio at hlog
  linarith

omit hmM in
lemma level_nonneg : 0 ≤ level m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m) := by
  have hL0 := L0_pos p hp
  have hL1 := L1_pos p hp
  have hε := ε_pos p hp
  have hr := ratio_pos m hm
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (one_le_m m hm)
  have hpk := KnownGapChainWeights.peak_pos m (p.L1 / 4) p.ε (ratio m) (by positivity) hε
  have harg : 0 ≤ p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio m) / (p.L0 / 4) := by
    positivity
  have hl1 := Real.log_nonneg (show (1 : ℝ) ≤ 1 + p.L1 / 4 *
    KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio m) / (p.L0 / 4) by linarith)
  have t1 : 0 ≤ 2 * (Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio m) /
      (p.L0 / 4)) / (p.L1 / 4)) := mul_nonneg (by norm_num) (div_nonneg hl1 (by positivity))
  have t2 : 0 ≤ 28 / (p.L1 / 4) * Real.log m := mul_nonneg (by positivity) hlm
  have t3 : 0 ≤ 140 / (p.L1 / 4 * ratio m) := by positivity
  unfold level
  linarith

lemma shift_norm_le : ‖shift m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m)‖ ≤ p.R / 4 := by
  have hL1 := L1_pos p hp
  have hR := R_pos p hp
  have hq := q_pos p hp
  have hlev := level_bound p hp m hm
  have hnn := level_nonneg p hp m hm
  have hs := sqrt_m_pos m hm
  have hsle := sqrt_m_le p hp m hmM
  have hmle := m_le p hp m hmM
  have hb := GeneralizedSmoothHardChainRadius.norm_bound_of_coordinate_bound
    (shift m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m)) _ hnn (fun i => by
      rw [shift_apply, abs_of_nonneg hnn])
  apply hb.trans
  have hlogm : Real.log m ≤ Real.log (1 + q p) :=
    Real.log_le_log (by have := one_le_m m hm; linarith) (by linarith)
  have hlq := log_le_two_sqrt (q p) hq.le
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (by positivity)
  have hsqq : Real.sqrt (q p) * Real.sqrt (q p) = q p := Real.mul_self_sqrt hq.le
  have hkey : Real.sqrt m * (142 * Real.sqrt m + 28 * Real.log m + 4 * Real.log (1 + q p)) ≤ q p / 16 := by
    have h1 : Real.sqrt m * (28 * Real.log m + 4 * Real.log (1 + q p)) ≤
        Real.sqrt m * (64 * Real.sqrt (q p)) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      linarith
    have h2 : Real.sqrt m * (64 * Real.sqrt (q p)) ≤ Real.sqrt (q p) / 2896 * (64 * Real.sqrt (q p)) :=
      mul_le_mul_of_nonneg_right hsle (by positivity)
    nlinarith
  have hfinal : Real.sqrt m * (p.L1 / 4 * level m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m)) ≤ q p / 16 :=
    (mul_le_mul_of_nonneg_left hlev hs.le).trans hkey
  unfold q at hfinal
  have he : Real.sqrt m * (p.L1 / 4 * level m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m)) =
      p.L1 / 4 * (Real.sqrt m * level m (p.L0 / 4) (p.L1 / 4) p.ε (ratio m)) := by ring
  rw [he] at hfinal
  have h4 : p.L1 * p.R / 16 = p.L1 / 4 * (p.R / 4) := by ring
  rw [h4] at hfinal
  exact le_of_mul_le_mul_left hfinal (by positivity)

omit hm hmM in
lemma threshold_eq : TailEntropySmoothedChain.threshold (p.L1 / 4) = 28 / p.L1 := by
  unfold TailEntropySmoothedChain.threshold margin
  have := L1_pos p hp
  field_simp
  ring

lemma dimension_sufficient :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * ((4 * width p) ^ 2 /
      TailEntropySmoothedChain.threshold (p.L1 / 4) ^ 2) ≤ p.d := by
  have hL1 := L1_pos p hp
  have hR := R_pos p hp
  have hq := q_pos p hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmq := m_le p hp m hmM
  rw [threshold_eq p hp]
  have hval : (4 * width p) ^ 2 / (28 / p.L1) ^ 2 = 274877906944 / 784 * q p ^ 2 := by
    unfold width q
    field_simp
    ring
  rw [hval]
  have hd : (⌈17592186044416 * (1 + q p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5⌉₊ : ℝ) ≤ p.d := by
    exact_mod_cast dim_ge p hp
  have hceil := Nat.le_ceil (17592186044416 * (1 + q p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5)
  have hs := Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)
  have hq5 : (1 + q p) ^ 5 ≤ (1 + q p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 5
  have hm2 : (m : ℝ) ^ 2 ≤ (q p / 8388608) ^ 2 := pow_le_pow_left₀ hm0.le hmq 2
  have hq4 : q p ^ 4 ≤ (1 + q p) ^ 5 := by
    have h1 : q p ^ 4 ≤ (1 + q p) ^ 4 := pow_le_pow_left₀ hq.le (by linarith) 4
    have h2 : (1 + q p) ^ 4 ≤ (1 + q p) ^ 5 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hq1 : q p ≤ (1 + q p) ^ 5 := by
    have h2 : (1 + q p) ^ 1 ≤ (1 + q p) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
    simp at h2; linarith
  have hbig : 2 * (m : ℝ) ^ 2 * (274877906944 / 784 * q p ^ 2) ≤ q p ^ 4 := by
    have : 2 * (q p / 8388608) ^ 2 * (274877906944 / 784 * q p ^ 2) ≤ q p ^ 4 := by
      have he : 2 * (q p / 8388608) ^ 2 * (274877906944 / 784 * q p ^ 2) = q p ^ 4 / 100352 := by ring
      rw [he]
      have := pow_nonneg hq.le 4
      linarith
    have hpos : 0 ≤ 274877906944 / 784 * q p ^ 2 := by positivity
    nlinarith
  nlinarith

end

end LongTails.Proofs.TailEntropyParameters
