import LongTails.Algorithms.Katyusha
import Mathlib.Tactic

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

lemma tuning_pos (p : Params) : 0 < tuning p :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma tuning_bounds (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) :
    0 < tau p ∧ tau p ≤ 1 / 2 ∧ 0 < alpha p ∧
      3 * alpha p * p.L * tau p ≤ 1 ∧
      ((2 * p.n : ℕ) : ℝ) * (alpha p * p.μ) = tau p / 6 := by
  have hm : (0 : ℝ) < (2 * p.n : ℕ) := by exact_mod_cast Nat.mul_pos (by decide) (NeZero.pos p.n)
  have hr : (1 : ℝ) ≤ tuning p := by exact_mod_cast tuning_pos p
  have hr0 : (0 : ℝ) < tuning p := lt_of_lt_of_le zero_lt_one hr
  have hτ : 0 < tau p := by unfold tau; positivity
  have hα : 0 < alpha p := by unfold alpha; positivity
  have hsq := Real.sq_sqrt (div_nonneg hL.le (mul_nonneg hm.le hμ.le))
  have hceil : Real.sqrt (p.L / (((2 * p.n : ℕ) : ℝ) * p.μ)) ≤ (tuning p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈Real.sqrt (p.L / ((2 * p.n : ℕ) * p.μ))⌉₊)
  have hs : p.L / (((2 * p.n : ℕ) : ℝ) * p.μ) ≤ (tuning p : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (p.L / (((2 * p.n : ℕ) : ℝ) * p.μ))]
  have hs' := (div_le_iff₀ (mul_pos hm hμ)).mp hs
  refine ⟨hτ, ?_, hα, ?_, ?_⟩
  · unfold tau
    apply (div_le_iff₀ (by positivity : 0 < 2 * (tuning p : ℝ))).mpr
    linarith
  · have he : 3 * alpha p * p.L * tau p =
        p.L / (8 * ((2 * p.n : ℕ) : ℝ) * p.μ * (tuning p : ℝ) ^ 2) := by
      unfold alpha tau
      field_simp; ring
    rw [he]
    apply (div_le_one (by positivity)).mpr
    nlinarith [mul_nonneg (mul_nonneg hm.le hμ.le) (sq_nonneg (tuning p : ℝ))]
  · unfold alpha tau
    field_simp; ring

lemma distance_scale (p : Params) (hμ : 0 < p.μ) :
    tau p / (2 * alpha p) = 3 * ((2 * p.n : ℕ) : ℝ) * p.μ := by
  have hm : (0 : ℝ) < (2 * p.n : ℕ) := by exact_mod_cast Nat.mul_pos (by decide) (NeZero.pos p.n)
  have hr : (0 : ℝ) < tuning p := by exact_mod_cast tuning_pos p
  unfold tau alpha
  field_simp; ring

lemma small_power_bound {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    (1 + δ) ^ m * (1 - (m : ℝ) * δ) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (1 + δ) * (1 - ((m : ℝ) + 1) * δ) ≤ 1 - (m : ℝ) * δ := by
        nlinarith [sq_nonneg δ, mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sq_nonneg δ)]
      have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (by linarith : 0 ≤ 1 + δ) m)
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [hh, ih]

lemma theta_epoch_bounds (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) :
    1 + tau p / 6 ≤ theta p ^ (2 * p.n) ∧
      theta p ^ (2 * p.n) ≤ 1 + tau p ∧
      (1 / 2 - tau p) * theta p + 1 / 2 * theta p ^ (2 * p.n) ≤ 1 := by
  obtain ⟨hτ, hτh, hα, _, he⟩ := tuning_bounds p hL hμ
  have hδ : 0 ≤ alpha p * p.μ := mul_nonneg hα.le hμ.le
  have hm : (1 : ℝ) ≤ (2 * p.n : ℕ) := by exact_mod_cast Nat.mul_pos (by decide) (NeZero.pos p.n)
  have hδle : alpha p * p.μ ≤ tau p / 6 := by nlinarith
  have hlo := one_add_mul_le_pow (show -2 ≤ alpha p * p.μ by linarith) (2 * p.n)
  have hup := small_power_bound hδ (2 * p.n)
  rw [he] at hlo hup
  have hden : 0 < 1 - tau p / 6 := by linarith
  have hupper : theta p ^ (2 * p.n) ≤ 1 + tau p := by
    have heq : theta p = 1 + alpha p * p.μ := rfl
    rw [← heq] at hup
    have hprod : 1 ≤ (1 + tau p) * (1 - tau p / 6) := by nlinarith
    exact (mul_le_mul_iff_left₀ hden).mp (hup.trans hprod)
  refine ⟨hlo, hupper, ?_⟩
  have htheta : theta p ≤ 1 + tau p / 6 := by unfold theta; linarith
  have hmul := mul_le_mul_of_nonneg_left htheta (show 0 ≤ 1 / 2 - tau p by linarith)
  nlinarith [sq_nonneg (tau p)]

lemma tuning_upper (p : Params) :
    (tuning p : ℝ) ≤ 1 + Real.sqrt (p.L / ((2 * p.n : ℕ) * p.μ)) := by
  unfold tuning
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith [Real.sqrt_nonneg (p.L / ((2 * p.n : ℕ) * p.μ))])
    (by have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (p.L / ((2 * p.n : ℕ) * p.μ))); linarith)

lemma tuning_cost_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) :
    p.n * tuning p ≤ p.n + ⌈Real.sqrt ((p.n : ℝ) * p.L / p.μ)⌉₊ := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hs : (p.n : ℝ) * Real.sqrt (p.L / ((2 * p.n : ℕ) * p.μ)) ≤
      Real.sqrt ((p.n : ℝ) * p.L / p.μ) := by
    conv_lhs => lhs; rw [← Real.sqrt_sq (Nat.cast_nonneg p.n)]
    rw [← Real.sqrt_mul (sq_nonneg (p.n : ℝ))]
    apply Real.sqrt_le_sqrt
    push_cast
    field_simp
    nlinarith [mul_pos hn hL]
  have ht := mul_le_mul_of_nonneg_left (tuning_upper p) hn.le
  have hc := Nat.le_ceil (Real.sqrt ((p.n : ℝ) * p.L / p.μ))
  exact_mod_cast (show (p.n : ℝ) * tuning p ≤
      p.n + (⌈Real.sqrt ((p.n : ℝ) * p.L / p.μ)⌉₊ : ℕ) by linarith)

end OracleTemplate.Katyusha
