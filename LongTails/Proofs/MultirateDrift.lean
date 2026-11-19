import LongTails.Proofs.MultirateCalendar
import LongTails.Proofs.MultirateEncoding
import LongTails.Proofs.MultiscaleAggregateSampling

namespace LongTails.Proofs.MultirateDrift

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateTrajectory
open LongTails.Algorithms.MultirateCalendar
open LongTails.Algorithms.MultiscaleAggregate (radius precision)
open MultirateCalendar

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

noncomputable abbrev point (k : ℕ) := (trajectory p g s k).points k
noncomputable abbrev estimate (k : ℕ) := (trajectory p g s (k+1)).estimates k

lemma past_point {a k : ℕ} (ha : a ≤ k) :
    (trajectory p g s k).points a = point g s a := by
  induction k, ha using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    simpa only [trajectory, advance, Function.update_of_ne (show a ≠ k+1 by omega)] using ih

lemma past_estimate {a k : ℕ} (ha : a < k) :
    (trajectory p g s k).estimates a = estimate g s a := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : a = k
    · subst k; rfl
    simpa only [trajectory, advance, Function.update_of_ne h] using ih (by omega)

lemma step_eq (k : ℕ) :
    point g s (k+1) = OracleTemplate.NormalizedStorm.stormStep (stepSize p) (point g s k) (estimate g s k) := by
  simp only [point, estimate, trajectory, advance, Function.update_self]

lemma step_nonneg (hL : 0 ≤ (aggregate p).L) (hε : 0 < p.ε) : 0 ≤ stepSize p :=
  div_nonneg (MultiscaleAggregateCodec.precision_pos (p := aggregate p) hε).le (by positivity)

lemma drift (hL : 0 ≤ (aggregate p).L) (hε : 0 < p.ε) {i k : ℕ} (hi : i ≤ k) :
    ‖point g s k - point g s i‖ ≤ (k - i : ℕ) * stepSize p := by
  induction k, hi using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have h := OracleTemplate.NormalizedStorm.stormStep_dist (step_nonneg hL hε) (point g s k) (estimate g s k)
    rw [← step_eq] at h
    have ht := norm_sub_le_norm_sub_add_norm_sub (point g s (k+1)) (point g s k) (point g s i)
    rw [show k+1-i = (k-i)+1 by omega, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith

lemma range_bound (hL : 0 < (aggregate p).L) (hε : 0 < p.ε) {k : ℕ} (hk : k ≤ steps p) :
    (aggregate p).L * ‖point g s k - p.x0‖ ≤ radius (aggregate p) 0 := by
  have h := drift g s hL.le hε (Nat.zero_le k)
  change ‖point g s k - p.x0‖ ≤ _ at h
  simp only [Nat.sub_zero] at h
  have hK : (k : ℝ) ≤ steps p := by exact_mod_cast hk
  have he := MultiscaleAggregateCodec.precision_pos (p := aggregate p) hε
  calc
    _ ≤ (aggregate p).L * (k * stepSize p) := mul_le_mul_of_nonneg_left h hL.le
    _ = (k : ℝ) * precision (aggregate p) := by
      unfold stepSize
      rw [mul_left_comm, mul_div_cancel₀ _ hL.ne']
    _ ≤ (steps p : ℝ) * precision (aggregate p) := mul_le_mul_of_nonneg_right hK he.le
    _ = _ := by simp [steps, Algorithms.MultiscaleAggregate.rounds, radius, Algorithms.MultiscaleAggregate.exponent]

lemma query_drift (hL : 0 < (aggregate p).L) (hε : 0 < p.ε) {k : ℕ} (hk : k ≤ steps p)
    (i : Fin p.n) :
    ‖input p k i (trajectory p g s k) - point g s k‖ ≤
      precision (aggregate p) / (aggregate p).L + (2 * period p i : ℕ) * stepSize p := by
  have ho := origin_le p i k
  rw [input, past_point g s ho]
  have hq := MultirateEncoding.query_accuracy hε hL _ (range_bound g s hL hε (ho.trans hk))
  have hd := drift g s hL.le hε ho
  rw [norm_sub_rev] at hd
  refine (norm_sub_le_norm_sub_add_norm_sub _ (point g s (origin p i k)) _).trans (add_le_add hq ?_)
  exact hd.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (age_lt p i k).le) (step_nonneg hL.le hε))

lemma average_lipschitz (f : Functions p)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖) (x y : Point p) :
    ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ (aggregate p).L * ‖x-y‖ := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  simp only [objective, (MultiscaleAggregateSampling.objective_gradient (p := aggregate p) f hf _).gradient,
    ← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  change _ ≤ ((∑ i, p.L i) / p.n) * _
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) x - gradient (f i) y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, p.L i * ‖x-y‖ := by gcongr with i; exact hl i x y
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma bias (hh : ∀ i, 0 < p.h i) (hLi : ∀ i, 0 ≤ p.L i) (hL : 0 < (aggregate p).L)
    (hε : 0 < p.ε) (f : Functions p) (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    {k : ℕ} (hk : k ≤ steps p) :
    ‖(p.n : ℝ)⁻¹ • (∑ i, gradient (f i) (input p k i (trajectory p g s k))) -
      gradient (objective p f) (point g s k)‖ ≤ 7 * precision (aggregate p) := by
  let δ := precision (aggregate p)
  let η := stepSize p
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have he := step_nonneg hL.le hε
  have hw := weighted_period hh hLi
  have hδ : (∑ i, p.L i) * η = (p.n : ℝ) * δ := by
    have hsum : (∑ i, p.L i) = (p.n : ℝ) * (aggregate p).L := by
      change _ = _ * (_ / _)
      field_simp
    rw [hsum, mul_assoc]
    change _ * ((aggregate p).L * (δ / (aggregate p).L)) = _
    rw [mul_div_cancel₀ _ hL.ne']
  rw [objective, (MultiscaleAggregateSampling.objective_gradient (p := aggregate p) f hf _).gradient,
    ← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, ‖gradient (f i) (input p k i (trajectory p g s k)) - gradient (f i) (point g s k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, p.L i * (η + (2 * (period p i : ℝ)) * η) := by
      apply Finset.sum_le_sum
      intro i _
      apply (hl i _ _).trans
      apply mul_le_mul_of_nonneg_left _ (hLi i)
      simpa only [Nat.cast_mul, Nat.cast_ofNat, η, stepSize] using query_drift g s hL hε hk i
    _ = (∑ i, p.L i) * η + 2 * (∑ i, p.L i * period p i) * η := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      change _ ≤ 7 * δ * p.n
      nlinarith [mul_le_mul_of_nonneg_right hw he]

end LongTails.Proofs.MultirateDrift
