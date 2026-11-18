import LongTails.Proofs.SublevelWeightedSchedule
import LongTails.Proofs.SublevelPLTrajectory

namespace OracleTemplate.SublevelWeighted

open LongTails.Setups.SublevelPLBoundedVariance

lemma trivial_gap (p : Public) {f : p.E → ℝ} {m : ℝ}
    (H : SublevelRobustGradient.Hyp f m p.L p.τ p.α p.x0) (hε : 0 < p.ε)
    (ht : 2 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) < 1) : f p.x0 - m ≤ p.ε := by
  by_contra! hh
  let u := (f p.x0 - m) / p.ε
  have hu : 1 ≤ u := (one_le_div hε).mpr hh.le
  have hL := H.hL
  have hτ := H.hτ
  have hα : 0 < p.α := by linarith [H.hα1]
  have hp : 1 ≤ 2 / p.α := (le_div_iff₀ hα).mpr (by linarith [H.hα2])
  have hg := SublevelRobustGradient.gradient_lower H (x := p.x0) le_rfl (hε.trans hh) le_rfl
  have hd := SublevelRobustGradient.pathwise_descent hL H.hg H.hlip p.x0 (gradient f p.x0)
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at hd
  have hgb : ‖gradient f p.x0‖ ^ 2 ≤ 2 * p.L * (f p.x0 - m) := by
    have h := H.hm (p.x0 - (1 / p.L) • gradient f p.x0)
    rw [sub_div' (by positivity : 2 * p.L ≠ 0), le_div_iff₀ (by positivity)] at hd
    nlinarith [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * p.L)]
  have hu' : u ≤ u ^ (2 / p.α) := by simpa using Real.rpow_le_rpow_of_exponent_le hu hp
  have he : u = ((f p.x0 - m) / p.τ) * (p.τ / p.ε) := by dsimp [u]; field_simp
  have hgap : 0 < f p.x0 - m := hε.trans hh
  nth_rw 2 [he] at hu'
  rw [Real.mul_rpow (by positivity) (by positivity)] at hu'
  have h := hu'.trans (mul_le_mul_of_nonneg_right (hg.trans hgb) (by positivity))
  have hEq : 2 * p.L * (f p.x0 - m) * (p.τ / p.ε) ^ (2 / p.α) =
      (2 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α)) * u := by dsimp [u]; field_simp
  rw [hEq] at h
  nlinarith [mul_lt_mul_of_pos_right ht (by linarith : 0 < u)]

lemma sufficient_calls (p : Public) (hL : 0 < p.L) (hτ : 0 < p.τ) (hε : 0 < p.ε)
    (hα1 : 1 ≤ p.α) (hα2 : p.α < 2) (ht : 1 ≤ 2 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α)) :
    calls (batch (steps p) (scale p)) (steps p) ≤
      ⌈110000 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α) *
        (1 + p.σ ^ 2 * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α))⌉₊ := by
  let A := (p.τ / p.ε) ^ (2 / p.α)
  let D := p.L * p.ε
  let r := 2 - p.α
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hT : 1 ≤ 2 * (D * A / r) := by
    change 1 ≤ 2 * p.L * p.ε * A at ht
    rw [← mul_div_assoc, le_div_iff₀ hr]
    dsimp [D]; nlinarith
  have hK : (steps p : ℝ) ≤ 20 * (D * A / r) := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 16 * D * A / r)
    unfold steps
    push_cast
    change (⌈16 * p.L * p.ε * A / r⌉₊ : ℝ) + 1 ≤ _
    rw [show 16 * p.L * p.ε * A / r = 16 * D * A / r by dsimp [D]; ring]
    simp only [div_eq_mul_inv] at h hT ⊢
    linarith
  have hv : scale p = 1 + 128 * p.σ ^ 2 * (steps p / D + A) := rfl
  have hv0 : 0 < scale p := by rw [hv]; positivity
  have hB : 1 + scale p ≤ 2700 * (1 + p.σ ^ 2 * A / r) := by
    have hKD : (steps p : ℝ) / D ≤ 20 * A / r := by
      rw [div_le_iff₀ hD]
      convert hK using 1; ring
    have hAr : A ≤ A / r := (le_div_iff₀ hr).mpr (by nlinarith)
    have hb := mul_le_mul_of_nonneg_left (add_le_add hKD hAr) (by positivity : 0 ≤ 128 * p.σ ^ 2)
    rw [hv]
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith [show 0 ≤ p.σ ^ 2 * A * r⁻¹ by positivity]
  have h := (batch_cost (steps p) hv0.le).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 2)) hB (by positivity)
      (by positivity))
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans _ (Nat.le_ceil _)
  change (calls _ _ : ℝ) ≤ 110000 * p.L * p.ε * A / r * (1 + p.σ ^ 2 * A / r)
  apply h.trans
  dsimp [D]
  have hn : 0 ≤ p.L * p.ε * A / r * (1 + p.σ ^ 2 * A / r) := by positivity
  simp only [div_eq_mul_inv] at hn ⊢
  nlinarith

end OracleTemplate.SublevelWeighted
