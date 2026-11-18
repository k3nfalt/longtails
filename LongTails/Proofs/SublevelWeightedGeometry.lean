import LongTails.Proofs.SublevelWeightedDescent
import LongTails.Algorithms.SublevelWeightedGradient

namespace OracleTemplate.SublevelWeighted

open LongTails.Setups.SublevelPLBoundedVariance

lemma normalized_descent (p : Public) {f : p.E → ℝ} {m : ℝ}
    (H : SublevelRobustGradient.Hyp f m p.L p.τ p.α p.x0) (hε : 0 < p.ε)
    (x v : ℕ → p.E) (hx0 : x 0 = p.x0)
    (hx : ∀ j, x (j + 1) = x j - (1 / p.L) • v j) :
    let K := steps p
    let e := fun j => ‖v j - gradient f (x j)‖ ^ 2 / (p.L * p.ε)
    2 * (f (x K) - m) / p.ε ≤ 1 + 3 * ∑ j ∈ Finset.range K, e j +
      16 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) * ∑ j ∈ Finset.range K, e j / (j + 1) := by
  let s := 2 / p.α
  let A := (p.τ / p.ε) ^ s
  let c := 1 / (4 * p.L * p.ε * A)
  let u := fun j => 2 * (f (x j) - m) / p.ε
  let e := fun j => ‖v j - gradient f (x j)‖ ^ 2 / (p.L * p.ε)
  have hL := H.hL
  have hτ := H.hτ
  have hα : 0 < p.α := by linarith [H.hα1]
  have hden : 0 < 2 - p.α := by linarith [H.hα2]
  have hs : 1 < s := (lt_div_iff₀ hα).mpr (by linarith [H.hα2])
  have hs2 : s ≤ 2 := (div_le_iff₀ hα).mpr (by linarith [H.hα1])
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have h2 : (2 : ℝ) ^ s ≤ 4 := by
    calc (2 : ℝ) ^ s ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs2
      _ = 4 := by norm_num
  have base (j : ℕ) : u (j + 1) ≤ u j - ‖gradient f (x j)‖ ^ 2 / (p.L * p.ε) + e j := by
    have h := SublevelRobustGradient.pathwise_descent hL H.hg H.hlip (x j) (v j)
    rw [← hx] at h
    dsimp [u, e]
    field_simp [hL.ne', hε.ne'] at h ⊢
    nlinarith
  have loc (j : ℕ) (h : u j ≤ u 0) : c * u j ^ s ≤ ‖gradient f (x j)‖ ^ 2 / (p.L * p.ε) := by
    have hj : f (x j) ≤ f p.x0 := by
      dsimp [u] at h
      rw [hx0, div_le_div_iff_of_pos_right hε] at h
      linarith
    have hgap := sub_nonneg.mpr (H.hm (x j))
    have hpl : (f (x j) - m) / p.τ ≤ ‖gradient f (x j)‖ ^ p.α := by
      rw [div_le_iff₀ hτ]; linarith [H.hpl (x j) hj]
    have hpow := Real.rpow_le_rpow (div_nonneg hgap hτ.le) hpl (by linarith : 0 ≤ s)
    rw [← Real.rpow_mul (norm_nonneg _), show p.α * s = 2 by dsimp [s]; field_simp,
      Real.rpow_two] at hpow
    have heq : u j = 2 * (p.τ / p.ε) * ((f (x j) - m) / p.τ) := by
      dsimp [u]; field_simp
    rw [heq, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) (by positivity)]
    change 1 / (4 * p.L * p.ε * A) * (2 ^ s * A * _) ≤ _
    field_simp [hL.ne', hε.ne', hA.ne']
    nlinarith [mul_le_mul_of_nonneg_right h2
      (Real.rpow_nonneg (div_nonneg hgap hτ.le) s)]
  have hnum : (1 : ℝ) ^ (-(s - 1)) < (s - 1) * c * steps p := by
    rw [Real.one_rpow]
    have hceil := Nat.le_ceil (16 * p.L * p.ε * A / (2 - p.α))
    have hk : 16 * p.L * p.ε * A / (2 - p.α) ≤ (steps p : ℝ) := by
      unfold steps
      push_cast
      linarith
    have hsc : (s - 1) * c * (16 * p.L * p.ε * A / (2 - p.α)) = 4 / p.α := by
      dsimp [s, c]; field_simp; ring
    have h4 : 1 < 4 / p.α := (lt_div_iff₀ hα).mpr (by linarith [H.hα2])
    exact h4.trans_le (hsc ▸ mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (s - 1) * c))
  have hd := weighted_descent (g := u) (e := e) (K := steps p) (ε := 1)
    (fun j => by dsimp [e]; positivity) hc hs hs2 (by norm_num) (fun j _ => by
      linarith [base j, show 0 ≤ ‖gradient f (x j)‖ ^ 2 / (p.L * p.ε) by positivity])
    (fun j _ hj => by linarith [base j, loc j hj]) hnum
  simp only [Real.one_rpow, mul_one] at hd
  have hco : 2 ^ s / c ≤ 16 * p.L * p.ε * A := by
    dsimp [c]
    rw [div_div_eq_mul_div, div_one]
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ 4 * p.L * p.ε * A)]
  apply hd.trans
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_right hco (Finset.sum_nonneg fun j _ => by dsimp [e]; positivity)

end OracleTemplate.SublevelWeighted
