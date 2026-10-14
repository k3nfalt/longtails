import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

lemma resolvent_slack {V Y I D N c : ℝ} (hc : 0 ≤ c)
    (hgen : Y ≤ V - c * I - D + N) (hjump : Y ≤ 4 * I + N) :
    Y ≤ 4 / (4 + c) * V - 4 / (4 + c) * D + N := by
  have hd : 0 < 4 + c := by positivity
  have hh := mul_le_mul_of_nonneg_left hjump hc
  have he : 4 / (4 + c) * V - 4 / (4 + c) * D + N =
      (4 * V - 4 * D + (4 + c) * N) / (4 + c) := by field_simp
  rw [he]
  apply (le_div_iff₀ hd).mpr
  nlinarith

lemma coupled_step {E E' H H' D G q v r a b d g w w' : ℝ}
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hw' : 0 ≤ w')
    (hE : E' ≤ q * E + v * H - a * D - b * G)
    (hH : H' ≤ r * H + d * D + g * G)
    (hweight : v + w' * r = q * w)
    (hd : w' * d ≤ a) (hg : w' * g ≤ b) :
    E' + w' * H' ≤ q * (E + w * H) := by
  have hh := mul_le_mul_of_nonneg_left hH hw'
  have hdd := mul_le_mul_of_nonneg_right hd hD
  have hgg := mul_le_mul_of_nonneg_right hg hG
  have he : q * (E + w * H) = q * E + (v + w' * r) * H := by
    rw [hweight]
    ring
  rw [he]
  nlinarith

lemma coupled_epoch {q : ℝ} (hq : 0 ≤ q) (E H w : ℕ → ℝ) (m : ℕ)
    (hzero : H 0 = 0) (hend : w m = 0)
    (hstep : ∀ k < m, E (k + 1) + w (k + 1) * H (k + 1) ≤
      q * (E k + w k * H k)) :
    E m ≤ q ^ m * E 0 := by
  have hi : ∀ k ≤ m, E k + w k * H k ≤ q ^ k * E 0 := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have hh := ih (by omega)
      calc
        E (k + 1) + w (k + 1) * H (k + 1) ≤
            q * (E k + w k * H k) := hstep k (by omega)
        _ ≤ q * (q ^ k * E 0) := mul_le_mul_of_nonneg_left hh hq
        _ = q ^ (k + 1) * E 0 := by rw [pow_succ]; ring
  simpa [hend] using hi m le_rfl

noncomputable def backwardWeight (q v r : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (v + r * backwardWeight q v r k) / q

lemma backwardWeight_nonneg {q v r : ℝ} (hq : 0 < q) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (k : ℕ) : 0 ≤ backwardWeight q v r k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [backwardWeight]; positivity

lemma backwardWeight_equation {q v r : ℝ} (hq : q ≠ 0) (k : ℕ) :
    v + backwardWeight q v r k * r = q * backwardWeight q v r (k + 1) := by
  simp only [backwardWeight]
  field_simp

lemma backwardWeight_sum {q v r : ℝ} (hq : q ≠ 0) (k : ℕ) :
    backwardWeight q v r k = (v / q) * ∑ j ∈ Finset.range k, (r / q) ^ j := by
  induction k with
  | zero => simp [backwardWeight]
  | succ k ih =>
    have hs : (∑ j ∈ Finset.range k, (r / q) ^ (j + 1)) =
        (r / q) * ∑ j ∈ Finset.range k, (r / q) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    rw [backwardWeight, ih, Finset.sum_range_succ', hs]
    simp only [pow_zero]
    field_simp
    ring

lemma bounded_geometric_power {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    (1 + 8 / (m : ℝ)) ^ k ≤ 6561 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx : 1 ≤ 1 + 8 / (m : ℝ) := by
    have hh : 0 ≤ 8 / (m : ℝ) := by positivity
    linarith
  have he : 1 + 8 / (m : ℝ) ≤ Real.exp (8 / (m : ℝ)) := by
    linarith [Real.add_one_le_exp (8 / (m : ℝ))]
  calc
    _ ≤ (1 + 8 / (m : ℝ)) ^ m := pow_le_pow_right₀ hx hk
    _ ≤ (Real.exp (8 / (m : ℝ))) ^ m := pow_le_pow_left₀ (by positivity) he m
    _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ = (Real.exp 1) ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (3 : ℝ) ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 8
    _ = 6561 := by norm_num

lemma backwardWeight_bound {q v r : ℝ} {m k : ℕ}
    (hq : 1 / 2 ≤ q) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (hm : 0 < m) (hk : k ≤ m) (hratio : r / q ≤ 1 + 8 / (m : ℝ)) :
    backwardWeight q v r k ≤ 16384 * v * m := by
  have hqp : 0 < q := by linarith
  rw [backwardWeight_sum hqp.ne']
  have hsum : (∑ j ∈ Finset.range k, (r / q) ^ j) ≤ (k : ℝ) * 6561 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (6561 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (pow_le_pow_left₀ (div_nonneg hr hqp.le) hratio j).trans
          (bounded_geometric_power hm ((Finset.mem_range.mp hj).le.trans hk))
      _ = _ := by simp
  have hdiv : v / q ≤ 2 * v := by
    apply (div_le_iff₀ hqp).mpr
    nlinarith
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk
  calc
    _ ≤ (v / q) * ((k : ℝ) * 6561) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 * v) * ((k : ℝ) * 6561) := mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ ≤ 16384 * v * m := by nlinarith [mul_le_mul_of_nonneg_left hkm hv]

lemma distance_coarsening {m θ η c H D G I Y : ℝ}
    (hm : 1 ≤ m) (hc : 0 ≤ c) (hsmall : c ≤ 1 / m)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hflow : I ≤ 2 * H + 4 * θ ^ 2 * D)
    (hstep : Y ≤ H + (2 / m + c) * I + m * θ ^ 2 * D + (m + 1) * η ^ 2 * G) :
    Y ≤ (1 + 6 / m) * H + 61 * m * θ ^ 2 * D + 2 * m * η ^ 2 * G := by
  have hm0 : 0 < m := by linarith
  have hcoef : 0 ≤ 2 / m + c := by positivity
  have h1 := mul_le_mul_of_nonneg_left hflow hcoef
  have h2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 2 * H + 4 * θ ^ 2 * D by positivity)
  have hinv : 1 / m ≤ m := by apply (div_le_iff₀ hm0).mpr; nlinarith
  have h3 := mul_le_mul_of_nonneg_right hinv (show 0 ≤ 12 * θ ^ 2 * D by positivity)
  have h4 := mul_le_mul_of_nonneg_right hm (show 0 ≤ η ^ 2 * G by positivity)
  simp only [div_eq_mul_inv] at hstep h1 h2 h3 ⊢
  nlinarith [show 0 ≤ m * θ ^ 2 * D by positivity]

lemma energy_coarsening {q V Y v H D G I a b θ : ℝ}
    (hv : 0 ≤ v) (hD : 0 ≤ D)
    (hflow : I ≤ 2 * H + 4 * θ ^ 2 * D)
    (hstep : Y ≤ q * V - a * D - b * G + v * I) :
    Y ≤ q * V + 2 * v * H - (a - 20 * v * θ ^ 2) * D - b * G := by
  have h1 := mul_le_mul_of_nonneg_left hflow hv
  nlinarith [show 0 ≤ v * θ ^ 2 * D by positivity]

end OracleTemplate.ContinuizedSimilarQuasar.Movement
