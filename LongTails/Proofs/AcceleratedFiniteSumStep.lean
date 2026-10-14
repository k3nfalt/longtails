import LongTails.Proofs.AcceleratedVariance
import LongTails.Proofs.AcceleratedFiniteSum
import LongTails.Proofs.AcceleratedStochastic

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.FiniteSum

open LongTails.Setups.FiniteSumSmoothAndConvex

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]

lemma accelerated_variance_reduced_step
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {L A a m : ℝ}
    (hL : 0 < L) (hA : 0 ≤ A) (ha : 0 < a) (hm : 0 < m)
    (hstep : 2 * L * a ^ 2 ≤ m * A)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (snapshot z u : E) :
    let B := A + a
    let y := (A / B) • snapshot + (a / B) • z
    let next := fun i => z - (a / m) • estimator g snapshot y i
    let output := fun i => (A / B) • snapshot + (a / B) • next i
    (𝔼 i, (B * (objective f (output i) - objective f u) + m / 2 * ‖next i - u‖ ^ 2)) ≤
      A * (objective f snapshot - objective f u) + m / 2 * ‖z - u‖ ^ 2 := by
  let B := A + a
  let y := (A / B) • snapshot + (a / B) • z
  let e := estimator g snapshot y
  let v := fullGradient g y
  let H := objective f snapshot - objective f y - ⟪v, snapshot - y⟫
  let D := m * B / a ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hLD : 2 * L ≤ D := by
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    dsimp [B]
    nlinarith
  have hgrad : ∀ x, gradient (objective f) x = fullGradient g x :=
    fun x => (objective_gradient hg x).gradient
  have hgF : ∀ x, HasGradientAt (objective f) (gradient (objective f) x) x := by
    intro x
    rw [hgrad]
    exact objective_gradient hg x
  have hlipF : ∀ x y, ‖gradient (objective f) x - gradient (objective f) y‖ ≤ L * ‖x - y‖ := by
    intro x y
    simpa only [hgrad] using fullGradient_lipschitz hlip x y
  have hu := objective_support hc hg y u
  have hid : B • (y - u) = A • (snapshot - u) + a • (z - u) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hB.ne'] <;> dsimp [B] <;> ring
  have hi := congrArg (fun w => ⟪v, w⟫) hid
  simp only [inner_smul_right, inner_add_right, inner_sub_right] at hi
  have hw : B * (objective f y - objective f u) ≤
      A * (objective f snapshot - objective f u) + a * ⟪v, z - u⟫ - A * H := by
    have hu' := mul_le_mul_of_nonneg_left hu ha.le
    dsimp [H, B, v] at *
    simp only [inner_sub_right] at hu' ⊢
    nlinarith only [hu', hi]
  have hpoint (i : Fin n) :
      B * (objective f ((A / B) • snapshot + (a / B) • (z - (a / m) • e i)) - objective f u) +
          m / 2 * ‖z - (a / m) • e i - u‖ ^ 2 ≤
        A * (objective f snapshot - objective f u) + m / 2 * ‖z - u‖ ^ 2 -
          a * ⟪e i - v, z - u⟫ + a ^ 2 / m * ‖e i - v‖ ^ 2 - A * H := by
    have hout : (A / B) • snapshot + (a / B) • (z - (a / m) • e i) = y - (1 / D) • e i := by
      dsimp [y, D]
      match_scalars
      all_goals field_simp
    have hd := StochasticGradient.inexact_descent hD hLD hgF hlipF y (e i)
    rw [hgrad] at hd
    have hd' := mul_le_mul_of_nonneg_left hd hB.le
    have hcoef : B / D = a ^ 2 / m := by dsimp [D]; field_simp
    have hdescent : B * (objective f (y - (1 / D) • e i) - objective f u) ≤
        B * (objective f y - objective f u) - a ^ 2 / (2 * m) * ‖e i‖ ^ 2 +
          a ^ 2 / m * ‖e i - v‖ ^ 2 := by
      calc
        _ ≤ B * (objective f y - ‖e i‖ ^ 2 / (2 * D) + ‖e i - v‖ ^ 2 / D - objective f u) := by
          dsimp [v]
          nlinarith only [hd']
        _ = _ := by
          have h1 : B * (‖e i‖ ^ 2 / (2 * D)) = a ^ 2 / (2 * m) * ‖e i‖ ^ 2 := by
            calc
              _ = (B / D) / 2 * ‖e i‖ ^ 2 := by field_simp
              _ = _ := by rw [hcoef]; ring
          have h2 : B * (‖e i - v‖ ^ 2 / D) = a ^ 2 / m * ‖e i - v‖ ^ 2 := by
            calc
              _ = B / D * ‖e i - v‖ ^ 2 := by ring
              _ = _ := by rw [hcoef]
          nlinarith only [h1, h2]
    rw [hout, show z - (a / m) • e i - u = (z - u) - (a / m) • e i by module,
      norm_sub_sq_real]
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← real_inner_comm (z - u) (e i), inner_sub_left]
    have hm0 := hm.ne'
    field_simp at hdescent ⊢
    have hw' := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * m by positivity)
    nlinarith only [hdescent, hw']
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hpoint i)
  have hmean : (n : ℝ)⁻¹ • ∑ i, (e i - v) = 0 := by
    simp only [Finset.sum_sub_distrib, smul_sub]
    rw [show (n : ℝ)⁻¹ • ∑ i, e i = v from estimator_unbiased g snapshot y]
    simp [v, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, NeZero.ne n]
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const, expect_inner_left, hmean, inner_zero_left, mul_zero, sub_zero] at hav
  have hvar := estimator_variance_bound hL hc hg hlip snapshot y
  have hH : 0 ≤ H := sub_nonneg.mpr (objective_support hc hg y snapshot)
  have hv := mul_le_mul_of_nonneg_left hvar (show 0 ≤ a ^ 2 / m by positivity)
  have hc' : a ^ 2 / m * (2 * L) ≤ A := by
    calc
      _ = (2 * L * a ^ 2) / m := by ring
      _ ≤ A := (div_le_iff₀ hm).mpr (by nlinarith only [hstep])
  have hh := mul_le_mul_of_nonneg_right hc' hH
  change (𝔼 i, (B * (objective f ((A / B) • snapshot + (a / B) • (z - (a / m) • e i)) - objective f u) +
    m / 2 * ‖z - (a / m) • e i - u‖ ^ 2)) ≤ _
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const]
  dsimp [e, v, H] at hav hv hh ⊢
  nlinarith only [hav, hv, hh]

end OracleTemplate.FiniteSum
