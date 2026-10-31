import LongTails.Proofs.GeneralizedFiniteSumSampling
import LongTails.Proofs.GeneralizedFiniteSumLocal

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.GeneralizedFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma local_inexact_descent {f : E → ℝ} {L D : ℝ}
    (hD : 0 < D) (hLD : 2 * L ≤ D)
    (y g v : E)
    (hupper : f (y - (1 / D) • g) ≤ f y + ⟪v, y - (1 / D) • g - y⟫ +
      L / 2 * ‖y - (1 / D) • g - y‖ ^ 2) :
    f (y - (1 / D) • g) ≤ f y - ‖g‖ ^ 2 / (2 * D) +
      ‖g - v‖ ^ 2 / D := by
  have hd := hupper
  have he : y - (1 / D) • g - y = -(1 / D) • g := by module
  rw [he] at hd
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    mul_pow, sq_abs] at hd
  have hn := sq_nonneg ‖g - (2 : ℝ) • (g - v)‖
  rw [norm_sub_sq_real] at hn
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_right, real_inner_self_eq_norm_sq] at hn
  rw [← real_inner_comm g (v)] at hn
  have hcoef := mul_le_mul_of_nonneg_right hLD (sq_nonneg ‖g‖)
  have hD0 := hD.ne'
  field_simp at hd ⊢
  nlinarith

lemma local_accelerated_step {k : ℕ} [NeZero k]
    {f : E → ℝ} {L A a m V : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hm : 0 < m)
    (hstep : 2 * L * a ^ 2 ≤ m * A) (hvariance : a ^ 2 * V ≤ m * A)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (snapshot z u : E) (e : Fin k → E)
    (hunbiased : (k : ℝ)⁻¹ • ∑ i, e i =
      gradient f ((A / (A + a)) • snapshot + (a / (A + a)) • z))
    (hvar : (𝔼 i, ‖e i - gradient f ((A / (A + a)) • snapshot + (a / (A + a)) • z)‖ ^ 2) ≤
      V * (f snapshot - f ((A / (A + a)) • snapshot + (a / (A + a)) • z) -
        ⟪gradient f ((A / (A + a)) • snapshot + (a / (A + a)) • z),
          snapshot - ((A / (A + a)) • snapshot + (a / (A + a)) • z)⟫))
    (hupper : ∀ i, let y := (A / (A + a)) • snapshot + (a / (A + a)) • z
      let D := m * (A + a) / a ^ 2
      f (y - (1 / D) • e i) ≤ f y + ⟪gradient f y, y - (1 / D) • e i - y⟫ +
        L / 2 * ‖y - (1 / D) • e i - y‖ ^ 2) :
    let B := A + a
    let next := fun i => z - (a / m) • e i
    let output := fun i => (A / B) • snapshot + (a / B) • next i
    (𝔼 i, (B * (f (output i) - f u) + m / 2 * ‖next i - u‖ ^ 2)) ≤
      A * (f snapshot - f u) + m / 2 * ‖z - u‖ ^ 2 := by
  let B := A + a
  let y := (A / B) • snapshot + (a / B) • z
  let v := gradient f y
  let H := f snapshot - f y - ⟪v, snapshot - y⟫
  let D := m * B / a ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hLD : 2 * L ≤ D := by
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    dsimp [B]
    nlinarith
  have hu := Gradient.convex_support hc hg y u
  have hid : B • (y - u) = A • (snapshot - u) + a • (z - u) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hB.ne'] <;> dsimp [B] <;> ring
  have hi := congrArg (fun w => ⟪v, w⟫) hid
  simp only [inner_smul_right, inner_add_right, inner_sub_right] at hi
  have hw : B * (f y - f u) ≤
      A * (f snapshot - f u) + a * ⟪v, z - u⟫ - A * H := by
    have hu' := mul_le_mul_of_nonneg_left hu ha.le
    dsimp [H, B, v] at *
    simp only [inner_sub_right] at hu' ⊢
    nlinarith only [hu', hi]
  have hpoint (i : Fin k) :
      B * (f ((A / B) • snapshot + (a / B) • (z - (a / m) • e i)) - f u) +
          m / 2 * ‖z - (a / m) • e i - u‖ ^ 2 ≤
        A * (f snapshot - f u) + m / 2 * ‖z - u‖ ^ 2 -
          a * ⟪e i - v, z - u⟫ + a ^ 2 / m * ‖e i - v‖ ^ 2 - A * H := by
    have hout : (A / B) • snapshot + (a / B) • (z - (a / m) • e i) = y - (1 / D) • e i := by
      dsimp [y, D]
      match_scalars
      all_goals field_simp
    have hd := local_inexact_descent hD hLD y (e i) v (hupper i)
    have hd' := mul_le_mul_of_nonneg_left hd hB.le
    have hcoef : B / D = a ^ 2 / m := by dsimp [D]; field_simp
    have hdescent : B * (f (y - (1 / D) • e i) - f u) ≤
        B * (f y - f u) - a ^ 2 / (2 * m) * ‖e i‖ ^ 2 +
          a ^ 2 / m * ‖e i - v‖ ^ 2 := by
      calc
        _ ≤ B * (f y - ‖e i‖ ^ 2 / (2 * D) + ‖e i - v‖ ^ 2 / D - f u) := by
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
  have hmean : (k : ℝ)⁻¹ • ∑ i, (e i - v) = 0 := by
    simp only [Finset.sum_sub_distrib, smul_sub]
    rw [hunbiased]
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, NeZero.ne k, v, y, B]
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const, FiniteSum.expect_inner_left, hmean, inner_zero_left, mul_zero, sub_zero] at hav
  have hH : 0 ≤ H := sub_nonneg.mpr (Gradient.convex_support hc hg y snapshot)
  have hv := mul_le_mul_of_nonneg_left hvar (show 0 ≤ a ^ 2 / m by positivity)
  have hc' : a ^ 2 / m * V ≤ A := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hm).mpr (by nlinarith only [hvariance])
  have hh := mul_le_mul_of_nonneg_right hc' hH
  change (𝔼 i, (B * (f ((A / B) • snapshot + (a / B) • (z - (a / m) • e i)) - f u) +
    m / 2 * ‖z - (a / m) • e i - u‖ ^ 2)) ≤ _
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const]
  dsimp [H] at hav hv hh ⊢
  nlinarith only [hav, hv, hh]


omit [CompleteSpace E] in
lemma mix_sub_snapshot {A a : ℝ} (hB : A + a ≠ 0) (s z : E) :
    mix A a s z - s = (a / (A + a)) • (z - s) := by
  unfold mix
  match_scalars
  all_goals field_simp <;> ring

omit [CompleteSpace E] in
lemma mix_dual_step {A a m : ℝ} (hB : A + a ≠ 0) (hm : m ≠ 0) (s z v : E) :
    mix A a s (z - (a / m) • v) = mix A a s z - (a ^ 2 / (m * (A + a))) • v := by
  unfold mix
  match_scalars
  all_goals field_simp

omit [CompleteSpace E] in
lemma mix_radius {A a R : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a)
    (s z u : E) (hs : ‖s - u‖ ≤ R) (hz : ‖z - u‖ ≤ R) :
    ‖mix A a s z - u‖ ≤ R := by
  have he : mix A a s z - u = (A / (A + a)) • (s - u) + (a / (A + a)) • (z - u) := by
    unfold mix
    match_scalars
    all_goals field_simp <;> ring
  rw [he]
  calc
    _ ≤ ‖(A / (A + a)) • (s - u)‖ + ‖(a / (A + a)) • (z - u)‖ := norm_add_le _ _
    _ = (A / (A + a)) * ‖s - u‖ + (a / (A + a)) * ‖z - u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hA hB.le), abs_of_nonneg (div_nonneg ha hB.le)]
    _ ≤ (A / (A + a)) * R + (a / (A + a)) * R := by gcongr
    _ = R := by field_simp

end OracleTemplate.GeneralizedFiniteSum
