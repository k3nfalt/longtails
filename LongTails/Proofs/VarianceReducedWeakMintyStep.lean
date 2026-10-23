import LongTails.Proofs.CohypoRegularizedOperator
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Expect

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.VarianceReducedWeakMinty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma monotone_resolvent_nonexpansive (A : E → Set E) (J : ℝ → E → E)
    (hJ : ∀ η z, 0 < η → η⁻¹ • (z - J η z) ∈ A (J η z))
    (hA : ∀ x y, ∀ a ∈ A x, ∀ b ∈ A y, 0 ≤ ⟪a - b, x - y⟫)
    {η : ℝ} (hη : 0 < η) (x y : E) : ‖J η x - J η y‖ ≤ ‖x - y‖ := by
  let H : StochasticCohypomonotone.OpHyp (fun _ : E => 0) A J 1 0 :=
    { res := hJ
      mono := hA
      lip := by intro x y; simp
      cohypo := by intro x y a ha b hb; simpa using hA x y a ha b hb
      L_pos := by norm_num
      ρ_nonneg := le_rfl }
  exact H.res_nonexp hη x y

lemma picard_fixed_point [CompleteSpace E] (P F : E → E) (z : E) {η L : ℝ}
    (hη : 0 < η) (hL : 0 ≤ L) (hηL : η * L < 1)
    (hP : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) :
    ∃ t, P (z - η • F t) = t := by
  let T := fun x => P (z - η • F x)
  let a : NNReal := ⟨η * L, mul_nonneg hη.le hL⟩
  have hc : ContractingWith a T := by
    refine ⟨hηL, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    simp only [dist_eq_norm, T]
    change ‖P (z - η • F x) - P (z - η • F y)‖ ≤ (η * L) * ‖x - y‖
    have he : (z - η • F x) - (z - η • F y) = -η • (F x - F y) := by module
    calc
      _ ≤ ‖(z - η • F x) - (z - η • F y)‖ := hP _ _
      _ = η * ‖F x - F y‖ := by
        rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη]
      _ ≤ η * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left (hF x y) hη.le
      _ = _ := by ring
  exact ⟨hc.fixedPoint T, hc.fixedPoint_isFixedPt⟩

lemma corrected_energy (z y xstar u : E) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hm : -(1 - s) * ‖u‖ ^ 2 ≤ ⟪u, y - xstar⟫) :
    ‖z - s • u - xstar‖ ^ 2 ≤ ‖z - xstar‖ ^ 2 -
      s ^ 2 / 2 * ‖z - y‖ ^ 2 + 2 * ‖u - (z - y)‖ ^ 2 := by
  have hi : ‖z - s • u - xstar‖ ^ 2 = ‖z - xstar‖ ^ 2 -
      2 * s * ⟪u, y - xstar⟫ - 2 * s * ⟪u, z - y⟫ + s ^ 2 * ‖u‖ ^ 2 := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm xstar z, real_inner_comm u z, real_inner_comm u xstar]
    ring
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * s)
  have hyoung := sq_nonneg ‖s • (z - y) - (2 * (1 - s)) • (u - (z - y))‖
  have he : 0 ≤ s * (2 - s) * ‖u - (z - y)‖ ^ 2 :=
    mul_nonneg (mul_nonneg hs (by linarith)) (sq_nonneg _)
  rw [hi]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at hyoung he ⊢
  simp only [real_inner_comm y z, real_inner_comm u z, real_inner_comm u y] at hyoung he ⊢
  simp only [← real_inner_self_eq_norm_sq, inner_sub_right] at hm'
  linear_combination hm' + hyoung / 2 + he

lemma corrected_energy_with_noise (z y xstar u ξ : E) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hm : -(1 - s) * ‖u‖ ^ 2 ≤ ⟪u, y - xstar⟫) :
    ‖z - s • (u + ξ) - xstar‖ ^ 2 ≤ ‖z - xstar‖ ^ 2 -
      s ^ 2 / 2 * ‖z - y‖ ^ 2 + 2 * ‖u - (z - y)‖ ^ 2 +
      s ^ 2 * ‖ξ‖ ^ 2 - 2 * s * ⟪ξ, z - s • u - xstar⟫ := by
  have hi : ‖z - s • (u + ξ) - xstar‖ ^ 2 =
      ‖z - s • u - xstar‖ ^ 2 + s ^ 2 * ‖ξ‖ ^ 2 -
      2 * s * ⟪ξ, z - s • u - xstar⟫ := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm ξ z, real_inner_comm ξ u, real_inner_comm ξ xstar]
    ring
  rw [hi]
  linarith [corrected_energy z y xstar u hs hs1 hm]

lemma mean_corrected_energy {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (z y xstar u : E) (ξ : Ω → E) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hξ : ∑ ω, ξ ω = 0)
    (hm : -(1 - s) * ‖u‖ ^ 2 ≤ ⟪u, y - xstar⟫) :
    (𝔼 ω, ‖z - s • (u + ξ ω) - xstar‖ ^ 2) ≤ ‖z - xstar‖ ^ 2 -
      s ^ 2 / 2 * ‖z - y‖ ^ 2 + 2 * ‖u - (z - y)‖ ^ 2 +
      s ^ 2 * (𝔼 ω, ‖ξ ω‖ ^ 2) := by
  have hzero : (𝔼 ω, ⟪ξ ω, z - s • u - xstar⟫) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, ← sum_inner, hξ, inner_zero_left, zero_div]
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun ω _ => corrected_energy_with_noise z y xstar u (ξ ω) hs hs1 hm)
  simpa only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, Fintype.expect_const, hzero, mul_zero, sub_zero] using h

lemma mean_norm_add_sq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : E) (ξ : Ω → E) (hξ : ∑ ω, ξ ω = 0) :
    (𝔼 ω, ‖u + ξ ω‖ ^ 2) = ‖u‖ ^ 2 + (𝔼 ω, ‖ξ ω‖ ^ 2) := by
  have hz : (𝔼 ω, ⟪u, ξ ω⟫) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, ← inner_sum, hξ, inner_zero_right, zero_div]
  simp only [norm_add_sq_real, Finset.expect_add_distrib,
    ← Finset.mul_expect, Fintype.expect_const, hz, mul_zero, add_zero]

lemma mean_picard_error {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P F : E → E) (z y t : E) (ξ : Ω → E) {η L v : ℝ}
    (hP : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖)
    (ht : P (z - η • F t) = t)
    (hF : ‖F y - F t‖ ≤ L * ‖y - t‖)
    (hξ : ∑ ω, ξ ω = 0) (hv : (𝔼 ω, ‖ξ ω‖ ^ 2) ≤ v) :
    (𝔼 ω, ‖P (z - η • (F y + ξ ω)) - t‖ ^ 2) ≤
      η ^ 2 * L ^ 2 * ‖y - t‖ ^ 2 + η ^ 2 * v := by
  have hp (ω : Ω) : ‖P (z - η • (F y + ξ ω)) - t‖ ^ 2 ≤
      η ^ 2 * ‖F y - F t + ξ ω‖ ^ 2 := by
    have hh := hP (z - η • (F y + ξ ω)) (z - η • F t)
    rw [ht] at hh
    have he : z - η • (F y + ξ ω) - (z - η • F t) =
        -η • (F y - F t + ξ ω) := by module
    rw [he] at hh
    have hb := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq] using hb
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun ω _ => hp ω)
  rw [← Finset.mul_expect, mean_norm_add_sq _ _ hξ] at hh
  have hf := pow_le_pow_left₀ (norm_nonneg _) hF 2
  simp only [mul_pow] at hf
  have h1 := mul_le_mul_of_nonneg_left hf (sq_nonneg η)
  have h2 := mul_le_mul_of_nonneg_left hv (sq_nonneg η)
  nlinarith

lemma snapshot_energy (x w xstar : E) (p : ℝ) :
    ‖(1 - p) • x + p • w - xstar‖ ^ 2 =
      (1 - p) * ‖x - xstar‖ ^ 2 + p * ‖w - xstar‖ ^ 2 -
      p * (1 - p) * ‖x - w‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm w x, real_inner_comm xstar x, real_inner_comm xstar w]
  ring

end OracleTemplate.VarianceReducedWeakMinty
