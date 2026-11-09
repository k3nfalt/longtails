import LongTails.Setups.GaussianVariationalInference
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory Real

theorem MeasureTheory.Integrable.addL {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a => f a + g a) μ := hf.add hg

theorem MeasureTheory.Integrable.subL {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a => f a - g a) μ := hf.sub hg

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

noncomputable def sqNorm {d : ℕ} (ξ : Fin d → ℝ) : ℝ := ∑ j, ξ j ^ 2

lemma sqNorm_nonneg {d : ℕ} (ξ : Fin d → ℝ) : 0 ≤ sqNorm ξ :=
  Finset.sum_nonneg fun j _ => sq_nonneg (ξ j)

lemma measurable_sqNorm (d : ℕ) : Measurable (sqNorm (d := d)) := by
  unfold sqNorm
  fun_prop

lemma coord_sq_le {d : ℕ} (ξ : Fin d → ℝ) (j : Fin d) : ξ j ^ 2 ≤ sqNorm ξ :=
  Finset.single_le_sum (f := fun k => ξ k ^ 2) (fun k _ => sq_nonneg (ξ k)) (Finset.mem_univ j)

lemma coord_measurePreserving {d : ℕ} (j : Fin d) :
    MeasurePreserving (fun ξ : Fin d → ℝ => ξ j) (noiseLaw d) (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j

lemma gaussian_sq_integral : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at h
  simpa using h

lemma gaussian_exp_quarter :
    Integrable (fun x : ℝ => rexp (x ^ 2 / 4)) (gaussianReal 0 1) ∧
      ∫ x, rexp (x ^ 2 / 4) ∂gaussianReal 0 1 = √2 := by
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x * rexp (x ^ 2 / 4) =
      (√(2 * π))⁻¹ * rexp (-(1 / 4) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [sub_zero, NNReal.coe_one, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hint : Integrable (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-(1 / 4) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  have hval : ∫ x : ℝ, (√(2 * π))⁻¹ * rexp (-(1 / 4) * x ^ 2) = √2 := by
    rw [integral_const_mul, integral_gaussian]
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    calc (√(2 * π))⁻¹ * √(π / (1 / 4)) = √(π / (1 / 4)) / √(2 * π) := by ring
      _ = √(π / (1 / 4) / (2 * π)) := (Real.sqrt_div (by positivity) _).symm
      _ = √2 := by
        congr 1
        field_simp; ring1
  have hmeas : Measurable (gaussianPDF 0 1) := measurable_gaussianPDF 0 1
  constructor
  · rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    refine hint.congr (ae_of_all _ fun x => ?_)
    simp only [toReal_gaussianPDF, smul_eq_mul]
    exact (hpdf x).symm
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul]
    simp_rw [hpdf]
    exact hval

lemma integrable_expQuarter (d : ℕ) :
    Integrable (fun ξ : Fin d → ℝ => rexp (sqNorm ξ / 4)) (noiseLaw d) ∧
      ∫ ξ, rexp (sqNorm ξ / 4) ∂noiseLaw d = √2 ^ d := by
  have hprod : ∀ ξ : Fin d → ℝ, rexp (sqNorm ξ / 4) = ∏ j, rexp (ξ j ^ 2 / 4) := by
    intro ξ
    rw [sqNorm, Finset.sum_div, Real.exp_sum]
  simp_rw [hprod]
  constructor
  · exact Integrable.fintype_prod (f := fun _ x => rexp (x ^ 2 / 4))
      (fun _ => gaussian_exp_quarter.1)
  · rw [noiseLaw, integral_fintype_prod_eq_prod (f := fun _ x => rexp (x ^ 2 / 4))]
    simp [gaussian_exp_quarter.2]

lemma one_add_le_exp_eighth (S : ℝ) : 1 + S ≤ 8 * rexp (S / 8) := by
  have h := Real.add_one_le_exp (S / 8)
  linarith

lemma one_add_sq_le_exp_quarter {S : ℝ} (hS : 0 ≤ S) : (1 + S) ^ 2 ≤ 64 * rexp (S / 4) := by
  have h := one_add_le_exp_eighth S
  have h0 : 0 ≤ 1 + S := by linarith
  have he : rexp (S / 4) = rexp (S / 8) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  nlinarith

lemma integrable_of_le_exp {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (noiseLaw d)) (c : ℝ)
    (h : ∀ ξ, |f ξ| ≤ c * rexp (sqNorm ξ / 4)) : Integrable f (noiseLaw d) :=
  ((integrable_expQuarter d).1.const_mul c).mono' hf
    (ae_of_all _ fun ξ => by simpa [Real.norm_eq_abs] using h ξ)

lemma integrable_poly {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (noiseLaw d)) (c : ℝ)
    (h : ∀ ξ, |f ξ| ≤ c * (1 + sqNorm ξ) ^ 2) : Integrable f (noiseLaw d) := by
  refine integrable_of_le_exp hf (|c| * 64) fun ξ => ?_
  have hS := sqNorm_nonneg ξ
  have h1 := one_add_sq_le_exp_quarter hS
  have h2 : c * (1 + sqNorm ξ) ^ 2 ≤ |c| * (1 + sqNorm ξ) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (sq_nonneg _)
  calc |f ξ| ≤ |c| * (1 + sqNorm ξ) ^ 2 := (h ξ).trans h2
    _ ≤ |c| * (64 * rexp (sqNorm ξ / 4)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    _ = |c| * 64 * rexp (sqNorm ξ / 4) := by ring

lemma integral_coord_fun {d : ℕ} (j : Fin d) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    ∫ ξ, f (ξ j) ∂noiseLaw d = ∫ x, f x ∂gaussianReal 0 1 := by
  have hmp := coord_measurePreserving (d := d) j
  have h := integral_map (μ := noiseLaw d) hmp.measurable.aemeasurable (f := f)
    (by rw [hmp.map_eq]; exact hf)
  rw [hmp.map_eq] at h
  exact h.symm

lemma integral_coord {d : ℕ} (j : Fin d) : ∫ ξ, ξ j ∂noiseLaw d = 0 := by
  rw [integral_coord_fun j (fun x => x) aestronglyMeasurable_id]
  simp [integral_id_gaussianReal]

lemma integral_coord_sq {d : ℕ} (j : Fin d) : ∫ ξ, ξ j ^ 2 ∂noiseLaw d = 1 := by
  rw [integral_coord_fun j (fun x => x ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable]
  exact gaussian_sq_integral

lemma coord_iIndep (d : ℕ) :
    iIndepFun (fun (j : Fin d) (ξ : Fin d → ℝ) => ξ j) (noiseLaw d) :=
  iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)

lemma integral_coord_mul {d : ℕ} (j k : Fin d) :
    ∫ ξ, ξ j * ξ k ∂noiseLaw d = if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst h
    simp only [↓reduceIte]
    simpa [sq] using integral_coord_sq (d := d) j
  · simp only [h, ↓reduceIte]
    have hind := (coord_iIndep d).indepFun h
    have he := hind.integral_mul_eq_mul_integral
      (measurable_pi_apply j).aestronglyMeasurable (measurable_pi_apply k).aestronglyMeasurable
    simp only [Pi.mul_apply] at he
    rw [he, integral_coord j, zero_mul]

lemma integrable_coord {d : ℕ} (j : Fin d) : Integrable (fun ξ : Fin d → ℝ => ξ j) (noiseLaw d) :=
  integrable_poly (measurable_pi_apply j).aestronglyMeasurable 1 fun ξ => by
    have hS := sqNorm_nonneg ξ
    have hj := coord_sq_le ξ j
    have habs : |ξ j| ≤ 1 + sqNorm ξ := by
      rcases le_or_gt |ξ j| 1 with h1 | h1
      · linarith
      · have : |ξ j| ≤ |ξ j| ^ 2 := by nlinarith
        rw [sq_abs] at this
        linarith
    nlinarith

lemma integrable_coord_mul {d : ℕ} (j k : Fin d) :
    Integrable (fun ξ : Fin d → ℝ => ξ j * ξ k) (noiseLaw d) :=
  integrable_poly ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable 1
    fun ξ => by
      have hS := sqNorm_nonneg ξ
      have hj := coord_sq_le ξ j
      have hk := coord_sq_le ξ k
      have h : |ξ j * ξ k| ≤ sqNorm ξ := by
        rw [abs_mul]
        nlinarith [sq_abs (ξ j), sq_abs (ξ k), abs_nonneg (ξ j), abs_nonneg (ξ k),
          sq_nonneg (|ξ j| - |ξ k|)]
      nlinarith

lemma integral_sqNorm (d : ℕ) : ∫ ξ, sqNorm ξ ∂noiseLaw d = d := by
  unfold sqNorm
  rw [integral_finsetSum _ fun j _ => (integrable_coord_mul j j).congr
    (ae_of_all _ fun ξ => by simp [sq])]
  simp [integral_coord_sq]

lemma tail_split {S τ A B : ℝ} (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A ≤ B * (1 + S)) :
    (1 + S) * A ≤ (1 + τ) * A + B * (64 / rexp 1 * rexp (S / 4 - τ / 8)) := by
  rcases le_or_gt S τ with h | h
  · have h1 : (1 + S) * A ≤ (1 + τ) * A := mul_le_mul_of_nonneg_right (by linarith) hA
    have h2 : 0 ≤ B * (64 / rexp 1 * rexp (S / 4 - τ / 8)) := by positivity
    linarith
  · have ht := Real.add_one_le_exp ((S - τ) / 8 - 1)
    have he1 : rexp ((S - τ) / 8 - 1) = rexp ((S - τ) / 8) / rexp 1 := by
      rw [Real.exp_sub]
    have hyt : S - τ ≤ 8 / rexp 1 * rexp ((S - τ) / 8) := by
      rw [he1] at ht
      have : (S - τ) / 8 ≤ rexp ((S - τ) / 8) / rexp 1 := by linarith
      calc S - τ = 8 * ((S - τ) / 8) := by ring
        _ ≤ 8 * (rexp ((S - τ) / 8) / rexp 1) := by linarith
        _ = 8 / rexp 1 * rexp ((S - τ) / 8) := by ring
    have hs := one_add_le_exp_eighth S
    have hprod : (S - τ) * (1 + S) ≤ 64 / rexp 1 * rexp (S / 4 - τ / 8) := by
      have hpos : 0 ≤ S - τ := by linarith
      have h0 : 0 ≤ 8 / rexp 1 * rexp ((S - τ) / 8) := by positivity
      have hm := mul_le_mul hyt hs (by linarith) h0
      have hexp : rexp ((S - τ) / 8) * rexp (S / 8) = rexp (S / 4 - τ / 8) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc (S - τ) * (1 + S) ≤ 8 / rexp 1 * rexp ((S - τ) / 8) * (8 * rexp (S / 8)) := hm
        _ = 64 / rexp 1 * (rexp ((S - τ) / 8) * rexp (S / 8)) := by ring
        _ = _ := by rw [hexp]
    have hsplit : (1 + S) * A = (1 + τ) * A + (S - τ) * A := by ring
    have hpos : 0 ≤ S - τ := by linarith
    have hstep : (S - τ) * A ≤ (S - τ) * (B * (1 + S)) := mul_le_mul_of_nonneg_left hAB hpos
    have hstep2 : (S - τ) * (B * (1 + S)) ≤ B * (64 / rexp 1 * rexp (S / 4 - τ / 8)) := by
      have := mul_le_mul_of_nonneg_left hprod hB
      linarith
    linarith

lemma tail_integral (d : ℕ) (τ : ℝ) :
    Integrable (fun ξ : Fin d → ℝ => 64 / rexp 1 * rexp (sqNorm ξ / 4 - τ / 8)) (noiseLaw d) ∧
      ∫ ξ, 64 / rexp 1 * rexp (sqNorm ξ / 4 - τ / 8) ∂noiseLaw d =
        64 / rexp 1 * rexp (-(τ / 8)) * √2 ^ d := by
  have he : ∀ ξ : Fin d → ℝ, 64 / rexp 1 * rexp (sqNorm ξ / 4 - τ / 8) =
      64 / rexp 1 * rexp (-(τ / 8)) * rexp (sqNorm ξ / 4) := by
    intro ξ
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  simp_rw [he]
  exact ⟨(integrable_expQuarter d).1.const_mul _, by
    rw [integral_const_mul, (integrable_expQuarter d).2]⟩

lemma tail_budget {d : ℕ} {κ : ℝ} (hκ : 1 ≤ κ) :
    2 * κ * (64 / rexp 1 * rexp (-((3 * d + 8 * Real.log (48 * κ)) / 8)) * √2 ^ d) ≤ 1 := by
  have hκ0 : 0 < κ := by linarith
  have h48 : 0 < 48 * κ := by positivity
  have hexp : rexp (-((3 * d + 8 * Real.log (48 * κ)) / 8)) =
      rexp (-(3 / 8 : ℝ)) ^ d / (48 * κ) := by
    rw [show -((3 * (d : ℝ) + 8 * Real.log (48 * κ)) / 8) =
        (d : ℝ) * (-(3 / 8)) + -Real.log (48 * κ) by ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_neg (Real.log _), Real.exp_log h48]
    field_simp
  rw [hexp]
  have he1 : (2.7182818283 : ℝ) < rexp 1 := Real.exp_one_gt_d9
  have he0 : 0 < rexp 1 := Real.exp_pos 1
  have hq : √2 * rexp (-(3 / 8 : ℝ)) ≤ 1 := by
    have h34 : (2 : ℝ) ≤ rexp (3 / 4) := by
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num)
      nlinarith
    have hsq : (√2 * rexp (-(3 / 8 : ℝ))) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), ← Real.exp_nat_mul]
      have : rexp ((2 : ℕ) * (-(3 / 8 : ℝ))) = (rexp (3 / 4))⁻¹ := by
        rw [← Real.exp_neg]
        congr 1
        push_cast
        ring
      rw [this]
      have hpos : 0 < rexp (3 / 4) := Real.exp_pos _
      rw [← div_eq_mul_inv, div_le_one hpos]
      exact h34
    have hnn : 0 ≤ √2 * rexp (-(3 / 8 : ℝ)) := by positivity
    nlinarith
  have hpow : (√2 * rexp (-(3 / 8 : ℝ))) ^ d ≤ 1 :=
    pow_le_one₀ (by positivity) hq
  have hrw : 2 * κ * (64 / rexp 1 * (rexp (-(3 / 8 : ℝ)) ^ d / (48 * κ)) * √2 ^ d) =
      128 / (48 * rexp 1) * (√2 * rexp (-(3 / 8 : ℝ))) ^ d := by
    rw [mul_pow]
    field_simp; ring1
  rw [hrw]
  have hc : 128 / (48 * rexp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc 128 / (48 * rexp 1) * (√2 * rexp (-(3 / 8 : ℝ))) ^ d ≤ 1 * 1 :=
        mul_le_mul hc hpow (by positivity) (by norm_num)
    _ = 1 := by norm_num

end OracleTemplate.GaussianVariational
