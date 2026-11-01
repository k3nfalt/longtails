import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace OracleTemplate.FractalChebyshev

open Real

noncomputable def bad (X β : ℝ) : ℝ := (1 + cos β) / (X - cos β)

lemma tan_le_four_div_pi_mul {x : ℝ} (hx : 0 < x) (hx' : x ≤ π / 4) :
    tan x ≤ 4 / π * x := by
  have hpi := Real.pi_pos
  let g : ℝ → ℝ := fun y => tan y / y
  have hcos : ∀ y ∈ Set.Ioo (0:ℝ) (π / 2), cos y ≠ 0 := fun y hy =>
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1], hy.2⟩).ne'
  have hderiv : ∀ y ∈ Set.Ioo (0:ℝ) (π / 2),
      HasDerivAt g ((1 / cos y ^ 2 * y - tan y * 1) / y ^ 2) y := by
    intro y hy
    exact (Real.hasDerivAt_tan (hcos y hy)).div (hasDerivAt_id y) hy.1.ne'
  have hmono : MonotoneOn g (Set.Ioo (0:ℝ) (π / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 (π / 2))
    · intro y hy; exact (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hderiv y hy).deriv]
      have hc : 0 < cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1], hy.2⟩
      have hs : sin y * cos y ≤ y := by
        have := Real.sin_le (by linarith [hy.1] : (0:ℝ) ≤ 2 * y)
        rw [Real.sin_two_mul] at this; linarith
      apply div_nonneg _ (sq_nonneg y)
      rw [Real.tan_eq_sin_div_cos]
      have : 1 / cos y ^ 2 * y - sin y / cos y * 1 = (y - sin y * cos y) / cos y ^ 2 := by
        field_simp
      rw [this]
      exact div_nonneg (by linarith) (sq_nonneg _)
  have hxI : x ∈ Set.Ioo (0:ℝ) (π / 2) := ⟨hx, by linarith⟩
  have h4 : π / 4 ∈ Set.Ioo (0:ℝ) (π / 2) := ⟨by linarith, by linarith⟩
  have := hmono hxI h4 hx'
  simp only [g, Real.tan_pi_div_four] at this
  rw [div_le_iff₀ hx] at this
  have e : 1 / (π / 4) * x = 4 / π * x := by field_simp
  linarith

lemma sin_ge_chord {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 4) :
    2 * Real.sqrt 2 / π * x ≤ sin x := by
  have hpi := Real.pi_pos
  have hc := strictConcaveOn_sin_Icc.concaveOn
  set t := 4 * x / π with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hpi]; linarith
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, hpi.le⟩
  have hmem1 : π / 4 ∈ Set.Icc 0 π := ⟨by linarith, by linarith⟩
  have := hc.2 hmem0 hmem1 (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at this
  have hx2 : t * (π / 4) = x := by rw [ht]; field_simp
  rw [hx2, Real.sin_pi_div_four] at this
  have e : 2 * Real.sqrt 2 / π * x = t * (Real.sqrt 2 / 2) := by rw [ht]; field_simp; ring
  linarith

lemma ineq_I {α n : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hn : 2 ≤ n) :
    cos α ≤ n ^ 2 * (sin ((π - α) / (2 * n)) ^ 2 - sin (α / (2 * n)) ^ 2) := by
  have hpi := Real.pi_pos
  have hnpos : 0 < n := by linarith
  set u := (π - α) / (2 * n)
  set w := α / (2 * n)
  have hdiff : sin u ^ 2 - sin w ^ 2 = sin (u + w) * sin (u - w) := by
    rw [Real.sin_add, Real.sin_sub]
    nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq w]
  have huw : u + w = π / (2 * n) := by simp only [u, w]; field_simp; ring
  have hum : u - w = (π - 2 * α) / (2 * n) := by simp only [u, w]; field_simp; ring
  rw [hdiff, huw, hum]
  have h1 : π / (2 * n) ≤ π / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : (π - 2 * α) / (2 * n) ≤ π / (2 * n) := by
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have hs1 := sin_ge_chord (by positivity : (0:ℝ) ≤ π / (2 * n)) h1
  have hs2 := sin_ge_chord (by apply div_nonneg <;> linarith : (0:ℝ) ≤ (π - 2 * α) / (2 * n))
    (h2.trans h1)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hprod : (2 * Real.sqrt 2 / π * (π / (2 * n))) *
      (2 * Real.sqrt 2 / π * ((π - 2 * α) / (2 * n)))
      = 2 * (π - 2 * α) / (π * n ^ 2) := by
    field_simp
    rw [hsq]
  have hp1 : 0 ≤ 2 * Real.sqrt 2 / π * (π / (2 * n)) := by positivity
  have hp2 : 0 ≤ 2 * Real.sqrt 2 / π * ((π - 2 * α) / (2 * n)) := by
    apply mul_nonneg (by positivity); apply div_nonneg <;> linarith
  have hmul := mul_le_mul hs1 hs2 hp2 (le_trans hp1 hs1)
  rw [hprod] at hmul
  have hcos : cos α ≤ π / 2 - α := by
    rw [← Real.sin_pi_div_two_sub]; exact Real.sin_le (by linarith)
  have hfin : π / 2 - α ≤ n ^ 2 * (2 * (π - 2 * α) / (π * n ^ 2)) := by
    rw [show n ^ 2 * (2 * (π - 2 * α) / (π * n ^ 2)) = 4 / π * (π / 2 - α) by
      field_simp; ring]
    have : 1 ≤ 4 / π := by rw [le_div_iff₀ hpi]; linarith [Real.pi_le_four]
    nlinarith
  have : n ^ 2 * (2 * (π - 2 * α) / (π * n ^ 2)) ≤
      n ^ 2 * (sin (π / (2 * n)) * sin ((π - 2 * α) / (2 * n))) :=
    mul_le_mul_of_nonneg_left hmul (sq_nonneg n)
  linarith

lemma ineq_II {α n : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hn : 2 ≤ n) :
    sin (α / (2 * n)) * cos (α / 2) * cos ((π - α) / (2 * n)) ≤
      sin (α / 2) * sin ((π - α) / (2 * n)) * cos (α / (2 * n)) := by
  have hpi := Real.pi_pos
  have hnpos : 0 < n := by linarith
  set u := (π - α) / (2 * n)
  set w := α / (2 * n)
  set A := α / 2
  set b := π / 4 - A
  have hb0 : 0 < b := by simp only [b, A]; linarith
  have hb1 : b < π / 4 := by simp only [b, A]; linarith
  have key : sin A * sin u * cos w - sin w * cos A * cos u =
      (sin (u + w) * (sin A - cos A) + sin (u - w) * (sin A + cos A)) / 2 := by
    rw [Real.sin_add, Real.sin_sub]; ring
  have huw : u + w = π / (2 * n) := by simp only [u, w]; field_simp; ring
  have hum : u - w = 2 * b / n := by simp only [u, w, b, A]; field_simp; ring
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsc : sin A - cos A = -(Real.sqrt 2 * sin b) := by
    simp only [b]; rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
    linear_combination ((cos A - sin A) / 2) * h2
  have hcs : sin A + cos A = Real.sqrt 2 * cos b := by
    simp only [b]; rw [Real.cos_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
    linear_combination (-(sin A + cos A) / 2) * h2
  have hcon := strictConcaveOn_sin_Icc.concaveOn
  set c := π / (2 * n) with hc
  have hc0 : 0 < c := by positivity
  have hcpi : c ≤ π := by
    rw [hc, div_le_iff₀ (by positivity)]; nlinarith
  set t := 4 * b / π with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hpi]; linarith
  have hch := hcon.2 (⟨le_rfl, hpi.le⟩ : (0:ℝ) ∈ Set.Icc 0 π) (⟨hc0.le, hcpi⟩ : c ∈ Set.Icc 0 π)
    (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at hch
  have htc : t * c = 2 * b / n := by rw [ht, hc]; field_simp; ring
  rw [htc] at hch
  have htan := tan_le_four_div_pi_mul hb0 hb1.le
  have hcb : 0 < cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan' : sin b ≤ t * cos b := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcb] at htan
    have : 4 / π * b * cos b = t * cos b := by rw [ht]; ring
    linarith
  have hsinc : 0 < sin c := Real.sin_pos_of_pos_of_lt_pi hc0 (by
    rw [hc, div_lt_iff₀ (by positivity)]; nlinarith)
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have hmain : sin c * sin b ≤ sin (2 * b / n) * cos b := by
    have h1 : sin c * sin b ≤ sin c * (t * cos b) := mul_le_mul_of_nonneg_left htan' hsinc.le
    have h2 : t * sin c * cos b ≤ sin (2 * b / n) * cos b :=
      mul_le_mul_of_nonneg_right hch hcb.le
    nlinarith
  have : 0 ≤ sin A * sin u * cos w - sin w * cos A * cos u := by
    rw [key, huw, hum, hsc, hcs]
    have : sin c * (-(Real.sqrt 2 * sin b)) + sin (2 * b / n) * (Real.sqrt 2 * cos b) =
        Real.sqrt 2 * (sin (2 * b / n) * cos b - sin c * sin b) := by ring
    rw [this]
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg hsq2.le (by linarith)
  linarith

end OracleTemplate.FractalChebyshev
