import LongTails.Proofs.CompositeAdaptiveGeometry
import LongTails.Algorithms.RadiusCompositeAccelerated

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeAdaptive

open OracleTemplate.CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma initial_prox_radius {f ψ : E → ℝ} {g : E → E} {Q : Set E}
    {L0 L1 R : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Continuous g) (hs : SymmetricSmooth g L0 L1)
    (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) {x0 xs u : E}
    (hxs : xs ∈ Q) (hmin : IsMinOn (fun x => f x + ψ x) Q xs)
    (hradius : ‖x0 - xs‖ ≤ R) (hu : u ∈ Q)
    (hprox : IsMinOn (fun w =>
      ‖w - x0‖ ^ 2 / (2 * (1 / ((L0 + L1 * ‖g x0‖) * Real.exp (L1 * R) + L0))) +
      ⟪g x0, w - x0⟫ + ψ w) Q u) :
    ‖u - xs‖ ≤ 2 * R := by
  let S := L0 + L1 * ‖g x0‖
  have hS : 0 < S := by dsimp [S]; positivity
  have hden : 0 < S * Real.exp (L1 * R) + L0 := by positivity
  have hgrad : ‖g x0 - g xs‖ ≤ S * Real.exp (L1 * R) * R := by
    have hh := symmetric_gradient_difference_nonneg hg hL0.le hL1 hs xs x0
    rw [norm_sub_rev (g xs) (g x0), norm_sub_rev xs x0] at hh
    calc
      _ ≤ S * Real.exp (L1 * ‖x0 - xs‖) * ‖x0 - xs‖ := hh
      _ ≤ S * Real.exp (L1 * R) * R := by gcongr
  have hb := prox_distance_sharp hQ hψ (one_div_pos.mpr hden) hu hxs hprox
    (optimality hc hf hg hQ hψ hxs hmin hu)
  have hscl := mul_le_mul_of_nonneg_left hgrad (one_div_nonneg.mpr hden.le)
  have hstep : 1 / (S * Real.exp (L1 * R) + L0) *
      (S * Real.exp (L1 * R) * R) ≤ R := by
    rw [one_div_mul_eq_div, div_le_iff₀ hden]
    nlinarith
  linarith

omit [CompleteSpace E] in
lemma initial_prox_gap {f ψ : E → ℝ} {Q : Set E} {a M R r D : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hR : 0 ≤ R) (hr : 0 ≤ r) (hD : 0 ≤ D)
    {x0 xs u g0 gs : E} (hxs : xs ∈ Q)
    (hprox : IsMinOn (fun w => ‖w - x0‖ ^ 2 / (2 * a) + ⟪g0, w - x0⟫ + ψ w) Q u)
    (hx0 : ‖x0 - xs‖ ≤ R) (hu : ‖u - xs‖ ≤ r) (hg : ‖gs - g0‖ ≤ D)
    (hupper : f u ≤ f xs + ⟪gs, u - xs⟫ + M / 2 * ‖u - xs‖ ^ 2) :
    f u + ψ u - (f xs + ψ xs) ≤ R ^ 2 / (2 * a) + D * r + M / 2 * r ^ 2 := by
  have hp := hprox hxs
  have hid : ⟪g0, u - x0⟫ - ⟪g0, xs - x0⟫ = ⟪g0, u - xs⟫ := by
    simp only [inner_sub_right]
    ring
  have hn : 0 ≤ ‖u - x0‖ ^ 2 / (2 * a) := by positivity
  have hr2 : ‖xs - x0‖ ^ 2 ≤ R ^ 2 := by
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (x0 - xs)]
  have hrd := div_le_div_of_nonneg_right hr2 (by positivity : 0 ≤ 2 * a)
  have hi := real_inner_le_norm (gs - g0) (u - xs)
  rw [inner_sub_left] at hi
  have hm := mul_le_mul hg hu (norm_nonneg _) hD
  have hu2 : ‖u - xs‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (u - xs)]
  have hmu := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ M / 2)
  change ‖u - x0‖ ^ 2 / (2 * a) + ⟪g0, u - x0⟫ + ψ u ≤
    ‖xs - x0‖ ^ 2 / (2 * a) + ⟪g0, xs - x0⟫ + ψ xs at hp
  linarith

lemma initial_gap_certificate {f ψ : E → ℝ} {g : E → E} {Q : Set E}
    {L0 L1 R : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 ≤ R)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) {x0 xs u : E} (hxs : xs ∈ Q)
    (hradius : ‖x0 - xs‖ ≤ R) (hu : ‖u - xs‖ ≤ 2 * R)
    (hprox : IsMinOn (fun w =>
      ‖w - x0‖ ^ 2 / (2 * (1 / ((L0 + L1 * ‖g x0‖) * Real.exp (L1 * R) + L0))) +
      ⟪g x0, w - x0⟫ + ψ w) Q u) :
    f u + ψ u - (f xs + ψ xs) ≤
      5 * (L0 + L1 * ‖g x0‖) * R ^ 2 * Real.exp (3 * L1 * R) := by
  let S := L0 + L1 * ‖g x0‖
  let k := L1 * R
  have hS : 0 < S := by dsimp [S]; positivity
  have hk : 0 ≤ k := mul_nonneg hL1 hR
  have hden : 0 < S * Real.exp k + L0 := by positivity
  have hgrad : ‖g xs - g x0‖ ≤ S * Real.exp k * R := by
    have hh := symmetric_gradient_difference_nonneg hg hL0.le hL1 hs xs x0
    rw [norm_sub_rev xs x0] at hh
    exact hh.trans (by dsimp [k]; gcongr)
  have hcurve : L0 + L1 * ‖g xs‖ ≤ S * Real.exp k := by
    have hh := symmetric_gradient_growth_nonneg hg hL1 hs xs x0
    rw [norm_sub_rev xs x0] at hh
    exact hh.trans (by dsimp [k]; gcongr)
  have hM : (L0 + L1 * ‖g xs‖) * Real.exp (L1 * ‖u - xs‖) ≤
      S * Real.exp (3 * k) := by
    calc
      _ ≤ (S * Real.exp k) * Real.exp (2 * k) :=
        mul_le_mul hcurve (Real.exp_le_exp.mpr (by dsimp [k]; nlinarith))
          (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hupper := symmetric_objective_upper hf hg hL0.le hL1 hs u xs
  have hm := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hM (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖u - xs‖)
  have hb := initial_prox_gap (one_div_pos.mpr hden)
    (by positivity : 0 ≤ S * Real.exp (3 * k)) hR (by positivity : 0 ≤ 2 * R)
    (by positivity : 0 ≤ S * Real.exp k * R) hxs hprox hradius hu hgrad
    (by linarith : f u ≤ f xs + ⟪g xs, u - xs⟫ +
      (S * Real.exp (3 * k)) / 2 * ‖u - xs‖ ^ 2)
  have hfrac : R ^ 2 / (2 * (1 / (S * Real.exp k + L0))) =
      R ^ 2 * (S * Real.exp k + L0) / 2 := by field_simp
  rw [hfrac] at hb
  have he : Real.exp k ≤ Real.exp (3 * k) := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1 ≤ Real.exp (3 * k) := Real.one_le_exp (by positivity)
  have hLS : L0 ≤ S := by dsimp [S]; nlinarith [mul_nonneg hL1 (norm_nonneg (g x0))]
  have hLSexp : L0 ≤ S * Real.exp (3 * k) := by nlinarith
  have hSE := mul_le_mul_of_nonneg_left he hS.le
  have hSEr := mul_le_mul_of_nonneg_right hSE (sq_nonneg R)
  have hLSr := mul_le_mul_of_nonneg_right hLSexp (sq_nonneg R)
  have hresult : f u + ψ u - (f xs + ψ xs) ≤ 5 * S * R ^ 2 * Real.exp (3 * k) := by
    nlinarith
  simpa only [S, k, mul_assoc] using hresult

lemma initial_energy_certificate {S κ R gap d : ℝ} (hS : 0 < S) (hκ : 0 ≤ κ)
    (hR : 0 ≤ R) (hd : 0 ≤ d) (hradius : d ≤ 2 * R)
    (hgap : gap ≤ 5 * S * R ^ 2 * Real.exp (3 * κ)) :
    1 / (8 * S * Real.exp (4 * κ)) * gap + d ^ 2 / 2 ≤ 3 * R ^ 2 := by
  have hden : 0 < 8 * S * Real.exp (4 * κ) := by positivity
  have he : Real.exp (3 * κ) ≤ Real.exp (4 * κ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 5 * S * R ^ 2)
  have hb : gap ≤ R ^ 2 * (8 * S * Real.exp (4 * κ)) := by
    nlinarith [mul_nonneg (sq_nonneg R) (Real.exp_pos (4 * κ)).le]
  have hdiv : 1 / (8 * S * Real.exp (4 * κ)) * gap ≤ R ^ 2 := by
    rw [one_div_mul_eq_div, div_le_iff₀ hden]
    exact hb
  nlinarith

lemma initial_trial_scales {S κ R L1 Su H : ℝ} (hS : 0 < S) (hκ : 0 ≤ κ)
    (hL1 : 0 ≤ L1) (hκdef : κ = L1 * R)
    (hSu : Su ≤ S * Real.exp (3 * κ)) (hH : H ≤ 9 * S * R * Real.exp (3 * κ)) :
    (1 / (8 * S * Real.exp (4 * κ))) * Su ≤ 1 ∧
      (1 / (8 * S * Real.exp (4 * κ))) * L1 * H ≤ 2 := by
  have hden : 0 < 8 * S * Real.exp (4 * κ) := by positivity
  have he : Real.exp (3 * κ) ≤ Real.exp (4 * κ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hSE := mul_le_mul_of_nonneg_left he hS.le
  have hkexp : κ ≤ Real.exp κ := by linarith [Real.add_one_le_exp κ]
  have hmul := mul_le_mul_of_nonneg_left hkexp
    (by positivity : 0 ≤ 9 * S * Real.exp (3 * κ))
  have hexp : Real.exp (3 * κ) * Real.exp κ = Real.exp (4 * κ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhexp : 9 * S * Real.exp (3 * κ) * Real.exp κ = 9 * S * Real.exp (4 * κ) := by
    rw [mul_assoc (9 * S), hexp]
  rw [hhexp] at hmul
  have hLH := mul_le_mul_of_nonneg_left hH hL1
  constructor
  · rw [one_div_mul_eq_div, div_le_iff₀ hden]
    nlinarith [Real.exp_pos (4 * κ)]
  · have heq : (1 / (8 * S * Real.exp (4 * κ))) * L1 * H =
        (L1 * H) / (8 * S * Real.exp (4 * κ)) := by ring
    rw [heq, div_le_iff₀ hden]
    have hfactor : 9 * S * Real.exp (3 * κ) * κ = L1 * (9 * S * R * Real.exp (3 * κ)) := by
      rw [hκdef]
      ring
    rw [hfactor] at hmul
    nlinarith [Real.exp_pos (4 * κ)]

omit [CompleteSpace E] in
lemma initial_gradient_data {g : E → E} {L0 L1 R : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 ≤ R) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) {x0 u : E} (hd : ‖u - x0‖ ≤ 3 * R) :
    L0 + L1 * ‖g u‖ ≤ (L0 + L1 * ‖g x0‖) * Real.exp (3 * (L1 * R)) ∧
      ‖g u - g x0‖ + ‖u - x0‖ /
        (1 / ((L0 + L1 * ‖g x0‖) * Real.exp (L1 * R) + L0)) ≤
      9 * (L0 + L1 * ‖g x0‖) * R * Real.exp (3 * (L1 * R)) := by
  let S := L0 + L1 * ‖g x0‖
  let k := L1 * R
  have hS : 0 < S := by dsimp [S]; positivity
  have hk : 0 ≤ k := mul_nonneg hL1 hR
  have hden : 0 < S * Real.exp k + L0 := by positivity
  have he : Real.exp (L1 * ‖u - x0‖) ≤ Real.exp (3 * k) := by
    apply Real.exp_le_exp.mpr
    dsimp [k]
    nlinarith [mul_le_mul_of_nonneg_left hd hL1]
  have hcurv := symmetric_gradient_growth_nonneg hg hL1 hs u x0
  have hdiff := symmetric_gradient_difference_nonneg hg hL0.le hL1 hs u x0
  have hdiff' : ‖g u - g x0‖ ≤ S * Real.exp (3 * k) * (3 * R) :=
    hdiff.trans (by gcongr)
  have he3 : 1 ≤ Real.exp (3 * k) := Real.one_le_exp (by positivity)
  have he13 : Real.exp k ≤ Real.exp (3 * k) := Real.exp_le_exp.mpr (by linarith)
  have hL : L0 ≤ S := by dsimp [S]; nlinarith [mul_nonneg hL1 (norm_nonneg (g x0))]
  have hLS : L0 ≤ S * Real.exp (3 * k) := by nlinarith
  have hSE := mul_le_mul_of_nonneg_left he13 hS.le
  have hsum : S * Real.exp k + L0 ≤ 2 * (S * Real.exp (3 * k)) := by linarith
  have hterm := mul_le_mul hd hsum hden.le (by positivity : 0 ≤ 3 * R)
  constructor
  · exact hcurv.trans (mul_le_mul_of_nonneg_left he hS.le)
  · have hid : ‖u - x0‖ / (1 / (S * Real.exp k + L0)) =
        ‖u - x0‖ * (S * Real.exp k + L0) := by simp only [div_eq_mul_inv, one_mul, inv_inv]
    change ‖g u - g x0‖ + ‖u - x0‖ / (1 / (S * Real.exp k + L0)) ≤
      9 * S * R * Real.exp (3 * k)
    rw [hid]
    nlinarith

end OracleTemplate.CompositeAdaptive
