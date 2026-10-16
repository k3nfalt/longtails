import LongTails.Proofs.EnergyHessianParameters
import LongTails.Proofs.GradientDependentLocal

namespace LongTails.Proofs.EnergyHessianStep

open LongTails.Setups.GradientDependentHessian LongTails.Algorithms.EnergyHessianReuse
open scoped RealInnerProductSpace

lemma model_step (p : Params) (f : p.E → ℝ) (a : Point p) (B : p.E →L[ℝ] p.E) (δ : ℝ)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hg : a.g = gradient f a.x) (hgn : a.g ≠ 0) (hδ : 0 ≤ δ)
    (hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (herr : ‖fderiv ℝ (gradient f) a.x - B‖ ≤ δ / 2) :
    let σ := coefficient p a
    let z := selectedStep p a.g B δ σ
    ‖gradient f (a.x + z.1)‖ ≤ 4 * (σ * ‖z.1‖ ^ 2 + δ * ‖z.1‖ + z.2 * ‖z.1‖) ∧
    f (a.x + z.1) - f a.x ≤ -stepEnergy σ δ z / 3 := by
  obtain ⟨hL₀, hL₁, hΔ, _, hε, hm⟩ := hv
  obtain ⟨hf', hg', hH'⟩ := GradientDependentLocal.derivative_chain hf
  obtain ⟨hr, hμ, hstat, _, hpsd⟩ := EnergyHessianParameters.step_certificate p a.g B δ
    (coefficient p a) hΔ hε hL₁ hgn hB
  have hm' : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hbase : p.L₀ ≤ p.m * p.L₀ := by nlinarith
  have hlower := EnergyHessianParameters.coefficient_lower p a
  have hσ : 0 ≤ coefficient p a := by
    have hn := norm_nonneg a.g
    nlinarith
  have htune : 100 * (p.L₀ + p.L₁ * ‖gradient f a.x‖) ≤ coefficient p a := by
    rw [← hg]
    linarith
  have hcap : p.L₁ * ‖(selectedStep p a.g B δ (coefficient p a)).1‖ ^ 2 ≤ 1 / 10000 := by
    apply le_trans _ (EnergyHessianParameters.radius_cap p hL₁)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hr 2) hL₁
  have hh := GradientDependentLocal.step_estimates hf' hg' hH' hL₀.le hL₁ hT a.x
    (selectedStep p a.g B δ (coefficient p a)).1 B hδ hσ hμ hcap htune herr
    (by simpa only [hg] using hstat) (hpsd _)
  exact hh

lemma transport_update {V : Type*} [NormedAddCommGroup V]
    {H Hnext B : V} {L₀ L₁ path energy previous e r gin gout : ℝ}
    (hL : 0 ≤ L₁)
    (herror : ‖H - B‖ ≤ 2 * L₀ * path + 36 * L₁ * energy - 18 * L₁ * previous)
    (hchange : ‖Hnext - H‖ ≤ 2 * L₀ * r + 2 * L₁ * (gin + gout) * r)
    (hin : gin * r ≤ 9 * previous + 5 * e)
    (hout : gout * r ≤ 4 * e) :
    ‖Hnext - B‖ ≤ 2 * L₀ * (path + r) + 36 * L₁ * (energy + e) - 18 * L₁ * e := by
  have hh := norm_add_le (Hnext - H) (H - B)
  have hid : Hnext - H + (H - B) = Hnext - B := by abel
  rw [hid] at hh
  have hc := mul_le_mul_of_nonneg_left (add_le_add hin hout) (show 0 ≤ 2 * L₁ by positivity)
  nlinarith

lemma fresh_step (p : Params) (f : p.E → ℝ) (a : Point p)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hg : a.g = gradient f a.x) (hgn : a.g ≠ 0) :
    let σ := coefficient p a
    let z := selectedStep p a.g (fderiv ℝ (gradient f) a.x) 0 σ
    let e := stepEnergy σ 0 z
    let next := move p a z.1 (gradient f (a.x + z.1))
    f next.x - f a.x ≤ -e / 3 ∧
      coefficient p next ≤ (3 / 4) * σ + 100 * p.m * p.L₀ +
        20000 * p.L₁ * Real.sqrt p.L₁ * e := by
  let σ := coefficient p a
  let B := fderiv ℝ (gradient f) a.x
  let z := selectedStep p a.g B 0 σ
  let e := stepEnergy σ 0 z
  let next := move p a z.1 (gradient f (a.x + z.1))
  change f next.x - f a.x ≤ -e / 3 ∧ _
  have hL₀ := hv.1
  have hL₁ := hv.2.1
  have hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫ := by
    intro x y
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num)) a.x x y).symm
  obtain ⟨hr, hμ, hstat, hcap, _⟩ := EnergyHessianParameters.step_certificate p a.g B 0 σ
    hv.2.2.1 hv.2.2.2.2.1 hL₁ hgn hB
  have hσ := EnergyHessianParameters.coefficient_nonneg p a hL₀.le hL₁
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast hv.2.2.2.2.2
  have hbase : p.L₀ ≤ p.m * p.L₀ := by nlinarith
  have htune : 100 * (p.L₀ + p.L₁ * ‖gradient f a.x‖) ≤ σ := by
    have hh := EnergyHessianParameters.coefficient_lower p a
    rw [← hg]
    dsimp [σ]
    linarith
  have hcap' : p.L₁ * ‖z.1‖ ^ 2 ≤ 1 / 10000 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z.1) hr 2) hL₁).trans
      (EnergyHessianParameters.radius_cap p hL₁)
  obtain ⟨hf', hg', hH'⟩ := GradientDependentLocal.derivative_chain hf
  have hgrad := GradientDependentLocal.fresh_estimate hf' hg' hH' hL₀.le hL₁ hT a.x z.1 hσ hμ
    hcap' htune (by simpa only [mul_zero, zero_mul, zero_add, ← hg] using hstat)
  have hd := (model_step p f a B 0 hv hf hT hg hgn le_rfl hB (by simp [B])).2
  refine ⟨hd, ?_⟩
  have hc := GradientDependentEnergy.fresh_coefficient_recurrence hσ (norm_nonneg z.1) hL₁
    (Real.sqrt_nonneg p.L₁) (Real.sq_sqrt hL₁) hgrad
    (EnergyHessianParameters.cap_multiplier_charge p hL₁ hcap).le
    (EnergyHessianParameters.coefficient_transition p a z.1 (gradient f (a.x + z.1)) hL₀.le hL₁)
  simpa only [e, stepEnergy, zero_mul, add_zero] using hc

end LongTails.Proofs.EnergyHessianStep
