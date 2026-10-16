import LongTails.Proofs.EnergyHessianStep

namespace LongTails.Proofs.EnergyHessianBlock

open LongTails.Setups.GradientDependentHessian LongTails.Algorithms.EnergyHessianReuse
open scoped RealInnerProductSpace

structure Previous where
  δ : ℝ
  r : ℝ
  μ : ℝ

def Previous.energy (v : Previous) (σ : ℝ) : ℝ := σ * v.r ^ 3 + v.δ * v.r ^ 2 + v.μ * v.r ^ 2

def damping (p : Params) (energy path : ℝ) : ℝ := 4 * p.L₀ * path + 100 * p.L₁ * energy

structure Invariant (p : Params) (f : p.E → ℝ) (B : p.E →L[ℝ] p.E)
    (a : Point p) (energy path : ℝ) (v : Previous) : Prop where
  gradient_eq : a.g = gradient f a.x
  energy_nonneg : 0 ≤ energy
  path_nonneg : 0 ≤ path
  sigma_nonneg : 0 ≤ a.σ
  delta_nonneg : 0 ≤ v.δ
  radius_nonneg : 0 ≤ v.r
  multiplier_nonneg : 0 ≤ v.μ
  cap : v.μ * (v.r - radius p) = 0
  damping_le : v.δ ≤ damping p energy path
  gradient_bound : ‖a.g‖ ≤ 4 * (a.σ * v.r ^ 2 + v.δ * v.r + v.μ * v.r)
  transport : ‖fderiv ℝ (gradient f) a.x - B‖ ≤
    2 * p.L₀ * path + 36 * p.L₁ * energy - 18 * p.L₁ * v.energy a.σ

lemma reused_step (p : Params) (f : p.E → ℝ) (B : p.E →L[ℝ] p.E)
    (a : Point p) (energy path : ℝ) (v : Previous)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hI : Invariant p f B a energy path v) (hgn : a.g ≠ 0) :
    let δ := damping p energy path
    let σ := coefficient p a
    let z := selectedStep p a.g B δ σ
    let e := stepEnergy σ δ z
    let next := move p a z.1 (gradient f (a.x + z.1))
    Invariant p f B next (energy + e) (path + ‖z.1‖) ⟨δ, ‖z.1‖, z.2⟩ ∧
      f next.x - f a.x ≤ -e / 3 := by
  dsimp only
  let δ := damping p energy path
  let σ := coefficient p a
  let z := selectedStep p a.g B δ σ
  let e := stepEnergy σ δ z
  let next := move p a z.1 (gradient f (a.x + z.1))
  change Invariant p f B next (energy + e) (path + ‖z.1‖) ⟨δ, ‖z.1‖, z.2⟩ ∧ _
  have hL₀ := hv.1
  have hL₁ := hv.2.1
  have hδ : 0 ≤ δ := by
    have hp := hI.path_nonneg
    have he := hI.energy_nonneg
    dsimp [δ, damping]
    positivity
  have hprev : 0 ≤ v.energy a.σ := by
    dsimp [Previous.energy]
    exact add_nonneg (add_nonneg (mul_nonneg hI.sigma_nonneg (pow_nonneg hI.radius_nonneg 3))
      (mul_nonneg hI.delta_nonneg (sq_nonneg v.r)))
      (mul_nonneg hI.multiplier_nonneg (sq_nonneg v.r))
  have herr : ‖fderiv ℝ (gradient f) a.x - B‖ ≤ δ / 2 := by
    have hh := hI.transport
    have hp := mul_nonneg hL₁ hprev
    have he := mul_nonneg hL₁ hI.energy_nonneg
    dsimp [δ, damping]
    nlinarith
  obtain ⟨hr, hμ, hstat, hcap, hpsd⟩ := EnergyHessianParameters.step_certificate p a.g B δ σ
    hv.2.2.1 hv.2.2.2.2.1 hL₁ hgn hB
  have hσ : 0 ≤ σ := by
    have hh := EnergyHessianParameters.coefficient_lower p a
    have hm : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
    have hg := norm_nonneg a.g
    dsimp [σ]
    nlinarith
  have he : 0 ≤ e := by dsimp [e, stepEnergy]; positivity
  obtain ⟨hgrad, hdescent⟩ := EnergyHessianStep.model_step p f a B δ hv hf hT
    hI.gradient_eq hgn hδ hB herr
  have hin := GradientDependentEnergy.incoming_gradient_charge hI.sigma_nonneg hσ
    hI.delta_nonneg hδ hI.multiplier_nonneg hI.radius_nonneg (norm_nonneg z.1)
    (EnergyHessianParameters.coefficient_previous p a) hI.damping_le hr hI.cap hI.gradient_bound
  have hin' : ‖a.g‖ * ‖z.1‖ ≤ 9 * v.energy a.σ + 5 * e := by
    have hp : 0 ≤ z.2 * ‖z.1‖ ^ 2 := by positivity
    dsimp [Previous.energy, e, stepEnergy]
    nlinarith
  have hout : ‖gradient f (a.x + z.1)‖ * ‖z.1‖ ≤ 4 * e := by
    have hh := mul_le_mul_of_nonneg_right hgrad (norm_nonneg z.1)
    dsimp [e, stepEnergy]
    nlinarith
  obtain ⟨hf', hg', hH'⟩ := GradientDependentLocal.derivative_chain hf
  have hcap' : p.L₁ * ‖z.1‖ ^ 2 ≤ 4 := by
    have hh := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z.1) hr 2) hL₁).trans
      (EnergyHessianParameters.radius_cap p hL₁)
    linarith
  obtain ⟨hchange, _, _⟩ := GradientDependentLocal.local_models hf' hg' hH' hL₀.le hL₁ hT a.x z.1 hcap'
  have htransport := EnergyHessianStep.transport_update
    (gin := ‖gradient f a.x‖) (gout := ‖gradient f (a.x + z.1)‖) hL₁ hI.transport (by convert hchange using 1; ring)
    (by simpa only [hI.gradient_eq] using hin') hout
  refine ⟨?_, hdescent⟩
  constructor
  · rfl
  · exact add_nonneg hI.energy_nonneg he
  · exact add_nonneg hI.path_nonneg (norm_nonneg _)
  · exact hσ
  · exact hδ
  · exact norm_nonneg _
  · exact hμ
  · exact hcap
  · dsimp [damping, δ]
    have hp := mul_nonneg hL₀.le (norm_nonneg z.1)
    have hpe := mul_nonneg hL₁ he
    nlinarith
  · exact hgrad
  · exact htransport

lemma prep_invariant (p : Params) (f : p.E → ℝ) (a : Point p)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hg : a.g = gradient f a.x) (hgn : a.g ≠ 0) :
    let σ := coefficient p a
    let z := selectedStep p a.g (fderiv ℝ (gradient f) a.x) 0 σ
    let e := stepEnergy σ 0 z
    let next := move p a z.1 (gradient f (a.x + z.1))
    Invariant p f (fderiv ℝ (gradient f) next.x) next e 0 ⟨0, ‖z.1‖, z.2⟩ ∧
      f next.x - f a.x ≤ -e / 3 := by
  let σ := coefficient p a
  let B := fderiv ℝ (gradient f) a.x
  let z := selectedStep p a.g B 0 σ
  let e := stepEnergy σ 0 z
  let next := move p a z.1 (gradient f (a.x + z.1))
  change Invariant p f (fderiv ℝ (gradient f) next.x) next e 0 ⟨0, ‖z.1‖, z.2⟩ ∧ _
  have hL₀ := hv.1
  have hL₁ := hv.2.1
  have hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫ := by
    intro x y
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num)) a.x x y).symm
  obtain ⟨hr, hμ, _, hcap, _⟩ := EnergyHessianParameters.step_certificate p a.g B 0 σ
    hv.2.2.1 hv.2.2.2.2.1 hL₁ hgn hB
  have hσ : 0 ≤ σ := by
    have hh := EnergyHessianParameters.coefficient_lower p a
    have hm : (0 : ℝ) ≤ p.m := Nat.cast_nonneg _
    have hn := norm_nonneg a.g
    dsimp [σ]
    nlinarith
  have he : 0 ≤ e := by dsimp [e, stepEnergy]; positivity
  obtain ⟨hgrad, hdescent⟩ := EnergyHessianStep.model_step p f a B 0 hv hf hT hg hgn
    le_rfl hB (by simp [B])
  refine ⟨?_, hdescent⟩
  constructor
  · rfl
  · exact he
  · rfl
  · exact hσ
  · rfl
  · exact norm_nonneg _
  · exact hμ
  · exact hcap
  · dsimp [damping]
    positivity
  · exact hgrad
  · change ‖fderiv ℝ (gradient f) next.x - fderiv ℝ (gradient f) next.x‖ ≤ _
    simp only [sub_self, norm_zero, mul_zero, zero_add]
    change 0 ≤ 36 * p.L₁ * e - 18 * p.L₁ * e
    have hh := mul_nonneg hL₁ he
    nlinarith

end LongTails.Proofs.EnergyHessianBlock
