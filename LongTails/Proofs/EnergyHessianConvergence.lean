import LongTails.Proofs.EnergyHessianRun

namespace LongTails.Proofs.EnergyHessianConvergence

open LongTails.Setups.GradientDependentHessian LongTails.Algorithms.EnergyHessianReuse
open OracleTemplate OracleTemplate.QueryPlan EnergyHessianExecution

lemma plan_accuracy (p : Params) (f : p.E → ℝ)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (hG : ‖gradient f p.x0‖ ≤ p.G₀) :
    ‖gradient f (eval (replies p f) (plan p))‖ ≤ p.ε := by
  let a0 := LongTails.Algorithms.EnergyHessianReuse.initial p (gradient f p.x0)
  let a1 := eval (replies p f) (iteratePlans (fresh p) (burnCount p) a0)
  let a2 := eval (replies p f) (iteratePlans (block p) (blockCount p) a1)
  have hc0 : Correct p f a0 := correct_initial p f
  have hc1 : Correct p f a1 := (eval_iterate_correct f (fresh p)
    (fun a h => eval_fresh_correct p f a h) (burnCount p) a0 hc0).1
  have hc2 : Correct p f a2 := (eval_iterate_correct f (block p)
    (fun a h => eval_block_correct p f a h) (blockCount p) a1 hc1).1
  have hout : eval (replies p f) (plan p) = a2.best := by
    simp only [plan, eval, replies, ite_true, readGradient, eval_bind, eval_map]
    rfl
  rw [hout, hc2.best_eq]
  by_contra hbad
  have hbest : p.ε < a2.bestNorm := lt_of_not_ge hbad
  have hbest1 : p.ε < a1.bestNorm := hbest.trans_le
    (eval_iterate_correct f (block p) (fun a h => eval_block_correct p f a h) (blockCount p) a1 hc1).2
  have hvalid := hv
  obtain ⟨hL₀, hL₁, hΔ, hG₀, hε, hm⟩ := hv
  have hm' : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < p.m := by linarith
  have hA : 0 < (p.m : ℝ) * p.L₀ := mul_pos hmpos hL₀
  obtain ⟨Eb, hEb, hdb, hcb, _⟩ := EnergyHessianRun.burn_run p f hvalid hf hT
    (burnCount p) 0 a0 0 (coefficient p a0) le_rfl hc0 (by
      have hp : 0 ≤ 400 * (p.m : ℝ) * p.L₀ := by positivity
      simp only [pow_zero, one_mul, mul_zero, add_zero]
      linarith) hbest1
  have hdb' : f a1.x - f p.x0 ≤ -Eb / 3 := by
    change f a1.x - f p.x0 ≤ -(Eb - 0) / 3 at hdb
    simpa only [sub_zero] using hdb
  have hEbΔ : Eb ≤ 3 * p.Δ := by linarith [hgap a1.x]
  have hstart : coefficient p a1 ≤ 500 * p.m * p.L₀ + 60000 * p.L₁ * Real.sqrt p.L₁ * p.Δ := by
    have hini : coefficient p a0 ≤ 100 * (p.m * p.L₀ + p.L₁ * p.G₀) := by
      rw [EnergyHessianParameters.coefficient_initial p _ hL₀.le hL₁]
      have hh := mul_le_mul_of_nonneg_left hG hL₁
      nlinarith
    have hh := (mul_le_mul_of_nonneg_left hini (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (burnCount p))).trans
      (EnergyHessianParameters.burn_initial_bound p hL₀ hL₁ hG₀ hm)
    have he := mul_le_mul_of_nonneg_left hEbΔ
      (show 0 ≤ 20000 * p.L₁ * Real.sqrt p.L₁ by positivity)
    simp only [Nat.zero_add] at hcb
    nlinarith
  let q := Real.sqrt (p.m * p.L₀) / Real.sqrt p.ε
  let v := Real.sqrt p.L₁
  let R := Real.sqrt (p.m * p.L₁)
  let b := 1 / (100 * (q + v))
  have hq : 0 < q := div_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hε)
  have hvn : 0 ≤ v := Real.sqrt_nonneg _
  have hRn : 0 ≤ R := Real.sqrt_nonneg _
  have hq2 : q ^ 2 * p.ε = p.m * p.L₀ := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hε.le]
    exact div_mul_cancel₀ _ (ne_of_gt hε)
  obtain ⟨hb, hbq, hbv, hbinv⟩ := EnergyHessianParameters.interpolation_scale hq hvn hε hq2
  have hbv' : b ^ 2 * p.L₁ ≤ 1 / 10000 := by
    simpa only [v, Real.sq_sqrt hL₁] using hbv
  obtain ⟨S, C, E, hS, hC, hE, hd, hc, hs, hlower, _⟩ :=
    EnergyHessianRun.blocks_run p f hvalid hf hT hb (blockCount p) a1 hc1 hbest
  let T : ℝ := (blockCount p : ℝ) * (p.m + 1)
  have hEΔ : E ≤ 3 * p.Δ := by
    have hg := hgap a2.x
    change f a2.x - f a1.x ≤ -E / 3 at hd
    nlinarith
  have hc' : C ≤ b ^ 2 * (2 * coefficient p a1 + 200 * T * p.m * p.L₀ + 200 * p.L₁ * S) + E / b := by
    have hp := mul_nonneg (sq_nonneg b)
      (EnergyHessianParameters.coefficient_nonneg p a2 hL₀.le hL₁)
    change C ≤ 2 * b ^ 2 * (coefficient p a1 - coefficient p a2) +
      200 * b ^ 2 * T * p.m * p.L₀ + 200 * b ^ 2 * p.L₁ * S + E / b at hc
    nlinarith
  have hU : E / radius p ≤ (100 * v + p.ε / p.Δ) * E := by
    have hh := mul_le_mul_of_nonneg_right
      (EnergyHessianParameters.radius_inverse_bound p hΔ hε hL₁) hE
    simpa only [v, one_div, div_eq_mul_inv, mul_comm E, one_mul] using hh
  have hvR : v ≤ R := by
    apply Real.sqrt_le_sqrt
    have hh := mul_le_mul_of_nonneg_right hm' hL₁
    simpa using hh
  have hs' : S ≤ 4 * C + 4 * (C / 25 + 10 * R * E) + 4 * (E / radius p) := by
    convert hs using 1; ring
  have hbq' : b ^ 2 * (p.m : ℝ) * p.L₀ ≤ p.ε / 10000 := by
    simpa only [mul_assoc] using hbq
  have hglobal := GradientDependentEnergy.global_absorption hs' hc' (le_refl (C / 25 + 10 * R * E))
    hU hEΔ hstart (show 0 ≤ T by positivity) hS hC hΔ hε hb hvn hvR hbq' hbv' hbinv
  have hTcount : 27000 * p.Δ * q / p.ε + 15000 * p.Δ * R / p.ε + 72 ≤ T := by
    have hh := EnergyHessianParameters.block_horizon p
    have heq : 27000 * p.Δ * q / p.ε =
        27000 * p.Δ * Real.sqrt (p.m * p.L₀) / (p.ε * Real.sqrt p.ε) := by
      dsimp [q]
      ring
    rw [heq]
    exact hh
  have hstrict := GradientDependentEnergy.horizon_suffices hε hΔ.le hq.le hRn hglobal hTcount
  change T * p.ε ≤ S at hlower
  linarith

end LongTails.Proofs.EnergyHessianConvergence
