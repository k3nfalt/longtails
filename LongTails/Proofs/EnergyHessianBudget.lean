import LongTails.Proofs.EnergyHessianExecution

namespace LongTails.Proofs.EnergyHessianBudget

open LongTails.Setups.GradientDependentHessian LongTails.Algorithms.EnergyHessianReuse
open EnergyHessianExecution

lemma sqrt_weighted_identity {m L : ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L) :
    Real.sqrt (m * L) / m = Real.sqrt (L / m) := by
  rw [Real.sqrt_mul hm, Real.sqrt_div hL]
  rw [mul_comm (Real.sqrt m), mul_div_assoc, Real.sqrt_div_self']
  ring

lemma counts_sufficient (p : Params) (g : Fin 2 × p.E → Reply p) (hv : spec.valid p) (i : Fin 2) :
    counts g (plan p) i ≤ burnCount p +
      if i = 0 then
        ⌈27000 * p.Δ * Real.sqrt (p.m * p.L₀) / (p.ε * Real.sqrt p.ε) +
          15000 * p.Δ * Real.sqrt (p.m * p.L₁) / p.ε⌉₊ + p.m + 74
      else
        ⌈54000 * p.Δ * Real.sqrt (p.L₀ / p.m) / (p.ε * Real.sqrt p.ε) +
          30000 * p.Δ * Real.sqrt (p.L₁ / p.m) / p.ε⌉₊ + 146 := by
  let R := 27000 * p.Δ * Real.sqrt (p.m * p.L₀) / (p.ε * Real.sqrt p.ε) +
    15000 * p.Δ * Real.sqrt (p.m * p.L₁) / p.ε
  let H := 54000 * p.Δ * Real.sqrt (p.L₀ / p.m) / (p.ε * Real.sqrt p.ε) +
    30000 * p.Δ * Real.sqrt (p.L₁ / p.m) / p.ε
  obtain ⟨hL₀, hL₁, hΔ, _, hε, hm⟩ := hv
  have hm' : (0 : ℝ) < p.m := by exact_mod_cast (show 0 < p.m by omega)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hidentity : 2 * R / p.m = H := by
    have hs0 := sqrt_weighted_identity hm'.le hL₀.le
    have hs1 := sqrt_weighted_identity hm'.le hL₁
    calc
      _ = 54000 * p.Δ * (Real.sqrt (p.m * p.L₀) / p.m) / (p.ε * Real.sqrt p.ε) +
          30000 * p.Δ * (Real.sqrt (p.m * p.L₁) / p.m) / p.ε := by
        dsimp [R]
        ring
      _ = H := by rw [hs0, hs1]
  obtain ⟨hg, hh⟩ := EnergyHessianParameters.rounded_block_costs hR hm
  have hg' : blockCount p * (p.m + 1) ≤ ⌈R⌉₊ + p.m + 73 := by
    simpa only [blockCount, R, Nat.cast_add, Nat.cast_one] using hg
  have hh' : 2 * blockCount p ≤ ⌈H⌉₊ + 146 := by
    simpa only [blockCount, R, Nat.cast_add, Nat.cast_one, hidentity] using hh
  rw [counts_plan]
  change (if i = 0 then burnCount p + blockCount p * (p.m + 1) + 1 else burnCount p + 2 * blockCount p) ≤
    burnCount p + if i = 0 then ⌈R⌉₊ + p.m + 74 else ⌈H⌉₊ + 146
  split_ifs <;> omega

end LongTails.Proofs.EnergyHessianBudget
