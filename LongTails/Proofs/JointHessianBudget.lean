import LongTails.Algorithms.JointHessianStationarity
import LongTails.Proofs.RelativeHessianTuning

namespace LongTails.Proofs.JointHessianBudget

open LongTails.Setups.PointwiseHessianStationarity
open LongTails.Algorithms.JointHessianStationarity

lemma relative_term {p : Params} (hp : broadSpec.valid p) :
    p.Δ * Real.sqrt p.L₁ / p.ε ≤ RelativeHessianTuning.scale p := by
  have hε := hp.2.2.2.2.2
  have hsε := Real.sqrt_pos.2 hε
  have hroot : Real.sqrt p.L₁ * Real.sqrt p.ε ≤ Real.sqrt (p.L₀ + p.L₁ * p.ε) := by
    rw [← Real.sqrt_mul hp.2.1]
    exact Real.sqrt_le_sqrt (by linarith [hp.1])
  unfold RelativeHessianTuning.scale
  apply (le_div_iff₀ (mul_pos hε hsε)).2
  have heq : p.Δ * Real.sqrt p.L₁ / p.ε * (p.ε * Real.sqrt p.ε) =
      p.Δ * (Real.sqrt p.L₁ * Real.sqrt p.ε) := by field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hroot hp.2.2.2.1.le

lemma sufficient {p : Params} (hp : broadSpec.valid p) :
    count p ≤ ⌈100000 * p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)⌉₊ +
      2 * ⌈Real.log (1 + p.L₁ * p.G / (p.L₀ + p.L₁ * p.ε)) / Real.log (4 / 3)⌉₊ + 200 := by
  let S := RelativeHessianTuning.scale p
  let V := p.Δ * Real.sqrt p.L₁ / p.ε
  have hS : 0 < S := RelativeHessianTuning.scale_pos hp
  have hV : V ≤ S := relative_term hp
  have hV0 : 0 ≤ V := div_nonneg (mul_nonneg hp.2.2.2.1.le (Real.sqrt_nonneg _)) hp.2.2.2.2.2.le
  have heq : LongTails.Algorithms.EnergyHessianReuse.blockCount (parameters p) =
      ⌈(27000 * S + 15000 * V + 72) / 2⌉₊ := by
    unfold LongTails.Algorithms.EnergyHessianReuse.blockCount parameters
    simp only [Nat.cast_one, one_mul]
    congr 1
    dsimp [S, V, RelativeHessianTuning.scale]
    ring
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (27000 * S + 15000 * V + 72) / 2 by positivity)
  have hceil := Nat.le_ceil (100000 * S)
  have hn : (4 * ⌈(27000 * S + 15000 * V + 72) / 2⌉₊ + 1 : ℕ) ≤ ⌈100000 * S⌉₊ + 200 := by
    have hr : ((4 * ⌈(27000 * S + 15000 * V + 72) / 2⌉₊ + 1 : ℕ) : ℝ) ≤
        (⌈100000 * S⌉₊ + 200 : ℕ) := by
      push_cast
      linarith
    exact_mod_cast hr
  have heqS : 100000 * p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε) = 100000 * S := by
    dsimp [S, RelativeHessianTuning.scale]
    ring
  unfold count
  rw [heq, heqS]
  simp only [LongTails.Algorithms.EnergyHessianReuse.burnCount, parameters, Nat.cast_one, one_mul]
  omega

end LongTails.Proofs.JointHessianBudget
