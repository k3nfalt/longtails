import LongTails.Setups.RidgeClockTwoTapLogistic
import LongTails.Proofs.RidgeClockTwoTapConvergence

open OracleTemplate
open LongTails.Setups.RidgeClockTwoTapLogistic
open LongTails.Algorithms.FirstFitGradientDescent

namespace LongTails.Theorems.RidgeClockTwoTapLogistic

noncomputable def budget : (let S := LongTails.Setups.RidgeClockTwoTapLogistic.spec
    S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let I := ∑ i : Fin p.bins, p.width i / (p.c i * p.W i)
  1 + p.burn + p.block * ⌈I/(2*p.η*p.block)⌉₊

theorem result : Convergence LongTails.Setups.RidgeClockTwoTapLogistic.spec budget := by
  classical
  refine ⟨fun (u : Input) => algorithm (E := LongTails.Setups.TwoSampleQuadraticPerceptron.Space .conv u.d) u.x₀ u.η, ?_, ?_⟩
  · intro (p : Params) hp X o ho
    obtain ⟨k,hk,hfit⟩ := LongTails.Proofs.RidgeClockTwoTapConvergence.reaches_fit X hp ho.1
    dsimp only
    intro ω
    have hK : k ≤ budget p (⟨0, Nat.zero_lt_one⟩ : Fin 1) := by
      change k ≤ 1 + p.burn + p.block * ⌈(∑ i : Fin p.bins, p.width i / (p.c i * p.W i))/(2*p.η*p.block)⌉₊
      rw [LongTails.Proofs.RidgeClockTwoTapConvergence.epochs_formula p] at hk
      omega
    have hs := LongTails.Proofs.FirstFitGradientExecution.execute_first_fit (descent X) (fit X)
      o ho.2 p.input.η p.input.x₀ hK hfit ω.2
    exact of_decide_eq_true hs
  · intro p _
    exact ⟨id,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

end LongTails.Theorems.RidgeClockTwoTapLogistic
