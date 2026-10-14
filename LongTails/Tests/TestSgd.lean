import LongTails.Proofs.SgdExecution

namespace OracleTemplate.StochasticGradient.Tests

noncomputable def sampledOracle : Oracle ℝ ℝ where
  Seed := fun _ => ℝ
  law := ⟨MeasureTheory.Measure.infinitePi (fun _ : ℕ => MeasureTheory.Measure.dirac (1 : ℝ)),
    inferInstance⟩
  answer := fun _ (_, x) seed => x + seed

theorem zero_steps_return_initial_point :
    execute sampledOracle (sgd (1 : ℝ) 3) (fun _ => 0) () (fun _ => (0 : ℝ)) = 3 := by
  rfl

theorem two_steps_average_preupdate_iterates :
    execute sampledOracle (sgd (1 : ℝ) 3) (fun _ => 2) () (fun _ => (1 : ℝ)) = 1 := by
  have h := execute_sgd (E := ℝ) ⟨MeasureTheory.Measure.dirac (1 : ℝ), inferInstance⟩
      (fun x seed => x + seed) 1 3 2 (by decide) (fun _ => 1)
  norm_num [run] at h
  exact h

end OracleTemplate.StochasticGradient.Tests
