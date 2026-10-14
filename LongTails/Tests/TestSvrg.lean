import LongTails.Proofs.SvrgExecution

namespace OracleTemplate.FiniteSum.Tests

noncomputable def quadraticOracle : Oracle (Fin 2 × ℝ) ℝ where
  answer := fun _ (_, query) _ => if query.1 = 0 then query.2 else 2 * query.2

def zeroSeed : EpochSeeds 2 2 2 := (fun _ => 0, (fun _ => 0, ()))
def oneSeed : EpochSeeds 2 2 2 := (fun _ => 1, (fun _ => 1, ()))

theorem two_epochs_use_sixteen_component_queries : queryCount 2 2 2 = 16 := rfl

theorem sampling_changes_output :
    (execute quadraticOracle (svrg 2 (1 : ℝ) 2) (fun _ => (queryCount 2 2 2)) zeroSeed) ≠
      (execute quadraticOracle (svrg 2 (1 : ℝ) 2) (fun _ => (queryCount 2 2 2)) oneSeed) := by
  have hzero := execute_svrg (fun query => quadraticOracle.answer 0 (0, query) ())
    2 (1 : ℝ) 2 zeroSeed
  have hone := execute_svrg (fun query => quadraticOracle.answer 0 (0, query) ())
    2 (1 : ℝ) 2 oneSeed
  intro h
  have he := hzero.symm.trans (h.trans hone)
  dsimp only [quadraticOracle] at he
  norm_num [epochRun, innerRun, zeroSeed, oneSeed, estimator, fullGradient,
    List.ofFn_succ, Fin.sum_univ_two] at he

theorem extra_queries_preserve_output (seed : EpochSeeds 2 2 2) :
    (execute quadraticOracle (svrg 2 (1 : ℝ) 2) (fun _ => 100) seed) =
      (execute quadraticOracle (svrg 2 (1 : ℝ) 2) (fun _ => 16) seed) := by
  exact (execute_svrg_of_le (fun query => quadraticOracle.answer 0 (0, query) ())
    2 (1 : ℝ) 2 100 (by decide) seed).trans
    (execute_svrg_of_le (fun query => quadraticOracle.answer 0 (0, query) ())
      2 (1 : ℝ) 2 16 (by decide) seed).symm

theorem zero_epochs_preserve_initial_point :
    (execute quadraticOracle (svrg 2 (1 : ℝ) 0) (fun _ => 100) ()) = 1 := by
  exact execute_svrg_of_le (fun query => quadraticOracle.answer 0 (0, query) ())
    2 (1 : ℝ) 0 100 (by decide) ()

end OracleTemplate.FiniteSum.Tests
