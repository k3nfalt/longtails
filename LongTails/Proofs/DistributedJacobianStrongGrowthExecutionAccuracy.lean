import LongTails.Proofs.DistributedJacobianStrongGrowthTimeTerminal
import LongTails.Proofs.DistributedJacobianStrongGrowthFallbackTerminal
import LongTails.Proofs.DistributedJacobianStrongGrowthTrivialExecution
import LongTails.Proofs.DistributedJacobianStrongGrowthAccuracy

namespace LongTails.Proofs.DistributedJacobianStrongGrowthExecutionAccuracy

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthTimeSchedule

lemma execute_selected (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle deadline : Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (hidle : deadline < idle)
    (hrich : p.ε < p.R → 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ) →
      roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) ≤ deadline)
    (hbase : p.ε < p.R → ¬ 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ) →
      (baselineCount p : Time) * p.computeTime ≤ deadline) :
    execute (system p g S) (algorithm p idle) deadline seed.1 seed.2 =
      selectedOutput p g (fun j => S.sample j seed.2) := by
  classical
  by_cases hε : p.R ≤ p.ε
  · simpa only [selectedOutput, ite_eq_left hε] using
      DistributedJacobianStrongGrowthTrivialExecution.execute_trivial p hp g S idle deadline seed hε hidle
  · have he := lt_of_not_ge hε
    by_cases hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)
    · simpa only [selectedOutput, ite_eq_right hε, ite_eq_left hn] using
        DistributedJacobianStrongGrowthTimeTerminal.execute_rich p hp g S idle deadline seed he hn hidle (hrich he hn)
    · simpa only [selectedOutput, ite_eq_right hε, ite_eq_right hn] using
        DistributedJacobianStrongGrowthFallbackTerminal.execute_fallback p hp g S idle deadline seed he hn hidle (hbase he hn)

open MeasureTheory

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma execute_accuracy (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (idle deadline : Time) (hidle : deadline < idle)
    (hrich : p.ε < p.R → 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ) →
      roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) ≤ deadline)
    (hbase : p.ε < p.R → ¬ 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ) →
      (baselineCount p : Time) * p.computeTime ≤ deadline) :
    spec.successful p I (fun seed => execute (system p g S) (algorithm p idle) deadline seed.1 seed.2)
      (law (system p g S) (algorithm p idle)) := by
  have heq : (fun seed => execute (system p g S) (algorithm p idle) deadline seed.1 seed.2) =
      (fun seed : (algorithm p idle).Seed × (system p g S).Seed =>
        selectedOutput p g (fun j => S.sample j seed.2)) :=
    funext (fun seed => execute_selected p hp g S idle deadline seed hidle hrich hbase)
  have ha := DistributedJacobianStrongGrowthAccuracy.selected_output_accuracy p hp I hI g S hg
  have hsuc : spec.successful p I
      (fun seed : (algorithm p idle).Seed × (system p g S).Seed => selectedOutput p g (fun j => S.sample j seed.2))
      (law (system p g S) (algorithm p idle)) := by
    refine ⟨ha.1.comp measurable_snd, ?_, ?_⟩
    · exact ha.2.1.comp_snd (↑((algorithm p idle).law) : Measure ((algorithm p idle).Seed))
    · change (∫ seed : (algorithm p idle).Seed × S.Seed,
        ‖selectedOutput p g (fun j => S.sample j seed.2) - I.solution‖ ^ 2
        ∂(↑((algorithm p idle).law) : Measure ((algorithm p idle).Seed)).prod (S.law : Measure S.Seed)) ≤ p.ε ^ 2
      have he := integral_fun_snd
        (μ := (↑((algorithm p idle).law) : Measure ((algorithm p idle).Seed)))
        (ν := (S.law : Measure S.Seed))
        (fun ω : S.Seed => ‖selectedOutput p g (fun j => S.sample j ω) - I.solution‖ ^ 2)
      exact (le_of_eq (by simpa using he)).trans ha.2.2
  exact (congrArg (fun out : (algorithm p idle).Seed × (system p g S).Seed → Point p =>
    spec.successful p I out (law (system p g S) (algorithm p idle))) heq).mpr hsuc

end LongTails.Proofs.DistributedJacobianStrongGrowthExecutionAccuracy
