import LongTails.Setups.FiniteLogisticTwoTap
import LongTails.Proofs.FiniteLogisticTwoTapBudget

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Algorithms.FiniteLogisticTwoTap
open LongTails.Proofs.FiniteLogisticTwoTapBudget
open LongTails.Proofs.FiniteLogisticTwoTapExecution
open LongTails.Proofs.FiniteLogisticTwoTapTrajectory
open LongTails.Proofs.TwoTapGaussianBounds

namespace OracleTemplate.FiniteLogisticTwoTapGradientDescent

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  2 * ⌈2^53 * Real.sqrt p.d / p.μ * Real.log (1 / p.r)⌉₊

theorem result : Convergence LongTails.Setups.FiniteLogisticTwoTap.spec budget := by
  refine ⟨fun p => algorithm p (stepsize p.d),?_,?_⟩
  · intro p hp i O hO
    change Params at p
    change Fin p.d at i
    change Oracle (Bool × Weights p.d) (Reply p.d) at O
    have hd : 3 ≤ p.d := hp.1
    have : NeZero p.d := ⟨by omega⟩
    have : Fact (1 < p.d) := ⟨by omega⟩
    have hi : finRotate p.d i ≠ i := by simp [finRotate_apply]; omega
    let N := ⌈2^53 * Real.sqrt p.d / p.μ * Real.log (1 / p.r)⌉₊
    let bad := {g : Weights p.d | ¬(‖start p.r g‖ = p.r ∧
      p.ρ/(32*Real.sqrt p.d)*p.r < |⟪mode i 1,start p.r g⟫| ∧
      p.ρ/(32*Real.sqrt p.d)*p.r < |⟪mode i (-1),start p.r g⟫|)}
    let P := (stdGaussian (Weights p.d)).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    change P {ω | ¬Separates p.μ i
      (execute O (algorithm p (stepsize p.d)) (fun _ => 2*N) ω.1 ω.2)} ≤ ENNReal.ofReal p.ρ
    calc
      _ ≤ P (bad ×ˢ Set.univ) := by
        apply measure_mono
        intro ω homega
        refine ⟨?_,Set.mem_univ _⟩
        intro good
        change ¬Separates p.μ i (execute O (algorithm p (stepsize p.d)) (fun _ => 2*N) ω.1 ω.2) at homega
        rw [execute_pairs p _ i O hO] at homega
        exact homega (reaches p hp i hi _ good.1.le good.2.1 good.2.2)
      _ = stdGaussian _ bad := by simp [P,Measure.prod_prod]
      _ ≤ _ := initial_modes (d := p.d) (by omega) i hi hp.2.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1.le
  · intro p hp
    exact algorithm_family p (scales p hp).hη

end OracleTemplate.FiniteLogisticTwoTapGradientDescent
