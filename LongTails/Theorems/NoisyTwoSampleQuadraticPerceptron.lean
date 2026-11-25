import LongTails.Setups.NoisyTwoSamplePerceptron
import LongTails.Proofs.NoisyTwoSamplePerceptronProbability

open MeasureTheory
open LongTails.Setups.FiniteLogisticTwoTap (Weights Reply Separates)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Algorithms.NoisyTwoSamplePerceptron
open LongTails.Proofs.NoisyTwoSamplePerceptronExecution
open LongTails.Proofs.NoisyTwoSamplePerceptronDynamics
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronHorizon
open LongTails.Proofs.NoisyTwoSamplePerceptronBlocks
open LongTails.Proofs.NoisyTwoSamplePerceptronProbability

namespace OracleTemplate.NoisyTwoSampleQuadraticPerceptron

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let X := Real.sqrt p.d / p.μ
  let C := (‖p.x₀‖ / p.signal)^2
  let K := 2^27 * X * Real.log (2^62 * C / p.ρ^3) * Real.log (2^15 * X * C)
  2 * ⌈K * Real.log K⌉₊

theorem result : Convergence LongTails.Setups.NoisyTwoSamplePerceptron.spec budget := by
  refine ⟨fun p => algorithm p (gamma p.d) (sigma p),?_,?_⟩
  · intro p hp i O hO
    change Params at p
    change Fin p.d at i
    change Oracle (Bool × Weights p.d) (Reply p.d) at O
    have hd := hp.1
    change 2 ≤ p.d at hd
    have : NeZero p.d := ⟨by omega⟩
    have hi : finRotate p.d i ≠ i := by simp [finRotate_apply]; omega
    have hK : 2^27*(Real.sqrt p.d/p.μ)*Real.log (2^62*(‖p.x₀‖/p.signal)^2/p.ρ^3)*
        Real.log (2^15*(Real.sqrt p.d/p.μ)*(‖p.x₀‖/p.signal)^2) = scale p*factor p := by
      dsimp [scale,factor,confidenceLog,geometryLog,ratio]
      rw [div_pow]
      ring
    have hB : budget p = fun _ => 2*horizon p := by
      funext j
      dsimp only [budget,horizon]
      rw [hK]
    let bad := {g | ¬Separates p.μ i (point p.μ (gamma p.d) (sigma p) i p.x₀ g (horizon p))}
    let P := (law p.d).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    change P {ω | ¬Separates p.μ i (execute O (algorithm p (gamma p.d) (sigma p)) (budget p) ω.1 ω.2)} ≤ ENNReal.ofReal p.ρ
    rw [hB]
    calc
      _ ≤ P (bad ×ˢ Set.univ) := by
        apply measure_mono
        intro ω h
        change ¬Separates p.μ i (execute O (algorithm p (gamma p.d) (sigma p)) (fun _ => 2*horizon p) ω.1 ω.2) at h
        rw [execute_pairs p _ _ i O hO] at h
        exact ⟨h,Set.mem_univ _⟩
      _ = law p.d bad := by simp [P,Measure.prod_prod]
      _ ≤ _ := fails_rarely p hp i hi hO.1
  · intro p hp
    change Params at p
    have hD : (0:ℝ) < p.d := by exact_mod_cast (by have h := hp.1; change 2 ≤ p.d at h; omega : 0 < p.d)
    have hT := (valid_scales p hp).2.2.2.2.2
    have hM := (horizon_bounds p hp).2.2.1
    have hs := hp.2.2.2.1
    change 0 < p.signal at hs
    exact algorithm_family p (by dsimp [gamma]; positivity) (by dsimp [sigma]; positivity)

end OracleTemplate.NoisyTwoSampleQuadraticPerceptron
