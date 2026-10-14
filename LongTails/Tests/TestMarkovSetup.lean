import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.HeavyTailedMarkovGradient.Tests

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

theorem valid_moment_range (α : ℝ) :
    spec.valid { E := ℝ, Ω := Unit, L := 1, R := 1, σ := 1, α := α, τ := 1, β := 1, ε := 1, x0 := 0 } ↔ 1 < α ∧ α ≤ 2 := by
  dsimp only [spec]
  norm_num

theorem accepts_finite_variance :
    spec.valid { E := ℝ, Ω := Unit, L := 1, R := 1, σ := 1, α := 2, τ := 1, β := 1, ε := 1, x0 := 0 } := by
  dsimp only [spec]
  norm_num

theorem accepts_infinite_variance_moment_range :
    spec.valid { E := ℝ, Ω := Unit, L := 1, R := 1, σ := 1, α := 3 / 2, τ := 1, β := 1, ε := 1, x0 := 0 } := by
  dsimp only [spec]
  norm_num

theorem independent_transition_has_zero_mixing_distance {Ω : Type}
    [MeasurableSpace Ω] (π : ProbabilityMeasure Ω) (z : Ω) :
    mixingDistance (Kernel.const Ω (π : Measure Ω)) π 1 z = 0 := by
  simp [mixingDistance]

theorem public_input_exposes_mixing_time (L R σ α τ β ε x0 : ℝ) :
    (spec.publicInput { E := ℝ, Ω := Unit, L := L, R := R, σ := σ, α := α, τ := τ, β := β, ε := ε, x0 := x0 }).τ = τ := rfl

theorem next_sample_depends_on_current_state {Ω : Type} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (initial : ProbabilityMeasure Ω) (n : ℕ) :
    condDistrib (fun ξ : ℕ → Ω => ξ (n + 1))
      (fun ξ : ℕ → Ω => fun i : Finset.Iic n => ξ i)
      (pathLaw κ initial : Measure (ℕ → Ω)) =ᵐ[
        (pathLaw κ initial : Measure (ℕ → Ω)).map
          (fun ξ => fun i : Finset.Iic n => ξ i)]
      κ.comap (fun z : Finset.Iic n → Ω => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (by fun_prop) := by
  exact Kernel.condDistrib_trajMeasure

end OracleTemplate.HeavyTailedMarkovGradient.Tests
