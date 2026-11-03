import LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
import LongTails.Proofs.StrongGrowthBatchConvergence
import LongTails.Proofs.StrongGrowthBatchExecution
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped BigOperators

namespace LongTails.Theorems.StrongGrowthFiniteSumAcceleration

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
open LongTails.Algorithms.StrongGrowthBatchProx
open LongTails.Proofs.StrongGrowthBatchProx

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 108 * (min p.n ⌈128 * p.ρ⌉₊ + ⌈Real.sqrt (((min p.n ⌈128 * p.ρ⌉₊ : ℕ) : ℝ) * p.L / p.μ)⌉₊) * Nat.clog 2 ⌈7168 * (1 + p.L / p.μ)⌉₊ * Nat.clog 2 ⌈p.L * p.R ^ 2 / p.ε⌉₊

theorem result : Convergence LongTails.Setups.FiniteSumStrongGrowthStronglyConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => method p (Nat.clog 2 ⌈p.L * p.R ^ 2 / p.ε⌉₊), ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hμ, hρ, hR, hε⟩
  rintro f O ⟨hc, hg, hlip, hsc, hsg, hO, u, hu, hdist⟩
  let T := Nat.clog 2 ⌈p.L * p.R ^ 2 / p.ε⌉₊
  let K := 108 * (min p.n ⌈128 * p.ρ⌉₊ + ⌈Real.sqrt (((min p.n ⌈128 * p.ρ⌉₊ : ℕ) : ℝ) * p.L / p.μ)⌉₊) * Nat.clog 2 ⌈7168 * (1 + p.L / p.μ)⌉₊ * Nat.clog 2 ⌈p.L * p.R ^ 2 / p.ε⌉₊
  let g : Fin p.n × p.E → p.E := fun q => gradient (f q.1) q.2
  let out := fun ξ : Seeds p T => output p g T p.x0 ξ
  have hsg' (x : p.E) : (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2 := by
    have he : gradient (objective f) x = FiniteSum.fullGradient g x :=
      (FiniteSum.objective_gradient hg x).gradient
    simpa only [he] using hsg x
  have hgood : (𝔼 ξ : Seeds p T, (objective f (out ξ) - objective f u)) ≤ p.ε := by
    have hh := output_gap_bound p hL hμ hρ f g hc hg hlip hsg' hsc hu T p.x0
    have hd := pow_le_pow_left₀ (norm_nonneg (p.x0 - u)) hdist 2
    have hb := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hd (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) T))
      (show 0 ≤ p.L / 2 by positivity)
    exact hh.trans (hb.trans (accuracy_tuning p hε))
  have hK : innerCost p * T ≤ K := totalCost_bound p hL hμ hρ T
  have hanswer : ∀ k q seed, O.answer k (0, q) seed = g q := by
    intro k q seed
    exact hO k seed q.1 q.2
  have hexec (ξ : Seeds p T) (ω : (k : ℕ) → O.Seed k) :
      execute O (method p T) (fun _ => K) ξ ω = out ξ :=
    execute_method p g O hanswer T K hK ξ ω
  change spec.successful p f
    (fun seed => execute O (method p T) (fun _ => K) seed.1 seed.2)
    ⟨(PMF.uniformOfFintype (Seeds p T)).toMeasure.prod
      (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : Seeds p T × ((k : ℕ) → O.Seed k) => out seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, u, hu, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun ξ : Seeds p T => objective f (out ξ) - objective f u)
        (μ := (PMF.uniformOfFintype (Seeds p T)).toMeasure))
  · change (∫ seed : Seeds p T × ((k : ℕ) → O.Seed k),
      objective f (out seed.1) - objective f u
      ∂(PMF.uniformOfFintype (Seeds p T)).toMeasure.prod
        (O.law : Measure ((k : ℕ) → O.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun ξ => objective f (out ξ) - objective f u)]
    simp only [probReal_univ, one_smul]
    rw [FiniteSum.uniform_integral]
    exact hgood

end LongTails.Theorems.StrongGrowthFiniteSumAcceleration
