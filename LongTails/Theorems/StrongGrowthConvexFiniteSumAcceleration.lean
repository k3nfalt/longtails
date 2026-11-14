import LongTails.Setups.FiniteSumStrongGrowthConvex
import LongTails.Proofs.EmpiricalProximalConvergence
import LongTails.Proofs.EmpiricalProximalExecution
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped BigOperators

namespace LongTails.Theorems.StrongGrowthConvexFiniteSumAcceleration

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex
open LongTails.Algorithms.EmpiricalProximalAcceleration
open LongTails.Proofs.EmpiricalProximalParameters
open LongTails.Proofs.EmpiricalProximalConvergence
open LongTails.Proofs.EmpiricalProximalExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 7000 * (min p.n ⌈1024 * p.ρ⌉₊ + ⌈Real.sqrt (((min p.n ⌈1024 * p.ρ⌉₊ : ℕ) : ℝ) * p.L * p.R ^ 2 / p.ε)⌉₊) * Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊

theorem result : Convergence LongTails.Setups.FiniteSumStrongGrowthConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => method p (1 + ⌈Real.sqrt (4096 * p.L * p.R ^ 2 / (((min p.n ⌈1024 * p.ρ⌉₊ : ℕ) : ℝ) * p.ε))⌉₊), ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hρ, hR, hε⟩
  rintro f O ⟨hc, hg, hlip, hsg, hO, u, hu, hdist⟩
  let T := 1 + ⌈Real.sqrt (4096 * p.L * p.R ^ 2 / (((min p.n ⌈1024 * p.ρ⌉₊ : ℕ) : ℝ) * p.ε))⌉₊
  let K := 7000 * (min p.n ⌈1024 * p.ρ⌉₊ + ⌈Real.sqrt (((min p.n ⌈1024 * p.ρ⌉₊ : ℕ) : ℝ) * p.L * p.R ^ 2 / p.ε)⌉₊) * Nat.clog 2 ⌈2 ^ 32 * p.ρ ^ 5⌉₊
  let g : Fin p.n × p.E → p.E := fun q => gradient (f q.1) q.2
  let out := fun ξ : Seeds p T => output p g T ξ
  have hsg_sum (x : p.E) : (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2 := by
    have he : gradient (objective f) x = FiniteSum.fullGradient g x :=
      (FiniteSum.objective_gradient hg x).gradient
    simpa only [he] using hsg x
  have hsg' (x : p.E) : (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2 := by
    simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_mul_inv, mul_comm] using hsg_sum x
  have hcommon := LongTails.Proofs.StrongGrowthBatchProx.common_minima_of_strong_growth hc hg hsg_sum hu
  have hcommon' (i : Fin p.n) (x : p.E) : f i u ≤ f i x := hcommon i (mem_univ x)
  have hT : 0 < T := by dsimp [T]; omega
  have hTeq : T = 1 + ⌈Real.sqrt (4 * regularization p * p.R ^ 2 / p.ε)⌉₊ := outer_steps_eq p hρ
  have hgood : (𝔼 ξ : Seeds p T, (objective f (out ξ) - objective f u)) ≤ p.ε := by
    have hh := output_gap_bound p hL hρ f g hc hg hlip hsg' hcommon' T hT
    have hd := pow_le_pow_left₀ (norm_nonneg (p.x0 - u)) hdist 2
    have hμ := LongTails.Proofs.EmpiricalProximalInner.regularization_pos p hL
    have hb := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * regularization p by positivity))
      (sq_nonneg (T : ℝ))
    have ht : 2 * regularization p * p.R ^ 2 / (T : ℝ) ^ 2 ≤ p.ε := by
      rw [hTeq]
      exact accuracy_tuning p hL hε
    exact hh.trans (hb.trans ht)
  have hK : stepCost p * T ≤ K := by
    rw [hTeq]
    exact totalCost_bound p hL hρ hε
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

end LongTails.Theorems.StrongGrowthConvexFiniteSumAcceleration
