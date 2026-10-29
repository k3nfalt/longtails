import LongTails.Setups.HeavyTailedPLHessian
import LongTails.Proofs.RobustPLConvergence
import LongTails.Proofs.RobustPLExecution

open MeasureTheory Set
open OracleTemplate OracleTemplate.HeavyTailedPLHessian OracleTemplate.RobustPLPotential

namespace LongTails.Theorems.KappaFreeHeavyTailedPLHessian

open LongTails.Setups.HeavyTailedPLHessian

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 65 * (⌈512 * ((q.L / q.μ) ^ (5 / 4 : ℝ) + ((2 : ℝ) ^ (128 / q.p + 27) * q.σ ^ 2 * (1 / (q.μ * q.ε) + (q.L / q.μ) ^ (5 / 2 : ℝ) * q.ρ ^ 2 / q.μ ^ 4)) ^ (q.p / (2 * (q.p - 1)))) * (Real.log (1 + 48 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε) + 1)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.HeavyTailedPLHessian.spec budget := by
  refine ⟨fun q =>
    let h := stepFraction q.L q.μ q.ρ q.σ q.p q.ε
    let η := h / q.μ
    let τ := clipRadius q.L q.μ q.ρ q.σ q.p q.ε
    let n := ⌈64 / h * Real.log (1 + 48 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε)⌉₊
    let m := ⌈8 / h⌉₊
    method η τ n m q.x0, ?_, ?_⟩
  · intro q hvalid f O hadm
    obtain ⟨hμ, hμL, hρ, hσ, hp, hp2, hΔ, hε⟩ := hvalid
    obtain ⟨g, P0, P, hIID, rfl, hgrad, hlip, hdiff, hhess,
      ⟨u, hmin, hpl, hgap⟩, hgm, hgi, hmean, hpi, hpm⟩ := hadm
    let h := stepFraction q.L q.μ q.ρ q.σ q.p q.ε
    let η := h / q.μ
    let τ := clipRadius q.L q.μ q.ρ q.σ q.p q.ε
    let n := ⌈64 / h * Real.log (1 + 48 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε)⌉₊
    let m := ⌈8 / h⌉₊
    let K := ⌈512 * ((q.L / q.μ) ^ (5 / 4 : ℝ) + ((2 : ℝ) ^ (128 / q.p + 27) * q.σ ^ 2 * (1 / (q.μ * q.ε) + (q.L / q.μ) ^ (5 / 2 : ℝ) * q.ρ ^ 2 / q.μ ^ 4)) ^ (q.p / (2 * (q.p - 1)))) * (Real.log (1 + 48 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε) + 1)⌉₊ + 1
    have hK : n + m ≤ K := total_iterations hμ hμL hσ hp hΔ hε
    let Q : ProbabilityMeasure (ℕ → Fin 65 → q.Ω) :=
      ⟨Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin 65 => (P0 : Measure q.Ω), inferInstance⟩
    have H := geometry_hyp (P := Measure.pi fun _ : Fin 65 => (P0 : Measure q.Ω))
      hgrad hlip hdiff hhess hmin hpl hμ hμL hρ
    let out := fun ω : Fin (m + 1) × (ℕ → q.Ω) =>
      output g η τ q.x0 n m ω.1 (fun k i => ω.2 (k * 65 + i.val))
    have hexec : ∀ (seed : Fin (m + 1)) (ξ : ℕ → q.Ω),
      execute (PLHessian.winOracle g P) (method η τ n m q.x0) (budget q) seed ξ =
        out (seed, ξ) := by
      intro seed ξ
      have hb : budget q = fun _ => K * 65 := by funext i; dsimp [budget, K]; omega
      rw [hb]
      exact execute_method P Q g η τ n m K q.x0 seed ξ hK
    have hout : (fun ω : Fin (m + 1) × (ℕ → q.Ω) =>
      execute (PLHessian.winOracle g P) (method η τ n m q.x0) (budget q) ω.1 ω.2) = out := by
      funext ω
      exact hexec ω.1 ω.2
    have hfun : (fun ω : Fin (m + 1) × (ℕ → q.Ω) =>
        f (execute (PLHessian.winOracle g P) (method η τ n m q.x0)
          (budget q) ω.1 ω.2) - f u) = (fun ω => f (out ω) - f u) := by
      funext ω
      rw [hexec]
    have hm : Measurable out := measurable_output hgm η τ q.x0 n m
    have hf : Continuous f := H.continuous
    have hbound := tuned_accuracy H hgm hgi hmean hp hp2 hσ hpi hpm hΔ hε hgap
    have htransfer := iid_output_integral (P0 : Measure q.Ω) (P : Measure (ℕ → q.Ω))
      hIID.independent hIID.marginal hgm hf u q.x0 η τ n m
    have hl : ∫⁻ ω, ENNReal.ofReal (f (out ω) - f u)
        ∂((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤
        ENNReal.ofReal q.ε := htransfer.trans_le hbound
    have hfm : Measurable (fun ω => f (out ω) - f u) := (hf.measurable.comp hm).sub_const _
    have hnn : ∀ ω, 0 ≤ f (out ω) - f u := fun ω => sub_nonneg.mpr (hmin (mem_univ _))
    change Measurable _ ∧ ∃ xstar, IsMinOn f univ xstar ∧ Integrable _ _ ∧ _
    change Measurable (fun ω : Fin (m + 1) × (ℕ → q.Ω) =>
      execute (PLHessian.winOracle g P) (method η τ n m q.x0) (budget q) ω.1 ω.2) ∧ _
    rw [hout]
    refine ⟨hm, u, hmin, ?_, ?_⟩
    · change Integrable (fun ω : Fin (m + 1) × (ℕ → q.Ω) =>
        f (execute (PLHessian.winOracle g P) (method η τ n m q.x0)
          (budget q) ω.1 ω.2) - f u)
        ((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω)))
      rw [hfun]
      have hi := integrable_toReal_of_lintegral_ne_top
        (ENNReal.measurable_ofReal.comp hfm).aemeasurable
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)
      simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hnn _)] using hi
    · change (∫ ω : Fin (m + 1) × (ℕ → q.Ω),
        (f (execute (PLHessian.winOracle g P) (method η τ n m q.x0)
          (budget q) ω.1 ω.2) - f u)
        ∂((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω)))) ≤ q.ε
      rw [hfun]
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
        hfm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hl
  · intro q hq
    trivial

end LongTails.Theorems.KappaFreeHeavyTailedPLHessian
