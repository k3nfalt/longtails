import LongTails.Setups.HessianAdaptiveStochasticConvex
import LongTails.Proofs.HessianAdaptiveCubicAccuracy

open MeasureTheory

namespace LongTails.Theorems.HessianAdaptiveCubic

open OracleTemplate
open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants
open LongTails.Proofs.HessianAdaptiveCubicExecution
open LongTails.Proofs.HessianAdaptiveCubicMeasurability
open LongTails.Proofs.HessianAdaptiveCubicRate
open LongTails.Proofs.HessianAdaptiveCubicAccuracy

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 3 * ⌈1000000000000000000 * (1 + (p.σg * p.D / p.ε) ^ 2 + Real.sqrt (p.σh * p.D ^ 2 / p.ε) + (p.ρ * p.D ^ 3 / p.ε) ^ (2 / 7 : ℝ)) * (1 + Real.log ((1 + p.σh / (p.ρ * p.D)) * (1 + (p.σg * p.D / p.ε) ^ 2 + Real.sqrt (p.σh * p.D ^ 2 / p.ε) + (p.ρ * p.D ^ 3 / p.ε) ^ (2 / 7 : ℝ)))) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.HessianAdaptiveStochasticConvex.spec budget := by
  classical
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I O ho
  rcases hp with ⟨hD, hρ, hσ, hσh, hε, hx, hdiam⟩
  rcases ho with ⟨hxs, hmin, hf, hgrad, hdiff, hLip, g, H, μ, P, hIID, rfl,
    hg, hH, hgint, hgmean, hgi, hgb, hPSD, hhi, hhb⟩
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure (μ : Measure p.Ω)
  let Q := 1 + (p.σg * p.D / p.ε) ^ 2 + Real.sqrt (p.σh * p.D ^ 2 / p.ε) + (p.ρ * p.D ^ 3 / p.ε) ^ (2 / 7 : ℝ)
  let J := 1 + Real.log ((1 + p.σh / (p.ρ * p.D)) * Q)
  let N := ⌈1000000000000000000 * Q * J ^ 2⌉₊
  let F := fun ξ : ℕ → p.Ω => (roundState p.toPublic g H ξ N).point
  have hb := accuracy_at_shape_budget p.ρ p.σg p.σh p.D p.ε
    (∫ ξ, I.f (F ξ) - I.f I.xstar ∂(P : Measure _)) hρ hσh hD hε
  have hr := model_rate_squared p.toPublic (μ : Measure _) (P : Measure _) hIID ω0
    hD hρ hσ hx hdiam I.xstar hxs I.f hf hgrad hmin hdiff hLip g H hg hH hPSD p.σh
    hgint hgmean hgi hgb hhi hhb hσh N hb.1
  have hm : Measurable F := (measurable_roundState p.toPublic hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → p.Ω) => ξ k) (fun k => measurable_pi_apply k) N).point
  have hmem (ξ : ℕ → p.Ω) : F ξ ∈ p.C :=
    (roundState_invariant p.toPublic g H ξ hD hρ hσ hx N).point
  have hacc : (∫ ξ, I.f (F ξ) - I.f I.xstar ∂(P : Measure _)) ≤ p.ε := hb.2 hr.2
  have he (w : Unit × (ℕ → p.Ω)) :
      execute
        { Seed := fun _ => p.Ω, law := P,
          answer := fun _ (_, hessian, x) ω => if hessian then (0, H x ω) else (g x ω, 0) }
        (algorithm p.toPublic) (budget p) w.1 w.2 = F w.2 := by
    rcases w with ⟨⟨⟩, ξ⟩
    exact execute_roundState p.toPublic g H P ξ N
  let R := fun w : Unit × (ℕ → p.Ω) => execute
    { Seed := fun _ => p.Ω, law := P,
      answer := fun _ (_, hessian, x) ω => if hessian then (0, H x ω) else (g x ω, 0) }
    (algorithm p.toPublic) (budget p) w.1 w.2
  change Measurable R ∧ (∀ w, R w ∈ p.C) ∧
    Integrable (fun w => I.f (R w) - I.f I.xstar) ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ w, I.f (R w) - I.f I.xstar ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.ε
  have heq : R = fun w => F w.2 := funext he
  rw [heq]
  refine ⟨hm.comp measurable_snd, fun w => hmem w.2, hr.1.comp_snd _, ?_⟩
  rw [integral_fun_snd (fun ξ : ℕ → p.Ω => I.f (F ξ) - I.f I.xstar)]
  simpa only [probReal_univ, one_smul] using hacc

end LongTails.Theorems.HessianAdaptiveCubic
