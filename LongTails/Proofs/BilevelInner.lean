import LongTails.Proofs.AcceleratedConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LongTails.Proofs.BilevelPenalty
import LongTails.Proofs.BilevelExecution

set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.BilevelInner

open OracleTemplate OracleTemplate.Gradient
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma accelerated_radius_halving (f : E → ℝ) (oracle : E → E)
    {M μ R : ℝ} (hM : 0 < M) (hμ : 0 < μ) (hR : 0 < R)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ M * ‖x - y‖)
    (x0 xstar : E) (hdist : ‖x0 - xstar‖ ≤ R)
    (hgrowth : ∀ y, μ / 2 * ‖y - xstar‖ ^ 2 ≤ f y - f xstar)
    (K : ℕ) (hK : max 1 ⌈Real.sqrt (16 * M / μ)⌉₊ ≤ K) :
    ‖execute { answer := fun _ (_, query) _ => oracle query }
      (accelerated (M, x0)) (fun _ => K) - xstar‖ ≤ R / 2 := by
  have he : 2 * M * R ^ 2 / (μ * R ^ 2 / 8) = 16 * M / μ := by
    field_simp
    ring
  have hh := accelerated_accuracy f oracle M R (μ * R ^ 2 / 8) x0 xstar
    hM hR.le (by positivity) hc hg hlip hdist K (by simpa [he] using hK)
  have hl := hgrowth (execute { answer := fun _ (_, query) _ => oracle query }
    (accelerated (M, x0)) (fun _ => K))
  have hnorm := norm_nonneg (execute { answer := fun _ (_, query) _ => oracle query }
    (accelerated (M, x0)) (fun _ => K) - xstar)
  have hsquare : ‖execute { answer := fun _ (_, query) _ => oracle query }
      (accelerated (M, x0)) (fun _ => K) - xstar‖ ^ 2 ≤ R ^ 2 / 4 := by
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [hl, hh]
  nlinarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma restarted_radius (Φ : E → E) (x0 xstar : E) {D : ℝ} (hD : 0 < D)
    (hinit : ‖x0 - xstar‖ ≤ D)
    (hhalf : ∀ y R, 0 < R → ‖y - xstar‖ ≤ R → ‖Φ y - xstar‖ ≤ R / 2)
    (J : ℕ) : ‖Φ^[J] x0 - xstar‖ ≤ D / 2 ^ J := by
  induction J with
  | zero => simpa using hinit
  | succ J ih =>
    rw [Function.iterate_succ_apply']
    have hh := hhalf (Φ^[J] x0) (D / 2 ^ J) (by positivity) ih
    simpa [pow_succ, div_div] using hh

lemma log_restart_residual {M D τ : ℝ} (hM : 0 < M) (hD : 0 ≤ D) (hτ : 0 < τ) :
    M * (D / 2 ^ ⌈Real.log (1 + M * D / τ) / Real.log 2⌉₊) ≤ τ := by
  let J := ⌈Real.log (1 + M * D / τ) / Real.log 2⌉₊
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 0 < 1 + M * D / τ := by positivity
  have hceil : Real.log (1 + M * D / τ) / Real.log 2 ≤ (J : ℝ) := Nat.le_ceil _
  have hlog : Real.log (1 + M * D / τ) ≤ Real.log ((2 : ℝ) ^ J) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog2).mp hceil
  have hpow : 1 + M * D / τ ≤ (2 : ℝ) ^ J :=
    (Real.log_le_log_iff harg (by positivity)).mp hlog
  have hh : M * D ≤ τ * (2 : ℝ) ^ J := by
    have ht := (div_le_iff₀ hτ).mp (show M * D / τ ≤ (2 : ℝ) ^ J from by linarith)
    nlinarith
  change M * (D / (2 : ℝ) ^ J) ≤ τ
  rw [← mul_div_assoc]
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ J)).mpr (by nlinarith)

open LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated BilevelPenalty

lemma innerSolve_residual {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam D τ : ℝ} (ha : 0 ≤ lam⁻¹) (hb : lam⁻¹ ≤ 1) (hc : p.L * lam⁻¹ ≤ p.μ / 2)
    (hD : 0 < D) (hτ : 0 < τ) (x : p.X) (ystar : p.Y)
    (hmin : ∀ y, innerObjective I x lam ystar ≤ innerObjective I x lam y)
    (hinit : ‖p.y0 - ystar‖ ≤ D) (t : Tuning)
    (hm : max 1 ⌈Real.sqrt (64 * p.L / p.μ)⌉₊ ≤ t.m)
    (hJ : t.J = ⌈Real.log (1 + 2 * p.L * D / τ) / Real.log 2⌉₊) :
    ‖lowerReply p lam (firstOrderReply I (x, QueryPlan.eval (firstOrderReply I) (innerSolve p t x lam)))‖ ≤ τ := by
  let oracle := fun y => lowerReply p lam (firstOrderReply I (x, y))
  let Φ := fun y => execute { answer := fun _ (_, query) _ => oracle query }
    (accelerated (2 * p.L, y)) (fun _ => t.m)
  have hstat : oracle ystar = 0 := inner_stationary hf hg x lam ystar hmin
  have hgrowth : ∀ y, (p.μ / 2) / 2 * ‖y - ystar‖ ^ 2 ≤
      innerObjective I x lam y - innerObjective I x lam ystar := by
    intro y
    have hh := inner_quadratic_support hf hf1 hsc ha hc x ystar y
    change innerObjective I x lam ystar + ⟪oracle ystar, y - ystar⟫ + _ ≤ _ at hh
    rw [hstat, inner_zero_left] at hh
    linarith
  have hhalf : ∀ y R, 0 < R → ‖y - ystar‖ ≤ R → ‖Φ y - ystar‖ ≤ R / 2 := by
    intro y R hR hdist
    apply accelerated_radius_halving (innerObjective I x lam) oracle
      (by positivity) (half_pos hμ) hR (inner_convex hf hμ.le hf1 hsc ha hc x)
      (inner_hasGradientAt hf hg x lam) (inner_lipschitz hf1 hg1 ha hb x) y ystar hdist hgrowth t.m
    have he : 16 * (2 * p.L) / (p.μ / 2) = 64 * p.L / p.μ := by ring
    simpa only [he] using hm
  have hd := restarted_radius Φ p.y0 ystar hD hinit hhalf t.J
  have hl := inner_lipschitz hf1 hg1 ha hb x (Φ^[t.J] p.y0) ystar
  change ‖oracle (Φ^[t.J] p.y0) - oracle ystar‖ ≤ _ at hl
  rw [hstat, sub_zero] at hl
  have hr : (2 * p.L) * (D / 2 ^ t.J) ≤ τ := by
    rw [hJ]
    simpa [mul_assoc] using log_restart_residual (M := 2 * p.L) (by positivity) hD.le hτ
  have hout : QueryPlan.eval (firstOrderReply I) (innerSolve p t x lam) = Φ^[t.J] p.y0 := by
    rw [BilevelExecution.eval_innerSolve]
  rw [hout]
  exact hl.trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans hr)

lemma estimate_error_within_radius {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hg2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hG : ‖gradient (fun y => I.g (p.x0, y)) p.y0‖ ≤ p.G) (hG0 : 0 ≤ p.G)
    {R κ τ : ℝ} (hR : 0 ≤ R) (hτ : 0 < τ) (hκ : 1 ≤ κ) (heq : p.μ * κ = p.L)
    (t : Tuning) (hlam : 1 ≤ t.lam) (hcoef : p.L * t.lam⁻¹ ≤ p.μ / 2)
    (hm : max 1 ⌈Real.sqrt (64 * p.L / p.μ)⌉₊ ≤ t.m)
    (hJ : t.J = ⌈Real.log (1 + 2 * p.L * ((p.G + p.L * R + p.L / t.lam) / p.μ) / τ) / Real.log 2⌉₊)
    (x : p.X) (hx : ‖x - p.x0‖ ≤ R) :
    ‖QueryPlan.eval (firstOrderReply I) (estimate p t x) - gradient (hyperObjective I) x‖ ≤
      4 * p.L * κ ^ 3 / t.lam + 5 * t.lam * p.L * τ / p.μ := by
  have hgd := hg.differentiable (by norm_num)
  have hlam0 : 0 < t.lam := by linarith
  have ha : 0 ≤ t.lam⁻¹ := inv_nonneg.mpr hlam0.le
  have hb : t.lam⁻¹ ≤ 1 := (inv_le_one₀ hlam0).mpr hlam
  let D := (p.G + p.L * R + p.L / t.lam) / p.μ
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨ystar, hmin⟩ := inner_minimum_exists hf hgd hμ hf1 hsc ha hcoef x
  have hinit : ‖p.y0 - ystar‖ ≤ D := initial_penalty_radius hf hgd hμ hL.le hf0 hsc hg1 hG hlam0 x hx ystar hmin
  have hbase : ‖p.y0 - lowerSolution I x‖ ≤ D := by
    have hh := initial_base_radius hgd hμ hL.le hsc hg1 hG x hx
    apply hh.trans
    dsimp [D]
    apply (div_le_div_iff_of_pos_right hμ).mpr
    exact le_add_of_nonneg_right (div_nonneg hL.le hlam0.le)
  have hmin0 : ∀ y, innerObjective I x 0 (lowerSolution I x) ≤ innerObjective I x 0 y := by
    intro y
    simpa [innerObjective] using BilevelMinimizers.lowerSolution_minimum hgd.continuous hμ hsc x y
  have hy := innerSolve_residual hf hgd hμ hL hf1 hg1 hsc ha hb hcoef hD hτ x ystar hmin hinit t hm hJ
  have hz := innerSolve_residual hf hgd hμ hL hf1 hg1 hsc
    (lam := 0) (by simp) (by simp) (by simp; positivity) hD hτ x (lowerSolution I x) hmin0 hbase t hm hJ
  have hh := estimate_error_of_residuals hf hg hμ hL hf0 hf1 hg1 hg2 hsc hlam hcoef hκ heq hτ.le x ystar
    (QueryPlan.eval (firstOrderReply I) (innerSolve p t x t.lam))
    (QueryPlan.eval (firstOrderReply I) (innerSolve p t x 0)) hmin hy hz
  rw [BilevelExecution.eval_estimate]
  simpa only [firstOrderReply] using hh

end LongTails.Proofs.BilevelInner
