import LongTails.Proofs.QuarticFiniteSumStage
import LongTails.Proofs.QuarticStageTuning

namespace LongTails.Proofs.QuarticTrialStages

open LongTails.Algorithms.QuarticProximalTrial LongTails.Algorithms.QuarticProximal
open LongTails.Algorithms.TaylorCorrectedNewton
open LongTails.Setups.FiniteSumSmoothAndConvex
open OracleTemplate OracleTemplate.QueryPlan
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma stage_mem (oracle : Fin n × E → Reply E) (L : ℝ) {γ Δ : ℝ} (hγ : 0 < γ) (hΔ : 0 ≤ Δ) (c y0 : E)
    (J : ℕ) (seed : StageSeed n J) :
    eval oracle (stage L γ Δ c y0 J seed) ∈ Metric.closedBall y0 ((12 * Δ / γ) ^ (1 / 4 : ℝ)) := by
  rw [stage, TaylorCorrectedStep.eval_augmentPlan]
  exact TaylorCorrectedConvergence.restarts_mem _ (Real.rpow_nonneg (by positivity) _) _ y0 epochCount (J + 1) y0
    (by simpa using Real.rpow_nonneg (by positivity : 0 ≤ 12 * Δ / γ) (1 / 4 : ℝ)) seed

lemma stage_failure [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L γ Δ δ : ℝ} (hL : 0 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hLγ : L ≤ (n : ℝ) * γ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y0 v : E)
    (hmin : ∀ x, objective f v + γ * value (v - c) ≤ objective f x + γ * value (x - c))
    (hgap : (objective f y0 + γ * value (y0 - c)) -
      (objective f v + γ * value (v - c)) ≤ Δ)
    (J : ℕ) (hJ : (n : ℝ) * (1 / 2 : ℝ) ^ J ≤ δ / 2) :
    let X := fun seed : StageSeed n J =>
      eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
        (stage (L + 6 * γ) γ Δ c y0 J seed)
    (𝔼 seed, (if (objective f (X seed) + γ * value (X seed - c)) -
      (objective f v + γ * value (v - c)) > 3 * Δ / 4 then (1 : ℝ) else 0)) ≤ δ / 46 := by
  have hρ : 0 < (12 * Δ / γ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hr : ((12 * Δ / γ) ^ (1 / 4 : ℝ)) ^ 4 = 12 * Δ / γ := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4)
      (by positivity : 0 ≤ 12 * Δ / γ) (by decide)
  exact QuarticFiniteSumStage.stage_failure f hf hc hL hγ hρ hΔ hT hr c y0 v hmin hgap epochCount J
    (QuarticStageTuning.epoch_count_suffices hγ hLγ) hJ


lemma radius_contract {γ Δ : ℝ} (hγ : 0 < γ) (hΔ : 0 ≤ Δ) :
    (12 * ((3 / 4 : ℝ) * Δ) / γ) ^ (1 / 4 : ℝ) ≤
      (15 / 16 : ℝ) * (12 * Δ / γ) ^ (1 / 4 : ℝ) := by
  have h₀ : ((12 * Δ / γ) ^ (1 / 4 : ℝ)) ^ 4 = 12 * Δ / γ := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4) (by positivity : 0 ≤ 12 * Δ / γ) (by decide)
  have h₁ : ((12 * ((3 / 4 : ℝ) * Δ) / γ) ^ (1 / 4 : ℝ)) ^ 4 = 12 * ((3 / 4 : ℝ) * Δ) / γ := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4)
      (by positivity : 0 ≤ 12 * ((3 / 4 : ℝ) * Δ) / γ) (by decide)
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  rw [h₁, mul_pow, h₀]
  field_simp
  nlinarith

lemma stages_distance (oracle : Fin n × E → Reply E) (L : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (c : E) (J S : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (y : E) (seed : Fin S → StageSeed n J) :
    ‖eval oracle (stages L γ c J S Δ y seed) - y‖ ≤ 16 * (12 * Δ / γ) ^ (1 / 4 : ℝ) := by
  induction S generalizing Δ y with
  | zero => simp only [stages, eval, sub_self, norm_zero]; positivity
  | succ S ih =>
    rw [stages, eval_bind]
    let next := eval oracle (stage L γ Δ c y J (seed 0))
    have hrec := ih ((3 / 4 : ℝ) * Δ) (by positivity) next (fun i => seed i.succ)
    have hstage : ‖next - y‖ ≤ (12 * Δ / γ) ^ (1 / 4 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using stage_mem oracle L hγ hΔ c y J (seed 0)
    have htriangle := norm_sub_le_norm_sub_add_norm_sub (eval oracle (stages L γ c J S ((3 / 4 : ℝ) * Δ) next (fun i => seed i.succ))) next y
    have hr := radius_contract hγ hΔ
    change ‖eval oracle (stages L γ c J S ((3 / 4 : ℝ) * Δ) next (fun i => seed i.succ)) - y‖ ≤ _
    linarith


lemma stages_failure [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L γ δ : ℝ} (hL : 0 ≤ L) (hγ : 0 < γ) (hδ : 0 ≤ δ) (hLγ : L ≤ (n : ℝ) * γ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c v : E) (hmin : ∀ x, objective f v + γ * value (v - c) ≤ objective f x + γ * value (x - c))
    (J : ℕ) (hJ : (n : ℝ) * (1 / 2 : ℝ) ^ J ≤ δ / 2)
    (S : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) (y : E)
    (hgap : (objective f y + γ * value (y - c)) - (objective f v + γ * value (v - c)) ≤ Δ) :
    let X := fun seed : Fin S → StageSeed n J =>
      eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
        (stages (L + 6 * γ) γ c J S Δ y seed)
    (𝔼 seed, (if (objective f (X seed) + γ * value (X seed - c)) -
      (objective f v + γ * value (v - c)) > (3 / 4 : ℝ) ^ S * Δ then (1 : ℝ) else 0)) ≤ S * δ / 46 := by
  let oracle := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  let gap := fun x => (objective f x + γ * value (x - c)) - (objective f v + γ * value (v - c))
  induction S generalizing Δ y with
  | zero =>
    dsimp only
    simp only [stages, eval, pow_zero, one_mul, not_lt.mpr hgap, ↓reduceIte,
      Fintype.expect_const, Nat.cast_zero, zero_mul, zero_div, le_refl]
  | succ S ih =>
    dsimp only
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    let next := fun seed => eval oracle (stage (L + 6 * γ) γ Δ c y J seed)
    have he (seed : StageSeed n J) (seeds : Fin S → StageSeed n J) :
        eval oracle (stages (L + 6 * γ) γ c J (S + 1) Δ y (Fin.cons seed seeds)) =
          eval oracle (stages (L + 6 * γ) γ c J S ((3 / 4 : ℝ) * Δ) (next seed) seeds) := by
      rw [stages, eval_bind]
      rfl
    have hp : (3 / 4 : ℝ) ^ (S + 1) * Δ = (3 / 4 : ℝ) ^ S * ((3 / 4 : ℝ) * Δ) := by
      rw [pow_succ]
      ring
    change (𝔼 seed : StageSeed n J, 𝔼 seeds : Fin S → StageSeed n J,
      (if gap (eval oracle (stages (L + 6 * γ) γ c J (S + 1) Δ y (Fin.cons seed seeds))) >
        (3 / 4 : ℝ) ^ (S + 1) * Δ then (1 : ℝ) else 0)) ≤ (S + 1 : ℕ) * δ / 46
    simp only [he, hp]
    have hpoint (seed : StageSeed n J) :
        (𝔼 seeds : Fin S → StageSeed n J,
          (if gap (eval oracle (stages (L + 6 * γ) γ c J S ((3 / 4 : ℝ) * Δ) (next seed) seeds)) >
            (3 / 4 : ℝ) ^ S * ((3 / 4 : ℝ) * Δ) then (1 : ℝ) else 0)) ≤
          (if gap (next seed) > 3 * Δ / 4 then (1 : ℝ) else 0) + S * δ / 46 := by
      by_cases hh : gap (next seed) ≤ 3 * Δ / 4
      · simp only [not_lt.mpr hh, ↓reduceIte, zero_add]
        exact ih ((3 / 4 : ℝ) * Δ) (by positivity) (next seed) (by dsimp [gap] at hh; linarith)
      · simp only [lt_of_not_ge hh, ↓reduceIte]
        have hbound : (𝔼 seeds : Fin S → StageSeed n J,
          (if gap (eval oracle (stages (L + 6 * γ) γ c J S ((3 / 4 : ℝ) * Δ) (next seed) seeds)) >
            (3 / 4 : ℝ) ^ S * ((3 / 4 : ℝ) * Δ) then (1 : ℝ) else 0)) ≤ 1 := by
          calc
            _ ≤ (𝔼 _ : Fin S → StageSeed n J, (1 : ℝ)) :=
              Finset.expect_le_expect (s := Finset.univ) (fun _ _ => by split_ifs <;> norm_num)
            _ = 1 := Fintype.expect_const _
        exact hbound.trans (by linarith [show (0 : ℝ) ≤ S * δ / 46 by positivity])
    have hmean := Finset.expect_le_expect (s := Finset.univ) (fun seed _ => hpoint seed)
    rw [Finset.expect_add_distrib, Fintype.expect_const] at hmean
    have hfirst := stage_failure f hf hc hL hγ hΔ hLγ hT c y v hmin hgap J hJ
    change (𝔼 seed : StageSeed n J, (if gap (next seed) > 3 * Δ / 4 then (1 : ℝ) else 0)) ≤ δ / 46 at hfirst
    push_cast
    linarith

end LongTails.Proofs.QuarticTrialStages
