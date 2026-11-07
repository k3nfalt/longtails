import LongTails.Proofs.SurjectiveProxLinearGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearMoreau

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearGeometry
open OracleTemplate.WeaklyConvexHeavyTailed

noncomputable def moreauPoint (p : Params) (I : Problem p) (x : p.E) : p.E := by
  classical
  exact if h : ∃ z, ∀ y, penalty p I z + gamma p * ‖z - x‖ ^ 2 ≤
      penalty p I y + gamma p * ‖y - x‖ ^ 2 then Classical.choose h else x

noncomputable def envelope (p : Params) (I : Problem p) (x : p.E) : ℝ :=
  penalty p I (moreauPoint p I x) + gamma p * ‖moreauPoint p I x - x‖ ^ 2

lemma moreau_exists (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) :
    ∃ z, ∀ y, penalty p I z + gamma p * ‖z - x‖ ^ 2 ≤
      penalty p I y + gamma p * ‖y - x‖ ^ 2 := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  obtain ⟨z, _, hz⟩ := exists_prox isClosed_univ (penalty_weak_subgradient p I hp H)
    (fun y _ => penaltySubgradient_bound p I hp H y)
    (valid_tuning_positive p hp).2.1
    (by positivity : 0 ≤ p.H + p.H * (rho p * p.m)) (Set.mem_univ x) x
  exact ⟨z, fun y => hz (Set.mem_univ y)⟩

lemma moreauPoint_spec (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x y : p.E) :
    envelope p I x ≤ penalty p I y + gamma p * ‖y - x‖ ^ 2 := by
  have h := moreau_exists p I hp H x
  unfold envelope moreauPoint
  rw [dite_eq_left h]
  exact Classical.choose_spec h y

lemma moreauPoint_growth (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x y : p.E) :
    envelope p I x + gamma p / 2 * ‖y - moreauPoint p I x‖ ^ 2 ≤
      penalty p I y + gamma p * ‖y - x‖ ^ 2 := by
  apply growth_of_isMinOn (convex_univ) (penalty_weak_subgradient p I hp H)
    (valid_tuning_positive p hp).2.1 (Set.mem_univ _) _ (Set.mem_univ _)
  intro z _
  exact moreauPoint_spec p I hp H x z

lemma envelope_le_penalty (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) : envelope p I x ≤ penalty p I x := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    using moreauPoint_spec p I hp H x x

lemma envelope_gap (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) : envelope p I p.x0 - envelope p I x ≤ p.Δ := by
  have h := envelope_le_penalty p I hp H p.x0
  have hgap := H.initialGap (moreauPoint p I x)
  have hg := (valid_tuning_positive p hp).2.1.le
  have hn : 0 ≤ gamma p * ‖moreauPoint p I x - x‖ ^ 2 := by positivity
  unfold envelope at *
  linarith

lemma exact_model_prox_distance (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) :
    ‖x + exactModelStep p I x - moreauPoint p I x‖ ^ 2 ≤
      3 / 5 * ‖moreauPoint p I x - x‖ ^ 2 - 1 / 5 * ‖exactModelStep p I x‖ ^ 2 := by
  have hy := (abs_le.mp (penalty_model_abs_error p I hp H x
    (x + exactModelStep p I x))).2
  have hz := (abs_le.mp (penalty_model_abs_error p I hp H x (moreauPoint p I x))).1
  have hgrowth := moreauPoint_growth p I hp H x (x + exactModelStep p I x)
  have hm := linearModel_strong_growth p I hp x (moreauPoint p I x)
  have hh := ProxLinearEnvelope.model_prox_distance
    (F := penalty p I) (model := linearModel p I x)
    (x := x) (y := x + exactModelStep p I x) (z := moreauPoint p I x)
    (valid_tuning_positive p hp).2.1
    (by linarith) (by linarith)
    (by simpa only [add_sub_cancel_left] using hm)
    (by simpa only [envelope] using hgrowth)
  simpa only [add_sub_cancel_left] using hh

lemma envelope_perturbed_descent (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x s : p.E) {θ : ℝ} (hθ : 0 ≤ θ) (hθmax : θ ≤ 1 / 10) :
    envelope p I (x + θ • s) ≤ envelope p I x -
      gamma p * θ * ‖exactModelStep p I x‖ ^ 2 +
      6 * gamma p * θ * ‖s - exactModelStep p I x‖ ^ 2 := by
  have hdist := exact_model_prox_distance p I hp H x
  have hh := ProxLinearEnvelope.relaxed_envelope_step
    (x := x) (y := x + exactModelStep p I x) (z := moreauPoint p I x)
    (yhat := x + s) (γ := gamma p) (θ := θ)
    (φold := envelope p I x) (φnew := envelope p I (x + θ • s))
    (Fz := penalty p I (moreauPoint p I x))
    (valid_tuning_positive p hp).2.1.le hθ hθmax
    (by simpa only [add_sub_cancel_left] using hdist) rfl (by
      simpa only [add_sub_cancel_left, norm_sub_rev (moreauPoint p I x)] using
        moreauPoint_spec p I hp H (x + θ • s) (moreauPoint p I x))
  simpa only [add_sub_cancel_left, add_sub_add_left_eq_sub] using hh

lemma continuous_moreauPoint (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : Continuous (moreauPoint p I) := by
  have h : LipschitzWith 2 (moreauPoint p I) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm, NNReal.coe_ofNat]
      apply prox_lipschitz convex_univ (penalty_weak_subgradient p I hp H)
        (valid_tuning_positive p hp).2.1 (Set.mem_univ _) _ (Set.mem_univ _) _
      · intro z _; exact moreauPoint_spec p I hp H x z
      · intro z _; exact moreauPoint_spec p I hp H y z
  exact h.continuous

lemma continuous_envelope (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : Continuous (envelope p I) := by
  have hf : Continuous I.f := continuous_iff_continuousAt.mpr fun x =>
    (H.hasGradient x).differentiableAt.continuousAt
  have hc := constraints_continuous p I H
  have hz := continuous_moreauPoint p I hp H
  unfold envelope penalty
  fun_prop

end LongTails.Proofs.SurjectiveProxLinearMoreau
