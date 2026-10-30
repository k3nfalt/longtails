import LongTails.Proofs.CappedProximalInner
import LongTails.Proofs.AcceleratedFiniteSum

open Set
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CappedProximalOuter

open LongTails.Setups.CappedHessianSimilarConvex
open LongTails.Algorithms.CappedProximal
open CappedProximalOracle CappedProximalParameters CappedProximalPotential

noncomputable def exactProx (p : Params) (inst : Instance p) (center : p.E) : p.E :=
  RecursiveEnvelopeGeometry.prox (gradient (objective inst)) (outerRegularization p) center

abbrev SolveSamples (p : Params) := Fin (solveLength p) → Fin (epochLength p) → Cohorts p

noncomputable def outerPoint (p : Params) (inst : Instance p) (state : State p.E)
    (samples : SolveSamples p) : p.E :=
  OracleTemplate.ComponentEnvelope.Program.eval (reply inst)
    (solvePlan p (predictor (outerRegularization p) state) (solveLength p) samples state.primal)

noncomputable def outerState (p : Params) (inst : Instance p) (start : p.E)
    (n : ℕ) (samples : Fin n → SolveSamples p) : State p.E :=
  OracleTemplate.ComponentEnvelope.Program.eval (reply inst) (outerSteps p n samples ⟨0, start, start⟩)

lemma outer_state_zero (p : Params) (inst : Instance p) (start : p.E)
    (samples : Fin 0 → SolveSamples p) : outerState p inst start 0 samples = ⟨0, start, start⟩ := rfl

lemma outer_state_snoc (p : Params) (inst : Instance p) (start : p.E) (n : ℕ)
    (samples : Fin n → SolveSamples p) (last : SolveSamples p) :
    outerState p inst start (n + 1) (Fin.snoc samples last) =
      advance (outerRegularization p) (outerState p inst start n samples)
        (outerPoint p inst (outerState p inst start n samples) last) := by
  unfold outerState
  rw [CappedProximalExecution.outer_steps_eval_snoc, CappedProximalExecution.outer_one_eval]
  rfl

lemma exact_prox_field {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center : p.E) :
    gradient (objective inst) (exactProx p inst center) =
      outerRegularization p • (center - exactProx p inst center) := by
  obtain ⟨xs, hxs, _⟩ := h.2.2.2.2.2
  exact OracleTemplate.ComponentEnvelope.component_prox_field (objective_hasGradient h)
    (outer_regularization_pos hm hd) (fun y => hxs (mem_univ y)) center

lemma exact_prox_minimum {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center y : p.E) :
    objective inst (exactProx p inst center) + outerRegularization p / 2 *
      ‖exactProx p inst center - center‖ ^ 2 ≤
        objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2 := by
  obtain ⟨xs, hxs, _⟩ := h.2.2.2.2.2
  have hc : ConvexOn ℝ univ (objective inst) := OracleTemplate.FiniteSum.objective_convex h.1
  have hr := outer_regularization_pos hm hd
  have hh := OracleTemplate.ComponentEnvelope.component_prox_minimum hc (objective_hasGradient h)
    hr (fun y => hxs (mem_univ y)) center y
  change (objective inst (exactProx p inst center) + outerRegularization p / 2 *
    ‖exactProx p inst center - center‖ ^ 2) +
    outerRegularization p / 2 * ‖y - exactProx p inst center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2 at hh
  have hn : 0 ≤ outerRegularization p / 2 * ‖y - exactProx p inst center‖ ^ 2 := by positivity
  linarith

lemma exact_prox_distance {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center xs : p.E) (hmin : ∀ y, objective inst xs ≤ objective inst y) :
    ‖exactProx p inst center - xs‖ ^ 2 ≤ ‖center - xs‖ ^ 2 := by
  let prox := exactProx p inst center
  have hr := outer_regularization_pos hm hd
  have hc : ConvexOn ℝ univ (objective inst) := OracleTemplate.FiniteSum.objective_convex h.1
  have hh := OracleTemplate.Gradient.convex_support hc (objective_hasGradient h) prox xs
  rw [exact_prox_field h hm hd center, real_inner_smul_left] at hh
  change outerRegularization p * ⟪center - prox, xs - prox⟫ ≤ _ at hh
  have hi : ⟪center - prox, xs - prox⟫ = -⟪center - prox, prox - xs⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hi] at hh
  have hp : 0 ≤ outerRegularization p * ⟪center - prox, prox - xs⟫ := by linarith [hmin prox]
  have hn : 0 ≤ ⟪center - prox, prox - xs⟫ := (mul_nonneg_iff_of_pos_left hr).mp hp
  change ‖prox - xs‖ ^ 2 ≤ ‖center - xs‖ ^ 2
  rw [show center - xs = (center - prox) + (prox - xs) by abel, norm_add_sq_real]
  nlinarith [sq_nonneg ‖center - prox‖]

lemma inexact_prox_comparison {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center z v : p.E) :
    let rho := outerRegularization p
    let prox := exactProx p inst center
    let H := fun y => objective inst y + rho / 2 * ‖y - center‖ ^ 2
    objective inst z - objective inst v ≤
      ⟪rho • (center - z), z - v⟫ + rho * ⟪z - prox, z - v⟫ -
        rho / 2 * ‖z - prox‖ ^ 2 + (H z - H prox) := by
  dsimp only
  let prox := exactProx p inst center
  have hc : ConvexOn ℝ univ (objective inst) := OracleTemplate.FiniteSum.objective_convex h.1
  have hs := OracleTemplate.Gradient.convex_support hc (objective_hasGradient h) prox v
  rw [exact_prox_field h hm hd center, real_inner_smul_left] at hs
  have hnorm : ‖z - center‖ ^ 2 = ‖prox - center‖ ^ 2 -
      2 * ⟪center - prox, z - prox⟫ + ‖z - prox‖ ^ 2 := by
    rw [show z - center = (prox - center) + (z - prox) by abel, norm_add_sq_real]
    have hi : ⟪prox - center, z - prox⟫ = -⟪center - prox, z - prox⟫ := by
      rw [← inner_neg_left, neg_sub]
    rw [hi]
    ring
  have he :
      ⟪outerRegularization p • (center - z), z - v⟫ +
        outerRegularization p * ⟪z - prox, z - v⟫ - outerRegularization p / 2 * ‖z - prox‖ ^ 2 +
        ((objective inst z + outerRegularization p / 2 * ‖z - center‖ ^ 2) -
          (objective inst prox + outerRegularization p / 2 * ‖prox - center‖ ^ 2)) =
      objective inst z - objective inst prox - outerRegularization p * ⟪center - prox, v - prox⟫ := by
    rw [hnorm]
    simp only [real_inner_smul_left, inner_sub_left, inner_sub_right]
    ring
  change objective inst z - objective inst v ≤ _
  change outerRegularization p * ⟪center - prox, v - prox⟫ ≤ _ at hs
  rw [he]
  linarith

lemma prox_error_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center z : p.E) :
    subproblemConvexity p / 2 * ‖z - exactProx p inst center‖ ^ 2 ≤
      (objective inst z + outerRegularization p / 2 * ‖z - center‖ ^ 2) -
        (objective inst (exactProx p inst center) + outerRegularization p / 2 *
          ‖exactProx p inst center - center‖ ^ 2) := by
  exact OracleTemplate.Composite.strong_minimum_bound
    (regularized_strongConvex h.2.2.1 (outerRegularization p) center)
    (fun y _ => exact_prox_minimum h hm hd center y) z

lemma outer_step_potential {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (xs : p.E) (hmin : ∀ y, objective inst xs ≤ objective inst y)
    (state : State p.E) (hw : 0 ≤ state.weight) (z : p.E) {theta : ℝ} (ht : 0 < theta) :
    let rho := outerRegularization p
    let a := nextWeight rho state.weight
    let x := predictor rho state
    let prox := exactProx p inst x
    let H := fun y => objective inst y + rho / 2 * ‖y - x‖ ^ 2
    potential (objective inst) xs (advance rho state z) ≤
      (1 + a * rho * theta) * potential (objective inst) xs state +
        (state.weight + a + a * rho / (subproblemConvexity p * theta)) * (H z - H prox) := by
  dsimp only
  have hr := outer_regularization_pos hm hd
  have hq := subproblem_convexity_pos hm hd
  have ha := CappedProximalGeometry.accelerated_weight_properties hr hw
  have hy := inexact_prox_comparison h hm hd (predictor (outerRegularization p) state) z state.primal
  have hs := inexact_prox_comparison h hm hd (predictor (outerRegularization p) state) z xs
  have he := prox_error_bound h hm hd (predictor (outerRegularization p) state) z
  dsimp only at hy hs
  have hp := CappedProximalGeometry.proximal_potential_young hw ha.1.le hr hq ht rfl
    (by simpa only [mul_comm] using ha.2) (predictor_identity hr state hw) rfl
    (hmin state.primal) he hy hs
  simpa only [potential, advance, smul_smul, nextWeight] using! hp

lemma outer_step_expected {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (xs : p.E)
    (hmin : ∀ y, objective inst xs ≤ objective inst y) (state : State p.E)
    (hw : 0 ≤ state.weight) {theta : ℝ} (ht : 0 < theta) :
    let rho := outerRegularization p
    let a := nextWeight rho state.weight
    let beta := (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (solveLength p - 1)
    let prox := exactProx p inst (predictor rho state)
    (𝔼 sample : SolveSamples p, potential (objective inst) xs
      (advance rho state (outerPoint p inst state sample))) ≤
      (1 + a * rho * theta) * potential (objective inst) xs state +
        (state.weight + a + a * rho / (subproblemConvexity p * theta)) *
          (subproblemConvexity p * beta * ‖state.primal - prox‖ ^ 2) := by
  dsimp only
  have hr := outer_regularization_pos hm hd
  have hq := subproblem_convexity_pos hm hd
  have ha : 0 < nextWeight (outerRegularization p) state.weight :=
    (CappedProximalGeometry.accelerated_weight_properties hr hw).1
  have hp (sample : SolveSamples p) := outer_step_potential h hm hd xs hmin state hw
    (outerPoint p inst state sample) ht
  dsimp only at hp
  have havg := Finset.expect_le_expect (fun sample (_ : sample ∈ Finset.univ) => hp sample)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at havg
  have hsolve := CappedProximalInner.solve_actual_distance h hs hm hd
    (predictor (outerRegularization p) state) state.primal
    (exactProx p inst (predictor (outerRegularization p) state))
    (exact_prox_minimum h hm hd (predictor (outerRegularization p) state))
  dsimp only at hsolve
  have hcoef : 0 ≤ state.weight + nextWeight (outerRegularization p) state.weight +
      nextWeight (outerRegularization p) state.weight * outerRegularization p /
        (subproblemConvexity p * theta) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsolve hcoef
  have htotal := havg.trans (add_le_add le_rfl hscaled)
  convert htotal using 1; ring

lemma expected_warm_distance {p : Params} {inst : Instance p} {Ω : Type*} [Fintype Ω]
    (h : Assumptions p inst) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (xs : p.E)
    (hmin : ∀ y, objective inst xs ≤ objective inst y) (state : Ω → State p.E)
    {B : ℝ} (hB : 0 ≤ B) (hw : ∀ ω, (state ω).weight = B) :
    (𝔼 ω, ‖(state ω).primal - exactProx p inst (predictor (outerRegularization p) (state ω))‖ ^ 2) ≤
      2 * (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) +
        2 * max (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2)
          (2 * (𝔼 ω, potential (objective inst) xs (state ω))) := by
  let R := max (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2)
    (2 * (𝔼 ω, potential (objective inst) xs (state ω)))
  have hdual := expected_dual_distance (objective inst) xs state
    (fun ω => by rw [hw]; exact hB) hmin
  have hy : (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) ≤ R := le_max_left _ _
  have hv : (𝔼 ω, ‖(state ω).dual - xs‖ ^ 2) ≤ R := hdual.trans (le_max_right _ _)
  have hquery := expected_predictor_distance state xs (outer_regularization_pos hm hd) hB hw hy hv
  have hp (ω : Ω) :
      ‖(state ω).primal - exactProx p inst (predictor (outerRegularization p) (state ω))‖ ^ 2 ≤
        2 * ‖(state ω).primal - xs‖ ^ 2 + 2 * ‖predictor (outerRegularization p) (state ω) - xs‖ ^ 2 := by
    have ha := anchor_distance_bound (state ω).primal
      (exactProx p inst (predictor (outerRegularization p) (state ω))) xs
    have hb := exact_prox_distance h hm hd (predictor (outerRegularization p) (state ω)) xs hmin
    linarith
  have ht := Finset.expect_le_expect (fun ω (_ : ω ∈ Finset.univ) => hp ω)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at ht
  change _ ≤ 2 * (𝔼 ω, ‖(state ω).primal - xs‖ ^ 2) + 2 * R
  linarith

lemma outer_coefficients_sum {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    let rho := outerRegularization p
    let q := subproblemConvexity p
    let beta := (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (solveLength p - 1)
    let theta := 1 / (1024 * (outerLength p : ℝ) ^ 2)
    (∑ n ∈ Finset.range (outerLength p),
      (nextWeight rho (weights rho n) * rho * theta +
        8 * ((weights rho (n + 1) + nextWeight rho (weights rho n) * rho / (q * theta)) * (q * beta)))) ≤ 1 / 4 := by
  dsimp only
  let rho := outerRegularization p
  let q := subproblemConvexity p
  let beta := (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (solveLength p - 1)
  let theta := 1 / (1024 * (outerLength p : ℝ) ^ 2)
  have hr : 0 < rho := outer_regularization_pos hm hd
  have hq : 0 < q := subproblem_convexity_pos hm hd
  have hk : 0 < (outerLength p : ℝ) := by exact_mod_cast outer_length_pos hm hd
  have hk1 : 1 ≤ (outerLength p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (outer_length_pos hm hd)
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have he (n : ℕ) :
      nextWeight rho (weights rho n) * rho * theta +
        8 * ((weights rho (n + 1) + nextWeight rho (weights rho n) * rho / (q * theta)) * (q * beta)) =
      (8 * q * beta) * weights rho (n + 1) +
        (rho * (theta + 8 * beta / theta)) * nextWeight rho (weights rho n) := by
    field_simp
    ring
  change (∑ n ∈ Finset.range (outerLength p),
    (nextWeight rho (weights rho n) * rho * theta +
      8 * ((weights rho (n + 1) + nextWeight rho (weights rho n) * rho / (q * theta)) * (q * beta)))) ≤ _
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, weights_increment_sum]
  have h1 := mul_le_mul_of_nonneg_left (weights_sum_bound hr (outerLength p))
    (show 0 ≤ 8 * q * beta by positivity)
  have h2 := mul_le_mul_of_nonneg_left (weights_bounds hr (outerLength p)).2.2
    (show 0 ≤ rho * (theta + 8 * beta / theta) by positivity)
  apply (add_le_add h1 h2).trans
  exact outer_error_coefficient hr hq hk1 hb (by dsimp [q, rho, subproblemConvexity]; linarith)
    (solve_error_bound hm hd)

set_option maxHeartbeats 1200000 in
lemma outer_potential_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (start xs : p.E)
    (hmin : ∀ y, objective inst xs ≤ objective inst y) :
    (𝔼 ξ, potential (objective inst) xs (outerState p inst start (outerLength p) ξ)) ≤ ‖start - xs‖ ^ 2 := by
  let rho := outerRegularization p
  let q := subproblemConvexity p
  let beta := (1 / 16 : ℝ) * (1 / 8 : ℝ) ^ (solveLength p - 1)
  let theta := 1 / (1024 * (outerLength p : ℝ) ^ 2)
  have hr : 0 < rho := outer_regularization_pos hm hd
  have hq : 0 < q := subproblem_convexity_pos hm hd
  have hk : 0 < (outerLength p : ℝ) := by exact_mod_cast outer_length_pos hm hd
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hw := trajectory_weights rho (outerState p inst start)
    (fun n ξ => outerPoint p inst (outerState p inst start n ξ))
    (fun ξ => by rw [outer_state_zero]) (outer_state_snoc p inst start)
  let P := fun n => (𝔼 ξ, potential (objective inst) xs (outerState p inst start n ξ))
  let Y := fun n => (𝔼 ξ, ‖(outerState p inst start n ξ).primal - xs‖ ^ 2)
  let W := fun n => (𝔼 ξ, ‖(outerState p inst start n ξ).primal -
    exactProx p inst (predictor rho (outerState p inst start n ξ))‖ ^ 2)
  let u := fun n => nextWeight rho (weights rho n) * rho * theta
  let v := fun n => (weights rho (n + 1) + nextWeight rho (weights rho n) * rho / (q * theta)) * (q * beta)
  have hu (n : ℕ) : 0 ≤ u n := by
    have ha : 0 < nextWeight rho (weights rho n) :=
      (CappedProximalGeometry.accelerated_weight_properties hr (weights_bounds hr n).1).1
    dsimp [u]
    positivity
  have hv (n : ℕ) : 0 ≤ v n := by
    have ha : 0 < nextWeight rho (weights rho n) :=
      (CappedProximalGeometry.accelerated_weight_properties hr (weights_bounds hr n).1).1
    have hA := (weights_bounds hr (n + 1)).1
    dsimp [v]
    positivity
  have hp0 : P 0 ≤ ‖start - xs‖ ^ 2 / 2 := by
    simp only [P, outer_state_zero, potential, zero_mul, zero_add, Fintype.expect_const, le_refl]
  have hy0 : Y 0 ≤ ‖start - xs‖ ^ 2 := by simp only [Y, outer_state_zero, Fintype.expect_const, le_refl]
  have hsum : ∑ n ∈ Finset.range (outerLength p), (u n + 8 * v n) ≤ 1 / 2 :=
    (outer_coefficients_sum hm hd).trans (by norm_num)
  have hpstep (n : ℕ) (_hn : n < outerLength p) : P (n + 1) ≤ (1 + u n) * P n + v n * W n := by
    dsimp only [P]
    rw [CappedProximalSampling.uniform_snoc]
    simp_rw [outer_state_snoc]
    have hp (ξ : Fin n → SolveSamples p) := outer_step_expected h hs hm hd xs hmin
      (outerState p inst start n ξ) (by rw [hw]; exact (weights_bounds hr n).1) ht
    dsimp only at hp
    have havg := Finset.expect_le_expect (fun ξ (_ : ξ ∈ Finset.univ) => hp ξ)
    simp only [hw, Finset.expect_add_distrib, ← Finset.mul_expect] at havg
    simpa only [P, W, u, v, weights, rho, q, beta, theta, mul_assoc] using! havg
  have hy (n : ℕ) (_hn : n < outerLength p) : Y (n + 1) ≤ max (Y n) (2 * P (n + 1)) :=
    trajectory_primal_bound (objective inst) xs hr hmin (outerState p inst start)
      (fun n ξ => outerPoint p inst (outerState p inst start n ξ)) hw (outer_state_snoc p inst start) n
  have hwarm (n : ℕ) (_hn : n < outerLength p) : W n ≤ 2 * Y n + 2 * max (Y n) (2 * P n) :=
    expected_warm_distance h hm hd xs hmin (outerState p inst start n) (weights_bounds hr n).1 (hw n)
  exact (finite_outer_bootstrap P Y W u v (outerLength p) (sq_nonneg _) hu hv hp0 hy0 hsum
    hpstep hy hwarm (outerLength p) le_rfl).1

lemma outer_distance_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (start xs : p.E)
    (hmin : ∀ y, objective inst xs ≤ objective inst y) :
    (𝔼 ξ, (objective inst (outerState p inst start (outerLength p) ξ).primal - objective inst xs)) ≤
      p.μ / 16 * ‖start - xs‖ ^ 2 := by
  have hr := outer_regularization_pos hm hd
  have hw := trajectory_weights (outerRegularization p) (outerState p inst start)
    (fun n ξ => outerPoint p inst (outerState p inst start n ξ))
    (fun ξ => by rw [outer_state_zero]) (outer_state_snoc p inst start)
  have hg := expected_gap_from_potential (objective inst) xs (outerState p inst start (outerLength p))
    hr (outerLength p) (outer_length_pos hm hd) hmin (hw (outerLength p))
    (weights_bounds hr (outerLength p)).2.1 (outer_potential_bound h hs hm hd start xs hmin)
  have ht := mul_le_mul_of_nonneg_right (outer_accuracy_scale hm hd) (sq_nonneg ‖start - xs‖)
  apply hg.trans
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using ht

lemma outer_contraction {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (start xs : p.E)
    (hmin : ∀ y, objective inst xs ≤ objective inst y) :
    (𝔼 ξ, (objective inst (outerState p inst start (outerLength p) ξ).primal - objective inst xs)) ≤
      (objective inst start - objective inst xs) / 8 := by
  have hg := outer_distance_bound h hs hm hd start xs hmin
  have hmin' : IsMinOn (objective inst) Set.univ xs := fun y _ => hmin y
  have hq := OracleTemplate.Composite.strong_minimum_bound h.2.2.1 hmin' start
  nlinarith only [hg, hq]

set_option synthInstance.maxSize 256 in
lemma restarts_gap_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (xs : p.E)
    (hmin : ∀ y, objective inst xs ≤ objective inst y) (k : ℕ) (start : p.E) :
    (𝔼 ξ, (objective inst (OracleTemplate.ComponentEnvelope.Program.eval (reply inst)
      (restartsPlan p k ξ start)) - objective inst xs)) ≤
      (1 / 8 : ℝ) ^ k * (objective inst start - objective inst xs) := by
  induction k generalizing start with
  | zero => simp only [restartsPlan, OracleTemplate.ComponentEnvelope.Program.eval,
      Fintype.expect_const, pow_zero, one_mul, le_refl]
  | succ k ih =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    simp only [restartsPlan, OracleTemplate.ComponentEnvelope.Program.eval_bind, Fin.cons_zero, Fin.cons_succ]
    have hp (η : Fin (outerLength p) → SolveSamples p) :=
      ih (outerState p inst start (outerLength p) η).primal
    have ht := Finset.expect_le_expect (fun η (_ : η ∈ Finset.univ) => hp η)
    rw [← Finset.mul_expect] at ht
    have he := outer_contraction h hs hm hd start xs hmin
    have hm' := mul_le_mul_of_nonneg_left he (show 0 ≤ (1 / 8 : ℝ) ^ k by positivity)
    apply ht.trans
    calc
      _ ≤ _ := hm'
      _ = _ := by rw [pow_succ]; ring

set_option synthInstance.maxSize 256 in
lemma plan_accuracy {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (hD : 0 ≤ p.Δ) (he : 0 < p.ε)
    (xs : p.E) (hmin : ∀ y, objective inst xs ≤ objective inst y)
    (hgap : objective inst p.x0 - objective inst xs ≤ p.Δ) :
    (𝔼 ξ : Seeds p, (objective inst (OracleTemplate.ComponentEnvelope.Program.eval (reply inst)
      (plan p ξ)) - objective inst xs)) ≤ p.ε := by
  have hb := restarts_gap_bound h hs hm hd xs hmin (restartCount p) p.x0
  exact hb.trans ((mul_le_mul_of_nonneg_left hgap (by positivity)).trans (restart_accuracy hD he))

open MeasureTheory in
set_option synthInstance.maxSize 256 in
lemma successful_execution {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (hD : 0 ≤ p.Δ) (he : 0 < p.ε)
    (oracle : OracleTemplate.Oracle (Query p) (Fin p.m → p.E))
    (hanswer : ∀ history query seed, oracle.answer history (0, query) seed = reply inst query)
    (budget : ℕ) (hbudget : restartCount p * outerLength p * solveLength p *
      (snapshotLength p + 3 * epochLength p) ≤ budget) :
    spec.successful p inst
      (fun seed : Seeds p × ((k : ℕ) → oracle.Seed k) => output p oracle budget seed.1 seed.2)
      ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩ := by
  obtain ⟨xs, hmin, hgap⟩ := h.2.2.2.2.2
  let out := fun seed : Seeds p => OracleTemplate.ComponentEnvelope.Program.eval (reply inst) (plan p seed)
  have hexec (seed : Seeds p) (ξ : (k : ℕ) → oracle.Seed k) :
      output p oracle budget seed ξ = out seed :=
    CappedProximalExecution.output_eq_eval p inst oracle hanswer budget seed ξ hbudget
  change Measurable (fun seed : Seeds p × ((k : ℕ) → oracle.Seed k) => output p oracle budget seed.1 seed.2) ∧ _
  simp only [hexec]
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, xs, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : Seeds p => objective inst (out seed) - objective inst xs)
        (μ := (PMF.uniformOfFintype (Seeds p)).toMeasure))
  · change (∫ seed : Seeds p × ((k : ℕ) → oracle.Seed k),
        objective inst (out seed.1) - objective inst xs
        ∂(PMF.uniformOfFintype (Seeds p)).toMeasure.prod
          (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun seed => objective inst (out seed) - objective inst xs)]
    simp only [probReal_univ, one_smul]
    rw [OracleTemplate.FiniteSum.uniform_integral]
    exact plan_accuracy h hs hm hd hD he xs (fun y => hmin (Set.mem_univ y)) hgap

end LongTails.Proofs.CappedProximalOuter
