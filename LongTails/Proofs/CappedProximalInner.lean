import LongTails.Proofs.CappedProximalCertificate
import LongTails.Proofs.CappedProximalExecution
import LongTails.Proofs.CappedProximalParameters
import LongTails.Proofs.CappedProximalPotential
import LongTails.Proofs.CompositeProx

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CappedProximalInner

open LongTails.Setups.CappedHessianSimilarConvex
open LongTails.Algorithms.CappedProximal
open OracleTemplate.ComponentEnvelope
open CappedProximalOracle CappedProximalExecution CappedProximalParameters CappedProximalPotential

noncomputable def epochState (p : Params) (inst : Instance p) (center start : p.E)
    (n : ℕ) (samples : Fin n → Cohorts p) : State p.E :=
  Program.eval (reply inst) (epochSteps p center (fun i => gradient (inst.components i) start)
    n samples ⟨0, start, start⟩)

noncomputable def cohortPoint (p : Params) (inst : Instance p) (center start : p.E)
    (state : State p.E) (samples : Cohorts p) : p.E :=
  let x := predictor (innerRegularization p) state
  let g := gradient (objective inst) start + (p.s : ℝ)⁻¹ •
    (∑ j, (gradient (inst.components (samples.1 j)) x - gradient (inst.components (samples.1 j)) start)) +
      outerRegularization p • (x - center)
  (p.s : ℝ)⁻¹ • ∑ j, inst.prox (samples.2 j) (innerRegularization p + outerRegularization p)
    (x + (innerRegularization p + outerRegularization p)⁻¹ •
      (gradient (inst.components (samples.2 j)) x - g))

lemma epoch_state_zero (p : Params) (inst : Instance p) (center start : p.E)
    (samples : Fin 0 → Cohorts p) : epochState p inst center start 0 samples = ⟨0, start, start⟩ := rfl

lemma epoch_state_snoc {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center start : p.E)
    (n : ℕ) (samples : Fin n → Cohorts p) (last : Cohorts p) :
    epochState p inst center start (n + 1) (Fin.snoc samples last) =
      advance (innerRegularization p) (epochState p inst center start n samples)
        (cohortPoint p inst center start (epochState p inst center start n samples) last) := by
  unfold epochState
  rw [epoch_steps_eval_snoc]
  rw [epoch_one_eval p inst center (fun i => gradient (inst.components i) start) last _
    (add_pos (inner_regularization_pos hs hm hd) (outer_regularization_pos hm hd))]
  rw [← objective_gradient_eq h start]
  rfl

lemma epoch_eval (p : Params) (inst : Instance p) (hs : 0 < p.s) (center start : p.E)
    (samples : Fin (epochLength p) → Cohorts p) :
    Program.eval (reply inst) (LongTails.Algorithms.CappedProximal.epochPlan p center start samples) =
      (epochState p inst center start (epochLength p) samples).primal := by
  simp only [LongTails.Algorithms.CappedProximal.epochPlan, Program.eval_bind, Program.eval_map, full_snapshot_eval p inst hs]
  rfl

set_option maxHeartbeats 800000 in
lemma cohort_certificate {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ)
    (center start v : p.E) (state : State p.E) :
    let H := fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2
    let x := predictor (innerRegularization p) state
    (𝔼 sample : Cohorts p, (H (cohortPoint p inst center start state sample) - H v)) ≤
      (𝔼 sample : Cohorts p, ⟪innerRegularization p • (x - cohortPoint p inst center start state sample),
        cohortPoint p inst center start state sample - v⟫) +
      innerRegularization p / 8 * (𝔼 sample : Cohorts p, ‖x - cohortPoint p inst center start state sample‖ ^ 2) +
      (4 * p.δ ^ 2 / (p.s * innerRegularization p)) * ‖x - start‖ ^ 2 := by
  dsimp only
  have hp (f : Cohorts p → ℝ) : (𝔼 sample, f sample) =
      𝔼 η : Fin p.s → Fin p.m, 𝔼 ξ : Fin p.s → Fin p.m, f (η, ξ) :=
    Finset.expect_product Finset.univ Finset.univ _
  simp_rw [hp]
  have hc := CappedProximalCertificate.regularized_cohort_certificate h hd center
    (predictor (innerRegularization p) state) start v
    (inner_regularization_pos hs hm hd) (outer_regularization_pos hm hd) p.s hs
    (inner_regularization_threshold hs hm hd)
  dsimp only at hc
  have he : 4 / innerRegularization p *
      (p.δ ^ 2 * ‖predictor (innerRegularization p) state - start‖ ^ 2 / p.s) =
      (4 * p.δ ^ 2 / (p.s * innerRegularization p)) *
        ‖predictor (innerRegularization p) state - start‖ ^ 2 := by ring
  rw [he] at hc
  simpa only [cohortPoint] using hc

lemma epoch_potential_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center start xs : p.E)
    (hmin : ∀ y, objective inst xs + outerRegularization p / 2 * ‖xs - center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2) :
    (𝔼 ξ, potential (fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2)
      xs (epochState p inst center start (epochLength p) ξ)) ≤ ‖start - xs‖ ^ 2 := by
  have hl := inner_regularization_pos hs hm hd
  have hg : 0 ≤ 4 * p.δ ^ 2 / (p.s * innerRegularization p) := by positivity
  apply trajectory_potential_bound _ xs start hl hg hmin
    (epochState p inst center start)
    (fun n ξ => cohortPoint p inst center start (epochState p inst center start n ξ))
    (epoch_state_zero p inst center start) (epoch_state_snoc h hs hm hd center start)
    (epochLength p) ((inner_variance_weight_bound hs hm hd).trans (by norm_num))
  intro n _ ξ v
  exact cohort_certificate h hs hm hd center start v (epochState p inst center start n ξ)

lemma epoch_distance_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center start xs : p.E)
    (hmin : ∀ y, objective inst xs + outerRegularization p / 2 * ‖xs - center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2) :
    let H := fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2
    (𝔼 ξ, (H (Program.eval (reply inst)
      (LongTails.Algorithms.CappedProximal.epochPlan p center start ξ)) - H xs)) ≤
      subproblemConvexity p / 16 * ‖start - xs‖ ^ 2 := by
  dsimp only
  have hl := inner_regularization_pos hs hm hd
  have hT := epoch_length_pos hs
  have hw := trajectory_weights (innerRegularization p) (epochState p inst center start)
    (fun n ξ => cohortPoint p inst center start (epochState p inst center start n ξ))
    (fun ξ => by rw [epoch_state_zero]) (epoch_state_snoc h hs hm hd center start)
  have hg := expected_gap_from_potential _ xs (epochState p inst center start (epochLength p))
    hl (epochLength p) hT hmin (hw (epochLength p))
    (weights_bounds hl (epochLength p)).2.1 (epoch_potential_bound h hs hm hd center start xs hmin)
  have ht : (epochLength p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  have he : 4 * innerRegularization p * ‖start - xs‖ ^ 2 / (epochLength p : ℝ) ^ 2 =
      subproblemConvexity p / 16 * ‖start - xs‖ ^ 2 := by
    dsimp [innerRegularization]
    field_simp
    ring
  rw [he] at hg
  simpa only [epoch_eval p inst hs] using hg

lemma epoch_contraction {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center start xs : p.E)
    (hmin : ∀ y, objective inst xs + outerRegularization p / 2 * ‖xs - center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2) :
    let H := fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2
    (𝔼 ξ, (H (Program.eval (reply inst)
      (LongTails.Algorithms.CappedProximal.epochPlan p center start ξ)) - H xs)) ≤
      (H start - H xs) / 8 := by
  dsimp only
  have hg := epoch_distance_bound h hs hm hd center start xs hmin
  dsimp only at hg
  have hsc := regularized_strongConvex h.2.2.1 (outerRegularization p) center
  have hmin' : IsMinOn (fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2)
      Set.univ xs := fun y _ => hmin y
  have hq := OracleTemplate.Composite.strong_minimum_bound hsc hmin' start
  change subproblemConvexity p / 2 * ‖start - xs‖ ^ 2 ≤ _ at hq
  nlinarith only [hg, hq]

lemma solve_gap_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center xs : p.E)
    (hmin : ∀ y, objective inst xs + outerRegularization p / 2 * ‖xs - center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2) (k : ℕ) (start : p.E) :
    let H := fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2
    (𝔼 ξ, (H (Program.eval (reply inst) (solvePlan p center k ξ start)) - H xs)) ≤
      (1 / 8 : ℝ) ^ k * (H start - H xs) := by
  dsimp only
  induction k generalizing start with
  | zero => simp only [solvePlan, Program.eval, Fintype.expect_const, pow_zero, one_mul, le_refl]
  | succ k ih =>
    rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
    simp only [solvePlan, Program.eval_bind, Fin.cons_zero, Fin.cons_succ]
    have hp (η : Fin (epochLength p) → Cohorts p) :=
      ih (Program.eval (reply inst) (LongTails.Algorithms.CappedProximal.epochPlan p center start η))
    have ht := Finset.expect_le_expect (fun η (_ : η ∈ Finset.univ) => hp η)
    rw [← Finset.mul_expect] at ht
    have he := epoch_contraction h hs hm hd center start xs hmin
    dsimp only at he
    have hm' := mul_le_mul_of_nonneg_left he (show 0 ≤ (1 / 8 : ℝ) ^ k by positivity)
    apply ht.trans
    calc
      _ ≤ _ := hm'
      _ = _ := by rw [pow_succ]; ring

lemma solve_distance_bound {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center start xs : p.E)
    (hmin : ∀ y, objective inst xs + outerRegularization p / 2 * ‖xs - center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2) (length : ℕ) (hlength : 0 < length) :
    let H := fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2
    (𝔼 ξ, (H (Program.eval (reply inst) (solvePlan p center length ξ start)) - H xs)) ≤
      (1 / 8 : ℝ) ^ (length - 1) * (subproblemConvexity p / 16 * ‖start - xs‖ ^ 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlength)
  dsimp only
  rw [OracleTemplate.VarianceReducedWeakMinty.expect_fin_succ]
  simp only [solvePlan, Program.eval_bind, Fin.cons_zero, Fin.cons_succ]
  have hp (η : Fin (epochLength p) → Cohorts p) := solve_gap_bound h hs hm hd center xs hmin k
    (Program.eval (reply inst) (LongTails.Algorithms.CappedProximal.epochPlan p center start η))
  dsimp only at hp
  have ht := Finset.expect_le_expect (fun η (_ : η ∈ Finset.univ) => hp η)
  rw [← Finset.mul_expect] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (epoch_distance_bound h hs hm hd center start xs hmin)
    (by positivity))

lemma solve_actual_distance {p : Params} {inst : Instance p} (h : Assumptions p inst)
    (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (center start xs : p.E)
    (hmin : ∀ y, objective inst xs + outerRegularization p / 2 * ‖xs - center‖ ^ 2 ≤
      objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2) :
    let H := fun y => objective inst y + outerRegularization p / 2 * ‖y - center‖ ^ 2
    (𝔼 ξ, (H (Program.eval (reply inst) (solvePlan p center (solveLength p) ξ start)) - H xs)) ≤
      (1 / 8 : ℝ) ^ (solveLength p - 1) * (subproblemConvexity p / 16 * ‖start - xs‖ ^ 2) := by
  exact solve_distance_bound h hs hm hd center start xs hmin (solveLength p)
    (by dsimp [solveLength]; omega)

end LongTails.Proofs.CappedProximalInner
