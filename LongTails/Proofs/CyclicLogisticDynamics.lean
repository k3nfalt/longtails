import LongTails.Proofs.CyclicLogisticGroups

open scoped RealInnerProductSpace
open LongTails.Proofs.CyclicLogisticGroups
open LongTails.Proofs.BilinearLogisticDescent
open LongTails.Proofs.SoftQuadraticDynamics (weight weight_pos weight_le_one weight_ge_half)

namespace LongTails.Proofs.CyclicLogisticDynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

noncomputable def mean (m : Fin n → ℝ) (v : Fin n → E) : E :=
  (n : ℝ)⁻¹ • ∑ i, weight (m i) • v i

noncomputable def scores (z r : Fin n → E) (s : Point E) (i : Fin n) : ℝ :=
  margin (z i) (r i) s

noncomputable def risk (z r : Fin n → E) (s : Point E) : ℝ :=
  (∑ i, loss (scores z r s i)) / n

noncomputable def velocity (z r : Fin n → E) (s : Point E) : Point E :=
  let m := scores z r s
  marginGrad (mean m z) (mean m r) s

noncomputable def update (z r : Fin n → E) (η : ℝ) (s : Point E) : Point E :=
  s + η • velocity z r s

lemma velocity_eq (z r : Fin n → E) (s : Point E) :
    velocity z r s = direction (scores z r s) (fun i => marginGrad (z i) (r i) s) := by
  apply ext_inner_right ℝ
  intro v
  let m := scores z r s
  change ⟪grad (mean m z) s.fst, v.fst⟫ + ⟪grad (mean m r) s.snd, v.snd⟫ = _
  simp only [direction, real_inner_smul_left, sum_inner]
  change _ = (n : ℝ)⁻¹ * ∑ i, weight (m i) *
    (⟪grad (z i) s.fst, v.fst⟫ + ⟪grad (r i) s.snd, v.snd⟫)
  simp only [grad_inner, mean, real_inner_smul_left, sum_inner, mul_add,
    Finset.sum_add_distrib, mul_left_comm (weight _), ← Finset.mul_sum]
  ring

lemma mean_in_span (m : Fin n → ℝ) (z : Fin n → E) :
    mean m z ∈ Submodule.span ℝ (Set.range z) := by
  apply Submodule.smul_mem
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

lemma energy_update (hn : 0 < n) (z r : Fin n → E) (s : Point E) {η : ℝ} (hη : 0 ≤ η) :
    ‖update z r η s‖ ^ 2 ≤ ‖s‖ ^ 2 + 4 * η + η ^ 2 * ‖velocity z r s‖ ^ 2 := by
  simp only [update, velocity_eq]
  exact energy_step hn _ _ _ (fun i => margin_euler s (z i) (r i)) hη

lemma risk_descent (hn : 0 < n) (z r : Fin n → E) (s : Point E) {η μ M : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hμ : μ ≤ 1)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ μ)
    (hM : ‖s.fst‖ ^ 2 + μ ^ 2 * ‖s.snd‖ ^ 2 ≤ M) (hsmall : η * (1 + M) ≤ 1 / 8) :
    risk z r (update z r η s) ≤ risk z r s - η / 2 * ‖velocity z r s‖ ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hg (i : Fin n) : ‖marginGrad (z i) (r i) s‖ ≤ Real.sqrt M := by
    apply (Real.le_sqrt (norm_nonneg _) hM0).2
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖grad (z i) s.fst‖ ^ 2 + ‖grad (r i) s.snd‖ ^ 2 ≤ M
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hz i) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hr i) 2
    simp only [one_pow] at h1
    linarith [grad_norm s.fst (z i), grad_norm s.snd (r i),
      mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖s.fst‖),
      mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖s.snd‖)]
  let v := velocity z r s
  have hd := batch_descent hn (scores z r s) (fun i => margin (z i) (r i) v)
    (fun i => marginGrad (z i) (r i) s) hη hη' hg
    (fun i => by rw [← velocity_eq]; exact margin_bound v (hz i) ((hr i).trans hμ))
    (by simpa only [Real.sq_sqrt hM0] using hsmall)
  rw [← velocity_eq] at hd
  simpa only [risk, update, scores, margin_increment, v] using hd

private lemma imbalance_grad (s : CyclicLogisticGroups.Group E) (z : E) :
    s.fst * (grad z s).fst = ⟪s.snd, (grad z s).snd⟫ := by
  change _ = ⟪s.snd, s.fst • z⟫
  rw [real_inner_smul_right, real_inner_comm z s.snd]
  rfl

lemma balance_bounds (z r : Fin n → E) (s : Point E) (η : ℝ) :
    |imbalance (update z r η s).fst - imbalance s.fst| ≤ η ^ 2 * ‖velocity z r s‖ ^ 2 ∧
    |imbalance (update z r η s).snd - imbalance s.snd| ≤ η ^ 2 * ‖velocity z r s‖ ^ 2 := by
  let v := velocity z r s
  have hj : ‖v‖ ^ 2 = ‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 v
  have hb₁ := imbalance_step s.fst v.fst η (imbalance_grad s.fst (mean (scores z r s) z))
  have hb₂ := imbalance_step s.snd v.snd η (imbalance_grad s.snd (mean (scores z r s) r))
  change |imbalance (s.fst + η • v.fst) - _| ≤ η ^ 2 * ‖v‖ ^ 2 ∧
    |imbalance (s.snd + η • v.snd) - _| ≤ η ^ 2 * ‖v‖ ^ 2
  rw [hb₁, hb₂, add_sub_cancel_left, add_sub_cancel_left, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
  constructor
  · exact mul_le_mul_of_nonneg_left ((abs_imbalance_le _).trans (by linarith [sq_nonneg ‖v.snd‖]))
      (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_left ((abs_imbalance_le _).trans (by linarith [sq_nonneg ‖v.fst‖]))
      (sq_nonneg _)

end LongTails.Proofs.CyclicLogisticDynamics
