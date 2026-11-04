import LongTails.Proofs.TensorFreeModelConvergence
import LongTails.Proofs.AcceleratedFiniteSum

namespace LongTails.Proofs.TensorFreeModelExecution

open LongTails.Algorithms.TensorFreeModel LongTails.Algorithms.TaylorCorrectedNewton
open LongTails.Proofs.TensorFreeModel LongTails.Proofs.TensorFreeModelConvergence
open LongTails.Setups.FiniteSumSmoothAndConvex
open OracleTemplate OracleTemplate.QueryPlan
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma eval_modelRound (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (g : E) (H : E →L[ℝ] E) (L τ ρ δ tol : ℝ) (z : E) (st : ModelState E) :
    let F := objective f
    let estimate := estimateGradient g H (gradient F (z + τ • st.displacement))
      (gradient F (z - τ • st.displacement)) L τ st.displacement
    let fresh := gradient F (z + st.displacement)
    eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelRound g H L τ ρ δ tol z st) =
      if st.accepted then st
      else if ‖fresh‖ ≤ tol ∨ ‖estimate‖ ≤ ‖fresh‖ / 6 - δ
      then ⟨st.displacement, fresh, true⟩
      else ⟨stepPoint H L ρ st.displacement estimate, 0, false⟩ := by
  classical
  simp only [modelRound, eval_bind, eval_map, eval_probes f hf, snapshot,
    TaylorCorrectedStep.eval_collect, meanGradient, id_eq,
    FiniteSumThirdSmoothGeometry.objective_gradient f hf]

lemma estimate_error_ball [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L τ ρ δ : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (z s : E) (hs : s ∈ Metric.closedBall (0 : E) ρ) :
    let F := objective f
    ‖estimateGradient (gradient F z) (fderiv ℝ (gradient F) z)
      (gradient F (z + τ • s)) (gradient F (z - τ • s)) L τ s -
      exactGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (fderiv ℝ (fderiv ℝ (gradient F)) z) L s‖ ≤ δ := by
  have hh := estimate_error (FiniteSumThirdSmoothGeometry.objective_contDiff f hf) hτ
    (FiniteSumThirdSmoothGeometry.objective_third_lipschitz f hf hT) z s
  have hn : ‖s‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hs
  have hp := pow_le_pow_left₀ (norm_nonneg s) hn 3
  have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ τ * L by positivity)
  exact hh.trans ((div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 6)).trans hδ)

noncomputable def Certificate (F : E → ℝ) (L tol : ℝ) (z : E) (st : ModelState E) : Prop :=
  st.trueGradient = gradient F (z + st.displacement) ∧
    (‖st.trueGradient‖ ≤ tol ∨
      ‖exactGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (fderiv ℝ (fderiv ℝ (gradient F)) z) L st.displacement‖ ≤ ‖st.trueGradient‖ / 6)

lemma modelRound_certificate [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L τ ρ δ tol : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (z : E) (st : ModelState E)
    (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ)
    (hcert : st.accepted = true → Certificate (objective f) L tol z st) :
    let F := objective f
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelRound (gradient F z) (fderiv ℝ (gradient F) z) L τ ρ δ tol z st)
    next.accepted = true → Certificate F L tol z next := by
  classical
  dsimp only
  rw [eval_modelRound f hf]
  split_ifs with ha hb
  · intro _
    exact hcert ha
  · intro _
    refine ⟨rfl, ?_⟩
    rcases hb with hb | hb
    · exact Or.inl hb
    · right
      let F := objective f
      let estimate := estimateGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (gradient F (z + τ • st.displacement)) (gradient F (z - τ • st.displacement)) L τ st.displacement
      let model := exactGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (fderiv ℝ (fderiv ℝ (gradient F)) z) L st.displacement
      have herr : ‖estimate - model‖ ≤ δ := estimate_error_ball f hf hL hτ hT hδ z st.displacement hst
      have hh := norm_sub_norm_le model estimate
      rw [norm_sub_rev model estimate] at hh
      change ‖estimate‖ ≤ ‖gradient F (z + st.displacement)‖ / 6 - δ at hb
      change ‖model‖ ≤ ‖gradient F (z + st.displacement)‖ / 6
      linarith
  · simp

lemma modelRounds_certificate [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L τ ρ δ tol : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ) (hρ : 0 ≤ ρ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (z : E) (k : ℕ) (st : ModelState E)
    (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ)
    (hcert : st.accepted = true → Certificate (objective f) L tol z st) :
    let F := objective f
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelRounds (gradient F z) (fderiv ℝ (gradient F) z) L τ ρ δ tol z k st)
    next.accepted = true → Certificate F L tol z next := by
  induction k generalizing st with
  | zero => exact hcert
  | succ k ih =>
    dsimp only
    rw [modelRounds, eval_bind]
    exact ih _ (modelRound_mem _ _ _ _ _ _ _ hρ _ _ hst)
      (modelRound_certificate f hf hL hτ hT hδ z st hst hcert)

lemma solveModel_certificate [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L τ ρ δ tol : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ) (hρ : 0 ≤ ρ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (z : E) (K : ℕ) :
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (solveModel L τ ρ δ tol z K)
    next.accepted = true → Certificate (objective f) L tol z next := by
  have hh := modelRounds_certificate f hf (tol := tol) hL hτ hρ hT hδ z (K + 1)
    (⟨0, 0, false⟩ : ModelState E) (by simpa using hρ) (by simp)
  simpa only [solveModel, eval_bind, snapshot, TaylorCorrectedStep.eval_collect, id_eq,
    meanGradient, meanHessian, FiniteSumThirdSmoothGeometry.objective_gradient f hf,
    FiniteSumThirdSmoothGeometry.objective_hessian f hf] using hh

omit [FiniteDimensional ℝ E] in
lemma eval_modelRounds_iterate (oracle : Fin n × E → Reply E)
    (g : E) (H : E →L[ℝ] E) (L τ ρ δ tol : ℝ) (z : E) (k : ℕ) (st : ModelState E) :
    eval oracle (modelRounds g H L τ ρ δ tol z k st) =
      (fun s => eval oracle (modelRound g H L τ ρ δ tol z s))^[k] st := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    rw [modelRounds, eval_bind, ih, Function.iterate_succ_apply]

omit [FiniteDimensional ℝ E] in
lemma eval_modelRounds_succ (oracle : Fin n × E → Reply E)
    (g : E) (H : E →L[ℝ] E) (L τ ρ δ tol : ℝ) (z : E) (k : ℕ) (st : ModelState E) :
    eval oracle (modelRounds g H L τ ρ δ tol z (k + 1) st) =
      eval oracle (modelRound g H L τ ρ δ tol z (eval oracle (modelRounds g H L τ ρ δ tol z k st))) := by
  rw [eval_modelRounds_iterate, Function.iterate_succ_apply', eval_modelRounds_iterate]

lemma solveModel_mem (oracle : Fin n × E → Reply E) (L τ δ tol : ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (z : E) (K : ℕ) :
    (eval oracle (solveModel L τ ρ δ tol z K)).displacement ∈ Metric.closedBall (0 : E) ρ := by
  rw [solveModel, eval_bind]
  exact modelRounds_mem oracle _ _ L τ δ tol hρ z (K + 1) _ (by simpa using hρ)

noncomputable def maskedEnergy (H : E →L[ℝ] E) (L : ℝ) (u : E) (st : ModelState E) : ℝ :=
  if st.accepted then 0 else kernelBregman H L st.displacement u

noncomputable def maskedGap (M : E → ℝ) (u : E) (st : ModelState E) : ℝ :=
  if st.accepted then 0 else M st.displacement - M u

omit [FiniteDimensional ℝ E] in
lemma masked_step (H : E →L[ℝ] E) (L : ℝ) (M : E → ℝ) (u : E)
    (st next : ModelState E) {b C : ℝ} (hC : 0 ≤ C)
    (hA : 0 ≤ kernelBregman H L st.displacement u)
    (hkeep : st.accepted = true → next = st)
    (hstep : next.accepted = false → kernelBregman H L next.displacement u ≤
      (23 / 24 : ℝ) * kernelBregman H L st.displacement u -
      (M next.displacement - M u) / b + C) :
    maskedEnergy H L u next ≤ (23 / 24 : ℝ) * maskedEnergy H L u st - maskedGap M u next / b + C := by
  by_cases hn : next.accepted = true
  · by_cases hs : st.accepted = true
    · simpa [maskedEnergy, maskedGap, hn, hs] using hC
    · simp only [maskedEnergy, maskedGap, hn, hs, ↓reduceIte, zero_div, sub_zero]
      positivity
  · have hnf : next.accepted = false := Bool.eq_false_of_not_eq_true hn
    have hs : st.accepted ≠ true := by
      intro hh
      exact hn ((congrArg ModelState.accepted (hkeep hh)).trans hh)
    simpa [maskedEnergy, maskedGap, hn, hs] using hstep hnf

lemma objective_kernel_nonneg (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L : ℝ} (hL : 0 ≤ L) (z x u : E) :
    0 ≤ kernelBregman (fderiv ℝ (gradient (objective f)) z) L x u := by
  let F := objective f
  have hF := FiniteSumThirdSmoothGeometry.objective_contDiff f hf
  have hFc := OracleTemplate.FiniteSum.objective_convex hc
  have hH : ∀ a b, ⟪a, fderiv ℝ (gradient F) z b⟫ = ⟪fderiv ℝ (gradient F) z a, b⟫ := by
    intro a b
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) z a b).symm
  have hsupp (a b : E) : F a + ⟪gradient F a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ F b := by
    have hh := OracleTemplate.Gradient.convex_support hFc
      (fun w => (hF.differentiable (by norm_num) w).hasGradientAt) a b
    linarith
  have hp (v : E) : 0 ≤ ⟪v, fderiv ℝ (gradient F) z v⟫ := by
    have hh := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound
      ((GradientDependentLocal.gradient_contDiff_two hF).differentiable (by norm_num)) hsupp z v
    simpa only [real_inner_comm, zero_mul] using hh
  exact le_trans (by positivity) (kernel_bregman_lower _ hH hp hL x u)

lemma modelRound_masked_descent [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L τ ρ δ tol t : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (hδt : δ ≤ L * t ^ 3)
    (z u : E) (hu : u ∈ Metric.closedBall (0 : E) ρ) (st : ModelState E)
    (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ) :
    let F := objective f
    let H := fderiv ℝ (gradient F) z
    let M := modelValue (gradient F z) H (fderiv ℝ (fderiv ℝ (gradient F)) z) L
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelRound (gradient F z) H L τ ρ δ tol z st)
    maskedEnergy H L u next ≤ (23 / 24 : ℝ) * maskedEnergy H L u st -
      maskedGap M u next / (2 * (1 + 1 / Real.sqrt 2)) + 3 * L * t ^ 4 := by
  classical
  dsimp only
  apply masked_step _ L _ u st _ (by positivity) (objective_kernel_nonneg f hf hc hL z st.displacement u)
  · intro ha
    exact modelRound_preserves _ _ _ L τ ρ δ tol z st ha
  · intro hn
    rw [eval_modelRound f hf] at hn ⊢
    split_ifs at hn ⊢ with ha hb
    · simp [ha] at hn
    · let F := objective f
      let estimate := estimateGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (gradient F (z + τ • st.displacement)) (gradient F (z - τ • st.displacement)) L τ st.displacement
      have herr := (estimate_error_ball f hf hL hτ hT hδ z st.displacement hst).trans hδt
      have hh := actual_model_step (FiniteSumThirdSmoothGeometry.objective_contDiff f hf)
        (OracleTemplate.FiniteSum.objective_convex hc) hL hρ ht
        (FiniteSumThirdSmoothGeometry.objective_third_lipschitz f hf hT) z st.displacement estimate u hu herr
      convert hh using 1; ring


lemma modelRounds_masked_gap [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L τ ρ δ tol t : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (hδt : δ ≤ L * t ^ 3)
    (z u : E) (hu : u ∈ Metric.closedBall (0 : E) ρ) (st : ModelState E)
    (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ)
    (hmin : ∀ s, modelValue (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z)
      (fderiv ℝ (fderiv ℝ (gradient (objective f))) z) L u ≤
      modelValue (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z)
      (fderiv ℝ (fderiv ℝ (gradient (objective f))) z) L s) (k : ℕ) :
    let F := objective f
    let H := fderiv ℝ (gradient F) z
    let M := modelValue (gradient F z) H (fderiv ℝ (fderiv ℝ (gradient F)) z) L
    let next := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelRounds (gradient F z) H L τ ρ δ tol z (k + 1) st)
    maskedGap M u next ≤ (2 * (1 + 1 / Real.sqrt 2)) * (23 / 24 : ℝ) ^ (k + 1) *
      maskedEnergy H L u st + 24 * (2 * (1 + 1 / Real.sqrt 2)) * (3 * L * t ^ 4) := by
  let F := objective f
  let H := fderiv ℝ (gradient F) z
  let M := modelValue (gradient F z) H (fderiv ℝ (fderiv ℝ (gradient F)) z) L
  let oracle := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  let states := fun j => eval oracle (modelRounds (gradient F z) H L τ ρ δ tol z j st)
  have hmem (j : ℕ) : (states j).displacement ∈ Metric.closedBall (0 : E) ρ :=
    modelRounds_mem oracle _ _ L τ δ tol hρ z j st hst
  have hA (j : ℕ) : 0 ≤ maskedEnergy H L u (states j) := by
    unfold maskedEnergy
    split_ifs
    · exact le_rfl
    · exact objective_kernel_nonneg f hf hc hL z _ u
  have hgap (j : ℕ) : 0 ≤ maskedGap M u (states (j + 1)) := by
    unfold maskedGap
    split_ifs
    · exact le_rfl
    · exact sub_nonneg.mpr (hmin _)
  have hstep (j : ℕ) : maskedEnergy H L u (states (j + 1)) ≤
      (23 / 24 : ℝ) * maskedEnergy H L u (states j) -
      maskedGap M u (states (j + 1)) / (2 * (1 + 1 / Real.sqrt 2)) + 3 * L * t ^ 4 := by
    have hh := modelRound_masked_descent f hf hc (tol := tol) hL hτ hρ ht hT hδ hδt z u hu (states j) (hmem j)
    simpa only [states, eval_modelRounds_succ] using hh
  exact last_gap_bound (fun j => maskedEnergy H L u (states j))
    (fun j => maskedGap M u (states j)) (by positivity) (by positivity) hA hgap hstep k

end LongTails.Proofs.TensorFreeModelExecution
