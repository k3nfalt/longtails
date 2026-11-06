import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.ScheduleBlockScalar

namespace LongTails.Proofs.GdSnapshotDynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma residual_difference_bound {g : E → E} {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ ρ * ‖x - y‖)
    (u x y : E) (hx : ‖x - u‖ ≤ R) (hy : ‖y - u‖ ≤ R) :
    ‖g y - g x - fderiv ℝ g u (y - x)‖ ≤ ρ * R * ‖y - x‖ := by
  let F := fun z => g z - fderiv ℝ g u (z - u)
  have hF (z : E) : HasFDerivAt F (fderiv ℝ g z - fderiv ℝ g u) z := by
    have ha := (fderiv ℝ g u).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const u)
    have hb := (hg z).hasFDerivAt.sub ha
    simp only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] at hb
    convert hb using 1
  have hb (z : E) (hz : z ∈ Metric.closedBall u R) :
      ‖fderiv ℝ g z - fderiv ℝ g u‖ ≤ ρ * R :=
    (hH z u).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) hρ)
  have hh := (convex_closedBall u R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hF z).hasFDerivWithinAt) hb
    (show x ∈ Metric.closedBall u R by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
    (show y ∈ Metric.closedBall u R by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
  have he : F y - F x = g y - g x - fderiv ℝ g u (y - x) := by
    dsimp [F]
    simp only [map_sub]
    abel
  rw [he] at hh
  exact hh

lemma gd_gradient_forcing {g : E → E} {ρ R η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 ≤ η)
    (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ ρ * ‖x - y‖)
    (u x : E) (hx : ‖x - u‖ ≤ R) (hy : ‖x - η • g x - u‖ ≤ R) :
    ‖g (x - η • g x) - (g x - η • fderiv ℝ g u (g x))‖ ≤
      η * ρ * R * ‖g x‖ := by
  have hh := residual_difference_bound hρ hg hH u x (x - η • g x) hx hy
  have he : x - η • g x - x = -(η • g x) := by abel
  rw [he, map_neg, map_smul, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hh
  convert hh using 1 <;> first | congr 1; module | ring

lemma model_gradient_step (g : E → E) (H : E →L[ℝ] E) (z x : E) (η : ℝ) :
    g z + H (x - η • g x - z) =
      (g z + H (x - z)) - η • H ((g z + H (x - z)) +
        (g x - g z - H (x - z))) := by
  have he : (g z + H (x - z)) + (g x - g z - H (x - z)) = g x := by abel
  rw [he]
  have hx : x - η • g x - z = (x - z) - η • g x := by abel
  rw [hx, map_sub, map_smul]
  abel

lemma scalar_forced_solution_prefix (a u v : ℕ → ℝ) (lam : ℝ) (n : ℕ)
    (hu : ∀ i < n, u (i + 1) = (1 - a i * lam) * u i + a i * v i) :
    u n = OracleTemplate.ScheduleBlock.pr a lam n * u 0 +
      OracleTemplate.ScheduleBlock.errResp a lam v n := by
  induction n with
  | zero => simp [OracleTemplate.ScheduleBlock.pr, OracleTemplate.ScheduleBlock.win,
      OracleTemplate.ScheduleBlock.errResp]
  | succ n ih =>
    rw [hu n (by omega), OracleTemplate.ScheduleBlock.pr_succ,
      OracleTemplate.ScheduleBlock.errResp_succ, ih (fun i hi => hu i (by omega))]
    ring

lemma scalar_forced_solution (a u v : ℕ → ℝ) (lam : ℝ)
    (hu : ∀ i, u (i + 1) = (1 - a i * lam) * u i + a i * v i) (n : ℕ) :
    u n = OracleTemplate.ScheduleBlock.pr a lam n * u 0 +
      OracleTemplate.ScheduleBlock.errResp a lam v n := by
  induction n with
  | zero => simp [OracleTemplate.ScheduleBlock.pr, OracleTemplate.ScheduleBlock.win,
      OracleTemplate.ScheduleBlock.errResp]
  | succ n ih =>
    rw [hu, OracleTemplate.ScheduleBlock.pr_succ,
      OracleTemplate.ScheduleBlock.errResp_succ, ih]
    ring

lemma diagonal_forcing_square_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w v : ι → κ → ℝ) (W B : ℝ)
    (hw : ∀ i j, |w i j| ≤ W) (hv : ∀ i, ∑ j, v i j ^ 2 ≤ B ^ 2) :
    ∑ j, (∑ i, w i j * v i j) ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 * W ^ 2 * B ^ 2 := by
  have hp (j : κ) : (∑ i, w i j * v i j) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, (w i j * v i j) ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := Finset.univ) (f := fun _ : ι => (1 : ℝ))
      (g := fun i => (w i j * v i j) ^ 2) (r := fun i => w i j * v i j)
      (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
    simpa using h
  have hs (i : ι) : ∑ j, (w i j * v i j) ^ 2 ≤ W ^ 2 * B ^ 2 := by
    calc
      ∑ j, (w i j * v i j) ^ 2 ≤ ∑ j, W ^ 2 * v i j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [mul_pow]
        have h := pow_le_pow_left₀ (abs_nonneg (w i j)) (hw i j) 2
        rw [sq_abs] at h
        exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = W ^ 2 * ∑ j, v i j ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ W ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left (hv i) (sq_nonneg _)
  calc
    ∑ j, (∑ i, w i j * v i j) ^ 2 ≤
        ∑ j, (Fintype.card ι : ℝ) * ∑ i, (w i j * v i j) ^ 2 :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = (Fintype.card ι : ℝ) * ∑ i, ∑ j, (w i j * v i j) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Fintype.card ι : ℝ) * ∑ _ : ι, W ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hs i)) (by positivity)
    _ = (Fintype.card ι : ℝ) ^ 2 * W ^ 2 * B ^ 2 := by simp; ring

lemma forced_coordinate_square_error {κ : Type*} [Fintype κ]
    (a : ℕ → ℝ) (lam : κ → ℝ) (u v : ℕ → κ → ℝ)
    (n : ℕ)
    (hu : ∀ i < n, ∀ j, u (i + 1) j = (1 - a i * lam j) * u i j + a i * v i j)
    (W B : ℝ)
    (hw : ∀ i < n, ∀ j,
      |a i * OracleTemplate.ScheduleBlock.win a (lam j) (i + 1) n| ≤ W)
    (hv : ∀ i < n, ∑ j, v i j ^ 2 ≤ B ^ 2) :
    ∑ j, (u n j - OracleTemplate.ScheduleBlock.pr a (lam j) n * u 0 j) ^ 2 ≤
      (n : ℝ) ^ 2 * W ^ 2 * B ^ 2 := by
  have he (j : κ) :
      u n j - OracleTemplate.ScheduleBlock.pr a (lam j) n * u 0 j =
        ∑ i : Fin n, (a i * OracleTemplate.ScheduleBlock.win a (lam j) (i.val + 1) n) * v i j := by
    have h := scalar_forced_solution_prefix a (fun i => u i j) (fun i => v i j) (lam j) n
      (fun i hi => hu i hi j)
    rw [h]
    simp only [add_sub_cancel_left, OracleTemplate.ScheduleBlock.errResp]
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (a i * OracleTemplate.ScheduleBlock.win a (lam j) (i + 1) n) * v i j)]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  have h := diagonal_forcing_square_bound
    (fun (i : Fin n) j => a i * OracleTemplate.ScheduleBlock.win a (lam j) (i.val + 1) n)
    (fun (i : Fin n) j => v i j) W B (fun i j => hw i i.isLt j) (fun i => hv i i.isLt)
  simpa using h

end LongTails.Proofs.GdSnapshotDynamics
