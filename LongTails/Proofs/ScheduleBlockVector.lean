import LongTails.Proofs.ScheduleCoordinateCases
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.TemporalSpectralResponse

namespace OracleTemplate.ScheduleBlock

open Finset Set
open scoped RealInnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

lemma coord_traj (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i) (η : ℕ → ℝ) (x : ℕ → E) (z γ : E)
    (e : ℕ → E) (T : ℕ) (h0 : x 0 = z)
    (hstep : ∀ s < T, x (s + 1) = x s - η s • (γ + H (x s - z) + e s)) :
    ∀ t ≤ T, ∀ i, b.repr (x t - z) i =
      traj η (lam i) (b.repr γ i) (fun s => b.repr (e s) i) t := by
  intro t ht
  induction t with
  | zero => intro i; simp [h0, traj]
  | succ t ih =>
    intro i
    have h := hstep t (by omega)
    have ih' := ih (by omega) i
    rw [h, traj, ← ih']
    have e1 : x t - η t • (γ + H (x t - z) + e t) - z =
        (x t - z) - η t • (γ + H (x t - z) + e t) := by abel
    rw [e1, map_sub, map_smul, map_add, map_add]
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hb]
    ring

lemma inner_coord (b : OrthonormalBasis ι ℝ E) (v w : E) :
    ⟪v, w⟫ = ∑ i, b.repr v i * b.repr w i := by
  rw [← b.sum_inner_mul_inner v w]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, real_inner_comm v]

lemma norm_sq_coord (b : OrthonormalBasis ι ℝ E) (v : E) : ‖v‖ ^ 2 = ∑ i, b.repr v i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord b]
  simp [sq]

lemma model_coord (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i) (γ u : E) :
    ⟪γ, u⟫ + ⟪H u, u⟫ / 2 = ∑ i, (b.repr γ i * b.repr u i + lam i * b.repr u i ^ 2 / 2) := by
  rw [inner_coord b γ u, inner_coord b (H u) u, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb]; ring

lemma grad_coord (H : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i) (γ u : E) (i : ι) :
    b.repr (γ + H u) i = b.repr γ i + lam i * b.repr u i := by
  rw [map_add, PiLp.add_apply, hb]

lemma weighted_cs {s : Finset ℕ} (η a : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) :
    (∑ j ∈ s, η j * |a j|) ^ 2 ≤ (∑ j ∈ s, η j) * ∑ j ∈ s, η j * a j ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun j _ => hη j)
    (fun j _ => mul_nonneg (hη j) (sq_nonneg _))
  intro j _
  rw [mul_pow, sq_abs]; apply le_of_eq; ring

lemma wsum_sq_sum (b : OrthonormalBasis ι ℝ E) (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) (e : ℕ → E)
    (t : ℕ) {ε0 : ℝ} (he : ∀ s < t, ‖e s‖ ≤ ε0) :
    ∑ i, wsum η (fun s => b.repr (e s) i) t ^ 2 ≤ ssum η t ^ 2 * ε0 ^ 2 := by
  have h1 : ∀ i, wsum η (fun s => b.repr (e s) i) t ^ 2 ≤
      ssum η t * ∑ s ∈ range t, η s * b.repr (e s) i ^ 2 := fun i => weighted_cs η _ hη
  calc ∑ i, wsum η (fun s => b.repr (e s) i) t ^ 2
      ≤ ∑ i, ssum η t * ∑ s ∈ range t, η s * b.repr (e s) i ^ 2 := Finset.sum_le_sum fun i _ => h1 i
    _ = ssum η t * ∑ s ∈ range t, η s * ‖e s‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        rw [← Finset.mul_sum, norm_sq_coord b]
    _ ≤ ssum η t * ∑ s ∈ range t, η s * ε0 ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun s _ => hη s)
        apply Finset.sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_left _ (hη s)
        exact pow_le_pow_left₀ (norm_nonneg _) (he s (Finset.mem_range.mp hs)) 2
    _ = ssum η t ^ 2 * ε0 ^ 2 := by unfold ssum; rw [← Finset.sum_mul]; ring

lemma usum_sq_sum (b : OrthonormalBasis ι ℝ E) (e : ℕ → E) (t : ℕ) {ε0 : ℝ}
    (he : ∀ s < t, ‖e s‖ ≤ ε0) :
    ∑ i, usum (fun s => b.repr (e s) i) t ^ 2 ≤ (t : ℝ) ^ 2 * ε0 ^ 2 := by
  have h := wsum_sq_sum b (fun _ => 1) (fun _ => zero_le_one) e t he
  have e1 : ∀ i, wsum (fun _ => (1:ℝ)) (fun s => b.repr (e s) i) t =
      usum (fun s => b.repr (e s) i) t := by
    intro i; unfold wsum usum; simp
  have e2 : ssum (fun _ => (1:ℝ)) t = t := by unfold ssum; simp
  simp only [e1, e2] at h
  exact h

lemma cross_sum (c w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ∑ i, c i ^ 2 ≤ A ^ 2) (hws : ∑ i, w i ^ 2 ≤ B ^ 2) :
    ∑ i, |c i| * w i ≤ A * B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |c i|) w
  simp only [sq_abs] at h
  have h2 : (∑ i, |c i| * w i) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow]
    exact h.trans (mul_le_mul hc hws (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _))
  have h0 : 0 ≤ ∑ i, |c i| * w i := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hw i)
  exact (pow_le_pow_iff_left₀ h0 (mul_nonneg hA hB) (by norm_num)).mp h2

lemma taylor_cubic [FiniteDimensional ℝ E] {f : E → ℝ} {ρ : ℝ} (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖) (y x : E) :
    |f x - f y - ⟪gradient f y, x - y⟫ - ⟪fderiv ℝ (gradient f) y (x - y), x - y⟫ / 2| ≤
      ρ * ‖x - y‖ ^ 3 := by
  set d := x - y
  set H := fderiv ℝ (gradient f) y
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ (gradient f) :=
    (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable
      (by norm_num)
  let F := fun t : ℝ => f (y + t • d) - t * ⟪gradient f y, d⟫ - t ^ 2 / 2 * ⟪H d, d⟫
  let F' := fun t : ℝ => ⟪gradient f (y + t • d) - gradient f y - H (t • d), d⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h1 := (hdiff (y + t • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add y)
    simp only [id_eq, one_smul, InnerProductSpace.toDual_apply_apply] at h1
    have h2 := (hasDerivAt_id t).mul_const ⟪gradient f y, d⟫
    have h3 := ((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const ⟪H d, d⟫
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [F', inner_sub_left, map_smul, real_inner_smul_left]
    simp
  have hbound : ∀ t ∈ Ico (0:ℝ) 1, ‖F' t‖ ≤ ρ * ‖d‖ ^ 3 := by
    intro t ht
    have hl := OracleTemplate.NonlinearTemporalDiscrepancy.gradient_linearization_bound hρ hgd
      hH y (y + t • d)
    rw [add_sub_cancel_left] at hl
    have hnt : ‖t • d‖ ≤ ‖d‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    rw [Real.norm_eq_abs]
    calc |F' t| ≤ ‖gradient f (y + t • d) - gradient f y - H (t • d)‖ * ‖d‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (ρ * ‖t • d‖ ^ 2) * ‖d‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ ≤ (ρ * ‖d‖ ^ 2) * ‖d‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnt 2) hρ
      _ = ρ * ‖d‖ ^ 3 := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t _ => (hF t).hasDerivWithinAt) hbound 1 (by simp)
  simp only [F, one_smul, zero_smul, add_zero, one_pow, one_mul, zero_mul, sub_zero,
    Real.norm_eq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    mul_one] at h
  have e : y + d = x := by simp [d]
  rw [e] at h
  convert h using 2
  ring

lemma eig_bounds {g : E → E} {L : ℝ} (hL : 0 ≤ L) [FiniteDimensional ℝ E]
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (u : E)
    (hH : (fderiv ℝ g u).toLinearMap.IsSymmetric) (i : Fin (Module.finrank ℝ E)) :
    -L ≤ hH.eigenvalues rfl i ∧ hH.eigenvalues rfl i ≤ L := by
  have hn : ‖fderiv ℝ g u‖ ≤ L :=
    norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun x => hlip x u))
  apply OracleTemplate.TemporalDiscrepancy.spectral_eigenvalue_bounds _ hH
  · intro x
    have h1 := abs_real_inner_le_norm (fderiv ℝ g u x) x
    have h2 : ‖fderiv ℝ g u x‖ * ‖x‖ ≤ L * ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (((fderiv ℝ g u).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (norm_nonneg _)
    have := (abs_le.mp h1).1
    nlinarith
  · exact OracleTemplate.NonlinearTemporalDiscrepancy.hessian_upper_bound hL hlip u

end OracleTemplate.ScheduleBlock
