import LongTails.Proofs.SpectralGradientModel
import LongTails.Proofs.TemporalSpectralResponse

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedCurvatureGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma hessian_norm_bound {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ ≤ L :=
  norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun y => hLip y x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma shifted_quadratic_bounds (H : E →L[ℝ] E) {L γ : ℝ}
    (hH : ‖H‖ ≤ L) (v : E) :
    γ * ‖v‖ ^ 2 ≤ ⟪((L + γ) • ContinuousLinearMap.id ℝ E - H) v, v⟫ ∧
      ⟪((L + γ) • ContinuousLinearMap.id ℝ E - H) v, v⟫ ≤
        (2 * L + γ) * ‖v‖ ^ 2 := by
  have hb := (H.le_opNorm v).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg v))
  have hi := abs_real_inner_le_norm (H v) v
  have hi' := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith [le_abs_self ⟪H v, v⟫, neg_le_abs ⟪H v, v⟫]

omit [CompleteSpace E] in
lemma psd_top_eigenpair [Nontrivial E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) {M : ℝ}
    (hlo : ∀ v, 0 ≤ ⟪A v, v⟫) (hhi : ∀ v, ⟪A v, v⟫ ≤ M * ‖v‖ ^ 2) :
    ∃ (ell : ℝ) (u : E), 0 ≤ ell ∧ ell ≤ M ∧ ‖u‖ = 1 ∧
      A u = ell • u ∧ ‖A‖ ≤ ell := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  let i : Fin (Module.finrank ℝ E) := ⟨0, hd⟩
  let ell := hA.eigenvalues rfl i
  let u := hA.eigenvectorBasis rfl i
  have hb (j : Fin (Module.finrank ℝ E)) :=
    OracleTemplate.TemporalDiscrepancy.spectral_eigenvalue_bounds A hA
      (μ := 0) (by simpa using hlo) hhi j
  refine ⟨ell, u, (hb i).1, (hb i).2, ?_, ?_, ?_⟩
  · exact (hA.eigenvectorBasis rfl).norm_eq_one i
  · exact hA.apply_eigenvectorBasis rfl i
  · apply ContinuousLinearMap.opNorm_le_bound _ (hb i).1
    intro v
    conv_lhs => rw [OracleTemplate.TemporalDiscrepancy.spectral_diagonalization A hA]
    apply OracleTemplate.TemporalDiscrepancy.diagonalMap_bound _ _ (hb i).1
    intro j
    rw [abs_of_nonneg (hb j).1]
    exact hA.eigenvalues_antitone rfl (show i ≤ j from Nat.zero_le _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma energy_implies_negative_curvature (H : E →L[ℝ] E) {L γ ell : ℝ}
    {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hop : ‖(L + γ) • ContinuousLinearMap.id ℝ E - H‖ ≤ ell)
    (hbad : ⟪w, H w⟫ ≤ -4 * γ)
    (henergy : ell - ⟪v, ((L + γ) • ContinuousLinearMap.id ℝ E - H) v⟫ ≤ γ) :
    ⟪v, H v⟫ ≤ -3 * γ := by
  have hn := (((L + γ) • ContinuousLinearMap.id ℝ E - H).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg w))
  have hi := real_inner_le_norm w (((L + γ) • ContinuousLinearMap.id ℝ E - H) w)
  simp only [hw, mul_one, one_mul] at hn hi
  simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_sub_right,
    inner_smul_right, real_inner_self_eq_norm_sq, hw, hv, one_pow, mul_one] at hi henergy
  simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply] at hn
  linarith

end LongTails.Proofs.HeavyTailedCurvatureGeometry
