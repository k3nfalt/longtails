import LongTails.Proofs.LocalizedMonotoneCoercivity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LocalizedMonotoneInstance

open LocalizedMonotoneConstruction LocalizedMonotoneRadial LocalizedMonotoneCoercivity

noncomputable def field {d n : ℕ} (a b c γ : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  γ • (x - chain a c π (radial b x))

noncomputable def jacobian {d n : ℕ} (a b γ : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  γ • (ContinuousLinearMap.id ℝ _ - (chainJacobian a π (radial b x)).comp (radialJacobian b x))

lemma field_hasFDerivAt {d n : ℕ} (a b c γ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (field a b c γ π) (jacobian a b γ π x) x := by
  have h := (chain_hasFDerivAt a c ha π (radial b x)).comp x (radial_hasFDerivAt b hb x)
  convert ((hasFDerivAt_id x).sub h).const_smul γ using 1 <;> rfl

lemma field_monotone {d n : ℕ} (a b c γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 ≤ γ)
    (π : Fin (n + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ ⟪field a b c γ π x - field a b c γ π y, x - y⟫ := by
  have hT := (chain_nonexpansive a c ha π (radial b x) (radial b y)).trans
    (radial_nonexpansive b hb x y)
  have hi := real_inner_le_norm (chain a c π (radial b x) - chain a c π (radial b y)) (x - y)
  have hp := mul_le_mul_of_nonneg_right hT (norm_nonneg (x - y))
  have he : field a b c γ π x - field a b c γ π y =
      γ • ((x - y) - (chain a c π (radial b x) - chain a c π (radial b y))) := by
    dsimp [field]
    module
  rw [he, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
  apply mul_nonneg hγ
  nlinarith

lemma jacobian_difference {d n : ℕ} (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 ≤ γ)
    (π : Fin (n + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖jacobian a b γ π x - jacobian a b γ π y‖ ≤ γ * (2 / a + 32 / b) * ‖x - y‖ := by
  let A := chainJacobian a π (radial b x)
  let C := chainJacobian a π (radial b y)
  let B := radialJacobian b x
  let D := radialJacobian b y
  have hAC : ‖A - C‖ ≤ 2 / a * ‖x - y‖ :=
    (chainJacobian_difference a ha π (radial b x) (radial b y)).trans
      (mul_le_mul_of_nonneg_left (radial_nonexpansive b hb x y) (by positivity))
  have hB : ‖B‖ ≤ 1 := radialJacobian_norm_le b hb x
  have hC : ‖C‖ ≤ 1 := chainJacobian_norm a ha π (radial b y)
  have hBD : ‖B - D‖ ≤ 32 / b * ‖x - y‖ := radialJacobian_difference b hb x y
  have he : A.comp B - C.comp D = (A - C).comp B + C.comp (B - D) := by
    ext z
    simp
  have hcomp : ‖A.comp B - C.comp D‖ ≤ (2 / a + 32 / b) * ‖x - y‖ := by
    rw [he]
    calc
      _ ≤ ‖(A - C).comp B‖ + ‖C.comp (B - D)‖ := norm_add_le _ _
      _ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 2 / a * ‖x - y‖ + 32 / b * ‖x - y‖ := by
        have h1 := mul_le_mul hAC hB (norm_nonneg _) (by positivity : 0 ≤ 2 / a * ‖x - y‖)
        have h2 := mul_le_mul hC hBD (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simp only [mul_one, one_mul] at h1 h2
        exact add_le_add h1 h2
      _ = _ := by ring
  change ‖γ • (ContinuousLinearMap.id ℝ _ - A.comp B) -
      γ • (ContinuousLinearMap.id ℝ _ - C.comp D)‖ ≤ _
  have he' : γ • (ContinuousLinearMap.id ℝ _ - A.comp B) -
      γ • (ContinuousLinearMap.id ℝ _ - C.comp D) = γ • (C.comp D - A.comp B) := by module
  rw [he', norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ, norm_sub_rev]
  have h := mul_le_mul_of_nonneg_left hcomp hγ
  simpa only [mul_assoc] using h

lemma field_zero_of_chain_root {d n : ℕ} (a b c γ : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) (hz : chain a c π z = z) (hzb : ‖z‖ ≤ b) :
    field a b c γ π z = 0 := by
  simp only [field, radial_eq_self b z hzb, hz, sub_self, smul_zero]

lemma field_norm {d n : ℕ} (a b c γ : ℝ) (hγ : 0 ≤ γ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖field a b c γ π x‖ = γ * ‖x - chain a c π (radial b x)‖ := by
  simp only [field, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]

end LongTails.Proofs.LocalizedMonotoneInstance
