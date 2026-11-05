import LongTails.Algorithms.SymmetricThirdOrder
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace LongTails.Proofs.SymmetricThirdOrderHessian

open LongTails.Algorithms.SymmetricThirdOrder
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma form_abs_le (A : E →L[ℝ] E) (v : E) :
    |⟪A v, v⟫| ≤ ‖A‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖A v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

lemma unit_form_abs_le (A : E →L[ℝ] E) {v : E} (hv : v ∈ Metric.closedBall 0 1) :
    |⟪A v, v⟫| ≤ ‖A‖ := by
  have hn : ‖v‖ ≤ 1 := by simpa using hv
  calc
    _ ≤ ‖A‖ * ‖v‖ ^ 2 := form_abs_le A v
    _ ≤ ‖A‖ * 1 ^ 2 := by gcongr
    _ = _ := by ring

lemma rayleigh_nonempty (A : E →L[ℝ] E) :
    ((fun v : E => ⟪A v, v⟫) '' Metric.closedBall 0 1).Nonempty := by
  exact ⟨0, 0, by simp, by simp⟩

lemma rayleigh_bddBelow (A : E →L[ℝ] E) :
    BddBelow ((fun v : E => ⟪A v, v⟫) '' Metric.closedBall 0 1) := by
  refine ⟨-‖A‖, ?_⟩
  rintro z ⟨v, hv, rfl⟩
  exact (abs_le.mp (unit_form_abs_le A hv)).1

lemma lowerRayleigh_le (A : E →L[ℝ] E) {v : E} (hv : v ∈ Metric.closedBall 0 1) :
    lowerRayleigh A ≤ ⟪A v, v⟫ := csInf_le (rayleigh_bddBelow A) ⟨v, hv, rfl⟩

lemma lowerRayleigh_nonpos (A : E →L[ℝ] E) : lowerRayleigh A ≤ 0 := by
  simpa using lowerRayleigh_le A (v := 0) (by simp)

lemma le_lowerRayleigh (A : E →L[ℝ] E) {b : ℝ}
    (hb : ∀ v ∈ Metric.closedBall (0 : E) 1, b ≤ ⟪A v, v⟫) :
    b ≤ lowerRayleigh A := by
  apply le_csInf (rayleigh_nonempty A)
  rintro z ⟨v, hv, rfl⟩
  exact hb v hv

lemma lowerRayleigh_sub_le (A B : E →L[ℝ] E) :
    lowerRayleigh A - lowerRayleigh B ≤ ‖A - B‖ := by
  have hh : lowerRayleigh A - ‖A - B‖ ≤ lowerRayleigh B := by
    apply le_lowerRayleigh
    intro v hv
    have ha := lowerRayleigh_le A hv
    have hd := (abs_le.mp (unit_form_abs_le (A - B) hv)).2
    simp only [sub_apply, inner_sub_left] at hd
    linarith
  linarith

lemma lowerRayleigh_lipschitz (A B : E →L[ℝ] E) :
    |lowerRayleigh A - lowerRayleigh B| ≤ ‖A - B‖ := by
  have hp := lowerRayleigh_sub_le A B
  have hm := lowerRayleigh_sub_le B A
  rw [norm_sub_rev B A] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩

lemma continuous_lowerRayleigh : Continuous (lowerRayleigh (E := E)) := by
  apply LipschitzWith.continuous (K := 1)
  intro A B
  rw [edist_dist, edist_dist]
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, ENNReal.coe_one, one_mul]
    using ENNReal.ofReal_le_ofReal (lowerRayleigh_lipschitz A B)

lemma lowerRayleigh_form (A : E →L[ℝ] E) (v : E) :
    lowerRayleigh A * ‖v‖ ^ 2 ≤ ⟪A v, v⟫ := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖v‖⁻¹ • v ∈ Metric.closedBall (0 : E) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn]
  have hh := lowerRayleigh_le A hu
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * ⟪A v, v⟫)) = ⟪A v, v⟫ := by
    field_simp
  rw [he] at hm
  nlinarith

lemma shiftedHessian_nonneg (A : E →L[ℝ] E) (ε : ℝ) (v : E) :
    0 ≤ ⟪shiftedHessian A ε v, v⟫ := by
  have hh := lowerRayleigh_form A v
  have hs := mul_le_mul_of_nonneg_right (le_max_right ε (-lowerRayleigh A)) (sq_nonneg ‖v‖)
  simp only [shiftedHessian, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith

lemma lowerRayleigh_error {A H : E →L[ℝ] E} {ε : ℝ}
    (hH : ∀ v, 0 ≤ ⟪H v, v⟫) (herr : ‖A - H‖ ≤ ε) :
    -ε ≤ lowerRayleigh A := by
  apply le_lowerRayleigh
  intro v hv
  have hh := hH v
  have hd := (abs_le.mp ((unit_form_abs_le (A - H) hv).trans herr)).1
  simp only [sub_apply, inner_sub_left] at hd
  linarith

lemma shiftedHessian_good {A H : E →L[ℝ] E} {ε : ℝ}
    (hH : ∀ v, 0 ≤ ⟪H v, v⟫) (herr : ‖A - H‖ ≤ ε) :
    shiftedHessian A ε = A + ε • ContinuousLinearMap.id ℝ E := by
  have hm := lowerRayleigh_error hH herr
  simp only [shiftedHessian, max_eq_left (by linarith : -lowerRayleigh A ≤ ε)]

lemma shiftedHessian_interval {A H : E →L[ℝ] E} {ε : ℝ}
    (hH : ∀ v, 0 ≤ ⟪H v, v⟫) (herr : ‖A - H‖ ≤ ε) (v : E) :
    0 ≤ ⟪shiftedHessian A ε v, v⟫ - ⟪H v, v⟫ ∧
    ⟪shiftedHessian A ε v, v⟫ - ⟪H v, v⟫ ≤ 2 * ε * ‖v‖ ^ 2 := by
  have hd := abs_le.mp ((form_abs_le (A - H) v).trans
    (mul_le_mul_of_nonneg_right herr (sq_nonneg ‖v‖)))
  rw [shiftedHessian_good hH herr]
  simp only [sub_apply, inner_sub_left] at hd
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> linarith

lemma shiftedHessian_center_error {A H : E →L[ℝ] E} {ε : ℝ}
    (hH : ∀ v, 0 ≤ ⟪H v, v⟫) (herr : ‖A - H‖ ≤ ε) :
    ‖shiftedHessian A ε - H‖ ≤ 2 * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans herr
  have hs : ‖ε • ContinuousLinearMap.id ℝ E‖ ≤ ε := by
    calc
      _ ≤ ‖ε‖ * ‖ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ε * 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hε]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hε
      _ = ε := mul_one ε
  have he : shiftedHessian A ε - H = (A - H) + ε • ContinuousLinearMap.id ℝ E := by
    rw [shiftedHessian_good hH herr]
    abel
  rw [he]
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans (by linarith)

lemma shiftedHessian_cleanup_error {A H : E →L[ℝ] E} {ε : ℝ}
    (hH : ∀ v, 0 ≤ ⟪H v, v⟫) (herr : ‖A - H‖ ≤ ε) :
    ‖shiftedHessian A 0 - H‖ ≤ 2 * ε := by
  have hm := lowerRayleigh_error hH herr
  have hn := lowerRayleigh_nonpos A
  have hs : ‖(-lowerRayleigh A) • ContinuousLinearMap.id ℝ E‖ ≤ ε := by
    calc
      _ ≤ ‖-lowerRayleigh A‖ * ‖ContinuousLinearMap.id ℝ E‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ (-lowerRayleigh A) * 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ -lowerRayleigh A)]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by linarith)
      _ ≤ ε := by linarith
  have he : shiftedHessian A 0 - H = (A - H) +
      (-lowerRayleigh A) • ContinuousLinearMap.id ℝ E := by
    rw [shiftedHessian, max_eq_right (by linarith : 0 ≤ -lowerRayleigh A)]
    abel
  rw [he]
  exact (ContinuousLinearMap.opNorm_add_le _ _).trans (by linarith)

lemma continuous_shiftedHessian :
    Continuous (fun p : (E →L[ℝ] E) × ℝ => shiftedHessian p.1 p.2) := by
  exact continuous_fst.add ((continuous_snd.max (continuous_lowerRayleigh.comp continuous_fst).neg).smul
    continuous_const)

lemma symmetricHessian_symmetric [CompleteSpace E] (A : E →L[ℝ] E) (x y : E) :
    ⟪x, symmetricHessian A y⟫ = ⟪symmetricHessian A x, y⟫ := by
  simp only [symmetricHessian, smul_apply, add_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  ring

lemma symmetricHessian_error [CompleteSpace E] (A H : E →L[ℝ] E)
    (hH : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫) :
    ‖symmetricHessian A - H‖ ≤ ‖A - H‖ := by
  have hself : ContinuousLinearMap.adjoint H = H := by
    apply Eq.symm
    apply (ContinuousLinearMap.eq_adjoint_iff H H).mpr
    intro x y
    exact (hH x y).symm
  have he : symmetricHessian A - H =
      (1 / 2 : ℝ) • ((A - H) + ContinuousLinearMap.adjoint (A - H)) := by
    simp only [symmetricHessian, map_sub, hself]
    module
  rw [he]
  calc
    _ ≤ ‖(1 / 2 : ℝ)‖ * ‖(A - H) + ContinuousLinearMap.adjoint (A - H)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (1 / 2) * (‖A - H‖ + ‖ContinuousLinearMap.adjoint (A - H)‖) := by
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_add_le _ _) (by norm_num)
    _ = ‖A - H‖ := by rw [LinearIsometryEquiv.norm_map]; ring

lemma continuous_symmetricHessian [CompleteSpace E] :
    Continuous (symmetricHessian (E := E)) := by
  exact (continuous_id.add ContinuousLinearMap.adjoint.continuous).const_smul (1 / 2 : ℝ)

lemma shiftedHessian_symmetric (A : E →L[ℝ] E) (ε : ℝ)
    (hA : ∀ x y : E, ⟪x, A y⟫ = ⟪A x, y⟫) (x y : E) :
    ⟪x, shiftedHessian A ε y⟫ = ⟪shiftedHessian A ε x, y⟫ := by
  simp only [shiftedHessian, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hA]

end LongTails.Proofs.SymmetricThirdOrderHessian
