import LongTails.Algorithms.MonotoneHessianReuse
import LongTails.Proofs.HessianSnapshotGeometry
import LongTails.Proofs.MonotoneCurvatureModel
import LongTails.Proofs.ReusedCurvatureCertificate
import LongTails.Proofs.RelativeCurvatureSpectrum
import LongTails.Proofs.MonotoneCurvatureStageGuarantee
import LongTails.Proofs.MonotoneHessianParameters

namespace LongTails.Proofs.MonotoneHessianSnapshot

open LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse
open scoped RealInnerProductSpace

lemma no_negative_direction (p : Params) (H : p.E →L[ℝ] p.E)
    (hn : negativeDirection p H = none) (v : p.E) :
    -delta p * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  classical
  have hall : ∀ u : p.E, ‖u‖ = 1 → -delta p ≤ ⟪u, H u⟫ := by
    intro u hu
    by_contra h
    have hex : ∃ w : p.E, ‖w‖ = 1 ∧ ⟪w, H w⟫ < -delta p := ⟨u, hu, lt_of_not_ge h⟩
    simp [negativeDirection, hex] at hn
  by_cases hv : v = 0
  · simp [hv]
  have hn0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, hn0.ne']
  have hh := hall (‖v‖⁻¹ • v) hu
  have he : ⟪‖v‖⁻¹ • v, H (‖v‖⁻¹ • v)⟫ = ⟪v, H v⟫ / ‖v‖ ^ 2 := by
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [he] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hn0)).mp hh

lemma chosen_negative_direction (p : Params) (H : p.E →L[ℝ] p.E) (v : p.E)
    (hv : negativeDirection p H = some v) : ‖v‖ = 1 ∧ ⟪v, H v⟫ < -delta p := by
  classical
  unfold negativeDirection at hv
  split at hv
  · rename_i h
    have he := Option.some.inj hv
    rw [← he]
    exact Classical.choose_spec h
  · simp at hv

lemma shifted_symmetric (p : Params) (H : p.E →L[ℝ] p.E) (hH : H.toLinearMap.IsSymmetric) :
    (H + (4 * delta p) • ContinuousLinearMap.id ℝ p.E).toLinearMap.IsSymmetric := by
  intro u v
  change ⟪(H + (4 * delta p) • ContinuousLinearMap.id ℝ p.E) u, v⟫ =
    ⟪u, (H + (4 * delta p) • ContinuousLinearMap.id ℝ p.E) v⟫
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  exact congrArg (fun z : ℝ => z + 4 * delta p * ⟪u, v⟫) (hH u v)

lemma snapshot_metric (p : Params) (H : p.E →L[ℝ] p.E) (hH : H.toLinearMap.IsSymmetric)
    (hδ : 0 < delta p) (hn : negativeDirection p H = none) (v : p.E) :
    ‖LongTails.Algorithms.HessianSnapshot.coordinates
      (H + (4 * delta p) • ContinuousLinearMap.id ℝ p.E) v‖ ^ 2 =
        ⟪v, H v⟫ + 4 * delta p * ‖v‖ ^ 2 := by
  have hpos (u : p.E) : 3 * delta p * ‖u‖ ^ 2 ≤
      ⟪(H + (4 * delta p) • ContinuousLinearMap.id ℝ p.E) u, u⟫ := by
    have hh := no_negative_direction p H hn u
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [real_inner_comm u (H u)]
    linarith
  have hh := HessianSnapshotGeometry.coordinates_spec _ (shifted_symmetric p H hH)
    (by positivity : 0 < 3 * delta p) hpos v
  simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm (H v) v] using hh

section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def relative (S : E ≃L[ℝ] E) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  S.symm.toContinuousLinearMap.adjoint.comp (A.comp S.symm.toContinuousLinearMap)

lemma relative_pairing (S : E ≃L[ℝ] E) (A : E →L[ℝ] E) (u v : E) :
    ⟪u, relative S A v⟫ = ⟪S.symm u, A (S.symm v)⟫ := by
  simp only [relative, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe]

lemma relative_symmetric (S : E ≃L[ℝ] E) (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    (relative S A).toLinearMap.IsSymmetric := by
  intro u v
  change ⟪relative S A u, v⟫ = ⟪u, relative S A v⟫
  rw [real_inner_comm v (relative S A u), relative_pairing, relative_pairing,
    real_inner_comm (A (S.symm u)) (S.symm v)]
  exact hA _ _

lemma bad_relative_direction (S : E ≃L[ℝ] E) (A B : E →L[ℝ] E) {a δ γ : ℝ}
    (ha : 0 ≤ a) (hγ : 0 ≤ γ) (htune : 12 * a * δ ≤ γ)
    (hfactor : ∀ v, ‖S v‖ ^ 2 = ⟪v, B v⟫)
    (herror : ∀ v, ⟪v, B v⟫ ≤ ⟪v, A v⟫ + 6 * δ * ‖v‖ ^ 2)
    (v : E) (hv : ⟪v, A v⟫ < -γ * ‖v‖ ^ 2) :
    ⟪S v, relative S A (S v)⟫ < -(2 * a) * ‖S v‖ ^ 2 := by
  rw [relative_pairing, ContinuousLinearEquiv.symm_apply_apply, hfactor]
  exact ReusedCurvatureCertificate.relative_witness_of_absolute (by positivity : 0 ≤ 2 * a)
    (show 2 * a * (6 * δ) ≤ γ by nlinarith) (herror v) hv hγ

lemma relative_quadratic_bounds (S : E ≃L[ℝ] E) (A : E →L[ℝ] E) {δ : ℝ}
    (hmetric : ∀ v, 3 * δ * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hlo : ∀ v, ‖S v‖ ^ 2 - 6 * δ * ‖v‖ ^ 2 ≤ ⟪v, A v⟫)
    (hhi : ∀ v, ⟪v, A v⟫ ≤ ‖S v‖ ^ 2) (z : E) :
    -2 * ‖z‖ ^ 2 ≤ ⟪z, relative S A z⟫ ∧ ⟪z, relative S A z⟫ ≤ ‖z‖ ^ 2 := by
  have hm := hmetric (S.symm z)
  have hl := hlo (S.symm z)
  have hh := hhi (S.symm z)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hm hl hh
  rw [relative_pairing]
  constructor
  · nlinarith [sq_nonneg ‖z‖]
  · exact hh

lemma relative_norm (S : E ≃L[ℝ] E) (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    {δ : ℝ} (hmetric : ∀ v, 3 * δ * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hlo : ∀ v, ‖S v‖ ^ 2 - 6 * δ * ‖v‖ ^ 2 ≤ ⟪v, A v⟫)
    (hhi : ∀ v, ⟪v, A v⟫ ≤ ‖S v‖ ^ 2) : ‖relative S A‖ ≤ 2 := by
  let C := relative S A
  have hC := relative_symmetric S A hA
  have hbounds (z : E) := relative_quadratic_bounds S A hmetric hlo hhi z
  have heig (i : Fin (Module.finrank ℝ E)) : |hC.eigenvalues rfl i| ≤ 2 := by
    have hh := OracleTemplate.TemporalDiscrepancy.spectral_eigenvalue_bounds C hC (μ := -2) (L := 1)
      (fun z => by rw [real_inner_comm z (C z)]; exact (hbounds z).1)
      (fun z => by rw [real_inner_comm z (C z), one_mul]; exact (hbounds z).2) i
    exact abs_le.mpr ⟨hh.1, hh.2.trans (by norm_num)⟩
  exact RelativeCurvatureSpectrum.norm_bound C (hC.eigenvectorBasis rfl) (hC.eigenvalues rfl)
    (by norm_num) heig (RelativeCurvatureSpectrum.symmetric_coordinates C hC)

lemma returned_absolute_curvature (S : E ≃L[ℝ] E) (A : E →L[ℝ] E) {a δ : ℝ}
    (ha : 0 ≤ a) (hmetric : ∀ v, 3 * δ * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (z : E) (hz : ‖z‖ = 1) (hc : ⟪z, relative S A z⟫ ≤ -7 * a / 16) :
    ⟪S.symm z, A (S.symm z)⟫ ≤ -(21 * a * δ / 16) * ‖S.symm z‖ ^ 2 := by
  have hm := hmetric (S.symm z)
  simp only [ContinuousLinearEquiv.apply_symm_apply, hz, one_pow] at hm
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 7 * a / 16 by positivity)
  rw [relative_pairing] at hc
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma local_metric_order (S : E ≃L[ℝ] E) (A : E → E →L[ℝ] E) {H δ : ℝ}
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (s x : E)
    (hmetric : ∀ v, ‖S v‖ ^ 2 = ⟪v, A s v⟫ + 4 * δ * ‖v‖ ^ 2)
    (hlower : ∀ v, -δ * ‖v‖ ^ 2 ≤ ⟪v, A s v⟫)
    (hr : H * ‖x - s‖ ≤ δ) (v : E) :
    3 * δ * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2 ∧
    ‖S v‖ ^ 2 - 5 * δ * ‖v‖ ^ 2 ≤ ⟪v, A x v⟫ ∧
    ⟪v, A x v⟫ ≤ ‖S v‖ ^ 2 - 3 * δ * ‖v‖ ^ 2 := by
  have hm := hmetric v
  have hl := hlower v
  obtain ⟨h₁, h₂⟩ := MonotoneCurvatureModel.snapshot_order hLip s x hr v
  constructor
  · linarith
  constructor <;> linarith

omit [FiniteDimensional ℝ E] in
lemma local_operator_error (A : E → E →L[ℝ] E) {H δ : ℝ} (hδ : 0 ≤ δ)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (s x : E)
    (hr : H * ‖x - s‖ ≤ δ) :
    ‖A s + (4 * δ) • ContinuousLinearMap.id ℝ E - A x‖ ≤ 5 * δ := by
  have he : A s + (4 * δ) • ContinuousLinearMap.id ℝ E - A x =
      (A s - A x) + (4 * δ) • ContinuousLinearMap.id ℝ E := by abel
  have hh : ‖A s - A x‖ ≤ δ := by rw [norm_sub_rev]; exact (hLip x s).trans hr
  have hi : ‖(4 * δ) • ContinuousLinearMap.id ℝ E‖ ≤ 4 * δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * δ)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)).trans_eq (mul_one _)
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hh hi).trans_eq (by ring))

end

lemma stage_local_metric (p : Params) (hp : spec.valid p)
    (A : p.E → p.E →L[ℝ] p.E) (hA : ∀ x, (A x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ p.H * ‖x - y‖)
    (s c : p.E) (S : p.E ≃L[ℝ] p.E)
    (hfactor : ∀ v, ‖S v‖ ^ 2 = ⟪v, A s v⟫ + 4 * delta p * ‖v‖ ^ 2)
    (hlower : ∀ v, -delta p * ‖v‖ ^ 2 ≤ ⟪v, A s v⟫)
    (hr : ‖c - s‖ ≤ delta p / (4 * p.H)) :
    MonotoneCurvatureStageGuarantee.LocalMetric A S
      (A s + (4 * delta p) • ContinuousLinearMap.id ℝ p.E) c p.H (gamma p) (scale p) := by
  have hδ := MonotoneHessianParameters.delta_pos p hp
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  have ht := MonotoneHessianParameters.scale_ge_one p
  have hnear (x : p.E) (hx : ‖x - c‖ ≤ 160 * MonotoneCurvatureTuning.distanceScale p.H (gamma p)) :
      p.H * ‖x - s‖ ≤ delta p := by
    have hd := norm_sub_le (x - c) (s - c)
    rw [sub_sub_sub_cancel_right, norm_sub_rev s c] at hd
    have hh := mul_le_mul_of_nonneg_left hd hp.1.le
    have hc := mul_le_mul_of_nonneg_left hr hp.1.le
    have hxe := mul_le_mul_of_nonneg_left hx hp.1.le
    have hc' : p.H * (delta p / (4 * p.H)) = delta p / 4 := by field_simp [hp.1.ne']
    rw [hc'] at hc
    have hs := MonotoneCurvatureTuning.small_query_radius hp.1 hγ ht
    change p.H * (160 * MonotoneCurvatureTuning.distanceScale p.H (gamma p)) ≤ delta p / 16 at hs
    nlinarith
  refine ⟨shifted_symmetric p (A s) (hA s), ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq] using hfactor v
  · intro v
    have hh := hlower v
    rw [hfactor]
    change delta p * ‖v‖ ^ 2 ≤ _
    nlinarith [mul_nonneg hδ.le (sq_nonneg ‖v‖)]
  · intro x hx v
    have hh := (local_metric_order S A hLip s x hfactor hlower (hnear x hx) v).2.2
    change ⟪v, A x v⟫ ≤ ‖S v‖ ^ 2 - delta p * ‖v‖ ^ 2
    nlinarith [mul_nonneg hδ.le (sq_nonneg ‖v‖)]
  · intro x hx
    exact (local_operator_error A hδ.le hLip s x (hnear x hx)).trans (by
      change 5 * delta p ≤ 6 * delta p
      linarith)

end LongTails.Proofs.MonotoneHessianSnapshot
