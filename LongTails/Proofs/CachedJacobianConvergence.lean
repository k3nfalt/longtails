import LongTails.Proofs.CachedJacobianExecution
import LongTails.Proofs.CachedJacobianOuter

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CachedJacobianConvergence

open OracleTemplate LongTails.Setups.LipschitzJacobianMonotone
open LongTails.Algorithms.CachedJacobian
open CachedJacobianExecution CachedJacobianGeometry CachedJacobianTuning

noncomputable def initialState (p : Params) (F : p.E → p.E) : State p where
  point := p.x0
  value := F p.x0
  normal := 0
  snapshot := p.x0
  matrix := fderiv ℝ F p.x0

noncomputable def trajectory (p : Params) (F : p.E → p.E) : ℕ → State p
  | 0 => initialState p F
  | t + 1 => QueryPlan.eval (replies p F) (outerStep p t (trajectory p F t))

noncomputable def residual (p : Params) (F : p.E → p.E) (t : ℕ) : p.E :=
  F (trajectory p F (t + 1)).point + (trajectory p F (t + 1)).normal

noncomputable def error (p : Params) (F : p.E → p.E) (t : ℕ) : p.E :=
  (trajectory p F (t + 1)).point - center p t (trajectory p F t) + stepSize p t • residual p F t

lemma trajectory_correct {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫) (t : ℕ) :
    Correct p F (trajectory p F t) := by
  induction t with
  | zero =>
    have hx := hv.2.2.2.2.2.2.1
    exact ⟨hx, rfl, by simp [trajectory, initialState], hx, rfl⟩
  | succ t ih =>
    exact repeatInner_correct t (center p t (trajectory p F t)) hv hF hmono (innerCount p) _ ih

lemma prefix_residual {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫)
    {k : ℕ} (hk : k < outerCount p)
    (herr : ∀ t ≤ k, ‖error p F t‖ ≤ p.D / (outerCount p : ℝ) ^ 2) :
    ‖residual p F k‖ ≤ 40 * p.D / (initialStep p * (k + 1 : ℝ) ^ 2) := by
  have hvalid := hv
  obtain ⟨hL, hD, _, hm, _, _, hx, hdiam⟩ := hv
  have hc := trajectory_correct hvalid hF hmono
  have hsums := error_sums hD.le (outerCount_pos p) hk herr
  have hzero : error p F 0 = (trajectory p F 1).point - p.x0 + initialStep p • residual p F 0 := by
    simp [error, center, stepSize]
  have hezero : ‖error p F 0‖ ≤ p.D := by
    have hT : (1 : ℝ) ≤ outerCount p := by exact_mod_cast outerCount_pos p
    have hTp : (0 : ℝ) < outerCount p := by linarith
    apply (herr 0 (Nat.zero_le k)).trans
    apply (div_le_iff₀ (sq_pos_of_pos hTp)).mpr
    nlinarith [mul_nonneg hD.le (show 0 ≤ (outerCount p : ℝ) ^ 2 - 1 by nlinarith)]
  have hrec (t : ℕ) (_ht : t < k) :
      (trajectory p F (t + 1 + 1)).point - (trajectory p F (t + 1)).point =
      -(2 / (t + 3 : ℝ)) • ((trajectory p F (t + 1)).point - p.x0) -
        CachedJacobianOuter.stepSize (initialStep p) (t + 1) • residual p F (t + 1) + error p F (t + 1) := by
    dsimp only [error, center, CachedJacobianOuter.stepSize, stepSize]
    simp only [Nat.cast_add, Nat.cast_one, show (t : ℝ) + 1 + 2 = t + 3 by ring]
    module
  have hmon (t : ℕ) (_ht : t < k) :
      0 ≤ ⟪residual p F (t + 1) - residual p F t,
        (trajectory p F (t + 1 + 1)).point - (trajectory p F (t + 1)).point⟫ := by
    have h₁ := hmono _ (hc (t + 1 + 1)).point_mem _ (hc (t + 1)).point_mem
    have h₂ := OracleTemplate.ConstrainedMonotone.normal_monotone
      (hc (t + 1 + 1)).point_mem (hc (t + 1)).point_mem
      (hc (t + 1 + 1)).normal_mem (hc (t + 1)).normal_mem
    dsimp only [residual]
    rw [add_sub_add_comm, inner_add_left]
    linarith
  exact CachedJacobianOuter.certified_prefix (initialStep_pos hL hD hm) hD.le
    (fun t _ => hdiam _ (hc (t + 1)).point_mem p.x0 hx) hzero hezero hrec hmon hsums.1 hsums.2

lemma proximal_exists {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ y ∈ p.X, 0 ≤ ⟪F x - F y, x - y⟫)
    (hJ : ∀ x ∈ p.X, ∀ y ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.L * ‖x - y‖)
    (t : ℕ) (c : p.E) : ∃ y ∈ p.X,
      ∀ z ∈ p.X, 0 ≤ ⟪F y + (stepSize p t)⁻¹ • (y - c), z - y⟫ := by
  obtain ⟨hL, hD, _, hm, hX, hc, hx, hdiam⟩ := hv
  apply regularized_vi_exists c hX hc ⟨p.x0, hx⟩
    (show 0 ≤ ‖fderiv ℝ F p.x0‖ + p.L * p.D by positivity)
    (inv_pos.mpr (stepSize_pos hL hD hm t)) hmono
  intro u hu v hv
  exact field_lipschitz hc hx hL.le hF hJ (fun x hx' => hdiam x hx' p.x0 hx) hu hv

lemma warm_root_distance {p : Params} {F : p.E → p.E} {a : State p}
    {c y : p.E} {η : ℝ} (ha : Correct p F a) (hη : 0 < η) (hy : y ∈ p.X)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hyvi : ∀ z ∈ p.X, 0 ≤ ⟪F y + η⁻¹ • (y - c), z - y⟫) :
    ‖a.point - y‖ ≤ ‖a.point - c‖ + η * ‖F a.point + a.normal‖ := by
  let e := F a.point + η⁻¹ • (a.point - c) + a.normal
  have huvi : ∀ z ∈ p.X, 0 ≤ ⟪F a.point + η⁻¹ • (a.point - c) - e, z - a.point⟫ := by
    intro z hz
    have heq : F a.point + η⁻¹ • (a.point - c) - e = -a.normal := by dsimp [e]; module
    rw [heq, inner_neg_left]
    exact neg_nonneg.mpr (ha.normal_mem z hz)
  have hh := regularized_vi_error ha.point_mem hy hmono huvi hyvi
  have hmul := mul_le_mul_of_nonneg_left hh hη.le
  have heq : η • e = a.point - c + η • (F a.point + a.normal) := by
    dsimp [e]
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    module
  have hnorm : η * ‖e‖ = ‖a.point - c + η • (F a.point + a.normal)‖ := by
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul, hnorm] at hmul
  apply hmul.trans
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hη] using
    norm_add_le (a.point - c) (η • (F a.point + a.normal))

lemma center_distance {p : Params} {a : State p} (hv : spec.valid p)
    (ha : a.point ∈ p.X) (t : ℕ) :
    ‖a.point - center p t a‖ ≤ (2 / (t + 2 : ℝ)) * p.D := by
  have heq : a.point - center p t a = (2 / (t + 2 : ℝ)) • (a.point - p.x0) := by
    dsimp [center]
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hv.2.2.2.2.2.2.2 _ ha _ hv.2.2.2.2.2.2.1) (by positivity)

lemma trajectory_warm_distance {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    {t : ℕ} (ht : 1 ≤ t) (htT : t ≤ outerCount p)
    (herr : ∀ k < t, ‖error p F k‖ ≤ p.D / (outerCount p : ℝ) ^ 2)
    {y : p.E} (hy : y ∈ p.X)
    (hyvi : ∀ z ∈ p.X, 0 ≤ ⟪F y + (stepSize p t)⁻¹ •
      (y - center p t (trajectory p F t)), z - y⟫) :
    ‖(trajectory p F t).point - y‖ ≤ 56 * p.D / t := by
  have hc := trajectory_correct hv hF hmono t
  have hL := hv.1
  have hD := hv.2.1
  have hm := hv.2.2.2.1
  have hh := warm_root_distance hc (stepSize_pos hL hD hm t) hy hmono hyvi
  have hcenter := center_distance hv hc.point_mem t
  have hres := prefix_residual hv hF hmono (show t - 1 < outerCount p by omega)
    (fun k hk => herr k (by omega))
  have hindex : t - 1 + 1 = t := by omega
  have hcast : (t - 1 : ℕ) + (1 : ℝ) = (t : ℝ) := by exact_mod_cast hindex
  simp only [residual, hindex, hcast] at hres
  have hmul := mul_le_mul_of_nonneg_left hres (stepSize_pos hL hD hm t).le
  apply le_trans (by linarith : ‖(trajectory p F t).point - y‖ ≤
    (2 / (t + 2 : ℝ)) * p.D + stepSize p t *
      (40 * p.D / (initialStep p * (t : ℝ) ^ 2)))
  exact warm_distance_bound (initialStep_pos hL hD hm) hD.le ht

lemma trajectory_error {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
    (t : ℕ) (ht : t < outerCount p) :
    ‖error p F t‖ ≤ p.D / (outerCount p : ℝ) ^ 2 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have hc := trajectory_correct hv hF hmono t
    obtain ⟨y, hy, hyvi⟩ := proximal_exists hv hF hmono hJ t (center p t (trajectory p F t))
    have hdiam : ‖(trajectory p F t).point - y‖ ≤ p.D :=
      hv.2.2.2.2.2.2.2 _ hc.point_mem _ hy
    have hsmall : stepSize p t * p.L * ‖(trajectory p F t).point - y‖ ≤ 1 / 64 := by
      by_cases hz : t = 0
      · subst t
        exact (mul_le_mul_of_nonneg_left hdiam
          (mul_nonneg (stepSize_pos hv.1 hv.2.1 hv.2.2.2.1 0).le hv.1.le)).trans
          (initial_root_scale hv.1 hv.2.1 hv.2.2.2.1)
      · have hw := trajectory_warm_distance hv hF hmono (show 1 ≤ t by omega) ht.le
          (fun k hk => ih k hk (by omega)) hy hyvi
        exact warm_root_scale hv.1 hv.2.1 hv.2.2.2.1 (by omega) hw
    have hcert := repeatInner_certificate t (center p t (trajectory p F t)) y
      ‖(trajectory p F t).point - y‖ hv hF hmono hJ ht hy hyvi hsmall
      (innerCount p) (by unfold innerCount; omega) (trajectory p F t) hc le_rfl
    change ‖error p F t‖ ≤ (1 / 4 : ℝ) ^ innerCount p * ‖(trajectory p F t).point - y‖ at hcert
    apply hcert.trans
    calc
      (1 / 4 : ℝ) ^ innerCount p * ‖(trajectory p F t).point - y‖ ≤
          (1 / (outerCount p : ℝ) ^ 2) * p.D :=
        mul_le_mul (inner_precision p) hdiam (norm_nonneg _) (by positivity)
      _ = p.D / (outerCount p : ℝ) ^ 2 := by ring

lemma final_residual {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖) :
    ‖F (trajectory p F (outerCount p)).point + (trajectory p F (outerCount p)).normal‖ ≤ p.ε := by
  have hT := outerCount_pos p
  have hh := prefix_residual hv hF hmono (show outerCount p - 1 < outerCount p by omega)
    (fun t ht => trajectory_error hv hF hmono hJ t (by omega))
  have hi : outerCount p - 1 + 1 = outerCount p := by omega
  have hc : ((outerCount p - 1 : ℕ) : ℝ) + 1 = outerCount p := by exact_mod_cast hi
  simpa only [residual, hi, hc] using
    hh.trans (by simpa only [hc] using accuracy_budget hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1)

end LongTails.Proofs.CachedJacobianConvergence
