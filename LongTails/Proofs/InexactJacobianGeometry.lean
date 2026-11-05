import LongTails.Proofs.FrozenJacobianSplitting
import LongTails.Proofs.RiverValleyCalculus

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InexactJacobianGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma shifted_monotone {D J : E →L[ℝ] E} {δ : ℝ}
    (hD : ∀ v, 0 ≤ ⟪D v, v⟫) (herr : ‖J - D‖ ≤ δ) (v : E) :
    0 ≤ ⟪(J + δ • ContinuousLinearMap.id ℝ E) v, v⟫ := by
  have hn : ‖(J - D) v‖ ≤ δ * ‖v‖ :=
    ((J - D).le_opNorm v).trans (mul_le_mul_of_nonneg_right herr (norm_nonneg v))
  have hi := real_inner_le_norm (-((J - D) v)) v
  simp only [inner_neg_left, norm_neg, sub_apply,
    inner_sub_left] at hi
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  simp only [sub_apply] at hn
  have h := hD v
  nlinarith [mul_le_mul_of_nonneg_right hn (norm_nonneg v)]

lemma shifted_error {D J : E →L[ℝ] E} {δ : ℝ}
    (hδ : 0 ≤ δ) (herr : ‖J - D‖ ≤ δ) (v : E) :
    ‖(J + δ • ContinuousLinearMap.id ℝ E) v - D v‖ ≤ 2 * δ * ‖v‖ := by
  have hn : ‖(J - D) v‖ ≤ δ * ‖v‖ :=
    ((J - D).le_opNorm v).trans (mul_le_mul_of_nonneg_right herr (norm_nonneg v))
  have he : (J + δ • ContinuousLinearMap.id ℝ E) v - D v =
      (J - D) v + δ • v := by simp; abel
  rw [he]
  calc
    ‖(J - D) v + δ • v‖ ≤ ‖(J - D) v‖ + ‖δ • v‖ := norm_add_le _ _
    _ ≤ 2 * δ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
      linarith

lemma shifted_model_error {F : E → E} {D J : E →L[ℝ] E} {δ M : ℝ}
    (hδ : 0 ≤ δ) (herr : ‖J - D‖ ≤ δ) (c y : E)
    (htaylor : ‖F y - F c - D (y - c)‖ ≤ M * ‖y - c‖ ^ 2) :
    ‖F y - (F c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c))‖ ≤
      (2 * δ + M * ‖y - c‖) * ‖y - c‖ := by
  have he : F y - (F c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c)) =
      (F y - F c - D (y - c)) -
        ((J + δ • ContinuousLinearMap.id ℝ E) (y - c) - D (y - c)) := by abel
  rw [he]
  calc
    _ ≤ ‖F y - F c - D (y - c)‖ +
        ‖(J + δ • ContinuousLinearMap.id ℝ E) (y - c) - D (y - c)‖ := norm_sub_le _ _
    _ ≤ M * ‖y - c‖ ^ 2 + 2 * δ * ‖y - c‖ :=
      add_le_add htaylor (shifted_error hδ herr _)
    _ = _ := by ring

lemma affine_resolvent_distance (B : E →L[ℝ] E)
    (hB : ∀ v, 0 ≤ ⟪B v, v⟫) {a : ℝ} (ha : 0 ≤ a)
    (v c b y xs : E) (hy : y + a • (v + B (y - c)) = b) :
    ‖y - xs‖ ≤ ‖b - xs - a • (v + B (xs - c))‖ := by
  have h := FrozenJacobianSplitting.op_norm_ge B hB (β := 1) ha (y - xs)
  have he : (ContinuousLinearMap.id ℝ E + a • B) (y - xs) =
      b - xs - a • (v + B (xs - c)) := by
    rw [← hy]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub]
    module
  simpa only [one_smul, one_mul, he] using h

lemma affine_resolvent_bound (B : E →L[ℝ] E)
    (hB : ∀ v, 0 ≤ ⟪B v, v⟫) {a : ℝ} (ha : 0 ≤ a)
    (v c b y xs : E) (hy : y + a • (v + B (y - c)) = b) :
    ‖y - xs‖ ≤ ‖b - xs‖ + a * ‖v + B (xs - c)‖ := by
  calc
    ‖y - xs‖ ≤ ‖b - xs - a • (v + B (xs - c))‖ :=
      affine_resolvent_distance B hB ha v c b y xs hy
    _ ≤ ‖b - xs‖ + ‖a • (v + B (xs - c))‖ := norm_sub_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]

lemma strongly_monotone_certificate {G : E → E} {μ : ℝ} {xs y : E}
    (hμ : 0 < μ) (hzero : G xs = 0)
    (hstrong : ∀ x z, μ * ‖x - z‖ ^ 2 ≤ ⟪G x - G z, x - z⟫) :
    ‖y - xs‖ ≤ ‖G y‖ / μ := by
  have h := hstrong y xs
  rw [hzero, sub_zero] at h
  have hc := real_inner_le_norm (G y) (y - xs)
  rw [le_div_iff₀ hμ]
  rcases eq_or_lt_of_le (norm_nonneg (y - xs)) with hz | hp
  · rw [← hz, zero_mul]; exact norm_nonneg _
  · nlinarith

lemma relative_certificate_of_residual {G : E → E} {μ r : ℝ} {xs c y : E}
    (hμ : 0 < μ) (hzero : G xs = 0)
    (hstrong : ∀ x z, μ * ‖x - z‖ ^ 2 ≤ ⟪G x - G z, x - z⟫)
    (hr : r = ‖c - xs‖) (hres : ‖G y‖ ≤ μ * r / 4) :
    ‖G y‖ / μ ≤ ‖y - c‖ / 2 := by
  have hd := strongly_monotone_certificate hμ hzero hstrong (y := y)
  have he : ‖G y‖ / μ ≤ r / 4 := by
    rw [div_le_iff₀ hμ]
    nlinarith
  have ht : r ≤ ‖y - c‖ + ‖y - xs‖ := by
    rw [hr]
    have h : ‖c - xs‖ ≤ ‖c - y‖ + ‖y - xs‖ := by
      calc
        ‖c - xs‖ = ‖(c - y) + (y - xs)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rwa [norm_sub_rev c y] at h
  linarith [norm_nonneg (y - c)]

lemma local_step_bounds {δ M ρ : ℝ} (hδ : 0 ≤ δ) (hM : 0 < M) (hρ : 0 < ρ) :
    let t := 1 / (128 * δ + 512 * M * ρ)
    0 < t ∧ t * (14 * δ + 50 * M * ρ) ≤ 1 ∧
      t * (2 * δ + 12 * M * ρ) ≤ 1 / 2 := by
  dsimp only
  have hd : 0 < 128 * δ + 512 * M * ρ := by positivity
  have ht : 0 < 1 / (128 * δ + 512 * M * ρ) := one_div_pos.mpr hd
  have he : (1 / (128 * δ + 512 * M * ρ)) * (128 * δ + 512 * M * ρ) = 1 := by
    field_simp
  have hm : 0 ≤ M * ρ := by positivity
  refine ⟨ht, ?_, ?_⟩
  · nlinarith [mul_nonneg ht.le hδ, mul_nonneg ht.le hm]
  · nlinarith [mul_nonneg ht.le hδ, mul_nonneg ht.le hm]

lemma model_at_root_bound {G : E → E} {D J : E →L[ℝ] E} {δ M r ρ : ℝ}
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hr : 0 ≤ r) (hrρ : r ≤ ρ)
    (herr : ‖J - D‖ ≤ δ) (c xs : E) (hzero : G xs = 0)
    (hc : ‖c - xs‖ ≤ 7 * r)
    (htaylor : ‖G xs - G c - D (xs - c)‖ ≤ M * ‖xs - c‖ ^ 2) :
    ‖G c + (J + δ • ContinuousLinearMap.id ℝ E) (xs - c)‖ ≤
      (14 * δ + 50 * M * ρ) * r := by
  have h := shifted_model_error hδ herr c xs htaylor
  rw [hzero, zero_sub, norm_neg, norm_sub_rev xs c] at h
  have hnorm := norm_nonneg (c - xs)
  have hs : ‖c - xs‖ ^ 2 ≤ 49 * r ^ 2 := by nlinarith
  have hδc := mul_le_mul_of_nonneg_left hc hδ
  have hMs := mul_le_mul_of_nonneg_left hs hM
  have hMr := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hrρ hr) hM
  have hn := mul_nonneg hM (sq_nonneg r)
  nlinarith

lemma local_trial_control {G : E → E} {D J : E →L[ℝ] E} {δ M r ρ : ℝ}
    (hδ : 0 ≤ δ) (hM : 0 < M) (hr : 0 ≤ r) (hρ : 0 < ρ) (hrρ : r ≤ ρ)
    (hD : ∀ v, 0 ≤ ⟪D v, v⟫) (herr : ‖J - D‖ ≤ δ)
    (c b y xs : E) (hzero : G xs = 0) (hc : ‖c - xs‖ ≤ 7 * r)
    (hb : ‖b - xs‖ ≤ 4 * r)
    (htaylor : ∀ z, ‖G z - G c - D (z - c)‖ ≤ M * ‖z - c‖ ^ 2)
    (hy : y + (1 / (128 * δ + 512 * M * ρ)) •
      (G c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c)) = b) :
    ‖y - xs‖ ≤ 5 * r ∧
      ‖(1 / (128 * δ + 512 * M * ρ)) •
        (G y - (G c + (J + δ • ContinuousLinearMap.id ℝ E) (y - c)))‖ ≤
        ‖y - c‖ / 2 := by
  let t := 1 / (128 * δ + 512 * M * ρ)
  obtain ⟨ht, ht₁, ht₂⟩ := local_step_bounds hδ hM hρ
  change 0 < t at ht
  change t * _ ≤ _ at ht₁ ht₂
  have hp := model_at_root_bound hδ hM.le hr hrρ herr c xs hzero hc (htaylor xs)
  have hyb := affine_resolvent_bound (J + δ • ContinuousLinearMap.id ℝ E)
    (shifted_monotone hD herr) ht.le (G c) c b y xs hy
  have hyd : ‖y - xs‖ ≤ 5 * r := by
    have hp' := mul_le_mul_of_nonneg_left hp ht.le
    have ht' := mul_le_mul_of_nonneg_right ht₁ hr
    nlinarith
  refine ⟨hyd, ?_⟩
  have hs : ‖y - c‖ ≤ 12 * r := by
    have h := norm_sub_le_norm_sub_add_norm_sub y xs c
    rw [norm_sub_rev xs c] at h
    linarith
  have he := shifted_model_error hδ herr c y (htaylor y)
  have hcoeff : t * (2 * δ + M * ‖y - c‖) ≤ 1 / 2 := by
    have hs' : M * ‖y - c‖ ≤ 12 * M * ρ := by
      have h := mul_le_mul_of_nonneg_left hs hM.le
      have h' := mul_le_mul_of_nonneg_left hrρ hM.le
      nlinarith
    have h := mul_le_mul_of_nonneg_left hs' ht.le
    nlinarith
  change ‖t • _‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le]
  have he' := mul_le_mul_of_nonneg_left he ht.le
  have hc' := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (y - c))
  nlinarith

lemma regularized_strong {F : E → E} (b : E) (μ : ℝ)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) (x y : E) :
    μ * ‖x - y‖ ^ 2 ≤
      ⟪(F x + μ • (x - b)) - (F y + μ • (y - b)), x - y⟫ := by
  have he : (F x + μ • (x - b)) - (F y + μ • (y - b)) =
      (F x - F y) + μ • (x - y) := by module
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith [hmono x y]

lemma regularized_deriv {F : E → E} {D : E →L[ℝ] E} (b c : E) (μ : ℝ)
    (hd : HasFDerivAt F D c) :
    HasFDerivAt (fun x => F x + μ • (x - b))
      (D + μ • ContinuousLinearMap.id ℝ E) c := by
  exact hd.add (((hasFDerivAt_id c).sub_const b).const_smul μ)

lemma regularized_taylor {F : E → E} {DF : E → E →L[ℝ] E} {M : ℝ}
    (hM : 0 ≤ M) (hd : ∀ x, HasFDerivAt F (DF x) x)
    (hL : ∀ x y, ‖DF x - DF y‖ ≤ M * ‖x - y‖) (b c y : E) (μ : ℝ) :
    ‖(F y + μ • (y - b)) - (F c + μ • (c - b)) -
      (DF c + μ • ContinuousLinearMap.id ℝ E) (y - c)‖ ≤ M * ‖y - c‖ ^ 2 := by
  have h := OracleTemplate.RiverValley.taylor_lip hd hM hL c (y - c)
  have he : (F y + μ • (y - b)) - (F c + μ • (c - b)) -
      (DF c + μ • ContinuousLinearMap.id ℝ E) (y - c) = F y - F c - DF c (y - c) := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply]
    module
  rw [he]
  simpa only [add_sub_cancel] using h

lemma regularized_root [FiniteDimensional ℝ E] {F : E → E} {DF : E → E →L[ℝ] E}
    {M a : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hd : ∀ x, HasFDerivAt F (DF x) x)
    (hL : ∀ x y, ‖DF x - DF y‖ ≤ M * ‖x - y‖)
    (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) (b : E) :
    ∃ xs, F xs + (1 / a) • (xs - b) = 0 := by
  obtain ⟨xs, hxs⟩ := FrozenJacobianSplitting.resolvent_exists hM hd hL hmono ha b
  refine ⟨xs, ?_⟩
  have he : xs - b = -(a • F xs) := by rw [← hxs]; abel
  rw [he, smul_neg, smul_smul, one_div_mul_cancel ha.ne', one_smul, add_neg_cancel]

end LongTails.Proofs.InexactJacobianGeometry
