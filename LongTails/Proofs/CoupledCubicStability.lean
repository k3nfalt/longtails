import LongTails.Proofs.CappedCubicModel
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledCubicStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma model_recenter (H : E →L[ℝ] E) (g s u : E) (M : ℝ)
    (hH : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0) :
    CappedCubicModel.model H g 0 (M / 2) u =
      (1 / 2 : ℝ) * ⟪u - s, H (u - s)⟫ + M * ‖s‖ / 4 * ‖u - s‖ ^ 2 -
      (1 / 2 : ℝ) * ⟪s, H s⟫ - M * ‖s‖ / 4 * ‖s‖ ^ 2 +
      M / 6 * ‖u‖ ^ 3 - M * ‖s‖ / 4 * ‖u‖ ^ 2 := by
  have hg := congrArg (fun v : E => ⟪v, u⟫) hs
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hg
  have hsym : ⟪s, H u⟫ = ⟪u, H s⟫ := by rw [hH, real_inner_comm]
  have hcomm : ⟪H s, u⟫ = ⟪u, H s⟫ := real_inner_comm _ _
  have hsu : ⟪s, u⟫ = ⟪u, s⟫ := real_inner_comm _ _
  rw [hcomm, hsu] at hg
  simp only [CappedCubicModel.model, zero_mul, add_zero, map_sub,
    inner_sub_left, inner_sub_right, hsym, norm_sub_sq_real]
  nlinarith [hg]

lemma radial_model_gap (M r t : ℝ) :
    M * t ^ 3 / 6 - M * r * t ^ 2 / 4 + M * r ^ 3 / 12 =
      M / 12 * (t - r) ^ 2 * (2 * t + r) := by
  ring

lemma radial_model_minimum (M r t : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    -M * r ^ 3 / 12 ≤ M * t ^ 3 / 6 - M * r * t ^ 2 / 4 := by
  have h : 0 ≤ M / 12 * (t - r) ^ 2 * (2 * t + r) :=
    mul_nonneg (mul_nonneg (div_nonneg hM (by norm_num)) (sq_nonneg (t - r)))
    (show 0 ≤ 2 * t + r by positivity)
  rw [← radial_model_gap] at h
  linarith

lemma normalized_radius_bounds (t η : ℝ) (ht : 0 ≤ t)
    (hη : η ≤ 1 / 10000)
    (h : (t - 1) ^ 2 * (2 * t + 1) / 12 ≤
      η * (t + 1) + 3 / 4 * η * (t + 1) ^ 2) :
    1 / 2 < t ∧ t < 2 := by
  have hp : 0 ≤ (t + 1) + 3 / 4 * (t + 1) ^ 2 := by positivity
  have he := mul_le_mul_of_nonneg_right hη hp
  have hb : (t - 1) ^ 2 * (2 * t + 1) / 12 ≤
      (1 / 10000 : ℝ) * ((t + 1) + 3 / 4 * (t + 1) ^ 2) := by
    nlinarith [h, he]
  constructor
  · by_contra hn
    have hu : t ≤ 1 / 2 := le_of_not_gt hn
    have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
    have ht3 : 0 ≤ t ^ 3 := by positivity
    nlinarith [hb]
  · by_contra hn
    have hl : 2 ≤ t := le_of_not_gt hn
    have hc : 0 ≤ t ^ 2 * (t - 2) := mul_nonneg (sq_nonneg t) (by linarith)
    have hq : 0 ≤ (t - 2) ^ 2 := sq_nonneg _
    nlinarith [hb]

lemma radius_bounds (M r t η p : ℝ) (hM : 0 < M) (hr : 0 < r)
    (ht : 0 ≤ t) (hp : 0 ≤ p) (hη : η ≤ 1 / 10000)
    (h : (1 - η) / 2 * p + M / 12 * (t - r) ^ 2 * (2 * t + r) ≤
      η * M * r ^ 2 * (t + r) + 3 / 4 * η * M * r * (t + r) ^ 2) :
    r / 2 < t ∧ t < 2 * r := by
  have hpos : 0 < M * r ^ 3 := by positivity
  have hpp : 0 ≤ (1 - η) / 2 * p :=
    mul_nonneg (by linarith) hp
  have hbase : M / 12 * (t - r) ^ 2 * (2 * t + r) ≤
      η * M * r ^ 2 * (t + r) + 3 / 4 * η * M * r * (t + r) ^ 2 := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hbase (le_of_lt hpos)
  have hleft : (M / 12 * (t - r) ^ 2 * (2 * t + r)) / (M * r ^ 3) =
      (t / r - 1) ^ 2 * (2 * (t / r) + 1) / 12 := by
    field_simp [ne_of_gt hM, ne_of_gt hr]
  have hright : (η * M * r ^ 2 * (t + r) +
      3 / 4 * η * M * r * (t + r) ^ 2) / (M * r ^ 3) =
      η * (t / r + 1) + 3 / 4 * η * (t / r + 1) ^ 2 := by
    field_simp [ne_of_gt hM, ne_of_gt hr]
  rw [hleft, hright] at hdiv
  obtain ⟨hlo, hhi⟩ := normalized_radius_bounds (t / r) η
    (div_nonneg ht (le_of_lt hr)) hη hdiv
  constructor
  · have := (lt_div_iff₀ hr).mp hlo
    linarith
  · exact (div_lt_iff₀ hr).mp hhi

lemma coercive_displacement_bound (M r t η p : ℝ) (hM : 0 < M) (hr : 0 < r)
    (ht : 0 ≤ t) (hp : 0 ≤ p) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (h : (1 - η) / 2 * p + M / 12 * (t - r) ^ 2 * (2 * t + r) ≤
      η * M * r ^ 2 * (t + r) + 3 / 4 * η * M * r * (t + r) ^ 2) :
    p ≤ 20 * η * M * r ^ 3 := by
  have hrad := radius_bounds M r t η p hM hr ht hp hη h
  have hsum : t + r ≤ 3 * r := by linarith
  have hsq : (t + r) ^ 2 ≤ 9 * r ^ 2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ η * M * r ^ 2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 3 / 4 * η * M * r by positivity)
  have hc : 0 ≤ M / 12 * (t - r) ^ 2 * (2 * t + r) := by positivity
  have hd := mul_le_mul_of_nonneg_right hη hp
  have he : 0 ≤ η * M * r ^ 3 := by positivity
  nlinarith [ha, hb, hc, hd, he]

lemma stationary_model_value (H : E →L[ℝ] E) (g s : E) (M : ℝ)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0)
    (hpsd : 0 ≤ ⟪s, H s⟫ + M / 2 * ‖s‖ ^ 3) :
    CappedCubicModel.model H g 0 (M / 2) s ≤ -M * ‖s‖ ^ 3 / 12 := by
  have hh := congrArg (fun v : E => ⟪v, s⟫) hs
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at hh
  have hcomm : ⟪H s, s⟫ = ⟪s, H s⟫ := real_inner_comm _ _
  rw [hcomm] at hh
  simp only [CappedCubicModel.model, zero_mul, add_zero]
  nlinarith

lemma perturbed_model_decrease (m mstar M r η : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (hstar : mstar ≤ -M * r ^ 3 / 12)
    (hpert : m ≤ mstar + (10 * η ^ 2 + 39 / 4 * η) * M * r ^ 3) :
    m ≤ -M * r ^ 3 / 16 := by
  have hs : η ^ 2 ≤ η / 10000 := by nlinarith
  have he : 10 * η ^ 2 + 39 / 4 * η ≤ 1 / 48 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ M * r ^ 3 by positivity)
  nlinarith

lemma model_error_difference (H D : E →L[ℝ] E) (g e s u : E) (M : ℝ)
    (hD : ∀ x y : E, ⟪x, D y⟫ = ⟪D x, y⟫) :
    CappedCubicModel.model (H + D) (g + e) 0 (M / 2) u -
      CappedCubicModel.model (H + D) (g + e) 0 (M / 2) s -
      (CappedCubicModel.model H g 0 (M / 2) u -
        CappedCubicModel.model H g 0 (M / 2) s) =
      ⟪e + D s, u - s⟫ + (1 / 2 : ℝ) * ⟪u - s, D (u - s)⟫ := by
  have hsym : ⟪s, D u⟫ = ⟪u, D s⟫ := by rw [hD, real_inner_comm]
  have hcomm : ⟪D s, u⟫ = ⟪u, D s⟫ := real_inner_comm _ _
  have hself : ⟪D s, s⟫ = ⟪s, D s⟫ := real_inner_comm _ _
  simp only [CappedCubicModel.model, add_apply, inner_add_left,
    inner_add_right, zero_mul, add_zero, map_sub, inner_sub_left, inner_sub_right,
    hsym, hcomm, hself]
  ring


lemma model_gap_identity (H : E →L[ℝ] E) (g s u : E) (M : ℝ)
    (hH : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0) :
    CappedCubicModel.model H g 0 (M / 2) u -
      CappedCubicModel.model H g 0 (M / 2) s =
      (1 / 2 : ℝ) * (⟪u - s, H (u - s)⟫ + M * ‖s‖ / 2 * ‖u - s‖ ^ 2) +
      M / 12 * (‖u‖ - ‖s‖) ^ 2 * (2 * ‖u‖ + ‖s‖) := by
  rw [model_recenter H g s u M hH hs, model_recenter H g s s M hH hs]
  simp only [sub_self, map_zero, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add]
  ring

lemma coercive_model_comparison (H D : E →L[ℝ] E) (g e s u : E) (M η : ℝ)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hH : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫)
    (hD : ∀ x y : E, ⟪x, D y⟫ = ⟪D x, y⟫)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0)
    (hq : ‖e + D s‖ ≤ η * M * ‖s‖ ^ 2)
    (hform : |⟪u - s, D (u - s)⟫| ≤
      η * (⟪u - s, H (u - s)⟫ + 2 * M * ‖s‖ * ‖u - s‖ ^ 2))
    (hu : CappedCubicModel.model (H + D) (g + e) 0 (M / 2) u ≤
      CappedCubicModel.model (H + D) (g + e) 0 (M / 2) s) :
    (1 - η) / 2 * (⟪u - s, H (u - s)⟫ + M * ‖s‖ / 2 * ‖u - s‖ ^ 2) +
      M / 12 * (‖u‖ - ‖s‖) ^ 2 * (2 * ‖u‖ + ‖s‖) ≤
      η * M * ‖s‖ ^ 2 * (‖u‖ + ‖s‖) +
      3 / 4 * η * M * ‖s‖ * (‖u‖ + ‖s‖) ^ 2 := by
  have he := model_error_difference H D g e s u M hD
  have hg := model_gap_identity H g s u M hH hs
  have hi := abs_real_inner_le_norm (e + D s) (u - s)
  have hqmul := mul_le_mul_of_nonneg_right hq (norm_nonneg (u - s))
  have hilow := neg_abs_le ⟪e + D s, u - s⟫
  have hdlow := neg_abs_le ⟪u - s, D (u - s)⟫
  have hn := norm_sub_le u s
  have hnsq : ‖u - s‖ ^ 2 ≤ (‖u‖ + ‖s‖) ^ 2 := by
    nlinarith [norm_nonneg (u - s), norm_nonneg u, norm_nonneg s]
  have hfirst := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ η * M * ‖s‖ ^ 2 by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hnsq
    (show 0 ≤ 3 / 4 * η * M * ‖s‖ by positivity)
  nlinarith [he, hg, hi, hqmul, hilow, hdlow, hform, hfirst, hsecond]


lemma stable_model_decrease (H D : E →L[ℝ] E) (g e s u : E) (M η : ℝ)
    (hM : 0 < M) (hspos : 0 < ‖s‖) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (hH : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫)
    (hD : ∀ x y : E, ⟪x, D y⟫ = ⟪D x, y⟫)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0)
    (hpsd : ∀ v : E, 0 ≤ ⟪v, H v⟫ + M * ‖s‖ / 2 * ‖v‖ ^ 2)
    (hq : ‖e + D s‖ ≤ η * M * ‖s‖ ^ 2)
    (hform : ∀ v : E, |⟪v, D v⟫| ≤ η * (⟪v, H v⟫ + 2 * M * ‖s‖ * ‖v‖ ^ 2))
    (hu : CappedCubicModel.model (H + D) (g + e) 0 (M / 2) u ≤
      CappedCubicModel.model (H + D) (g + e) 0 (M / 2) s) :
    ‖s‖ / 2 < ‖u‖ ∧ ‖u‖ < 2 * ‖s‖ ∧
      CappedCubicModel.model H g 0 (M / 2) u ≤ -M * ‖s‖ ^ 3 / 16 := by
  let p := ⟪u - s, H (u - s)⟫ + M * ‖s‖ / 2 * ‖u - s‖ ^ 2
  have hp : 0 ≤ p := hpsd (u - s)
  have hc := coercive_model_comparison H D g e s u M η hM.le hη0 hH hD hs hq
    (hform (u - s)) hu
  have hrad := radius_bounds M ‖s‖ ‖u‖ η p hM hspos (norm_nonneg u) hp hη hc
  have hpb := coercive_displacement_bound M ‖s‖ ‖u‖ η p hM hspos
    (norm_nonneg u) hp hη0 hη hc
  refine ⟨hrad.1, hrad.2, ?_⟩
  apply perturbed_model_decrease _ (CappedCubicModel.model H g 0 (M / 2) s)
    M ‖s‖ η hM.le (norm_nonneg s) hη0 hη
  · apply stationary_model_value H g s M hs
    have hh := hpsd s
    nlinarith
  · have he := model_error_difference H D g e s u M hD
    have hi := abs_real_inner_le_norm (e + D s) (u - s)
    have hqmul := mul_le_mul_of_nonneg_right hq (norm_nonneg (u - s))
    have hilow := neg_abs_le ⟪e + D s, u - s⟫
    have hdlow := neg_abs_le ⟪u - s, D (u - s)⟫
    have hf := hform (u - s)
    have hd : ‖u - s‖ ≤ 3 * ‖s‖ := (norm_sub_le u s).trans (by linarith [hrad.2])
    have hdsq : ‖u - s‖ ^ 2 ≤ 9 * ‖s‖ ^ 2 := by
      nlinarith [norm_nonneg (u - s), norm_nonneg s]
    have hfirst := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ η * M * ‖s‖ ^ 2 by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hdsq
      (show 0 ≤ 3 / 4 * η * M * ‖s‖ by positivity)
    have hthird := mul_le_mul_of_nonneg_left hpb (show 0 ≤ η / 2 by positivity)
    dsimp [p] at hthird
    nlinarith [he, hi, hqmul, hilow, hdlow, hf, hfirst, hsecond, hthird]


lemma stable_hessian_displacement (H D : E →L[ℝ] E) (g e s u : E) (M η : ℝ)
    (hM : 0 ≤ M) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (hs : g + H s + (M / 2 * ‖s‖) • s = 0)
    (hu : g + e + (H + D) u + (M / 2 * ‖u‖) • u = 0)
    (hradius : ‖u‖ ≤ 2 * ‖s‖)
    (hq : ‖e + D s‖ ≤ η * M * ‖s‖ ^ 2)
    (herror : ‖D (u - s)‖ ≤ η * (‖H (u - s)‖ + M * ‖s‖ * ‖u - s‖)) :
    ‖H (u - s)‖ ≤ 3 * M * ‖s‖ ^ 2 := by
  have hz : H (u - s) + (e + D s) + D (u - s) +
      (M / 2 * ‖u‖) • u - (M / 2 * ‖s‖) • s = 0 := by
    calc
      _ = (g + e + (H + D) u + (M / 2 * ‖u‖) • u) -
          (g + H s + (M / 2 * ‖s‖) • s) := by
        simp only [add_apply, map_sub]
        abel
      _ = 0 := by rw [hu, hs, sub_self]
  have hid : H (u - s) = -(e + D s) - D (u - s) -
      (M / 2 * ‖u‖) • u + (M / 2 * ‖s‖) • s := by
    apply eq_of_sub_eq_zero
    calc
      _ = H (u - s) + (e + D s) + D (u - s) +
          (M / 2 * ‖u‖) • u - (M / 2 * ‖s‖) • s := by abel
      _ = 0 := hz
  have hnorm : ‖H (u - s)‖ ≤ ‖e + D s‖ + ‖D (u - s)‖ +
      M / 2 * ‖u‖ ^ 2 + M / 2 * ‖s‖ ^ 2 := by
    rw [hid]
    calc
      _ ≤ ‖-(e + D s) - D (u - s) - (M / 2 * ‖u‖) • u‖ +
          ‖(M / 2 * ‖s‖) • s‖ := norm_add_le _ _
      _ ≤ (‖-(e + D s) - D (u - s)‖ + ‖(M / 2 * ‖u‖) • u‖) +
          ‖(M / 2 * ‖s‖) • s‖ := add_le_add (norm_sub_le (-(e + D s) - D (u - s))
            ((M / 2 * ‖u‖) • u)) le_rfl
      _ ≤ (‖-(e + D s)‖ + ‖D (u - s)‖ + ‖(M / 2 * ‖u‖) • u‖) +
          ‖(M / 2 * ‖s‖) • s‖ := add_le_add
            (add_le_add (norm_sub_le (-(e + D s)) (D (u - s))) le_rfl) le_rfl
      _ = _ := by
        simp only [norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ M / 2 * ‖u‖ by positivity),
          abs_of_nonneg (show 0 ≤ M / 2 * ‖s‖ by positivity)]
        ring
  have hd : ‖u - s‖ ≤ 3 * ‖s‖ := (norm_sub_le u s).trans (by linarith)
  have ht : ‖u‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg s]
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ η * M * ‖s‖ by positivity)
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ M / 2 by positivity)
  have he := mul_le_mul_of_nonneg_right hη (norm_nonneg (H (u - s)))
  have he' := mul_le_mul_of_nonneg_right hη (show 0 ≤ M * ‖s‖ ^ 2 by positivity)
  nlinarith [hnorm, herror, hq, hd', ht', he, he']


lemma sampled_stationarity_identity (H D : E →L[ℝ] E) (g e s u : E) (M : ℝ)
    (hu : g + e + (H + D) u + (M / 2 * ‖u‖) • u = 0) :
    g + H u = -(e + D s) - D (u - s) - (M / 2 * ‖u‖) • u := by
  apply eq_of_sub_eq_zero
  calc
    _ = g + e + (H + D) u + (M / 2 * ‖u‖) • u := by
      simp only [add_apply, map_sub]
      abel
    _ = 0 := hu

lemma stable_gradient_bound (H D : E →L[ℝ] E) (g e s u G : E) (M ρ η : ℝ)
    (hM : 0 ≤ M) (hρM : ρ ≤ M) (hη : η ≤ 1 / 10000)
    (hu : g + e + (H + D) u + (M / 2 * ‖u‖) • u = 0)
    (hradius : ‖u‖ ≤ 2 * ‖s‖)
    (hq : ‖e + D s‖ ≤ η * M * ‖s‖ ^ 2)
    (herror : ‖D (u - s)‖ ≤ 6 * η * M * ‖s‖ ^ 2)
    (hremainder : ‖G - (g + H u)‖ ≤ ρ / 2 * ‖u‖ ^ 2) :
    ‖G‖ ≤ 5 * M * ‖s‖ ^ 2 := by
  have hid := sampled_stationarity_identity H D g e s u M hu
  have hmodel : ‖g + H u‖ ≤ ‖e + D s‖ + ‖D (u - s)‖ + M / 2 * ‖u‖ ^ 2 := by
    rw [hid]
    calc
      _ ≤ ‖-(e + D s) - D (u - s)‖ + ‖(M / 2 * ‖u‖) • u‖ := norm_sub_le _ _
      _ ≤ (‖-(e + D s)‖ + ‖D (u - s)‖) + ‖(M / 2 * ‖u‖) • u‖ :=
        add_le_add (norm_sub_le (-(e + D s)) (D (u - s))) le_rfl
      _ = _ := by
        simp only [norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ M / 2 * ‖u‖ by positivity)]
        ring
  have hnorm : ‖G‖ ≤ ‖G - (g + H u)‖ + ‖g + H u‖ := by
    simpa only [sub_add_cancel] using norm_add_le (G - (g + H u)) (g + H u)
  have ht : ‖u‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg s]
  have ht' := mul_le_mul_of_nonneg_left ht hM
  have hρ' := mul_le_mul_of_nonneg_right hρM (sq_nonneg ‖u‖)
  have hη' := mul_le_mul_of_nonneg_right hη (show 0 ≤ M * ‖s‖ ^ 2 by positivity)
  nlinarith [hnorm, hmodel, hq, herror, hremainder, ht', hρ', hη']


lemma stable_curvature_bound (H Hnew : E →L[ℝ] E) (s u : E) (M ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρM : ρ ≤ M)
    (hpsd : ∀ v : E, 0 ≤ ⟪v, H v⟫ + M * ‖s‖ / 2 * ‖v‖ ^ 2)
    (hradius : ‖u‖ ≤ 2 * ‖s‖) (hchange : ‖Hnew - H‖ ≤ ρ * ‖u‖)
    (v : E) : -(5 / 2) * M * ‖s‖ * ‖v‖ ^ 2 ≤ ⟪v, Hnew v⟫ := by
  have hbound : ‖(Hnew - H) v‖ ≤ 2 * M * ‖s‖ * ‖v‖ := by
    have hh := (Hnew - H).le_opNorm v
    have hc := mul_le_mul_of_nonneg_right hchange (norm_nonneg v)
    have hr := mul_le_mul_of_nonneg_left hradius hρ
    have hm := mul_le_mul_of_nonneg_right hρM (norm_nonneg s)
    have hs := mul_le_mul_of_nonneg_right (show ρ * ‖u‖ ≤ 2 * M * ‖s‖ by linarith)
      (norm_nonneg v)
    exact hh.trans (hc.trans (by nlinarith))
  have hi := abs_real_inner_le_norm v ((Hnew - H) v)
  have hn := neg_abs_le ⟪v, (Hnew - H) v⟫
  have hb := mul_le_mul_of_nonneg_left hbound (norm_nonneg v)
  simp only [sub_apply, inner_sub_right] at hi hn hb
  nlinarith [hpsd v]

lemma stopping_accuracy (ρ ε t : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (ht : 0 ≤ t) (hstop : t ≤ Real.sqrt (ε / ρ) / 5) :
    20 * ρ * t ^ 2 ≤ ε ∧ 5 * ρ * t ≤ Real.sqrt (ρ * ε) := by
  have hs := Real.sq_sqrt (div_nonneg hε.le hρ.le)
  have hr := Real.sqrt_nonneg (ε / ρ)
  have hden : ε / ρ * ρ = ε := div_mul_cancel₀ ε hρ.ne'
  have ht2 : 25 * t ^ 2 ≤ ε / ρ := by nlinarith
  have htρ := mul_le_mul_of_nonneg_left ht2 hρ.le
  constructor
  · nlinarith [mul_nonneg hρ.le (sq_nonneg t)]
  · have hmul := mul_le_mul_of_nonneg_left htρ hρ.le
    have hden2 := congrArg (fun z : ℝ => ρ * z) hden
    have hs' := Real.sq_sqrt (mul_nonneg hρ.le hε.le)
    have hn := Real.sqrt_nonneg (ρ * ε)
    nlinarith

end LongTails.Proofs.CoupledCubicStability
