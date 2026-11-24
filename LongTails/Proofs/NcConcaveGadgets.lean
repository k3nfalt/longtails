import LongTails.Proofs.NcConcaveHuber

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveGadgets

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars
open LongTails.Proofs.NcConcaveHuber

noncomputable def rampR (θ t : ℝ) : ℝ := ramp (t / θ - 1)

noncomputable def rampL (θ t : ℝ) : ℝ := ramp (-t / θ - 1)

noncomputable def zeta (θ t : ℝ) : ℝ := θ * (rampR θ t - rampL θ t)

noncomputable def dzeta (θ t : ℝ) : ℝ := rampSlope (t / θ - 1) + rampSlope (-t / θ - 1)

noncomputable def omega (θ t : ℝ) : ℝ := θ * (rampR θ t + rampL θ t)

noncomputable def domega (θ t : ℝ) : ℝ := rampSlope (t / θ - 1) - rampSlope (-t / θ - 1)

lemma rampR_model {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    0 ≤ rampR θ y - rampR θ x - rampSlope (x / θ - 1) / θ * (y - x) ∧
      rampR θ y - rampR θ x - rampSlope (x / θ - 1) / θ * (y - x) ≤ (y - x) ^ 2 / (2 * θ ^ 2) := by
  have h := ramp_model (x / θ - 1) (y / θ - 1)
  have e1 : rampSlope (x / θ - 1) * (y / θ - 1 - (x / θ - 1)) = rampSlope (x / θ - 1) / θ * (y - x) := by
    field_simp; ring
  have e2 : (y / θ - 1 - (x / θ - 1)) ^ 2 / 2 = (y - x) ^ 2 / (2 * θ ^ 2) := by field_simp; ring
  rw [e1, e2] at h
  exact h

lemma rampL_model {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    0 ≤ rampL θ y - rampL θ x + rampSlope (-x / θ - 1) / θ * (y - x) ∧
      rampL θ y - rampL θ x + rampSlope (-x / θ - 1) / θ * (y - x) ≤ (y - x) ^ 2 / (2 * θ ^ 2) := by
  have h := ramp_model (-x / θ - 1) (-y / θ - 1)
  have e1 : rampSlope (-x / θ - 1) * (-y / θ - 1 - (-x / θ - 1)) =
      -(rampSlope (-x / θ - 1) / θ * (y - x)) := by field_simp; ring
  have e2 : (-y / θ - 1 - (-x / θ - 1)) ^ 2 / 2 = (y - x) ^ 2 / (2 * θ ^ 2) := by field_simp; ring
  rw [e1, e2] at h
  unfold rampL
  constructor <;> linarith [h.1, h.2]

lemma zeta_model {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    |zeta θ y - zeta θ x - dzeta θ x * (y - x)| ≤ 1 / (2 * θ) * (y - x) ^ 2 := by
  have h1 := rampR_model hθ x y
  have h2 := rampL_model hθ x y
  have e : zeta θ y - zeta θ x - dzeta θ x * (y - x) =
      θ * ((rampR θ y - rampR θ x - rampSlope (x / θ - 1) / θ * (y - x)) -
        (rampL θ y - rampL θ x + rampSlope (-x / θ - 1) / θ * (y - x))) := by
    simp only [zeta, dzeta]; field_simp; ring
  rw [e, abs_mul, abs_of_pos hθ]
  have hb : |(rampR θ y - rampR θ x - rampSlope (x / θ - 1) / θ * (y - x)) -
      (rampL θ y - rampL θ x + rampSlope (-x / θ - 1) / θ * (y - x))| ≤ (y - x) ^ 2 / (2 * θ ^ 2) := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc θ * _ ≤ θ * ((y - x) ^ 2 / (2 * θ ^ 2)) := mul_le_mul_of_nonneg_left hb hθ.le
    _ = 1 / (2 * θ) * (y - x) ^ 2 := by field_simp

lemma zeta_hasDerivAt {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : HasDerivAt (zeta θ) (dzeta θ x) x :=
  hasDerivAt_of_model (zeta_model hθ) x

lemma omega_model {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    0 ≤ omega θ y - omega θ x - domega θ x * (y - x) ∧
      omega θ y - omega θ x - domega θ x * (y - x) ≤ 1 / θ * (y - x) ^ 2 := by
  have h1 := rampR_model hθ x y
  have h2 := rampL_model hθ x y
  have e : omega θ y - omega θ x - domega θ x * (y - x) =
      θ * ((rampR θ y - rampR θ x - rampSlope (x / θ - 1) / θ * (y - x)) +
        (rampL θ y - rampL θ x + rampSlope (-x / θ - 1) / θ * (y - x))) := by
    simp only [omega, domega]; field_simp; ring
  rw [e]
  constructor
  · exact mul_nonneg hθ.le (by linarith [h1.1, h2.1])
  · calc θ * _ ≤ θ * ((y - x) ^ 2 / (2 * θ ^ 2) + (y - x) ^ 2 / (2 * θ ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1.2 h2.2) hθ.le
      _ = 1 / θ * (y - x) ^ 2 := by field_simp; ring

lemma omega_hasDerivAt {θ : ℝ} (hθ : 0 < θ) (x : ℝ) : HasDerivAt (omega θ) (domega θ x) x :=
  hasDerivAt_of_model (C := 1 / θ) (fun x y => by
    have h := omega_model hθ x y
    rw [abs_of_nonneg h.1]; exact h.2) x

lemma rampR_eq_zero {θ t : ℝ} (hθ : 0 < θ) (ht : t ≤ θ) : rampR θ t = 0 := by
  have : t / θ - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hθ]; exact ht
  simp [rampR, ramp, this]

lemma rampL_eq_zero {θ t : ℝ} (hθ : 0 < θ) (ht : -θ ≤ t) : rampL θ t = 0 := by
  have : -t / θ - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hθ]; linarith
  simp [rampL, ramp, this]

lemma slopeR_eq_zero {θ t : ℝ} (hθ : 0 < θ) (ht : t ≤ θ) : rampSlope (t / θ - 1) = 0 := by
  have : t / θ - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hθ]; exact ht
  simp [rampSlope, max_eq_left this]

lemma slopeL_eq_zero {θ t : ℝ} (hθ : 0 < θ) (ht : -θ ≤ t) : rampSlope (-t / θ - 1) = 0 := by
  have : -t / θ - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hθ]; linarith
  simp [rampSlope, max_eq_left this]

lemma zeta_small {θ t : ℝ} (hθ : 0 < θ) (ht : |t| ≤ θ) : zeta θ t = 0 := by
  have h := abs_le.mp ht
  simp [zeta, rampR_eq_zero hθ h.2, rampL_eq_zero hθ h.1]

lemma dzeta_small {θ t : ℝ} (hθ : 0 < θ) (ht : |t| ≤ θ) : dzeta θ t = 0 := by
  have h := abs_le.mp ht
  simp [dzeta, slopeR_eq_zero hθ h.2, slopeL_eq_zero hθ h.1]

lemma omega_small {θ t : ℝ} (hθ : 0 < θ) (ht : |t| ≤ θ) : omega θ t = 0 := by
  have h := abs_le.mp ht
  simp [omega, rampR_eq_zero hθ h.2, rampL_eq_zero hθ h.1]

lemma domega_small {θ t : ℝ} (hθ : 0 < θ) (ht : |t| ≤ θ) : domega θ t = 0 := by
  have h := abs_le.mp ht
  simp [domega, slopeR_eq_zero hθ h.2, slopeL_eq_zero hθ h.1]

lemma rampR_nonneg (θ t : ℝ) : 0 ≤ rampR θ t := by
  simp only [rampR, ramp]; split_ifs <;> nlinarith

lemma rampL_nonneg (θ t : ℝ) : 0 ≤ rampL θ t := by
  simp only [rampL, ramp]; split_ifs <;> nlinarith

lemma rampR_convex (θ : ℝ) (hθ : 0 < θ) : ConvexOn ℝ Set.univ (rampR θ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hzdef
  have h1 := (rampR_model hθ z x).1
  have h2 := (rampR_model hθ z y).1
  have hz : a * (x - z) + b * (y - z) = 0 := by
    rw [hzdef]; linear_combination (-(a * x + b * y)) * hab
  have key : a * (rampR θ x - rampR θ z - rampSlope (z / θ - 1) / θ * (x - z)) +
      b * (rampR θ y - rampR θ z - rampSlope (z / θ - 1) / θ * (y - z)) =
      a * rampR θ x + b * rampR θ y - rampR θ z := by
    linear_combination (-rampR θ z) * hab - (rampSlope (z / θ - 1) / θ) * hz
  linarith [mul_nonneg ha h1, mul_nonneg hb h2]

lemma rampL_convex (θ : ℝ) (hθ : 0 < θ) : ConvexOn ℝ Set.univ (rampL θ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y with hzdef
  have h1 := (rampL_model hθ z x).1
  have h2 := (rampL_model hθ z y).1
  have hz : a * (x - z) + b * (y - z) = 0 := by
    rw [hzdef]; linear_combination (-(a * x + b * y)) * hab
  have key : a * (rampL θ x - rampL θ z + rampSlope (-z / θ - 1) / θ * (x - z)) +
      b * (rampL θ y - rampL θ z + rampSlope (-z / θ - 1) / θ * (y - z)) =
      a * rampL θ x + b * rampL θ y - rampL θ z := by
    linear_combination (-rampL θ z) * hab + (rampSlope (-z / θ - 1) / θ) * hz
  linarith [mul_nonneg ha h1, mul_nonneg hb h2]

lemma repair_concave {θ lam c : ℝ} (hθ : 0 < θ) (hc : |c| ≤ lam) :
    ConcaveOn ℝ Set.univ (fun t => c * zeta θ t - lam * omega θ t) := by
  have h1 : 0 ≤ lam - c := by linarith [le_abs_self c]
  have h2 : 0 ≤ lam + c := by linarith [neg_abs_le c]
  have hcv : ConvexOn ℝ Set.univ (fun t => θ * ((lam - c) * rampR θ t + (lam + c) * rampL θ t)) :=
    (((rampR_convex θ hθ).smul h1).add ((rampL_convex θ hθ).smul h2)).smul hθ.le
  have he : (fun t => c * zeta θ t - lam * omega θ t) =
      fun t => -(θ * ((lam - c) * rampR θ t + (lam + c) * rampL θ t)) := by
    funext t; simp only [zeta, omega]; ring
  rw [he]
  exact hcv.neg

lemma ramp_bounds (s : ℝ) : s - 1 / 2 ≤ ramp s ∧ ramp s ≤ max 0 s := by
  simp only [ramp]
  split_ifs with h1 h2
  · exact ⟨by linarith, le_max_left _ _⟩
  · exact ⟨by nlinarith [sq_nonneg (s - 1)], by
      rw [max_eq_right (by linarith)]; nlinarith⟩
  · exact ⟨le_refl _ |>.trans' (by linarith), by rw [max_eq_right (by linarith)]; linarith⟩

lemma zeta_sub_le {θ t : ℝ} (hθ : 0 < θ) : |zeta θ t - t| ≤ 2 * θ := by
  rw [abs_le]
  rcases le_total 0 t with ht | ht
  · have hL := rampL_eq_zero hθ (by linarith : -θ ≤ t)
    have hb := ramp_bounds (t / θ - 1)
    have e1 : θ * (t / θ - 1) = t - θ := by field_simp
    have hmax : θ * max 0 (t / θ - 1) ≤ t := by
      rcases le_total 0 (t / θ - 1) with h | h
      · rw [max_eq_right h, e1]; linarith
      · rw [max_eq_left h]; linarith
    simp only [zeta, hL, sub_zero, rampR]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb.1 hθ.le]
    · nlinarith [mul_le_mul_of_nonneg_left hb.2 hθ.le]
  · have hR := rampR_eq_zero hθ (by linarith : t ≤ θ)
    have hb := ramp_bounds (-t / θ - 1)
    have e1 : θ * (-t / θ - 1) = -t - θ := by field_simp
    have hmax : θ * max 0 (-t / θ - 1) ≤ -t := by
      rcases le_total 0 (-t / θ - 1) with h | h
      · rw [max_eq_right h, e1]; linarith
      · rw [max_eq_left h]; linarith
    simp only [zeta, hR, zero_sub, rampL]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb.2 hθ.le]
    · nlinarith [mul_le_mul_of_nonneg_left hb.1 hθ.le]

end LongTails.Proofs.NcConcaveGadgets
