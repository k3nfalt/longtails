import LongTails.Proofs.SmoothConvexFiniteGeometry
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.QuasarHardProfiles

open SmoothConvexFiniteGeometry

lemma ramp_of_nonpos {t : ℝ} (h : t ≤ 0) : ramp t = 0 := by
  simp [ramp, h]

lemma ramp_of_mid {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ramp t = t ^ 2 / 2 := by
  unfold ramp
  split_ifs with h
  · have : t = 0 := le_antisymm h h0
    subst this
    norm_num
  · rfl

lemma ramp_of_ge {t : ℝ} (h : 1 ≤ t) : ramp t = t - 1 / 2 := by
  unfold ramp
  split_ifs with h0 h1
  · linarith
  · have : t = 1 := le_antisymm h1 h
    subst this
    norm_num
  · rfl

lemma rampSlope_of_nonpos {t : ℝ} (h : t ≤ 0) : rampSlope t = 0 := by
  simp [rampSlope, max_eq_left h]

lemma rampSlope_of_mid {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : rampSlope t = t := by
  simp [rampSlope, max_eq_right h0, min_eq_right h1]

lemma rampSlope_of_ge {t : ℝ} (h : 1 ≤ t) : rampSlope t = 1 := by
  simp [rampSlope, max_eq_right (by linarith : (0 : ℝ) ≤ t), min_eq_left h]

lemma ramp_nonneg (t : ℝ) : 0 ≤ ramp t := by
  unfold ramp
  split_ifs <;> nlinarith

noncomputable def bump (θ : ℝ) : ℝ :=
  35 / 4 - ramp (20 * θ - 1) / 2 + ramp (10 * θ - 9) + 50 * max (θ - 1) 0 ^ 2 +
    ramp (-20 * θ - 1) / 2

noncomputable def bumpSlope (θ : ℝ) : ℝ :=
  -10 * rampSlope (20 * θ - 1) + 10 * rampSlope (10 * θ - 9) + 100 * max (θ - 1) 0 -
    10 * rampSlope (-20 * θ - 1)

lemma maxsq_hasDerivAt (x : ℝ) :
    HasDerivAt (fun θ : ℝ => max (θ - 1) 0 ^ 2) (2 * max (x - 1) 0) x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun y => max (y - 1) 0 ^ 2 - max (x - 1) 0 ^ 2 - (y - x) • (2 * max (x - 1) 0)) =O[nhds x]
      (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with y
    simp only [Real.norm_eq_abs, smul_eq_mul, sq_abs, one_mul]
    have hy : |max (y - 1) 0 ^ 2 - max (x - 1) 0 ^ 2 - (y - x) * (2 * max (x - 1) 0)| ≤
        (y - x) ^ 2 := by
      rw [abs_le]
      simp only [max_def]
      split_ifs <;> constructor <;> nlinarith [sq_nonneg (y - x)]
    simpa [abs_of_nonneg (sq_nonneg (y - x))] using hy
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

lemma ramp_affine_hasDerivAt (c e x : ℝ) :
    HasDerivAt (fun θ => ramp (c * θ + e)) (rampSlope (c * x + e) * c) x := by
  have hf : HasDerivAt (fun θ : ℝ => c * θ + e) c x := by
    simpa using HasDerivAt.add_const e (HasDerivAt.const_mul c (hasDerivAt_id x))
  exact HasDerivAt.comp x (ramp_hasDerivAt (c * x + e)) hf

lemma bump_hasDerivAt (x : ℝ) : HasDerivAt bump (bumpSlope x) x := by
  have h1 : HasDerivAt (fun θ => ramp (20 * θ - 1)) (rampSlope (20 * x - 1) * 20) x := by
    simpa [sub_eq_add_neg] using ramp_affine_hasDerivAt 20 (-1) x
  have h2 : HasDerivAt (fun θ => ramp (10 * θ - 9)) (rampSlope (10 * x - 9) * 10) x := by
    simpa [sub_eq_add_neg] using ramp_affine_hasDerivAt 10 (-9) x
  have h3 := maxsq_hasDerivAt x
  have h4 : HasDerivAt (fun θ => ramp (-20 * θ - 1)) (rampSlope (-20 * x - 1) * -20) x := by
    simpa [sub_eq_add_neg] using ramp_affine_hasDerivAt (-20) (-1) x
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.add
    (HasDerivAt.const_sub (35 / 4) (HasDerivAt.div_const h1 2)) h2)
    (HasDerivAt.const_mul 50 h3)) (HasDerivAt.div_const h4 2)
  convert h using 1
  · funext θ
    simp only [bump, Pi.add_apply]
  · simp only [bumpSlope]
    ring

lemma bump_left {θ : ℝ} (h : θ ≤ -1 / 10) :
    bump θ = 8 - 10 * θ ∧ bumpSlope θ = -10 := by
  simp only [bump, bumpSlope, ramp_of_nonpos (by linarith : 20 * θ - 1 ≤ 0),
    ramp_of_nonpos (by linarith : 10 * θ - 9 ≤ 0), ramp_of_ge (by linarith : 1 ≤ -20 * θ - 1),
    rampSlope_of_nonpos (by linarith : 20 * θ - 1 ≤ 0),
    rampSlope_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    rampSlope_of_ge (by linarith : 1 ≤ -20 * θ - 1), max_eq_right (by linarith : θ - 1 ≤ 0)]
  constructor <;> ring

lemma bump_leftMid {θ : ℝ} (h0 : -1 / 10 ≤ θ) (h1 : θ ≤ -1 / 20) :
    bump θ = 35 / 4 + (-20 * θ - 1) ^ 2 / 4 ∧ bumpSlope θ = -10 * (-20 * θ - 1) := by
  simp only [bump, bumpSlope, ramp_of_nonpos (by linarith : 20 * θ - 1 ≤ 0),
    ramp_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    ramp_of_mid (by linarith : 0 ≤ -20 * θ - 1) (by linarith : -20 * θ - 1 ≤ 1),
    rampSlope_of_nonpos (by linarith : 20 * θ - 1 ≤ 0),
    rampSlope_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    rampSlope_of_mid (by linarith : 0 ≤ -20 * θ - 1) (by linarith : -20 * θ - 1 ≤ 1),
    max_eq_right (by linarith : θ - 1 ≤ 0)]
  constructor <;> ring

lemma bump_flat {θ : ℝ} (h0 : -1 / 20 ≤ θ) (h1 : θ ≤ 1 / 20) :
    bump θ = 35 / 4 ∧ bumpSlope θ = 0 := by
  simp only [bump, bumpSlope, ramp_of_nonpos (by linarith : 20 * θ - 1 ≤ 0),
    ramp_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    ramp_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    rampSlope_of_nonpos (by linarith : 20 * θ - 1 ≤ 0),
    rampSlope_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    rampSlope_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    max_eq_right (by linarith : θ - 1 ≤ 0)]
  constructor <;> ring

lemma bump_rightMid {θ : ℝ} (h0 : 1 / 20 ≤ θ) (h1 : θ ≤ 1 / 10) :
    bump θ = 35 / 4 - (20 * θ - 1) ^ 2 / 4 ∧ bumpSlope θ = -10 * (20 * θ - 1) := by
  simp only [bump, bumpSlope,
    ramp_of_mid (by linarith : 0 ≤ 20 * θ - 1) (by linarith : 20 * θ - 1 ≤ 1),
    ramp_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    ramp_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    rampSlope_of_mid (by linarith : 0 ≤ 20 * θ - 1) (by linarith : 20 * θ - 1 ≤ 1),
    rampSlope_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    rampSlope_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    max_eq_right (by linarith : θ - 1 ≤ 0)]
  constructor <;> ring

lemma bump_middle {θ : ℝ} (h0 : 1 / 10 ≤ θ) (h1 : θ ≤ 9 / 10) :
    bump θ = 19 / 2 - 10 * θ ∧ bumpSlope θ = -10 := by
  simp only [bump, bumpSlope, ramp_of_ge (by linarith : 1 ≤ 20 * θ - 1),
    ramp_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    ramp_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    rampSlope_of_ge (by linarith : 1 ≤ 20 * θ - 1),
    rampSlope_of_nonpos (by linarith : 10 * θ - 9 ≤ 0),
    rampSlope_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    max_eq_right (by linarith : θ - 1 ≤ 0)]
  constructor <;> ring

lemma bump_nearOne {θ : ℝ} (h0 : 9 / 10 ≤ θ) (h1 : θ ≤ 1) :
    bump θ = 50 * (1 - θ) ^ 2 ∧ bumpSlope θ = -100 * (1 - θ) := by
  simp only [bump, bumpSlope, ramp_of_ge (by linarith : 1 ≤ 20 * θ - 1),
    ramp_of_mid (by linarith : 0 ≤ 10 * θ - 9) (by linarith : 10 * θ - 9 ≤ 1),
    ramp_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    rampSlope_of_ge (by linarith : 1 ≤ 20 * θ - 1),
    rampSlope_of_mid (by linarith : 0 ≤ 10 * θ - 9) (by linarith : 10 * θ - 9 ≤ 1),
    rampSlope_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    max_eq_right (by linarith : θ - 1 ≤ 0)]
  constructor <;> ring

lemma bump_right {θ : ℝ} (h : 1 ≤ θ) :
    bump θ = 50 * (θ - 1) ^ 2 ∧ bumpSlope θ = 100 * (θ - 1) := by
  simp only [bump, bumpSlope, ramp_of_ge (by linarith : 1 ≤ 20 * θ - 1),
    ramp_of_ge (by linarith : 1 ≤ 10 * θ - 9),
    ramp_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    rampSlope_of_ge (by linarith : 1 ≤ 20 * θ - 1),
    rampSlope_of_ge (by linarith : 1 ≤ 10 * θ - 9),
    rampSlope_of_nonpos (by linarith : -20 * θ - 1 ≤ 0),
    max_eq_left (by linarith : 0 ≤ θ - 1)]
  constructor <;> ring

lemma bump_cases (θ : ℝ) (P : ℝ → ℝ → Prop)
    (hl : θ ≤ -1 / 10 → P (8 - 10 * θ) (-10))
    (hlm : -1 / 10 ≤ θ → θ ≤ -1 / 20 → P (35 / 4 + (-20 * θ - 1) ^ 2 / 4) (-10 * (-20 * θ - 1)))
    (hf : -1 / 20 ≤ θ → θ ≤ 1 / 20 → P (35 / 4) 0)
    (hrm : 1 / 20 ≤ θ → θ ≤ 1 / 10 → P (35 / 4 - (20 * θ - 1) ^ 2 / 4) (-10 * (20 * θ - 1)))
    (hm : 1 / 10 ≤ θ → θ ≤ 9 / 10 → P (19 / 2 - 10 * θ) (-10))
    (hn : 9 / 10 ≤ θ → θ ≤ 1 → P (50 * (1 - θ) ^ 2) (-100 * (1 - θ)))
    (hr : 1 ≤ θ → P (50 * (θ - 1) ^ 2) (100 * (θ - 1))) :
    P (bump θ) (bumpSlope θ) := by
  rcases le_total θ (-1 / 10) with h1 | h1
  · obtain ⟨e1, e2⟩ := bump_left h1; rw [e1, e2]; exact hl h1
  rcases le_total θ (-1 / 20) with h2 | h2
  · obtain ⟨e1, e2⟩ := bump_leftMid h1 h2; rw [e1, e2]; exact hlm h1 h2
  rcases le_total θ (1 / 20) with h3 | h3
  · obtain ⟨e1, e2⟩ := bump_flat h2 h3; rw [e1, e2]; exact hf h2 h3
  rcases le_total θ (1 / 10) with h4 | h4
  · obtain ⟨e1, e2⟩ := bump_rightMid h3 h4; rw [e1, e2]; exact hrm h3 h4
  rcases le_total θ (9 / 10) with h5 | h5
  · obtain ⟨e1, e2⟩ := bump_middle h4 h5; rw [e1, e2]; exact hm h4 h5
  rcases le_total θ 1 with h6 | h6
  · obtain ⟨e1, e2⟩ := bump_nearOne h5 h6; rw [e1, e2]; exact hn h5 h6
  · obtain ⟨e1, e2⟩ := bump_right h6; rw [e1, e2]; exact hr h6

lemma bump_nonneg (θ : ℝ) : 0 ≤ bump θ := by
  apply bump_cases θ (fun v _ => 0 ≤ v) <;> intros <;> nlinarith

lemma bump_one : bump 1 = 0 := by
  rw [(bump_right le_rfl).1]; ring

lemma bump_le_ten {θ : ℝ} (h0 : -1 / 10 < θ) (h1 : θ ≤ 9 / 10) : bump θ ≤ 10 := by
  apply bump_cases θ (fun v _ => v ≤ 10) <;> intros <;> nlinarith

lemma bump_slope_sign (θ : ℝ) : 0 ≤ (θ - 1) * bumpSlope θ := by
  apply bump_cases θ (fun _ s => 0 ≤ (θ - 1) * s) <;> intros <;> nlinarith

lemma bump_quasar {θ : ℝ} (h : 1 / 10 ≤ |θ|) : bump θ / 40 ≤ (θ - 1) * bumpSlope θ := by
  rcases le_abs'.mp h with h' | h'
  · apply bump_cases θ (fun v s => v / 40 ≤ (θ - 1) * s) <;> intros <;> nlinarith
  · apply bump_cases θ (fun v s => v / 40 ≤ (θ - 1) * s) <;> intros <;> nlinarith

lemma bump_middle_progress {θ : ℝ} (h0 : 1 / 10 ≤ θ) (h1 : θ ≤ 9 / 10) :
    1 ≤ (θ - 1) * bumpSlope θ := by
  rw [(bump_middle h0 h1).2]; nlinarith

lemma bump_flat_value {θ : ℝ} (h : |θ| ≤ 1 / 20) : bump θ = 35 / 4 :=
  (bump_flat (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])).1

lemma bump_flat_slope {θ : ℝ} (h : |θ| ≤ 1 / 20) : bumpSlope θ = 0 :=
  (bump_flat (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])).2

lemma maxpart_lipschitz (x y : ℝ) : |max (x - 1) 0 - max (y - 1) 0| ≤ |x - y| := by
  simp only [max_def, abs]
  split_ifs <;> linarith

lemma rampSlope_affine_lipschitz (c e x y : ℝ) :
    |rampSlope (c * x + e) - rampSlope (c * y + e)| ≤ |c| * |x - y| := by
  have h := rampSlope_lipschitz (c * x + e) (c * y + e)
  rwa [show c * x + e - (c * y + e) = c * (x - y) by ring, abs_mul] at h

lemma bumpSlope_lipschitz (x y : ℝ) : |bumpSlope x - bumpSlope y| ≤ 600 * |x - y| := by
  have h1 := rampSlope_affine_lipschitz 20 (-1) x y
  have h2 := rampSlope_affine_lipschitz 10 (-9) x y
  have h3 := maxpart_lipschitz x y
  have h4 := rampSlope_affine_lipschitz (-20) (-1) x y
  norm_num at h1 h2 h4
  have he : bumpSlope x - bumpSlope y =
      -10 * (rampSlope (20 * x - 1) - rampSlope (20 * y - 1)) +
        10 * (rampSlope (10 * x - 9) - rampSlope (10 * y - 9)) +
        100 * (max (x - 1) 0 - max (y - 1) 0) -
        10 * (rampSlope (-20 * x - 1) - rampSlope (-20 * y - 1)) := by
    simp only [bumpSlope]; ring
  have e1 : (20 : ℝ) * x - 1 = 20 * x + -1 := by ring
  have e2 : (20 : ℝ) * y - 1 = 20 * y + -1 := by ring
  have e3 : (10 : ℝ) * x - 9 = 10 * x + -9 := by ring
  have e4 : (10 : ℝ) * y - 9 = 10 * y + -9 := by ring
  have e5 : (-20 : ℝ) * x - 1 = -(20 * x) + -1 := by ring
  have e6 : (-20 : ℝ) * y - 1 = -(20 * y) + -1 := by ring
  rw [he, e1, e2, e3, e4, e5, e6]
  calc _ ≤ |-10 * (rampSlope (20 * x + -1) - rampSlope (20 * y + -1))| +
        |10 * (rampSlope (10 * x + -9) - rampSlope (10 * y + -9))| +
        |100 * (max (x - 1) 0 - max (y - 1) 0)| +
        |10 * (rampSlope (-(20 * x) + -1) - rampSlope (-(20 * y) + -1))| := by
          have := abs_sub (-10 * (rampSlope (20 * x + -1) - rampSlope (20 * y + -1)) +
            10 * (rampSlope (10 * x + -9) - rampSlope (10 * y + -9)) +
            100 * (max (x - 1) 0 - max (y - 1) 0))
            (10 * (rampSlope (-(20 * x) + -1) - rampSlope (-(20 * y) + -1)))
          have := abs_add_three (-10 * (rampSlope (20 * x + -1) - rampSlope (20 * y + -1)))
            (10 * (rampSlope (10 * x + -9) - rampSlope (10 * y + -9)))
            (100 * (max (x - 1) 0 - max (y - 1) 0))
          linarith
    _ ≤ 600 * |x - y| := by
          simp only [abs_mul]
          norm_num
          nlinarith [abs_nonneg (x - y)]

noncomputable def well (β u : ℝ) : ℝ :=
  ramp u + ramp (-u) - (1 - β) * (ramp (u - 1) + ramp (-u - 1))

noncomputable def wellSlope (β u : ℝ) : ℝ :=
  rampSlope u - rampSlope (-u) - (1 - β) * (rampSlope (u - 1) - rampSlope (-u - 1))

lemma well_hasDerivAt (β x : ℝ) : HasDerivAt (well β) (wellSlope β x) x := by
  have h1 : HasDerivAt (fun u => ramp u) (rampSlope x * 1) x := by
    simpa using ramp_affine_hasDerivAt 1 0 x
  have h2 : HasDerivAt (fun u => ramp (-u)) (rampSlope (-x) * -1) x := by
    simpa using ramp_affine_hasDerivAt (-1) 0 x
  have h3 : HasDerivAt (fun u => ramp (u - 1)) (rampSlope (x - 1) * 1) x := by
    simpa [sub_eq_add_neg] using ramp_affine_hasDerivAt 1 (-1) x
  have h4 : HasDerivAt (fun u => ramp (-u - 1)) (rampSlope (-x - 1) * -1) x := by
    simpa [sub_eq_add_neg] using ramp_affine_hasDerivAt (-1) (-1) x
  have h := HasDerivAt.sub (HasDerivAt.add h1 h2)
    (HasDerivAt.const_mul (1 - β) (HasDerivAt.add h3 h4))
  convert h using 1
  · funext u
    simp only [well, Pi.add_apply, Pi.sub_apply]
  · simp only [wellSlope]
    ring

lemma well_neg (β u : ℝ) : well β (-u) = well β u := by
  simp only [well, neg_neg]; ring

lemma wellSlope_neg (β u : ℝ) : wellSlope β (-u) = -wellSlope β u := by
  simp only [wellSlope, neg_neg]; ring

lemma well_inner {u : ℝ} (β : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    well β u = u ^ 2 / 2 ∧ wellSlope β u = u := by
  simp only [well, wellSlope, ramp_of_mid h0 h1, ramp_of_nonpos (by linarith : -u ≤ 0),
    ramp_of_nonpos (by linarith : u - 1 ≤ 0), ramp_of_nonpos (by linarith : -u - 1 ≤ 0),
    rampSlope_of_mid h0 h1, rampSlope_of_nonpos (by linarith : -u ≤ 0),
    rampSlope_of_nonpos (by linarith : u - 1 ≤ 0), rampSlope_of_nonpos (by linarith : -u - 1 ≤ 0)]
  constructor <;> ring

lemma well_transition {u : ℝ} (β : ℝ) (h0 : 1 ≤ u) (h1 : u ≤ 2) :
    well β u = u - 1 / 2 - (1 - β) * (u - 1) ^ 2 / 2 ∧
      wellSlope β u = 1 - (1 - β) * (u - 1) := by
  simp only [well, wellSlope, ramp_of_ge h0, ramp_of_nonpos (by linarith : -u ≤ 0),
    ramp_of_mid (by linarith : 0 ≤ u - 1) (by linarith : u - 1 ≤ 1),
    ramp_of_nonpos (by linarith : -u - 1 ≤ 0),
    rampSlope_of_ge h0, rampSlope_of_nonpos (by linarith : -u ≤ 0),
    rampSlope_of_mid (by linarith : 0 ≤ u - 1) (by linarith : u - 1 ≤ 1),
    rampSlope_of_nonpos (by linarith : -u - 1 ≤ 0)]
  constructor <;> ring

lemma well_outer {u : ℝ} (β : ℝ) (h : 2 ≤ u) :
    well β u = u - 1 / 2 - (1 - β) * (u - 3 / 2) ∧ wellSlope β u = β := by
  simp only [well, wellSlope, ramp_of_ge (by linarith : 1 ≤ u),
    ramp_of_nonpos (by linarith : -u ≤ 0), ramp_of_ge (by linarith : 1 ≤ u - 1),
    ramp_of_nonpos (by linarith : -u - 1 ≤ 0),
    rampSlope_of_ge (by linarith : 1 ≤ u), rampSlope_of_nonpos (by linarith : -u ≤ 0),
    rampSlope_of_ge (by linarith : 1 ≤ u - 1),
    rampSlope_of_nonpos (by linarith : -u - 1 ≤ 0)]
  constructor <;> ring

lemma well_cases_nonneg {u : ℝ} (β : ℝ) (hu : 0 ≤ u) (P : ℝ → ℝ → Prop)
    (h1 : u ≤ 1 → P (u ^ 2 / 2) u)
    (h2 : 1 ≤ u → u ≤ 2 → P (u - 1 / 2 - (1 - β) * (u - 1) ^ 2 / 2) (1 - (1 - β) * (u - 1)))
    (h3 : 2 ≤ u → P (u - 1 / 2 - (1 - β) * (u - 3 / 2)) β) :
    P (well β u) (wellSlope β u) := by
  rcases le_total u 1 with a | a
  · obtain ⟨e1, e2⟩ := well_inner β hu a; rw [e1, e2]; exact h1 a
  rcases le_total u 2 with b | b
  · obtain ⟨e1, e2⟩ := well_transition β a b; rw [e1, e2]; exact h2 a b
  · obtain ⟨e1, e2⟩ := well_outer β b; rw [e1, e2]; exact h3 b

lemma well_quasar_nonneg {γ u : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hu : 0 ≤ u) :
    γ * well (2 * γ / 3) u ≤ wellSlope (2 * γ / 3) u * u := by
  apply well_cases_nonneg (2 * γ / 3) hu (fun v s => γ * v ≤ s * u)
  · intro _; nlinarith [sq_nonneg u]
  · intro a b
    nlinarith [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b), mul_nonneg hγ.le
      (mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b)), mul_nonneg hγ.le (sub_nonneg.mpr hγ1),
      mul_nonneg (mul_nonneg hγ.le (sub_nonneg.mpr hγ1)) (sub_nonneg.mpr a)]
  · intro a
    nlinarith [mul_nonneg hγ.le (sub_nonneg.mpr hγ1),
      mul_nonneg (mul_nonneg hγ.le (sub_nonneg.mpr hγ1)) (sub_nonneg.mpr a)]

lemma well_quasar {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (u : ℝ) :
    γ * well (2 * γ / 3) u ≤ wellSlope (2 * γ / 3) u * u := by
  rcases le_total 0 u with hu | hu
  · exact well_quasar_nonneg hγ hγ1 hu
  · have h := well_quasar_nonneg hγ hγ1 (neg_nonneg.mpr hu)
    rw [well_neg, wellSlope_neg] at h
    linarith

lemma well_nonneg_of_nonneg {β u : ℝ} (hβ : 0 ≤ β) (hu : 0 ≤ u) :
    0 ≤ well β u := by
  apply well_cases_nonneg β hu (fun v _ => 0 ≤ v)
  · intro _; positivity
  · intro a b; nlinarith [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b)]
  · intro a; nlinarith

lemma well_nonneg {β : ℝ} (hβ : 0 ≤ β) (u : ℝ) : 0 ≤ well β u := by
  rcases le_total 0 u with hu | hu
  · exact well_nonneg_of_nonneg hβ hu
  · rw [← well_neg]; exact well_nonneg_of_nonneg hβ (neg_nonneg.mpr hu)

lemma well_zero (β : ℝ) : well β 0 = 0 := by
  rw [(well_inner β le_rfl zero_le_one).1]; ring

lemma well_far_nonneg {β u : ℝ} (hβ : 0 ≤ β) (hu : 2 ≤ u) : 1 ≤ well β u := by
  rw [(well_outer β hu).1]; nlinarith

lemma well_far {β u : ℝ} (hβ : 0 ≤ β) (hu : 2 ≤ |u|) : 1 ≤ well β u := by
  rcases le_abs'.mp hu with h | h
  · rw [← well_neg]; exact well_far_nonneg hβ (by linarith)
  · exact well_far_nonneg hβ h

lemma wellSlope_far {β u : ℝ} (hu : 2 ≤ |u|) : |wellSlope β u| = |β| := by
  rcases le_abs'.mp hu with h | h
  · have e := (well_outer β (by linarith : 2 ≤ -u)).2
    rw [wellSlope_neg] at e
    rw [show wellSlope β u = -β by linarith, abs_neg]
  · rw [(well_outer β h).2]

lemma wellSlope_bound_nonneg {β u : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hu : 0 ≤ u) :
    |wellSlope β u| ≤ 1 := by
  apply well_cases_nonneg β hu (fun _ s => |s| ≤ 1)
  · intro a; rw [abs_le]; constructor <;> linarith
  · intro a b; rw [abs_le]; constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hβ1)
      (sub_nonneg.mpr a), mul_nonneg (sub_nonneg.mpr hβ1) (sub_nonneg.mpr b)]
  · intro _; rw [abs_le]; constructor <;> linarith

lemma wellSlope_bound {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (u : ℝ) : |wellSlope β u| ≤ 1 := by
  rcases le_total 0 u with hu | hu
  · exact wellSlope_bound_nonneg hβ hβ1 hu
  · have h := wellSlope_bound_nonneg hβ hβ1 (neg_nonneg.mpr hu)
    rwa [wellSlope_neg, abs_neg] at h

lemma wellSlope_lipschitz {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (x y : ℝ) :
    |wellSlope β x - wellSlope β y| ≤ 4 * |x - y| := by
  have h1 := rampSlope_affine_lipschitz 1 0 x y
  have h2 := rampSlope_affine_lipschitz (-1) 0 x y
  have h3 := rampSlope_affine_lipschitz 1 (-1) x y
  have h4 := rampSlope_affine_lipschitz (-1) (-1) x y
  simp only [one_mul, add_zero, neg_mul, abs_neg, abs_one] at h1 h2 h3 h4
  have he : wellSlope β x - wellSlope β y =
      (rampSlope x - rampSlope y) - (rampSlope (-x) - rampSlope (-y)) -
        (1 - β) * ((rampSlope (x + -1) - rampSlope (y + -1)) -
          (rampSlope (-x + -1) - rampSlope (-y + -1))) := by
    simp only [wellSlope, sub_eq_add_neg]; ring
  rw [he]
  have hb : 0 ≤ 1 - β := by linarith
  have hb1 : 1 - β ≤ 1 := by linarith
  have key : |(1 - β) * ((rampSlope (x + -1) - rampSlope (y + -1)) -
      (rampSlope (-x + -1) - rampSlope (-y + -1)))| ≤ 2 * |x - y| := by
    rw [abs_mul, abs_of_nonneg hb]
    have := abs_sub (rampSlope (x + -1) - rampSlope (y + -1))
      (rampSlope (-x + -1) - rampSlope (-y + -1))
    nlinarith [abs_nonneg ((rampSlope (x + -1) - rampSlope (y + -1)) -
      (rampSlope (-x + -1) - rampSlope (-y + -1))), abs_nonneg (x - y)]
  have := abs_sub ((rampSlope x - rampSlope y) - (rampSlope (-x) - rampSlope (-y)))
    ((1 - β) * ((rampSlope (x + -1) - rampSlope (y + -1)) -
      (rampSlope (-x + -1) - rampSlope (-y + -1))))
  have := abs_sub (rampSlope x - rampSlope y) (rampSlope (-x) - rampSlope (-y))
  linarith

end LongTails.Proofs.QuasarHardProfiles
