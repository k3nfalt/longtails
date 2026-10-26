import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open scoped NNReal

namespace LongTails.Proofs.SmoothBanachAnchoring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma anchored_inverse_bound (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 ≤ a)
    (b x u : E) (hu : (1 + a) • u - T u - b = 0) :
    a * ‖x - u‖ ≤ ‖(1 + a) • x - T x - b‖ := by
  have hid : (1 + a) • (x - u) =
      ((1 + a) • x - T x - b) + (T x - T u) := by
    have hu' : (1 + a) • u = T u + b := by
      have h := sub_eq_zero.mp hu
      rw [sub_eq_iff_eq_add] at h
      simpa only [add_comm] using h
    rw [smul_sub, hu']
    abel
  have hn := norm_add_le ((1 + a) • x - T x - b) (T x - T u)
  rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + a)] at hn
  have ht := hT x u
  nlinarith

lemma damped_picard_contraction (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a η : ℝ)
    (hη : 0 ≤ η) (hstep : η * (1 + a) ≤ 1) (b x y : E) :
    ‖((1 - η * (1 + a)) • x + η • T x + η • b) -
      ((1 - η * (1 + a)) • y + η • T y + η • b)‖ ≤
        (1 - η * a) * ‖x - y‖ := by
  have hid : ((1 - η * (1 + a)) • x + η • T x + η • b) -
      ((1 - η * (1 + a)) • y + η • T y + η • b) =
      (1 - η * (1 + a)) • (x - y) + η • (T x - T y) := by
    simp only [smul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖(1 - η * (1 + a)) • (x - y)‖ + ‖η • (T x - T y)‖ := norm_add_le _ _
    _ = (1 - η * (1 + a)) * ‖x - y‖ + η * ‖T x - T y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), abs_of_nonneg hη]
    _ ≤ (1 - η * (1 + a)) * ‖x - y‖ + η * ‖x - y‖ := by
      gcongr
      exact hT x y
    _ = _ := by ring

lemma anchored_roots_bound (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 ≤ a)
    (b c u v : E) (hu : (1 + a) • u - T u - b = 0)
    (hv : (1 + a) • v - T v - c = 0) :
    a * ‖u - v‖ ≤ ‖b - c‖ := by
  have hb : (1 + a) • u - T u = b := sub_eq_zero.mp hu
  simpa only [hb] using anchored_inverse_bound T hT a ha c u v hv

lemma doubled_anchor_root_movement (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 < a)
    (b z u v : E) (hu : (1 + a) • u - T u - b = 0)
    (hv : (1 + 2 * a) • v - T v - (b + a • z) = 0) :
    ‖u - v‖ ≤ ‖z - u‖ / 2 := by
  have hid : (1 + 2 * a) • u - T u - (b + a • z) = a • (u - z) := by
    have hb : (1 + a) • u - T u = b := sub_eq_zero.mp hu
    rw [← hb]
    module
  have h := anchored_inverse_bound T hT (2 * a) (by positivity) (b + a • z) u v hv
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_sub_rev u z] at h
  nlinarith

lemma exists_anchored_root [CompleteSpace E] (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 < a) (b : E) :
    ∃ u, (1 + a) • u - T u - b = 0 := by
  let k : ℝ≥0 := ⟨(1 + a)⁻¹, by positivity⟩
  let f : E → E := fun x => (1 + a)⁻¹ • (T x + b)
  have hf : ContractingWith k f := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · change (1 + a)⁻¹ < 1
      exact inv_lt_one_of_one_lt₀ (by linarith)
    · intro x y
      simp only [f, dist_eq_norm, ← smul_sub, add_sub_add_right_eq_sub,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith : 0 < 1 + a))]
      exact mul_le_mul_of_nonneg_left (hT x y) k.property
  let u := hf.fixedPoint f
  have hu : f u = u := hf.fixedPoint_isFixedPt
  have he : T u + b = (1 + a) • u := by
    have h := congrArg (fun x : E => (1 + a) • x) hu
    simpa only [f, smul_smul, mul_inv_cancel₀ (by linarith : 1 + a ≠ 0), one_smul] using h
  refine ⟨u, ?_⟩
  rw [← he]
  abel

noncomputable def anchoredRoot [CompleteSpace E] (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 < a) (b : E) : E :=
  Classical.choose (exists_anchored_root T hT a ha b)

lemma anchoredRoot_equation [CompleteSpace E] (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 < a) (b : E) :
    (1 + a) • anchoredRoot T hT a ha b - T (anchoredRoot T hT a ha b) - b = 0 :=
  Classical.choose_spec (exists_anchored_root T hT a ha b)

lemma anchoredRoot_lipschitz [CompleteSpace E] (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 < a) :
    LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ (anchoredRoot T hT a ha) := by
  apply LipschitzWith.of_dist_le_mul
  intro b c
  simp only [dist_eq_norm]
  have h := anchored_roots_bound T hT a ha.le b c
    (anchoredRoot T hT a ha b) (anchoredRoot T hT a ha c)
    (anchoredRoot_equation T hT a ha b) (anchoredRoot_equation T hT a ha c)
  change ‖anchoredRoot T hT a ha b - anchoredRoot T hT a ha c‖ ≤ a⁻¹ * ‖b - c‖
  rw [← div_eq_inv_mul, le_div_iff₀ ha]
  nlinarith

lemma initial_root_distance (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a R : ℝ) (ha : 0 < a)
    (x0 xstar u : E) (hstar : T xstar = xstar) (hR : ‖x0 - xstar‖ ≤ R)
    (hu : (1 + a) • u - T u - a • x0 = 0) : ‖u - x0‖ ≤ 2 * R := by
  have hid : (1 + a) • xstar - T xstar - a • x0 = a • (xstar - x0) := by
    rw [hstar]
    module
  have h := anchored_inverse_bound T hT a ha.le (a • x0) xstar u hu
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h
  have hd : ‖xstar - u‖ ≤ ‖xstar - x0‖ := (mul_le_mul_iff_right₀ ha).mp h
  have ht := norm_sub_le_norm_sub_add_norm_sub u xstar x0
  rw [norm_sub_rev u xstar] at ht
  rw [norm_sub_rev xstar x0] at hd ht
  linarith

lemma remove_initial_anchor (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a R : ℝ) (ha : 0 ≤ a)
    (x0 u x : E) (hu : (1 + a) • u - T u - a • x0 = 0)
    (hR : ‖u - x0‖ ≤ 2 * R) :
    ‖x - T x‖ ≤ 2 * ‖(1 + a) • x - T x - a • x0‖ + 2 * a * R := by
  have hid : x - T x = ((1 + a) • x - T x - a • x0) - a • (x - x0) := by
    module
  have hn := norm_sub_le ((1 + a) • x - T x - a • x0) (a • (x - x0))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at hn
  rw [← hid] at hn
  have ht := norm_sub_le_norm_sub_add_norm_sub x u x0
  have hi := anchored_inverse_bound T hT a ha (a • x0) x u hu
  nlinarith [mul_le_mul_of_nonneg_left ht ha, mul_le_mul_of_nonneg_left hR ha]

lemma correction_step_bound (a a0 : ℝ) (ha0 : 0 ≤ a0) (ha : a0 ≤ a)
    (b b0 u v z : E) (hm : ‖u - v‖ ≤ ‖z - u‖ / 2) :
    ‖(2 * a - a0) • v - (b + a • z - b0)‖ ≤
      ‖(a - a0) • u - (b - b0)‖ + 2 * a * ‖z - u‖ := by
  have hid : (2 * a - a0) • v - (b + a • z - b0) =
      ((a - a0) • u - (b - b0)) +
        (2 * a - a0) • (v - u) + a • (u - z) := by module
  rw [hid]
  have hnorm := (norm_add_le (((a - a0) • u - (b - b0)) +
    (2 * a - a0) • (v - u)) (a • (u - z))).trans
    (add_le_add (norm_add_le ((a - a0) • u - (b - b0))
      ((2 * a - a0) • (v - u))) (le_refl _))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 2 * a - a0), abs_of_nonneg (by linarith : 0 ≤ a),
    norm_sub_rev v u, norm_sub_rev u z] at hnorm
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 2 * a - a0)
  nlinarith [mul_nonneg ha0 (norm_nonneg (z - u))]

lemma anchored_residual_lipschitz (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a : ℝ) (ha : 0 ≤ a)
    (b x y : E) :
    ‖((1 + a) • x - T x - b) - ((1 + a) • y - T y - b)‖ ≤
      (2 + a) * ‖x - y‖ := by
  have hid : ((1 + a) • x - T x - b) - ((1 + a) • y - T y - b) =
      (1 + a) • (x - y) - (T x - T y) := by
    simp only [smul_sub]
    abel
  rw [hid]
  have hn := norm_sub_le ((1 + a) • (x - y)) (T x - T y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + a)] at hn
  have ht := hT x y
  nlinarith

lemma correction_sum_bound (a : ℕ → ℝ) (b u z : ℕ → E)
    (ha0 : 0 ≤ a 0) (ha : ∀ j, a 0 ≤ a j)
    (had : ∀ j, a (j + 1) = 2 * a j)
    (hb : ∀ j, b (j + 1) = b j + a j • z j)
    (hm : ∀ j, ‖u j - u (j + 1)‖ ≤ ‖z j - u j‖ / 2) (n : ℕ) :
    ‖(a n - a 0) • u n - (b n - b 0)‖ ≤
      2 * ∑ j ∈ Finset.range n, a j * ‖z j - u j‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [had, hb]
    calc
      _ ≤ ‖(a n - a 0) • u n - (b n - b 0)‖ + 2 * a n * ‖z n - u n‖ :=
        correction_step_bound (a n) (a 0) ha0 (ha n) (b n) (b 0) (u n) (u (n + 1)) (z n) (hm n)
      _ ≤ 2 * ∑ j ∈ Finset.range n, a j * ‖z j - u j‖ + 2 * a n * ‖z n - u n‖ :=
        add_le_add ih (le_refl _)
      _ = _ := by rw [Finset.sum_range_succ]; ring

lemma residual_from_correction (T : E → E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (a a0 : ℝ) (ha0 : 0 ≤ a0)
    (b b0 u z : E) (hu : (1 + a) • u - T u - b = 0) :
    ‖(1 + a0) • z - T z - b0‖ ≤ (2 + a0) * ‖z - u‖ +
      ‖(a - a0) • u - (b - b0)‖ := by
  have he : (1 + a0) • u - T u - b0 = -((a - a0) • u - (b - b0)) := by
    have hb : (1 + a) • u - T u = b := sub_eq_zero.mp hu
    rw [← hb]
    module
  have hn := norm_sub_le_norm_sub_add_norm_sub ((1 + a0) • z - T z - b0)
    ((1 + a0) • u - T u - b0) 0
  simp only [sub_zero] at hn
  have hl := anchored_residual_lipschitz T hT a0 ha0 b0 z u
  rw [he, norm_neg] at hn
  rw [he] at hl
  linarith

end LongTails.Proofs.SmoothBanachAnchoring
