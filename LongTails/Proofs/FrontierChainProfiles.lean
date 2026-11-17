import LongTails.Proofs.QuasarHardProfiles
import Mathlib.Analysis.Calculus.MeanValue

namespace LongTails.Proofs.FrontierChainProfiles

open SmoothConvexFiniteGeometry QuasarHardProfiles

lemma ramp_difference {x y : ℝ} (h : y ≤ x) :
    0 ≤ ramp x - ramp y ∧ ramp x - ramp y ≤ x - y := by
  have h1 := (ramp_model y x).1
  have h2 := (ramp_model x y).1
  have h3 := mul_nonneg (rampSlope_nonneg y) (sub_nonneg.mpr h)
  have h4 := mul_le_mul_of_nonneg_right (rampSlope_le_one x) (sub_nonneg.mpr h)
  constructor <;> nlinarith

lemma rampSlope_mono {x y : ℝ} (h : x ≤ y) : rampSlope x ≤ rampSlope y := by
  unfold rampSlope
  exact min_le_min_left 1 (max_le_max_left 0 h)

noncomputable def gate (t : ℝ) : ℝ := ramp (4 * t - 2) - ramp (4 * t - 3)

noncomputable def gateSlope (t : ℝ) : ℝ :=
  4 * (rampSlope (4 * t - 2) - rampSlope (4 * t - 3))

noncomputable def potential (t : ℝ) : ℝ := ramp (t + 2) - ramp (t - 2)

noncomputable def potentialSlope (t : ℝ) : ℝ := rampSlope (t + 2) - rampSlope (t - 2)

lemma gate_bounds (t : ℝ) : 0 ≤ gate t ∧ gate t ≤ 1 := by
  have h := ramp_difference (x := 4 * t - 2) (y := 4 * t - 3) (by linarith)
  dsimp [gate]
  constructor <;> linarith

lemma potential_bounds (t : ℝ) : 0 ≤ potential t ∧ potential t ≤ 4 := by
  have h := ramp_difference (x := t + 2) (y := t - 2) (by linarith)
  dsimp [potential]
  constructor <;> linarith

lemma gateSlope_bounds (t : ℝ) : 0 ≤ gateSlope t ∧ gateSlope t ≤ 4 := by
  have h := rampSlope_mono (x := 4 * t - 3) (y := 4 * t - 2) (by linarith)
  have h1 := rampSlope_nonneg (4 * t - 3)
  have h2 := rampSlope_le_one (4 * t - 2)
  dsimp [gateSlope]
  constructor <;> linarith

lemma potentialSlope_bounds (t : ℝ) : 0 ≤ potentialSlope t ∧ potentialSlope t ≤ 1 := by
  have h := rampSlope_mono (x := t - 2) (y := t + 2) (by linarith)
  have h1 := rampSlope_nonneg (t - 2)
  have h2 := rampSlope_le_one (t + 2)
  dsimp [potentialSlope]
  constructor <;> linarith

lemma gate_flat {t : ℝ} (h : t ≤ 1 / 2) : gate t = 0 ∧ gateSlope t = 0 := by
  simp [gate, gateSlope, ramp_of_nonpos (by linarith : 4 * t - 2 ≤ 0),
    ramp_of_nonpos (by linarith : 4 * t - 3 ≤ 0),
    rampSlope_of_nonpos (by linarith : 4 * t - 2 ≤ 0),
    rampSlope_of_nonpos (by linarith : 4 * t - 3 ≤ 0)]

lemma gate_one {t : ℝ} (h : 1 ≤ t) : gate t = 1 ∧ gateSlope t = 0 := by
  simp only [gate, gateSlope, ramp_of_ge (by linarith : 1 ≤ 4 * t - 2),
    ramp_of_ge (by linarith : 1 ≤ 4 * t - 3),
    rampSlope_of_ge (by linarith : 1 ≤ 4 * t - 2),
    rampSlope_of_ge (by linarith : 1 ≤ 4 * t - 3)]
  constructor <;> ring

lemma potentialSlope_one {t : ℝ} (h : |t| ≤ 1) : potentialSlope t = 1 := by
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  simp [potentialSlope, rampSlope_of_ge (by linarith : 1 ≤ t + 2),
    rampSlope_of_nonpos (by linarith : t - 2 ≤ 0)]

lemma gate_deriv (t : ℝ) : HasDerivAt gate (gateSlope t) t := by
  have h := (ramp_affine_hasDerivAt 4 (-2) t).sub (ramp_affine_hasDerivAt 4 (-3) t)
  convert h using 1
  · ext x
    simp [gate, sub_eq_add_neg]
  · simp only [gateSlope, sub_eq_add_neg]
    ring

lemma potential_deriv (t : ℝ) : HasDerivAt potential (potentialSlope t) t := by
  have h := (ramp_affine_hasDerivAt 1 2 t).sub (ramp_affine_hasDerivAt 1 (-2) t)
  convert h using 1
  · ext x
    simp [potential, sub_eq_add_neg]
  · simp [potentialSlope, sub_eq_add_neg]

lemma gate_lipschitz (x y : ℝ) : |gate x - gate y| ≤ 4 * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => (gate_deriv t).hasDerivWithinAt)
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => show ‖gateSlope t‖ ≤ 4 by
      rw [Real.norm_eq_abs, abs_of_nonneg (gateSlope_bounds t).1]
      exact (gateSlope_bounds t).2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

lemma potential_lipschitz (x y : ℝ) : |potential x - potential y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => (potential_deriv t).hasDerivWithinAt)
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => show ‖potentialSlope t‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg (potentialSlope_bounds t).1]
      exact (potentialSlope_bounds t).2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

lemma gateSlope_lipschitz (x y : ℝ) : |gateSlope x - gateSlope y| ≤ 32 * |x - y| := by
  have h1 := rampSlope_affine_lipschitz 4 (-2) x y
  have h2 := rampSlope_affine_lipschitz 4 (-3) x y
  have ht := abs_sub (rampSlope (4 * x - 2) - rampSlope (4 * y - 2))
    (rampSlope (4 * x - 3) - rampSlope (4 * y - 3))
  rw [show gateSlope x - gateSlope y = 4 *
    ((rampSlope (4 * x - 2) - rampSlope (4 * y - 2)) -
      (rampSlope (4 * x - 3) - rampSlope (4 * y - 3))) by unfold gateSlope; ring,
    abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at *
  simp only [← sub_eq_add_neg] at h1 h2
  linarith

lemma potentialSlope_lipschitz (x y : ℝ) :
    |potentialSlope x - potentialSlope y| ≤ 2 * |x - y| := by
  have h1 := rampSlope_lipschitz (x + 2) (y + 2)
  have h2 := rampSlope_lipschitz (x - 2) (y - 2)
  have ht := abs_sub (rampSlope (x + 2) - rampSlope (y + 2))
    (rampSlope (x - 2) - rampSlope (y - 2))
  rw [show potentialSlope x - potentialSlope y =
    (rampSlope (x + 2) - rampSlope (y + 2)) -
      (rampSlope (x - 2) - rampSlope (y - 2)) by unfold potentialSlope; ring]
  rw [show x + 2 - (y + 2) = x - y by ring] at h1
  rw [show x - 2 - (y - 2) = x - y by ring] at h2
  linarith

lemma gate_disjoint (t : ℝ) : gate t = 0 ∨ gate (-t) = 0 := by
  by_cases h : t ≤ 1 / 2
  · exact Or.inl (gate_flat h).1
  · exact Or.inr (gate_flat (by linarith)).1

lemma gateSlope_disjoint (t : ℝ) : gateSlope t = 0 ∨ gateSlope (-t) = 0 := by
  by_cases h : t ≤ 1 / 2
  · exact Or.inl (gate_flat h).2
  · exact Or.inr (gate_flat (by linarith)).2

end LongTails.Proofs.FrontierChainProfiles
