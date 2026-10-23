import LongTails.Proofs.SeparationTrajectory

namespace LongTails.Proofs.NsgdLattice

open LongTails.Proofs.SeparationInstance LongTails.Proofs.SeparationTrajectory

lemma valleySlope_neg {w D u : ℝ} (hw : 0 < w) (hu : u < D) : valleySlope w D u < 0 := by
  unfold valleySlope
  exact div_neg_of_neg_of_pos (by linarith) (Real.sqrt_pos.mpr (valley_pos hw D u))

lemma valleySlope_near {w D u : ℝ} (hw : 0 < w) (hu : D + w ≤ u) :
    1 / 2 ≤ valleySlope w D u := by
  have h := valleySlope_far hw (u := 2 * D - u) (D := D) (by linarith)
  have hs : valleySlope w D (2 * D - u) = -valleySlope w D u := by
    unfold valleySlope
    rw [show 2 * D - u - D = -(u - D) by ring, neg_sq, neg_div]
  linarith

lemma valley_le (w D u : ℝ) (hw : 0 ≤ w) : valley w D u ≤ w + |u - D| := by
  unfold valley
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (u - D), sq_abs (u - D)]

lemma valley_ge (w D u : ℝ) : |u - D| ≤ valley w D u := by
  unfold valley
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg w])

noncomputable def pairShape {w : ℝ} (hw : 0 < w) (a b : ℝ) : FlatShape where
  value u := (valley w a u + valley w b u) / 2
  slope u := (valleySlope w a u + valleySlope w b u) / 2
  lip := 1 / w
  deriv u := ((hasDerivAt_valley hw a u).add (hasDerivAt_valley hw b u)).div_const 2
  lip_nonneg := by positivity
  lip_spec u v := by
    have h1 := valleySlope_lipschitz hw a u v
    have h2 := valleySlope_lipschitz hw b u v
    have he : (valleySlope w a u + valleySlope w b u) / 2 -
        (valleySlope w a v + valleySlope w b v) / 2 =
        ((valleySlope w a u - valleySlope w a v) + (valleySlope w b u - valleySlope w b v)) / 2 := by
      ring
    rw [he, abs_div, abs_two]
    have ht := abs_add_le (valleySlope w a u - valleySlope w a v)
      (valleySlope w b u - valleySlope w b v)
    rw [div_le_iff₀ two_pos]
    calc |valleySlope w a u - valleySlope w a v + (valleySlope w b u - valleySlope w b v)| ≤
          |u - v| / w + |u - v| / w := ht.trans (add_le_add h1 h2)
      _ = 1 / w * |u - v| * 2 := by ring
  nonneg u := by
    have := Real.sqrt_nonneg (w ^ 2 + (u - a) ^ 2)
    have := Real.sqrt_nonneg (w ^ 2 + (u - b) ^ 2)
    unfold valley
    positivity
  bounded u := by
    have h1 := abs_valleySlope_le w a u
    have h2 := abs_valleySlope_le w b u
    rw [abs_div, abs_two, div_le_one two_pos]
    exact (abs_add_le _ _).trans (by linarith)

lemma pairShape_value_ge {w : ℝ} (hw : 0 < w) (a b u : ℝ) :
    |b - a| / 2 ≤ (pairShape hw a b).value u := by
  change |b - a| / 2 ≤ (valley w a u + valley w b u) / 2
  have h1 := valley_ge w a u
  have h2 := valley_ge w b u
  have h3 : |b - a| ≤ |u - a| + |u - b| := by
    calc |b - a| = |(u - a) - (u - b)| := by ring_nf
      _ ≤ |u - a| + |u - b| := abs_sub _ _
  linarith

lemma pairShape_value_zero {w : ℝ} (hw : 0 < w) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (pairShape hw a b).value 0 ≤ w + a + |b - a| / 2 := by
  change (valley w a 0 + valley w b 0) / 2 ≤ _
  have h1 := valley_le w a 0 hw.le
  have h2 := valley_le w b 0 hw.le
  rw [zero_sub, abs_neg, abs_of_nonneg ha] at h1
  rw [zero_sub, abs_neg, abs_of_nonneg (ha.trans hab)] at h2
  rw [abs_of_nonneg (by linarith)]
  linarith

lemma pairShape_slope_left {w : ℝ} (hw : 0 < w) {a b u : ℝ} (ha : u ≤ a - w) (hb : u ≤ b - w) :
    (pairShape hw a b).slope u ≤ -(1 / 2) := by
  change (valleySlope w a u + valleySlope w b u) / 2 ≤ _
  have h1 := valleySlope_far hw ha
  have h2 := valleySlope_far hw hb
  linarith

lemma pairShape_slope_right {w : ℝ} (hw : 0 < w) {a b u : ℝ} (ha : a + w ≤ u) (hb : b + w ≤ u) :
    1 / 2 ≤ (pairShape hw a b).slope u := by
  change _ ≤ (valleySlope w a u + valleySlope w b u) / 2
  have h1 := valleySlope_near hw ha
  have h2 := valleySlope_near hw hb
  linarith

lemma pairShape_slope_neg {w : ℝ} (hw : 0 < w) {D u : ℝ} (hu : u < D) :
    (pairShape hw D D).slope u < 0 := by
  change (valleySlope w D u + valleySlope w D u) / 2 < 0
  have := valleySlope_neg hw hu
  linarith

noncomputable def latticeStep (r : ℕ) (c η : ℝ) (φ : FlatShape) (y : ℝ) : ℝ :=
  y - η * (c * φ.slope y / Real.sqrt ((r - 1 : ℕ) * (c * φ.slope y) ^ 2))

lemma nsgdScalar_fst (r : ℕ) (c η : ℝ) (φ : FlatShape) (B : ℕ) (ξ : ℕ → ℝ) (t : ℕ) :
    (nsgdScalar r 0 c 0 η φ B ξ t).1 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [nsgdScalar, ih]

lemma nsgdScalar_snd (r : ℕ) (c η : ℝ) (φ : FlatShape) (B : ℕ) (ξ : ℕ → ℝ) (t : ℕ) :
    (nsgdScalar r 0 c 0 η φ B ξ (t + 1)).2 =
      latticeStep r c η φ (nsgdScalar r 0 c 0 η φ B ξ t).2 := by
  simp [nsgdScalar, latticeStep, nsgdScalar_fst]

lemma latticeStep_of_neg {r : ℕ} (hr : 2 ≤ r) {c : ℝ} (hc : 0 < c) (η : ℝ) (φ : FlatShape)
    {y : ℝ} (hy : φ.slope y < 0) :
    latticeStep r c η φ y = y + η / Real.sqrt (r - 1 : ℕ) := by
  have hk : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (by omega : 0 < r - 1)
  have hq : c * φ.slope y < 0 := mul_neg_of_pos_of_neg hc hy
  have hs : Real.sqrt ((r - 1 : ℕ) * (c * φ.slope y) ^ 2) =
      Real.sqrt (r - 1 : ℕ) * -(c * φ.slope y) := by
    rw [Real.sqrt_mul hk.le, Real.sqrt_sq_eq_abs, abs_of_neg hq]
  have hr0 : Real.sqrt (r - 1 : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  unfold latticeStep
  rw [hs]
  field_simp
  rw [mul_div_assoc, div_self hy.ne, mul_one, sub_neg_eq_add]

lemma latticeStep_of_pos {r : ℕ} (hr : 2 ≤ r) {c : ℝ} (hc : 0 < c) (η : ℝ) (φ : FlatShape)
    {y : ℝ} (hy : 0 < φ.slope y) :
    latticeStep r c η φ y = y - η / Real.sqrt (r - 1 : ℕ) := by
  have hk : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (by omega : 0 < r - 1)
  have hq : 0 < c * φ.slope y := mul_pos hc hy
  have hs : Real.sqrt ((r - 1 : ℕ) * (c * φ.slope y) ^ 2) =
      Real.sqrt (r - 1 : ℕ) * (c * φ.slope y) := by
    rw [Real.sqrt_mul hk.le, Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hr0 : Real.sqrt (r - 1 : ℕ) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  unfold latticeStep
  rw [hs]
  field_simp

lemma climb {r : ℕ} (hr : 2 ≤ r) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 ≤ η) {w : ℝ} (hw : 0 < w)
    (D : ℝ)
    (B : ℕ) (ξ : ℕ → ℝ) (t : ℕ) (ht : t * (η / Real.sqrt (r - 1 : ℕ)) < D) :
    (nsgdScalar r 0 c 0 η (pairShape hw D D) B ξ t).2 = t * (η / Real.sqrt (r - 1 : ℕ)) := by
  induction t with
  | zero => simp [nsgdScalar]
  | succ t ih =>
      have h0 : 0 ≤ η / Real.sqrt (r - 1 : ℕ) := div_nonneg hη (Real.sqrt_nonneg _)
      have hprev : (t : ℝ) * (η / Real.sqrt (r - 1 : ℕ)) < D := by
        push_cast at ht
        nlinarith
      rw [nsgdScalar_snd, ih hprev,
        latticeStep_of_neg hr hc η _ (pairShape_slope_neg hw hprev)]
      push_cast
      ring

lemma cycle {r : ℕ} (hr : 2 ≤ r) {c : ℝ} (hc : 0 < c) {η w : ℝ} (hw : 0 < w)
    (hη : 2 * w ≤ η / Real.sqrt (r - 1 : ℕ)) (B : ℕ) (ξ : ℕ → ℝ) (t : ℕ) :
    (nsgdScalar r 0 c 0 η (pairShape hw w (η / Real.sqrt (r - 1 : ℕ) - w)) B ξ t).2 =
      if Even t then 0 else η / Real.sqrt (r - 1 : ℕ) := by
  set h := η / Real.sqrt (r - 1 : ℕ)
  induction t with
  | zero => simp [nsgdScalar]
  | succ t ih =>
      rw [nsgdScalar_snd, ih]
      by_cases ht : Even t
      · have hn : ¬ Even (t + 1) := Nat.not_even_iff_odd.mpr ht.add_one
        have hsl := pairShape_slope_left hw (a := w) (b := h - w) (u := 0) (by linarith)
          (by linarith)
        rw [ite_eq_left ht, ite_eq_right hn, latticeStep_of_neg hr hc η _ (by linarith)]
        simp only [zero_add, h]
      · have hn : Even (t + 1) := (Nat.not_even_iff_odd.mp ht).add_one
        have hsl := pairShape_slope_right hw (a := w) (b := h - w) (u := h) (by linarith)
          (by linarith)
        rw [ite_eq_right ht, ite_eq_left hn, latticeStep_of_pos hr hc η _ (by linarith)]
        simp only [h, sub_self]

lemma cycle_slope {r : ℕ} (hr : 2 ≤ r) {c : ℝ} (hc : 0 < c) {η w : ℝ} (hw : 0 < w)
    (hη : 2 * w ≤ η / Real.sqrt (r - 1 : ℕ)) (B : ℕ) (ξ : ℕ → ℝ) (t : ℕ) :
    1 / 2 ≤ |(pairShape hw w (η / Real.sqrt (r - 1 : ℕ) - w)).slope
      (nsgdScalar r 0 c 0 η (pairShape hw w (η / Real.sqrt (r - 1 : ℕ) - w)) B ξ t).2| := by
  set h := η / Real.sqrt (r - 1 : ℕ)
  rw [cycle hr hc hw hη B ξ t]
  split_ifs
  · have := pairShape_slope_left hw (a := w) (b := h - w) (u := 0) (by linarith) (by linarith)
    rw [abs_of_neg (by linarith)]
    linarith
  · have := pairShape_slope_right hw (a := w) (b := h - w) (u := h) (by linarith) (by linarith)
    rw [abs_of_pos (by linarith)]
    exact this

end LongTails.Proofs.NsgdLattice
