import LongTails.Proofs.MintyChainGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyPrefixSphere

def angle (s : ℝ) := min (Real.pi / 2) (max s (-(Real.pi / 2)))

lemma angle_bounds (s : ℝ) : -(Real.pi / 2) ≤ angle s ∧ angle s ≤ Real.pi / 2 := by
  exact ⟨le_min (by linarith [Real.pi_pos]) (le_max_right _ _), min_le_left _ _⟩

lemma angle_diff (s t : ℝ) : |angle s - angle t| ≤ |s - t| := by
  have h := abs_min_sub_min_le_max (Real.pi / 2) (max s (-(Real.pi / 2)))
    (Real.pi / 2) (max t (-(Real.pi / 2)))
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (max s (-(Real.pi/2)) - max t (-(Real.pi/2))))] at h
  exact h.trans (abs_max_sub_max_le_abs _ _ _)

lemma cos_angle_nonneg (s : ℝ) : 0 ≤ Real.cos (angle s) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [(angle_bounds s).1], (angle_bounds s).2⟩

lemma sin_angle_mul_nonneg (s : ℝ) : 0 ≤ Real.sin (angle s) * s := by
  by_cases h : 0 ≤ s
  · apply mul_nonneg _ h
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact le_min (by positivity) (h.trans (le_max_left _ _))
    · linarith [(angle_bounds s).2, Real.pi_pos]
  · apply mul_nonneg_of_nonpos_of_nonpos _ (le_of_not_ge h)
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
    · exact (min_le_right _ _).trans (max_le (le_of_not_ge h) (by linarith [Real.pi_pos]))
    · linarith [(angle_bounds s).1, Real.pi_pos]

def sphere : {n : ℕ} → (Fin n → ℝ) → Fin (n + 1) → ℝ
  | 0, _ => fun _ => 1
  | n + 1, x => Fin.cons (Real.sin (angle (x 0)))
      (fun i => Real.cos (angle (x 0)) * sphere (fun j : Fin n => x j.succ) i)

lemma sphere_unit {n : ℕ} (x : Fin n → ℝ) : ∑ i, sphere x i ^ 2 = 1 := by
  induction n with
  | zero => simp [sphere]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [sphere, Fin.cons_zero, Fin.cons_succ, mul_pow, ← Finset.mul_sum]
    rw [ih, mul_one, Real.sin_sq_add_cos_sq]

lemma scaled_chord {n : ℕ} (a b : ℝ) (x y : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) :
    ∑ i, (a * x i - b * y i) ^ 2 = (a - b) ^ 2 + a * b * ∑ i, (x i - y i) ^ 2 := by
  have h (i) : (a * x i - b * y i) ^ 2 =
      a * (a - b) * x i ^ 2 + b * (b - a) * y i ^ 2 + a * b * (x i - y i) ^ 2 := by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy]
  ring

lemma sphere_chord {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i, (sphere x i - sphere y i) ^ 2 ≤ 2 * ∑ i, (x i - y i) ^ 2 := by
  induction n with
  | zero => simp [sphere]
  | succ n ih =>
    rw [Fin.sum_univ_succ (f := fun i => (sphere x i - sphere y i) ^ 2),
      Fin.sum_univ_succ (f := fun i => (x i - y i) ^ 2)]
    simp only [sphere, Fin.cons_zero, Fin.cons_succ]
    rw [scaled_chord _ _ _ _ (sphere_unit _) (sphere_unit _)]
    have hc := (Real.abs_cos_sub_cos_le (angle (x 0)) (angle (y 0))).trans (angle_diff _ _)
    have hs := (Real.abs_sin_sub_sin_le (angle (x 0)) (angle (y 0))).trans (angle_diff _ _)
    have hcs := sq_le_sq.mpr hc
    have hss := sq_le_sq.mpr hs
    have hab : Real.cos (angle (x 0)) * Real.cos (angle (y 0)) ≤ 1 :=
      (mul_le_mul_of_nonneg_right (Real.cos_le_one _) (cos_angle_nonneg _)).trans
        (by simpa using Real.cos_le_one (angle (y 0)))
    have ht := mul_le_mul_of_nonneg_right hab (Finset.sum_nonneg (s := Finset.univ)
      (fun (i : Fin (n+1)) _ => sq_nonneg (sphere (fun j => x (Fin.succ j)) i -
        sphere (fun j => y (Fin.succ j)) i)))
    linarith [ih (fun j => x j.succ) (fun j => y j.succ)]

lemma sphere_sign {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ sphere x i.castSucc * x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [sphere] using sin_angle_mul_nonneg (x 0)
    · change 0 ≤ (Real.cos (angle (x 0)) * sphere (fun k => x k.succ) j.castSucc) * x j.succ
      rw [mul_assoc]
      exact mul_nonneg (cos_angle_nonneg _) (ih _ j)

lemma sphere_origin {n : ℕ} (i : Fin n) : sphere (fun _ : Fin n => 0) i.castSucc = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [sphere, angle, max_eq_left (show -(Real.pi / 2) ≤ 0 by linarith [Real.pi_pos]),
        min_eq_right (show 0 ≤ Real.pi/2 by positivity)]
    · change Real.cos _ * sphere (fun _ : Fin n => 0) j.castSucc = 0
      rw [ih, mul_zero]

lemma cos_angle_eq_zero {s : ℝ} (h : Real.pi / 2 ≤ |s|) : Real.cos (angle s) = 0 := by
  rcases le_abs.mp h with h | h
  · rw [angle, min_eq_left ((le_max_left _ _).trans' h), Real.cos_pi_div_two]
  · rw [angle, max_eq_right (by linarith : s ≤ -(Real.pi / 2)),
      min_eq_right (by linarith [Real.pi_pos]), Real.cos_neg, Real.cos_pi_div_two]

lemma terminal_zero {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (hi : Real.pi / 2 ≤ |x i|) :
    sphere x (Fin.last n) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    change Real.cos (angle (x 0)) * sphere (fun j => x j.succ) (Fin.last n) = 0
    revert hi
    refine Fin.cases ?_ (fun j hj => ?_) i
    · intro h
      rw [cos_angle_eq_zero h, zero_mul]
    · rw [ih _ j hj, mul_zero]

lemma sphere_prefix {n : ℕ} (x y : Fin n → ℝ) (i : Fin n)
    (hpre : ∀ j : Fin n, j.val < i.val → x j = y j)
    (he : angle (x i) = angle (y i)) (hz : Real.cos (angle (x i)) = 0) :
    sphere x = sphere y := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert hpre he hz
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _ he hz
      simp [sphere, ← he, hz]
    · intro hpre he hz
      have h0 : x 0 = y 0 := hpre 0 (by simp)
      have ht := ih (fun a => x a.succ) (fun a => y a.succ) j
        (fun a ha => hpre a.succ (by simpa using ha)) he hz
      simp only [sphere, h0, ht]

lemma saturated_norm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (hi : Real.pi / 2 ≤ |x i|) :
    ∑ j : Fin n, sphere x j.castSucc ^ 2 = 1 := by
  have h := sphere_unit x
  rwa [Fin.sum_univ_castSucc, terminal_zero x i hi, zero_pow (by decide), add_zero] at h

end LongTails.Proofs.MintyPrefixSphere
