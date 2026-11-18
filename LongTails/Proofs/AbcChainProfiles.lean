import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas

open scoped Topology

namespace LongTails.Proofs.AbcChainProfiles

noncomputable def pos (s : ℝ) : ℝ := max s 0

noncomputable def rr (s : ℝ) : ℝ := pos s ^ 2 / 2

lemma abs_sub_le_sum (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [abs_neg, ← sub_eq_add_neg] at h

lemma pos_nonneg (s : ℝ) : 0 ≤ pos s := le_max_right _ _

lemma pos_of_nonneg {s : ℝ} (h : 0 ≤ s) : pos s = s := max_eq_left h

lemma pos_of_nonpos {s : ℝ} (h : s ≤ 0) : pos s = 0 := max_eq_right h

lemma pos_lipschitz (x y : ℝ) : |pos x - pos y| ≤ |x - y| := by
  simpa [pos] using abs_max_sub_max_le_abs x y 0

lemma rr_model (x y : ℝ) : |rr y - rr x - pos x * (y - x)| ≤ (y - x) ^ 2 / 2 := by
  rw [abs_le]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simp only [rr, pos_of_nonneg hx, pos_of_nonneg hy]; constructor <;> nlinarith
  · simp only [rr, pos_of_nonneg hx, pos_of_nonpos hy]; constructor <;> nlinarith [mul_nonneg hx (neg_nonneg.mpr hy)]
  · simp only [rr, pos_of_nonpos hx, pos_of_nonneg hy]; constructor <;> nlinarith
  · simp only [rr, pos_of_nonpos hx, pos_of_nonpos hy]; constructor <;> nlinarith

noncomputable def psi (t : ℝ) : ℝ := 16 * (rr (t - 1 / 2) - 2 * rr (t - 3 / 4) + rr (t - 1))

noncomputable def dpsi (t : ℝ) : ℝ := 16 * (pos (t - 1 / 2) - 2 * pos (t - 3 / 4) + pos (t - 1))

noncomputable def phi (t : ℝ) : ℝ := rr (t + 2) - rr (t + 1) - rr (t - 1) + rr (t - 2)

noncomputable def dphi (t : ℝ) : ℝ := pos (t + 2) - pos (t + 1) - pos (t - 1) + pos (t - 2)

lemma psi_model (x y : ℝ) :
    |psi y - psi x - dpsi x * (y - x)| ≤ 32 * (y - x) ^ 2 := by
  have h1 := rr_model (x - 1 / 2) (y - 1 / 2)
  have h2 := rr_model (x - 3 / 4) (y - 3 / 4)
  have h3 := rr_model (x - 1) (y - 1)
  have e : psi y - psi x - dpsi x * (y - x) =
      16 * ((rr (y - 1 / 2) - rr (x - 1 / 2) - pos (x - 1 / 2) * ((y - 1 / 2) - (x - 1 / 2))) -
        2 * (rr (y - 3 / 4) - rr (x - 3 / 4) - pos (x - 3 / 4) * ((y - 3 / 4) - (x - 3 / 4))) +
        (rr (y - 1) - rr (x - 1) - pos (x - 1) * ((y - 1) - (x - 1)))) := by
    simp only [psi, dpsi]; ring
  have e1 : (y - 1 / 2) - (x - 1 / 2) = y - x := by ring
  have e2 : (y - 3 / 4) - (x - 3 / 4) = y - x := by ring
  have e3 : (y - 1) - (x - 1) = y - x := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e, e1, e2, e3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  have ht := abs_add_three (rr (y - 1 / 2) - rr (x - 1 / 2) - pos (x - 1 / 2) * (y - x))
    (-(2 * (rr (y - 3 / 4) - rr (x - 3 / 4) - pos (x - 3 / 4) * (y - x))))
    (rr (y - 1) - rr (x - 1) - pos (x - 1) * (y - x))
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  have hs : rr (y - 1 / 2) - rr (x - 1 / 2) - pos (x - 1 / 2) * (y - x) -
      2 * (rr (y - 3 / 4) - rr (x - 3 / 4) - pos (x - 3 / 4) * (y - x)) +
      (rr (y - 1) - rr (x - 1) - pos (x - 1) * (y - x)) =
      rr (y - 1 / 2) - rr (x - 1 / 2) - pos (x - 1 / 2) * (y - x) +
      -(2 * (rr (y - 3 / 4) - rr (x - 3 / 4) - pos (x - 3 / 4) * (y - x))) +
      (rr (y - 1) - rr (x - 1) - pos (x - 1) * (y - x)) := by ring
  rw [hs]
  nlinarith

lemma phi_model (x y : ℝ) :
    |phi y - phi x - dphi x * (y - x)| ≤ 2 * (y - x) ^ 2 := by
  have h1 := rr_model (x + 2) (y + 2)
  have h2 := rr_model (x + 1) (y + 1)
  have h3 := rr_model (x - 1) (y - 1)
  have h4 := rr_model (x - 2) (y - 2)
  have e1 : (y + 2) - (x + 2) = y - x := by ring
  have e2 : (y + 1) - (x + 1) = y - x := by ring
  have e3 : (y - 1) - (x - 1) = y - x := by ring
  have e4 : (y - 2) - (x - 2) = y - x := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  have e : phi y - phi x - dphi x * (y - x) =
      (rr (y + 2) - rr (x + 2) - pos (x + 2) * (y - x)) +
      -(rr (y + 1) - rr (x + 1) - pos (x + 1) * (y - x)) +
      -(rr (y - 1) - rr (x - 1) - pos (x - 1) * (y - x)) +
      (rr (y - 2) - rr (x - 2) - pos (x - 2) * (y - x)) := by
    simp only [phi, dphi]; ring
  rw [e]
  have k1 := abs_add_le (rr (y + 2) - rr (x + 2) - pos (x + 2) * (y - x) +
      -(rr (y + 1) - rr (x + 1) - pos (x + 1) * (y - x)) +
      -(rr (y - 1) - rr (x - 1) - pos (x - 1) * (y - x)))
    (rr (y - 2) - rr (x - 2) - pos (x - 2) * (y - x))
  have k2 := abs_add_three (rr (y + 2) - rr (x + 2) - pos (x + 2) * (y - x))
    (-(rr (y + 1) - rr (x + 1) - pos (x + 1) * (y - x)))
    (-(rr (y - 1) - rr (x - 1) - pos (x - 1) * (y - x)))
  rw [abs_neg, abs_neg] at k2
  linarith

lemma model_hasDerivAt (f f' : ℝ → ℝ) (C : ℝ) (h : ∀ x y, |f y - f x - f' x * (y - x)| ≤ C * (y - x) ^ 2)
    (x : ℝ) : HasDerivAt f (f' x) x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun y => f y - f x - (y - x) • f' x) =O[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [] with y
    have hm := h x y
    simp only [Real.norm_eq_abs, smul_eq_mul, mul_comm (y - x), sq_abs]
    rw [abs_of_nonneg (sq_nonneg (y - x))]
    exact hm
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

lemma psi_hasDerivAt (x : ℝ) : HasDerivAt psi (dpsi x) x :=
  model_hasDerivAt psi dpsi 32 psi_model x

lemma phi_hasDerivAt (x : ℝ) : HasDerivAt phi (dphi x) x :=
  model_hasDerivAt phi dphi 2 phi_model x

lemma dpsi_nonneg (t : ℝ) : 0 ≤ dpsi t := by
  simp only [dpsi, pos, max_def]
  split_ifs <;> linarith

lemma dpsi_le (t : ℝ) : dpsi t ≤ 4 := by
  simp only [dpsi, pos, max_def]
  split_ifs <;> linarith

lemma dphi_nonneg (t : ℝ) : 0 ≤ dphi t := by
  simp only [dphi, pos, max_def]
  split_ifs <;> linarith

lemma dphi_le_one (t : ℝ) : dphi t ≤ 1 := by
  simp only [dphi, pos, max_def]
  split_ifs <;> linarith

lemma psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  simp only [psi, rr, pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (1 - t)]

lemma psi_le_one (t : ℝ) : psi t ≤ 1 := by
  simp only [psi, rr, pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (1 - t)]

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by
  simp only [phi, rr, pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (t + 2), sq_nonneg (2 - t)]

lemma phi_le (t : ℝ) : phi t ≤ 3 := by
  simp only [phi, rr, pos, max_def]
  split_ifs <;> nlinarith [sq_nonneg (t + 2), sq_nonneg (2 - t)]

lemma psi_of_le {t : ℝ} (h : t ≤ 1 / 2) : psi t = 0 := by
  simp only [psi, rr, pos_of_nonpos (by linarith : t - 1 / 2 ≤ 0),
    pos_of_nonpos (by linarith : t - 3 / 4 ≤ 0), pos_of_nonpos (by linarith : t - 1 ≤ 0)]
  ring

lemma dpsi_of_le {t : ℝ} (h : t ≤ 1 / 2) : dpsi t = 0 := by
  simp only [dpsi, pos_of_nonpos (by linarith : t - 1 / 2 ≤ 0),
    pos_of_nonpos (by linarith : t - 3 / 4 ≤ 0), pos_of_nonpos (by linarith : t - 1 ≤ 0)]
  ring

lemma psi_of_ge {t : ℝ} (h : 1 ≤ t) : psi t = 1 := by
  simp only [psi, rr, pos_of_nonneg (by linarith : 0 ≤ t - 1 / 2),
    pos_of_nonneg (by linarith : 0 ≤ t - 3 / 4), pos_of_nonneg (by linarith : 0 ≤ t - 1)]
  ring

lemma dpsi_of_ge {t : ℝ} (h : 1 ≤ t) : dpsi t = 0 := by
  simp only [dpsi, pos_of_nonneg (by linarith : 0 ≤ t - 1 / 2),
    pos_of_nonneg (by linarith : 0 ≤ t - 3 / 4), pos_of_nonneg (by linarith : 0 ≤ t - 1)]
  ring

lemma dphi_of_abs_le {t : ℝ} (h : |t| ≤ 1) : dphi t = 1 := by
  have h1 := neg_abs_le t
  have h2 := le_abs_self t
  simp only [dphi, pos_of_nonneg (by linarith : 0 ≤ t + 2), pos_of_nonneg (by linarith : 0 ≤ t + 1),
    pos_of_nonpos (by linarith : t - 1 ≤ 0), pos_of_nonpos (by linarith : t - 2 ≤ 0)]
  ring

lemma dphi_of_two_le {t : ℝ} (h : 2 ≤ t) : dphi t = 0 := by
  simp only [dphi, pos_of_nonneg (by linarith : 0 ≤ t + 2), pos_of_nonneg (by linarith : 0 ≤ t + 1),
    pos_of_nonneg (by linarith : 0 ≤ t - 1), pos_of_nonneg (by linarith : 0 ≤ t - 2)]
  ring

lemma dphi_of_le_neg_two {t : ℝ} (h : t ≤ -2) : dphi t = 0 := by
  simp only [dphi, pos_of_nonpos (by linarith : t + 2 ≤ 0), pos_of_nonpos (by linarith : t + 1 ≤ 0),
    pos_of_nonpos (by linarith : t - 1 ≤ 0), pos_of_nonpos (by linarith : t - 2 ≤ 0)]
  ring

lemma phi_of_two_le {t : ℝ} (h : 2 ≤ t) : phi t = 3 := by
  simp only [phi, rr, pos_of_nonneg (by linarith : 0 ≤ t + 2), pos_of_nonneg (by linarith : 0 ≤ t + 1),
    pos_of_nonneg (by linarith : 0 ≤ t - 1), pos_of_nonneg (by linarith : 0 ≤ t - 2)]
  ring

lemma phi_of_le_neg_two {t : ℝ} (h : t ≤ -2) : phi t = 0 := by
  simp only [phi, rr, pos_of_nonpos (by linarith : t + 2 ≤ 0), pos_of_nonpos (by linarith : t + 1 ≤ 0),
    pos_of_nonpos (by linarith : t - 1 ≤ 0), pos_of_nonpos (by linarith : t - 2 ≤ 0)]
  ring

lemma phi_zero : phi 0 = 3 / 2 := by
  simp only [phi, rr, pos_of_nonneg (by norm_num : (0 : ℝ) ≤ 0 + 2),
    pos_of_nonneg (by norm_num : (0 : ℝ) ≤ 0 + 1), pos_of_nonpos (by norm_num : (0 : ℝ) - 1 ≤ 0),
    pos_of_nonpos (by norm_num : (0 : ℝ) - 2 ≤ 0)]
  norm_num

lemma psi_one : psi 1 = 1 := psi_of_ge le_rfl

lemma dpsi_lipschitz (x y : ℝ) : |dpsi x - dpsi y| ≤ 64 * |x - y| := by
  have h1 := pos_lipschitz (x - 1 / 2) (y - 1 / 2)
  have h2 := pos_lipschitz (x - 3 / 4) (y - 3 / 4)
  have h3 := pos_lipschitz (x - 1) (y - 1)
  have e1 : x - 1 / 2 - (y - 1 / 2) = x - y := by ring
  have e2 : x - 3 / 4 - (y - 3 / 4) = x - y := by ring
  have e3 : x - 1 - (y - 1) = x - y := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have e : dpsi x - dpsi y = 16 * ((pos (x - 1 / 2) - pos (y - 1 / 2)) +
      -(2 * (pos (x - 3 / 4) - pos (y - 3 / 4))) + (pos (x - 1) - pos (y - 1))) := by
    simp only [dpsi]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  have k := abs_add_three (pos (x - 1 / 2) - pos (y - 1 / 2))
    (-(2 * (pos (x - 3 / 4) - pos (y - 3 / 4)))) (pos (x - 1) - pos (y - 1))
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at k
  nlinarith

lemma dphi_lipschitz (x y : ℝ) : |dphi x - dphi y| ≤ 4 * |x - y| := by
  have h1 := pos_lipschitz (x + 2) (y + 2)
  have h2 := pos_lipschitz (x + 1) (y + 1)
  have h3 := pos_lipschitz (x - 1) (y - 1)
  have h4 := pos_lipschitz (x - 2) (y - 2)
  have e1 : x + 2 - (y + 2) = x - y := by ring
  have e2 : x + 1 - (y + 1) = x - y := by ring
  have e3 : x - 1 - (y - 1) = x - y := by ring
  have e4 : x - 2 - (y - 2) = x - y := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  have e : dphi x - dphi y = (pos (x + 2) - pos (y + 2)) + -(pos (x + 1) - pos (y + 1)) +
      -(pos (x - 1) - pos (y - 1)) + (pos (x - 2) - pos (y - 2)) := by
    simp only [dphi]; ring
  rw [e]
  have k1 := abs_add_le ((pos (x + 2) - pos (y + 2)) + -(pos (x + 1) - pos (y + 1)) +
      -(pos (x - 1) - pos (y - 1))) (pos (x - 2) - pos (y - 2))
  have k2 := abs_add_three (pos (x + 2) - pos (y + 2)) (-(pos (x + 1) - pos (y + 1)))
    (-(pos (x - 1) - pos (y - 1)))
  rw [abs_neg, abs_neg] at k2
  linarith

lemma lipschitz_of_deriv (f f' : ℝ → ℝ) (C : ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x, |f' x| ≤ C) (x y : ℝ) : |f x - f y| ≤ C * |x - y| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := C) (fun z _ => (hf z).hasDerivWithinAt)
    (fun z _ => by simpa [Real.norm_eq_abs] using hb z) (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

lemma psi_lipschitz (x y : ℝ) : |psi x - psi y| ≤ 4 * |x - y| :=
  lipschitz_of_deriv psi dpsi 4 psi_hasDerivAt
    (fun z => by rw [abs_of_nonneg (dpsi_nonneg z)]; exact dpsi_le z) x y

lemma phi_lipschitz (x y : ℝ) : |phi x - phi y| ≤ |x - y| := by
  have h := lipschitz_of_deriv phi dphi 1 phi_hasDerivAt
    (fun z => by rw [abs_of_nonneg (dphi_nonneg z)]; exact dphi_le_one z) x y
  simpa using h

end LongTails.Proofs.AbcChainProfiles
