import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronHistory

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_unit_bound {u v : E} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |⟪u, v⟫| ≤ 1 := by
  have hm := mul_le_mul hu hv (norm_nonneg v) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_real_inner_le_norm u v).trans (by simpa using hm)

lemma signed_product_lower {a b C e : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ e)
    : -C * e ≤ a * b := by
  have hm := mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)
  have hn := neg_le_abs (a * b)
  rw [abs_mul] at hn
  nlinarith

lemma history_step {p r : ι → E} {z : E} {a t T C e g : ℝ} (j : ι)
    (ht : 0 ≤ t)
    (ha : |a| ≤ C * t)
    (hp : ∀ i, ‖p i‖ ≤ 1)
    (hcross : ∀ i j, |⟪p i, r j⟫| ≤ e)
    (hgram : ∀ i j, g ≤ ⟪r i, r j⟫)
    (hP : ∀ i, |⟪p i, z⟫| ≤ (C + e) * T)
    (hR : ∀ i, (g - C * e) * T ≤ ⟪r i, z⟫) :
    (∀ i, |⟪p i, z + a • p j + t • r j⟫| ≤ (C + e) * (T + t)) ∧
    (∀ i, (g - C * e) * (T + t) ≤ ⟪r i, z + a • p j + t • r j⟫) := by
  constructor
  · intro i
    simp only [inner_add_right, real_inner_smul_right]
    have hpp := inner_unit_bound (hp i) (hp j)
    have hpa : |a * ⟪p i, p j⟫| ≤ C * t := by
      rw [abs_mul]
      calc
        _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hpp (abs_nonneg a)
        _ ≤ C * t := by simpa using ha
    have hpr : |t * ⟪p i, r j⟫| ≤ t * e := by
      rw [abs_mul, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left (hcross i j) ht
    have hsum := abs_add_le (⟪p i, z⟫ + a * ⟪p i, p j⟫) (t * ⟪p i, r j⟫)
    have hsum' := abs_add_le ⟪p i, z⟫ (a * ⟪p i, p j⟫)
    have hpi := hP i
    nlinarith
  · intro i
    simp only [inner_add_right, real_inner_smul_right]
    have hc : |⟪r i, p j⟫| ≤ e := by rw [real_inner_comm]; exact hcross j i
    have ha' := signed_product_lower ha hc
    have ht' := mul_le_mul_of_nonneg_left (hgram i j) ht
    have hri := hR i
    nlinarith

lemma history_margin {a t T P R C F H : ℝ} (ht : 0 ≤ t)
    (ha : |a| ≤ C * t)
    (hP : |P| ≤ F * T) (hR : H * T ≤ R) :
    (H - C * F) * t * T ≤ a * P + t * R := by
  have hp := signed_product_lower ha hP
  have hr := mul_le_mul_of_nonneg_left hR ht
  nlinarith

lemma cross_perturbation {u v u₀ v₀ : E} {d : ℝ}
    (hu : ‖u - u₀‖ ≤ d) (hv : ‖v - v₀‖ ≤ d)
    (hv1 : ‖v‖ ≤ 1) (hu1 : ‖u₀‖ ≤ 1) (horth : ⟪u₀, v₀⟫ = 0) :
    |⟪u, v⟫| ≤ 2 * d := by
  have hd : 0 ≤ d := (norm_nonneg _).trans hu
  have h1 : |⟪u - u₀, v⟫| ≤ d := by
    have hm := mul_le_mul hu hv1 (norm_nonneg v) hd
    exact (abs_real_inner_le_norm _ _).trans (by simpa using hm)
  have h2 : |⟪u₀, v - v₀⟫| ≤ d := by
    have hm := mul_le_mul hu1 hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact (abs_real_inner_le_norm _ _).trans (by simpa using hm)
  have he : ⟪u, v⟫ = ⟪u - u₀, v⟫ + ⟪u₀, v - v₀⟫ := by
    simp only [inner_sub_left, inner_sub_right, horth]
    ring
  rw [he]
  have ha := abs_add_le ⟪u - u₀, v⟫ ⟪u₀, v - v₀⟫
  linarith

lemma gram_perturbation {u v w : E} {d : ℝ}
    (hu : ‖u - w‖ ≤ d) (hv : ‖v - w‖ ≤ d) :
    ‖w‖ ^ 2 - 2 * ‖w‖ * d - d ^ 2 ≤ ⟪u, v⟫ := by
  have hd : 0 ≤ d := (norm_nonneg _).trans hu
  have h1 : |⟪u - w, w⟫| ≤ d * ‖w‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg w))
  have h2 : |⟪w, v - w⟫| ≤ ‖w‖ * d :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg w))
  have h3 : |⟪u - w, v - w⟫| ≤ d ^ 2 := by
    have hm := mul_le_mul hu hv (norm_nonneg _) hd
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith)
  have he : ⟪u, v⟫ = ‖w‖ ^ 2 + ⟪u - w, w⟫ + ⟪w, v - w⟫ +
      ⟪u - w, v - w⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  rw [he]
  have h1' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).1
  have h3' := (abs_le.mp h3).1
  linarith

lemma cap_gram {u v w : E} {κ : ℝ} (hκ : 0 < κ)
    (hu : ‖u - w‖ ≤ κ / 32) (hv : ‖v - w‖ ≤ κ / 32)
    (hw : 2 * κ ≤ ‖w‖) : κ ^ 2 ≤ ⟪u, v⟫ := by
  have hg := gram_perturbation hu hv
  have hm := mul_nonneg (sub_nonneg.mpr hw)
    (show 0 ≤ ‖w‖ + 2 * κ - κ / 16 by nlinarith [norm_nonneg w])
  nlinarith [sq_nonneg κ]

end LongTails.Proofs.ClusteredConvolutionalPerceptronHistory
