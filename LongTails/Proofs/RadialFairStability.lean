import LongTails.Algorithms.RadialFairLocation
import Mathlib.Tactic

namespace OracleTemplate.RadialFairLocation

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma score_neg (r : ℝ) (z : E) : score r (-z) = -score r z := by
  simp [score]

lemma score_norm_le {r : ℝ} (hr : 0 < r) (z : E) : ‖score r z‖ ≤ 1 := by
  have hp : 0 < r + ‖z‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg z)
  rw [score, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp),
    inv_mul_eq_div, div_le_one hp]
  linarith

lemma score_monotonicity_identity {r : ℝ} (hr : 0 < r) (u v : E) :
    (r + ‖u‖) * (r + ‖v‖) * ⟪score r u - score r v, u - v⟫ =
      r * ‖u - v‖ ^ 2 + (‖u‖ + ‖v‖) * (‖u‖ * ‖v‖ - ⟪u, v⟫) := by
  have hu : r + ‖u‖ ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hr (norm_nonneg u))
  have hv : r + ‖v‖ ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hr (norm_nonneg v))
  simp only [score, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_comm v u, norm_sub_sq_real]
  field_simp
  ring

lemma score_strong_monotonicity {r : ℝ} (hr : 0 < r) (u v : E) :
    r / ((r + ‖u‖) * (r + ‖v‖)) * ‖u - v‖ ^ 2 ≤
      ⟪score r u - score r v, u - v⟫ := by
  have hp : 0 < (r + ‖u‖) * (r + ‖v‖) :=
    mul_pos (add_pos_of_pos_of_nonneg hr (norm_nonneg u))
      (add_pos_of_pos_of_nonneg hr (norm_nonneg v))
  rw [div_mul_eq_mul_div, div_le_iff₀ hp, mul_comm _ ((r + ‖u‖) * (r + ‖v‖)),
    score_monotonicity_identity hr]
  exact le_add_of_nonneg_right (mul_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))
    (sub_nonneg.mpr (real_inner_le_norm u v)))

lemma score_difference_ordered {r : ℝ} (hr : 0 < r) (u v : E)
    (huv : ‖u‖ ≤ ‖v‖) :
    ‖score r u - score r v‖ ≤ 2 * ‖u - v‖ / (r + ‖v‖) := by
  have hu : 0 < r + ‖u‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg u)
  have hv : 0 < r + ‖v‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg v)
  have hc : 0 ≤ (r + ‖u‖)⁻¹ - (r + ‖v‖)⁻¹ := by
    exact sub_nonneg.mpr (inv_anti₀ hu (by linarith))
  have he : score r u - score r v = (r + ‖v‖)⁻¹ • (u - v) +
      ((r + ‖u‖)⁻¹ - (r + ‖v‖)⁻¹) • u := by
    simp only [score, smul_sub, sub_smul]
    abel
  rw [he]
  have ht := norm_add_le ((r + ‖v‖)⁻¹ • (u - v))
    (((r + ‖u‖)⁻¹ - (r + ‖v‖)⁻¹) • u)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv),
    abs_of_nonneg hc] at ht
  have hid : ((r + ‖u‖)⁻¹ - (r + ‖v‖)⁻¹) * ‖u‖ =
      ((‖v‖ - ‖u‖) / (r + ‖v‖)) * (‖u‖ / (r + ‖u‖)) := by
    field_simp
    ring
  rw [hid] at ht
  have hf : ‖u‖ / (r + ‖u‖) ≤ 1 := (div_le_one hu).mpr (by linarith)
  have hn : ‖v‖ - ‖u‖ ≤ ‖u - v‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le v u
  have hmul := mul_le_mul_of_nonneg_left hf
    (div_nonneg (sub_nonneg.mpr huv) hv.le)
  have hdiv := div_le_div_of_nonneg_right hn hv.le
  rw [mul_one] at hmul
  rw [inv_mul_eq_div] at ht
  rw [mul_div_assoc]
  linarith

lemma score_difference {r : ℝ} (hr : 0 < r) (u v : E) :
    (r + ‖u‖ + ‖v‖) * ‖score r u - score r v‖ ≤ 4 * ‖u - v‖ := by
  have ordered (a b : E) (hab : ‖a‖ ≤ ‖b‖) :
      (r + ‖a‖ + ‖b‖) * ‖score r a - score r b‖ ≤ 4 * ‖a - b‖ := by
    have h := (le_div_iff₀ (add_pos_of_pos_of_nonneg hr (norm_nonneg b))).mp
      (score_difference_ordered hr a b hab)
    have hm := mul_le_mul_of_nonneg_right
      (show r + ‖a‖ + ‖b‖ ≤ 2 * (r + ‖b‖) by linarith)
      (norm_nonneg (score r a - score r b))
    nlinarith
  rcases le_total ‖u‖ ‖v‖ with h | h
  · exact ordered u v h
  · have h' := ordered v u h
    simpa only [norm_sub_rev, add_right_comm r ‖v‖ ‖u‖] using h'

lemma score_central_direction {r : ℝ} (hr : 0 < r) (z a : E)
    (ha : ‖a‖ ≤ r) (hz : 3 * r ≤ ‖z‖) :
    (2 / 5 : ℝ) * ‖z‖ ≤ ⟪score r (z - a), z⟫ := by
  have hp : 0 < r + ‖z - a‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg _)
  rw [score, real_inner_smul_left, inv_mul_eq_div, le_div_iff₀ hp]
  have hi : ⟪a, z⟫ ≤ r * ‖z‖ :=
    (real_inner_le_norm a z).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg z))
  have hn : ‖z - a‖ ≤ ‖z‖ + r := (norm_sub_le z a).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg z)
  have hz' := mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg z)
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith

lemma score_direction_lower {r : ℝ} (hr : 0 < r) (z a : E) :
    -‖z‖ ≤ ⟪score r (z - a), z⟫ := by
  have h := (abs_real_inner_le_norm (score r (z - a)) z).trans
    (mul_le_mul_of_nonneg_right (score_norm_le hr (z - a)) (norm_nonneg z))
  simpa only [one_mul] using (abs_le.mp h).1

lemma central_cluster_bound {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (a : Fin n → E) (z : E) (G : Finset (Fin n))
    (hcard : 3 * n ≤ 4 * G.card) (hG : ∀ i ∈ G, ‖a i‖ ≤ r)
    (hzero : ∑ i, score r (z - a i) = 0) : ‖z‖ ≤ 3 * r := by
  classical
  by_contra hz
  have hz' : 3 * r ≤ ‖z‖ := (lt_of_not_ge hz).le
  have hsum : (∑ i : Fin n, if i ∈ G then (2 / 5 : ℝ) * ‖z‖ else -‖z‖) ≤
      ∑ i : Fin n, ⟪score r (z - a i), z⟫ := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact score_central_direction hr z (a i) (hG i hi) hz'
    · exact score_direction_lower hr z (a i)
  have hsc : (∑ i : Fin n, if i ∈ G then (2 / 5 : ℝ) * ‖z‖ else -‖z‖) =
      (G.card : ℝ) * ((2 / 5 : ℝ) * ‖z‖) + ((n : ℝ) - G.card) * (-‖z‖) := by
    rw [Finset.sum_ite]
    simp only [Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
    have he : (Finset.univ.filter (fun i : Fin n => i ∉ G)).card + G.card = n := by
      simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun i : Fin n => i ∉ G)
    have her : ((Finset.univ.filter (fun i : Fin n => i ∉ G)).card : ℝ) = n - G.card := by
      have he' : ((Finset.univ.filter (fun i : Fin n => i ∉ G)).card : ℝ) + G.card = n := by exact_mod_cast he
      linarith
    rw [her]
  rw [hsc, ← sum_inner, hzero, inner_zero_left] at hsum
  have hc : 3 * (n : ℝ) ≤ 4 * (G.card : ℝ) := by exact_mod_cast hcard
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hzn : 0 < ‖z‖ := by linarith
  have hmul := mul_le_mul_of_nonneg_right hc hzn.le
  have hp := mul_pos hnr hzn
  nlinarith

lemma score_monotone {r : ℝ} (hr : 0 < r) (u v : E) :
    0 ≤ ⟪score r u - score r v, u - v⟫ :=
  (mul_nonneg (div_nonneg hr.le (mul_nonneg
    (add_nonneg hr.le (norm_nonneg u)) (add_nonneg hr.le (norm_nonneg v))))
    (sq_nonneg _)).trans (score_strong_monotonicity hr u v)

lemma score_local_strong_monotonicity {r M : ℝ} (hr : 0 < r) (u v : E)
    (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    r / (r + M) ^ 2 * ‖u - v‖ ^ 2 ≤ ⟪score r u - score r v, u - v⟫ := by
  have hpu : 0 < r + ‖u‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg u)
  have hpv : 0 < r + ‖v‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg v)
  have hd : (r + ‖u‖) * (r + ‖v‖) ≤ (r + M) ^ 2 := by
    nlinarith [mul_le_mul (show r + ‖u‖ ≤ r + M by linarith)
      (show r + ‖v‖ ≤ r + M by linarith) hpv.le (by linarith : 0 ≤ r + M)]
  exact (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hr.le (mul_pos hpu hpv) hd) (sq_nonneg _)).trans
      (score_strong_monotonicity hr u v)

lemma cluster_score_monotonicity {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (a : Fin n → E) (z w : E) (G : Finset (Fin n))
    (hz : ∀ i ∈ G, ‖z - a i‖ ≤ M) (hw : ∀ i ∈ G, ‖w - a i‖ ≤ M) :
    (G.card : ℝ) * (r / (r + M) ^ 2 * ‖z - w‖ ^ 2) ≤
      ⟪(∑ i, score r (z - a i)) - (∑ i, score r (w - a i)), z - w⟫ := by
  classical
  have hsum : (∑ i : Fin n, if i ∈ G then r / (r + M) ^ 2 * ‖z - w‖ ^ 2 else 0) ≤
      ∑ i : Fin n, ⟪score r (z - a i) - score r (w - a i), z - w⟫ := by
    apply Finset.sum_le_sum
    intro i _
    have he : (z - a i) - (w - a i) = z - w := by abel
    split_ifs with hi
    · simpa only [he] using score_local_strong_monotonicity hr
        (z - a i) (w - a i) (hz i hi) (hw i hi)
    · simpa only [he] using score_monotone hr (z - a i) (w - a i)
  simpa only [Finset.sum_ite_irrel, Finset.sum_ite, Finset.filter_univ_mem,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    ← sum_inner, Finset.sum_sub_distrib] using hsum

lemma cluster_root_stability {n : ℕ} {r M : ℝ} (hr : 0 < r) (K : Fin n → ℝ)
    (a b : Fin n → E) (z w : E) (G : Finset (Fin n))
    (hz : ∀ i ∈ G, ‖z - a i‖ ≤ M) (hw : ∀ i ∈ G, ‖w - a i‖ ≤ M)
    (hza : ∑ i, score r (z - a i) = 0) (hwb : ∑ i, score r (w - b i) = 0)
    (herr : ∀ i, ‖score r (w - a i) - score r (w - b i)‖ ≤ K i) :
    (G.card : ℝ) * (r / (r + M) ^ 2) * ‖z - w‖ ≤ ∑ i, K i := by
  have hmono := cluster_score_monotonicity hr a z w G hz hw
  rw [hza, zero_sub] at hmono
  have he : (∑ i, score r (w - a i)) =
      ∑ i, (score r (w - a i) - score r (w - b i)) := by
    rw [Finset.sum_sub_distrib, hwb, sub_zero]
  have hn : ‖∑ i, score r (w - a i)‖ ≤ ∑ i, K i := by
    rw [he]
    exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => herr i))
  have hi := (real_inner_le_norm (-(∑ i, score r (w - a i))) (z - w)).trans
    (mul_le_mul_of_nonneg_right (by simpa only [norm_neg] using hn) (norm_nonneg _))
  by_cases hd : ‖z - w‖ = 0
  · rw [hd, mul_zero]
    exact (norm_nonneg _).trans hn
  · have hpos := lt_of_le_of_ne (norm_nonneg (z - w)) (Ne.symm hd)
    have hm : ((G.card : ℝ) * (r / (r + M) ^ 2) * ‖z - w‖) * ‖z - w‖ ≤
        (∑ i, K i) * ‖z - w‖ := by nlinarith
    exact (mul_le_mul_iff_left₀ hpos).mp hm

lemma score_relative_perturbation {r h : ℝ} (hr : 0 < r) (u v : E)
    (hrel : ‖u - v‖ ≤ h * (r + ‖u‖ + ‖v‖)) :
    ‖score r u - score r v‖ ≤ 4 * h := by
  have hp : 0 < r + ‖u‖ + ‖v‖ := by positivity
  have hs := score_difference hr u v
  have hm : (r + ‖u‖ + ‖v‖) * ‖score r u - score r v‖ ≤
      (r + ‖u‖ + ‖v‖) * (4 * h) := by linarith
  exact (mul_le_mul_iff_right₀ hp).mp hm

lemma score_shifted_relative {r t h M : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hh : 0 ≤ h) (a b w : E) (hw : ‖w‖ ≤ M)
    (hrel : ‖a - b‖ ≤ t + h * (‖a‖ + ‖b‖)) :
    ‖score r (w - a) - score r (w - b)‖ ≤ 4 * ((t + h * (r + 2 * M)) / r) := by
  apply score_relative_perturbation hr
  have he : (w - a) - (w - b) = -(a - b) := by abel
  rw [he, norm_neg]
  have ha : ‖a‖ ≤ ‖w - a‖ + M := by
    have hn := norm_sub_le w (w - a)
    rw [sub_sub_cancel] at hn
    linarith
  have hb : ‖b‖ ≤ ‖w - b‖ + M := by
    have hn := norm_sub_le w (w - b)
    rw [sub_sub_cancel] at hn
    linarith
  have hM : 0 ≤ M := (norm_nonneg w).trans hw
  have hD : h ≤ (t + h * (r + 2 * M)) / r := by
    rw [le_div_iff₀ hr]
    nlinarith
  have heq : (t + h * (r + 2 * M)) / r * r = t + h * (r + 2 * M) :=
    div_mul_cancel₀ _ hr.ne'
  have ham := mul_le_mul_of_nonneg_left (add_le_add ha hb) hh
  have hdm := mul_le_mul_of_nonneg_right hD (add_nonneg (norm_nonneg (w - a))
    (norm_nonneg (w - b)))
  nlinarith

lemma score_ratio_bound {r : ℝ} (hr : 0 < r) (a b w : E) (hw : ‖w‖ ≤ 3 * r) :
    ‖score r (w - a) - score r (w - b)‖ ≤
      32 * (‖a - b‖ / (r + ‖a‖ + ‖b‖)) := by
  let h := ‖a - b‖ / (r + ‖a‖ + ‖b‖)
  have hp : 0 < r + ‖a‖ + ‖b‖ := by positivity
  have hh : 0 ≤ h := div_nonneg (norm_nonneg _) hp.le
  have he : h * (r + ‖a‖ + ‖b‖) = ‖a - b‖ := div_mul_cancel₀ _ hp.ne'
  have hrel : ‖a - b‖ ≤ h * r + h * (‖a‖ + ‖b‖) := by nlinarith
  have hs := score_shifted_relative hr (mul_nonneg hh hr.le) hh a b w hw hrel
  have hid : 4 * ((h * r + h * (r + 2 * (3 * r))) / r) = 32 * h := by
    field_simp
    ring
  rwa [hid] at hs

lemma relative_cluster_root_stability {n : ℕ} {r : ℝ} (hr : 0 < r)
    (a b : Fin n → E) (z w : E) (G : Finset (Fin n))
    (hcard : 3 * n ≤ 4 * G.card) (ha : ∀ i ∈ G, ‖a i‖ ≤ r)
    (hz : ‖z‖ ≤ 3 * r) (hw : ‖w‖ ≤ 3 * r)
    (hza : ∑ i, score r (z - a i) = 0) (hwb : ∑ i, score r (w - b i) = 0) :
    (n : ℝ) * ‖z - w‖ ≤
      2048 * r * ∑ i, ‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖) := by
  have hz' : ∀ i ∈ G, ‖z - a i‖ ≤ 4 * r := by
    intro i hi
    exact (norm_sub_le _ _).trans (by linarith [ha i hi])
  have hw' : ∀ i ∈ G, ‖w - a i‖ ≤ 4 * r := by
    intro i hi
    exact (norm_sub_le _ _).trans (by linarith [ha i hi])
  have hs := cluster_root_stability hr
    (fun i => 32 * (‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖))) a b z w G hz' hw'
    hza hwb (fun i => score_ratio_bound hr (a i) (b i) w hw)
  rw [← Finset.mul_sum] at hs
  have hid : r / (r + 4 * r) ^ 2 = 1 / (25 * r) := by
    field_simp
    ring
  rw [hid] at hs
  have hm := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 25 * r)
  have he : ((G.card : ℝ) * (1 / (25 * r)) * ‖z - w‖) * (25 * r) =
      (G.card : ℝ) * ‖z - w‖ := by field_simp
  rw [he] at hm
  have hc : 3 * (n : ℝ) ≤ 4 * (G.card : ℝ) := by exact_mod_cast hcard
  have hcm := mul_le_mul_of_nonneg_right hc (norm_nonneg (z - w))
  have hsum : 0 ≤ ∑ i : Fin n, ‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖) := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  nlinarith [mul_nonneg hr.le hsum]

lemma score_lipschitz {r : ℝ} (hr : 0 < r) (u v : E) :
    ‖score r u - score r v‖ ≤ (4 / r) * ‖u - v‖ := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  have h := score_difference hr u v
  have hp := mul_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))
    (norm_nonneg (score r u - score r v))
  nlinarith

lemma sum_score_lipschitz {n : ℕ} {r : ℝ} (hr : 0 < r)
    (a : Fin n → E) (z w : E) :
    ‖(∑ i, score r (z - a i)) - (∑ i, score r (w - a i))‖ ≤
      (4 * n / r) * ‖z - w‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖score r (z - a i) - score r (w - a i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (4 / r) * ‖z - w‖ := by
      apply Finset.sum_le_sum
      intro i _
      have he : (z - a i) - (w - a i) = z - w := by abel
      simpa only [he] using score_lipschitz hr (z - a i) (w - a i)
    _ = _ := by simp; ring

lemma sum_score_local_strong {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (a : Fin n → E) (ha : ∀ i, ‖a i‖ ≤ M) (z w : E)
    (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ((n : ℝ) * r / (r + 2 * M) ^ 2) * ‖z - w‖ ^ 2 ≤
      ⟪(∑ i, score r (z - a i)) - (∑ i, score r (w - a i)), z - w⟫ := by
  have hza : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖z - a i‖ ≤ 2 * M := by
    intro i _
    exact (norm_sub_le _ _).trans (by linarith [ha i])
  have hwa : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖w - a i‖ ≤ 2 * M := by
    intro i _
    exact (norm_sub_le _ _).trans (by linarith [ha i])
  simpa only [Finset.card_univ, Fintype.card_fin, ← mul_assoc, ← mul_div_assoc]
    using cluster_score_monotonicity hr a z w Finset.univ hza hwa

end OracleTemplate.RadialFairLocation
