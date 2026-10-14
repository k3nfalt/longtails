import LongTails.Proofs.ReshuffledAnchorMoments
import LongTails.Proofs.ReshuffledLastIterateStep

set_option autoImplicit false

open Finset

namespace OracleTemplate.ReshuffledHarmonicRate

open ReshuffledHarmonic ReshuffledWeighted

noncomputable def previous (w : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then w 0 else w (t - 1)

lemma sum_previous {T : ℕ} (hT : 0 < T) (w F : ℕ → ℝ) :
    (∑ t ∈ range T, previous w t * F t) =
      w 0 * F 0 + ∑ t ∈ range (T - 1), w t * F (t + 1) := by
  cases T with
  | zero => omega
  | succ m => simp [sum_range_succ', previous, add_comm]

lemma previous_nonneg {T t : ℕ} (ht : t < T) : 0 ≤ previous (weight T) t := by
  unfold previous
  split_ifs with he
  · exact (weight_pos (by omega : 0 < T)).le
  · exact (weight_pos (by omega : t - 1 < T)).le

lemma previous_le {T t : ℕ} (ht : t < T) : previous (weight T) t ≤ weight T t := by
  by_cases he : t = 0
  · simp [previous, he]
  · have hm := weight_mono (T := T) (t := t - 1) (by omega)
    simpa [previous, he, Nat.sub_add_cancel (by omega : 1 ≤ t)] using hm

lemma weight_le_previous {T t : ℕ} (ht : t < T) : weight T t ≤ 2 * previous (weight T) t := by
  by_cases he : t = 0
  · subst t
    have h := (weight_pos ht).le
    change weight T 0 ≤ 2 * weight T 0
    linarith
  · have hm := weight_adjacent (T := T) (t := t - 1) (by omega)
    simpa [previous, he, Nat.sub_add_cancel (by omega : 1 ≤ t)] using hm

lemma sum_kernel_le_previous {T : ℕ} (hT : 0 < T) (F : ℕ → ℝ)
    (hF : ∀ t, t < T → 0 ≤ F t) :
    (∑ t ∈ range T, (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) * F (t + 1)) ≤
      ∑ t ∈ range T, previous (weight T) t * F t := by
  rw [sum_previous hT]
  have hsplit : (∑ t ∈ range T,
      (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) * F (t + 1)) =
      ∑ t ∈ range (T - 1),
        (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) * F (t + 1) := by
    cases T with
    | zero => omega
    | succ m => simp [sum_range_succ]
  rw [hsplit]
  have hs : (∑ t ∈ range (T - 1),
      (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) * F (t + 1)) ≤
      ∑ t ∈ range (T - 1), weight T t * F (t + 1) := by
    apply sum_le_sum
    intro t ht
    have ht' := mem_range.mp ht
    exact mul_le_mul_of_nonneg_right (weight_kernel (by omega)) (hF _ (by omega))
  have hp := mul_nonneg (weight_pos hT).le (hF 0 hT)
  linarith

lemma summed_anchor_moment {T : ℕ} (hT : 0 < T) (A R N : ℕ → ℝ) {η L H V0 : ℝ}
     (hL : 0 ≤ L) (hV : 0 ≤ V0)
    (hstep : η * L * H ≤ 1 / 40)
    (hA : ∀ t, t < T → 0 ≤ A t) (hR : ∀ t, t < T → 0 ≤ R t)
    (hcenter : (∑ t ∈ range T, previous (weight T) t * A t) ≤
      2 * (∑ t ∈ range T, previous (weight T) t * R t) +
        4 * η * H * V0 * ∑ t ∈ range T, previous (weight T) t)
    (hanchor : (∑ t ∈ range T, weight T t * N t) ≤
      4 * L * (∑ t ∈ range T, (T - (t + 1) : ℕ) *
        (weight T (t + 1) - weight T t) * (A (t + 1) + R (t + 1))) +
        2 * V0 * ∑ t ∈ range T, weight T t) :
    (∑ t ∈ range T, weight T t * N t) ≤
      12 * L * (∑ t ∈ range T, previous (weight T) t * R t) +
        3 * V0 * ∑ t ∈ range T, weight T t := by
  have hk := sum_kernel_le_previous hT (fun t => A t + R t)
    (fun t ht => add_nonneg (hA t ht) (hR t ht))
  simp only [mul_add, sum_add_distrib] at hk hanchor
  have hkl := mul_le_mul_of_nonneg_left hk (show 0 ≤ 4 * L by positivity)
  have hc := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 4 * L by positivity)
  have hv : (∑ t ∈ range T, previous (weight T) t) ≤ ∑ t ∈ range T, weight T t :=
    sum_le_sum fun t ht => previous_le (mem_range.mp ht)
  have hv0 : 0 ≤ ∑ t ∈ range T, previous (weight T) t :=
    sum_nonneg fun t ht => previous_nonneg (mem_range.mp ht)
  have hsmall := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ 16 * V0 * ∑ t ∈ range T, previous (weight T) t by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv hV
  have hnoise0 := mul_nonneg hV hv0
  nlinarith

lemma aggregate_step {n η L H G D M N B P R V W V0 : ℝ}
    (hn : 0 < n) (hη : 0 ≤ η) (hL : 0 ≤ L) (hH : 1 ≤ H)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hstep : η * L * H ≤ 1 / 40)
    (hs : 2 * η * G ≤ D + (4 + η * L) * η ^ 2 * M + 2 * η ^ 2 * N +
      (14 / (3 * n)) * η ^ 2 * P + 2 * η ^ 2 * L * R - 2 * η * B)
    (hh : P ≤ n * H * M) (hb : M ≤ 4 * L * B + 2 * N)
    (hr : R ≤ 2 * V) (ha : N ≤ 12 * L * V + 3 * V0 * W) :
    η * G ≤ D / 2 + 134 * H * η ^ 2 * L * V + 33 * H * η ^ 2 * V0 * W := by
  have hH0 : 0 ≤ H := by linarith
  have he : η * L ≤ 1 / 40 := by
    have hm := mul_le_mul_of_nonneg_left hH (mul_nonneg hη hL)
    nlinarith
  have hh' := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (14 / (3 * n)) * η ^ 2 by positivity)
  have hid : (14 / (3 * n)) * η ^ 2 * (n * H * M) = (14 / 3 : ℝ) * H * η ^ 2 * M := by
    field_simp [hn.ne']

  rw [hid] at hh'
  have hc : (4 + η * L + (14 / 3 : ℝ) * H) ≤ 10 * H := by linarith
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ η ^ 2 * M by positivity)
  have hbr := bregman_absorption hη hH hB hstep hb
  have hn' := mul_le_mul_of_nonneg_right hH (show 0 ≤ 2 * η ^ 2 * N by positivity)
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * η ^ 2 * L by positivity)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 22 * H * η ^ 2 by positivity)
  have hH' := mul_le_mul_of_nonneg_right hH (show 0 ≤ 4 * η ^ 2 * L * V by positivity)
  nlinarith

lemma initial_absorption {η L H w R0 D : ℝ}
    (hη : 0 ≤ η) (hL : 0 ≤ L) (hH : 1 ≤ H) (hw : 0 ≤ w) (hD : 0 ≤ D)
    (hstep : η * L * H ≤ 1 / 40) (hR : R0 ≤ L * D / 2) :
    w * D / 2 + 134 * H * η ^ 2 * L * w * R0 ≤ w * D := by
  have hH0 : 0 ≤ H := by linarith
  have hsmall : η * L ≤ 1 / 40 := by
    have hm := mul_le_mul_of_nonneg_left hH (mul_nonneg hη hL)
    nlinarith
  have hs : η ^ 2 * L ^ 2 * H ≤ 1 / 1600 := by
    have hh := mul_le_mul hsmall hstep (show 0 ≤ η * L * H by positivity)
      (by norm_num : (0 : ℝ) ≤ 1 / 40)
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right hs (show 0 ≤ 134 * w * D / 2 by positivity)
  have hr := mul_le_mul_of_nonneg_left hR (show 0 ≤ 134 * H * η ^ 2 * L * w by positivity)
  nlinarith

lemma terminal_absorption {η L H HT G D R0 w0 wlast RT S V0 W : ℝ}
    (hη : 0 < η) (hL : 0 ≤ L) (hH : 1 ≤ H) (hHT : 1 ≤ HT)
    (hw : 0 ≤ w0) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hstep : η * L * H * HT ≤ 1 / 536) (hR : R0 ≤ L * D / 2)
    (hlower : wlast * RT + S / (2 * HT) ≤ G)
    (hupper : η * G ≤ w0 * D / 2 + 134 * H * η ^ 2 * L * (w0 * R0 + S) +
      33 * H * η ^ 2 * V0 * W) :
    η * wlast * RT ≤ w0 * D + 33 * H * η ^ 2 * V0 * W := by
  have hH0 : 0 ≤ H := by linarith
  have hHT0 : 0 < HT := by linarith
  have hs : η * L * H ≤ 1 / 40 := by
    have hm := mul_le_mul_of_nonneg_left hHT (show 0 ≤ η * L * H by positivity)
    nlinarith
  have hi := initial_absorption hη.le hL hH hw hD hs hR
  have hc : 134 * H * η ^ 2 * L ≤ η / (2 * HT) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * HT)).mpr
    have hm := mul_le_mul_of_nonneg_right hstep hη.le
    nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc hS
  have hlo := mul_le_mul_of_nonneg_left hlower hη.le
  have hid : η / (2 * HT) * S = η * (S / (2 * HT)) := by ring
  rw [hid] at hc'
  nlinarith

lemma rate_extraction {T : ℕ} (hT : 0 < T) {η Hn D V0 RT : ℝ}
    (hη : 0 < η) (hH : 0 ≤ Hn) (hV : 0 ≤ V0) (hR : 0 ≤ RT)
    (hfinal : η * weight T (T - 1) * RT ≤ weight T 0 * D +
      33 * Hn * η ^ 2 * V0 * ∑ t ∈ range T, weight T t) :
    RT ≤ 2 * D / (η * T) + 66 * η * Hn * H T * V0 := by
  have hHT := H_pos hT
  have hw := weight_sum_le T
  have hw' := mul_le_mul_of_nonneg_left hw (show 0 ≤ 33 * Hn * η ^ 2 * V0 by positivity)
  rw [weight_initial, weight_terminal hT] at hfinal
  have he : (η * H T) * (2 * D / (η * T) + 66 * η * Hn * H T * V0) =
      (2 * H T / T) * D + 66 * Hn * η ^ 2 * V0 * H T ^ 2 := by
    field_simp [hη.ne', (Nat.cast_pos.mpr hT : (0 : ℝ) < T).ne']

  apply le_of_mul_le_mul_left (a := η * H T) _ (mul_pos hη hHT)
  rw [he]
  have hr := mul_nonneg hη.le hR
  nlinarith

lemma weighted_progress_lower {T : ℕ} (hT : 0 < T) (R Φ : ℕ → ℝ)
    (hR : ∀ t, t ≤ T → 0 ≤ R t)
    (hanchor : (∑ t ∈ range T, weight T t * Φ t) ≤
      ∑ t ∈ range T, (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) * R (t + 1)) :
    weight T (T - 1) * R T + (∑ t ∈ range (T - 1), weight T t * R (t + 1)) / (2 * H T) ≤
      ∑ t ∈ range T, weight T t * (R (t + 1) - Φ t) := by
  have hslack : (∑ t ∈ range (T - 1), weight T t * R (t + 1)) / (2 * H T) ≤
      ∑ t ∈ range (T - 1),
        (weight T t - (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t)) * R (t + 1) := by
    calc
      _ = ∑ t ∈ range (T - 1), (weight T t / (2 * H T)) * R (t + 1) := by
        simp only [div_mul_eq_mul_div, ← sum_div]
      _ ≤ _ := by
        apply sum_le_sum
        intro t ht
        have ht' := mem_range.mp ht
        exact mul_le_mul_of_nonneg_right (weight_slack (by omega)) (hR _ (by omega))
  have hid : weight T (T - 1) * R T +
      (∑ t ∈ range (T - 1),
        (weight T t - (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t)) * R (t + 1)) =
      (∑ t ∈ range T, weight T t * R (t + 1)) -
        ∑ t ∈ range T, (T - (t + 1) : ℕ) * (weight T (t + 1) - weight T t) * R (t + 1) := by
    cases T with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [sum_range_succ, sum_range_succ]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_mul, sum_sub_distrib]
      ring
  simp only [mul_sub, sum_sub_distrib]
  linarith

lemma previous_eq (T t : ℕ) : previous (weight T) t =
    if t = 0 then V (H T) T else V (H T) (T + 1 - t) := by
  unfold previous weight
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ite_eq_right ht]
    congr 1
    omega

lemma history_previous {n K : ℕ} (hn : 0 < n) (hK : 0 < K) (M : ℕ → ℝ)
    (hM : ∀ t, t < n * K → 0 ≤ M t) :
    (∑ t ∈ range (n * K), previous (weight (n * K)) t * history n M t) ≤
      n * H n * ∑ t ∈ range (n * K), previous (weight (n * K)) t * M t := by
  simpa only [previous_eq] using weighted_history_shifted (H_nonneg (n * K)) hn hK M hM

end OracleTemplate.ReshuffledHarmonicRate
