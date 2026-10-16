import LongTails.Proofs.LinearDecaySgdWeights

open Finset
open OracleTemplate.SampledConvex (step tail step_pos step_le tail_pos tail_nonneg tail_succ tail_last
  tail_zero ratio_le ratio_sum)

namespace OracleTemplate.SampledComposite

noncomputable def pcharge (L η : ℝ) (T k : ℕ) : ℝ :=
  2 * L * step η T k ^ 2 * (1 + 2 * L * step η T k)

noncomputable def pweight (L η : ℝ) (T : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pweight L η T k * tail η T k / (tail η T (k + 1) + pcharge L η T (k + 1))

lemma pcharge_nonneg {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) (T k : ℕ) (hk : k ≤ T) :
    0 ≤ pcharge L η T k := by
  have hs : 0 ≤ step η T k := by
    unfold step
    have hk' : (k : ℝ) ≤ T := by exact_mod_cast hk
    apply div_nonneg (mul_nonneg hη (by linarith)) (Nat.cast_nonneg _)
  unfold pcharge
  positivity

lemma pcharge_le {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T k : ℕ}
    (hk : k < T) : pcharge L η T k ≤ (5 / 16) * step η T k := by
  have hs := step_pos hη hk
  have hsl := step_le hη.le hk
  have hLs : L * step η T k ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hsl hL) hLη
  unfold pcharge
  have h1 : 2 * L * step η T k ^ 2 * (1 + 2 * L * step η T k) =
      step η T k * (2 * (L * step η T k) * (1 + 2 * (L * step η T k))) := by ring
  rw [h1, mul_comm (5 / 16 : ℝ)]
  have : 0 ≤ L * step η T k := mul_nonneg hL hs.le
  have h2 : 2 * (L * step η T k) * (1 + 2 * (L * step η T k)) ≤ 5 / 16 := by nlinarith
  exact mul_le_mul_of_nonneg_left h2 hs.le

lemma pcharge_sum {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ} (m : ℕ)
    (hm : m ≤ T) : ∑ k ∈ range m, pcharge L η T k / tail η T k ≤ 5 / 8 := by
  have hb : ∀ k ∈ range m, pcharge L η T k / tail η T k ≤
      (5 / 2 * L) * (step η T k ^ 2 / tail η T k) := by
    intro k hk
    have hkT := lt_of_lt_of_le (mem_range.mp hk) hm
    have ht := tail_pos hη hkT
    have hs := step_le hη.le hkT
    have hsp := step_pos hη hkT
    have hLs : L * step η T k ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hs hL) hLη
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right ht]
    unfold pcharge
    have : 0 ≤ L * step η T k := mul_nonneg hL hsp.le
    nlinarith [mul_nonneg hL (sq_nonneg (step η T k))]
  calc ∑ k ∈ range m, pcharge L η T k / tail η T k ≤
        ∑ k ∈ range m, (5 / 2 * L) * (step η T k ^ 2 / tail η T k) := sum_le_sum hb
    _ = (5 / 2 * L) * ∑ k ∈ range m, step η T k ^ 2 / tail η T k := by rw [mul_sum]
    _ ≤ (5 / 2 * L) * (2 * η) := mul_le_mul_of_nonneg_left (ratio_sum hη m hm) (by positivity)
    _ ≤ 5 / 8 := by nlinarith

lemma pweight_identity {L η : ℝ} {T k : ℕ} (hL : 0 ≤ L) (hη : 0 < η) (hk : k + 1 < T) :
    pweight L η T (k + 1) * (tail η T (k + 1) + pcharge L η T (k + 1)) =
      pweight L η T k * tail η T k := by
  have hpos : 0 < tail η T (k + 1) + pcharge L η T (k + 1) :=
    add_pos_of_pos_of_nonneg (tail_pos hη hk) (pcharge_nonneg hL hη.le T (k + 1) hk.le)
  simp only [pweight]
  field_simp

lemma pweight_bounds {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ} :
    ∀ k, k < T → 0 < pweight L η T k ∧
      pweight L η T k * tail η T k ≤ tail η T 0 ∧
      tail η T 0 * (1 - ∑ j ∈ range k, pcharge L η T (j + 1) / tail η T (j + 1)) ≤
        pweight L η T k * tail η T k := by
  intro k
  induction k with
  | zero =>
    intro hT
    simp only [pweight, one_mul, range_zero, sum_empty, sub_zero, mul_one]
    exact ⟨one_pos, le_rfl, le_rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hv, hup, hlow⟩ := ih (lt_trans (Nat.lt_succ_self k) hk)
    have ht := tail_pos hη hk
    have ht0 := tail_pos hη (lt_trans (Nat.lt_succ_self k) hk)
    have hc := pcharge_nonneg hL hη.le T (k + 1) hk.le
    have hid := pweight_identity hL hη hk
    have hden : 0 < tail η T (k + 1) + pcharge L η T (k + 1) := add_pos_of_pos_of_nonneg ht hc
    have hv' : 0 < pweight L η T (k + 1) := by
      simp only [pweight]
      exact div_pos (mul_pos hv ht0) hden
    refine ⟨hv', ?_, ?_⟩
    · have : pweight L η T (k + 1) * tail η T (k + 1) ≤
          pweight L η T (k + 1) * (tail η T (k + 1) + pcharge L η T (k + 1)) := by nlinarith
      linarith
    · rw [sum_range_succ]
      have hrat : pweight L η T (k + 1) * tail η T (k + 1) =
          pweight L η T k * tail η T k * (tail η T (k + 1) /
            (tail η T (k + 1) + pcharge L η T (k + 1))) := by
        rw [← hid]
        field_simp
      have hsplit : tail η T (k + 1) / (tail η T (k + 1) + pcharge L η T (k + 1)) =
          1 - pcharge L η T (k + 1) / (tail η T (k + 1) + pcharge L η T (k + 1)) := by
        field_simp
        ring
      have hmono : pcharge L η T (k + 1) / (tail η T (k + 1) + pcharge L η T (k + 1)) ≤
          pcharge L η T (k + 1) / tail η T (k + 1) :=
        div_le_div_of_nonneg_left hc ht (by linarith)
      have hcle : pcharge L η T (k + 1) ≤ tail η T (k + 1) := by
        have h1 := pcharge_le hL hη hLη hk
        have h2 := tail_succ η T (k + 1) (lt_of_le_of_lt (Nat.zero_le _) hk)
        have h3 := tail_nonneg (η := η) (T := T) (k := k + 1 + 1) hη.le (Nat.succ_le_of_lt hk)
        have h4 := step_pos hη hk
        linarith
      have hq : 0 ≤ 1 - pcharge L η T (k + 1) / tail η T (k + 1) := by
        rw [sub_nonneg, div_le_one ht]
        exact hcle
      have hwt : 0 ≤ pweight L η T k * tail η T k := (mul_pos hv ht0).le
      have hS0 : 0 ≤ tail η T 0 := tail_nonneg hη.le (Nat.zero_le _)
      have hs0 : 0 ≤ ∑ j ∈ range k, pcharge L η T (j + 1) / tail η T (j + 1) :=
        sum_nonneg (fun j hj => div_nonneg (pcharge_nonneg hL hη.le T (j + 1)
          (by have := mem_range.mp hj; omega)) (tail_nonneg hη.le (by have := mem_range.mp hj; omega)))
      have hr0 : 0 ≤ pcharge L η T (k + 1) / tail η T (k + 1) := div_nonneg hc ht.le
      have hstep := mul_le_mul_of_nonneg_right hlow hq
      rw [hrat, hsplit]
      set s := ∑ j ∈ range k, pcharge L η T (j + 1) / tail η T (j + 1)
      set r := pcharge L η T (k + 1) / tail η T (k + 1)
      set r' := pcharge L η T (k + 1) / (tail η T (k + 1) + pcharge L η T (k + 1))
      have h5 : pweight L η T k * tail η T k * (1 - r) ≤ pweight L η T k * tail η T k * (1 - r') :=
        mul_le_mul_of_nonneg_left (by linarith) hwt
      nlinarith [mul_nonneg hS0 (mul_nonneg hs0 hr0)]

lemma pweight_mono {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T k : ℕ}
    (hk : k + 1 < T) : pweight L η T k ≤ pweight L η T (k + 1) := by
  obtain ⟨hv, -, -⟩ := pweight_bounds hL hη hLη k (Nat.lt_of_succ_lt hk)
  have hid := pweight_identity hL hη hk
  have ht := tail_pos hη hk
  have hc := pcharge_nonneg hL hη.le T (k + 1) hk.le
  have h1 := pcharge_le hL hη hLη hk
  have h2 := tail_succ η T k (lt_of_le_of_lt (Nat.zero_le _) hk)
  have h3 := step_pos hη (Nat.lt_of_succ_lt hk)
  have h4 : step η T (k + 1) ≤ step η T k := by
    have hT : (0 : ℝ) < T := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hk)
    unfold step
    apply div_le_div_of_nonneg_right _ hT.le
    push_cast
    nlinarith
  have hle : tail η T (k + 1) + pcharge L η T (k + 1) ≤ tail η T k := by linarith
  have hv' : 0 < pweight L η T (k + 1) := by
    simp only [pweight]
    exact div_pos (mul_pos hv (tail_pos hη (Nat.lt_of_succ_lt hk))) (by positivity)
  nlinarith

lemma ppotential_recursion {L η σ : ℝ} (hL : 0 ≤ L) (hη : 0 < η) {T : ℕ} (A Φ d e : ℕ → ℝ)
    (hH : ∀ k, k < T → step η T k * pweight L η T k * (A (k + 1) - Φ k) ≤
      pweight L η T k / 2 * (d k - e k) + pweight L η T k * pcharge L η T k * A k +
        step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2)
    (hJ : ∀ k, k + 1 < T → pweight L η T (k + 1) * Φ (k + 1) ≤
      pweight L η T k * Φ k + (pweight L η T (k + 1) - pweight L η T k) * A (k + 1))
    (hD : ∀ k, k + 1 < T → pweight L η T (k + 1) * d (k + 1) ≤ pweight L η T k * e k) :
    ∀ m, m < T →
      pweight L η T m * tail η T m * Φ m + pweight L η T m * pcharge L η T m * A m +
        pweight L η T m / 2 * d m ≤
      pweight L η T 0 * tail η T 0 * Φ 0 + pweight L η T 0 * pcharge L η T 0 * A 0 +
        pweight L η T 0 / 2 * d 0 +
        ∑ k ∈ range m, step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hprev := ih (Nat.lt_of_succ_lt hm)
    have hid := pweight_identity hL hη hm
    have hts := tail_succ η T m (lt_of_le_of_lt (Nat.zero_le _) hm)
    have hH' := hH m (Nat.lt_of_succ_lt hm)
    have hJ' := hJ m hm
    have hD' := hD m hm
    have htn : 0 ≤ tail η T (m + 1) := (tail_pos hη hm).le
    have hJs := mul_le_mul_of_nonneg_left hJ' htn
    rw [sum_range_succ]
    linear_combination hJs + (1 / 2 : ℝ) * hD' + hH' + hprev + A (m + 1) * hid +
      (pweight L η T m * A (m + 1) - pweight L η T m * Φ m) * hts

set_option maxHeartbeats 1000000 in
lemma ppotential_bound {L η σ D Δ : ℝ} (hL : 0 ≤ L) (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ}
    (hT : 0 < T) (A Φ d e : ℕ → ℝ)
    (hH : ∀ k, k < T → step η T k * pweight L η T k * (A (k + 1) - Φ k) ≤
      pweight L η T k / 2 * (d k - e k) + pweight L η T k * pcharge L η T k * A k +
        step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2)
    (hJ : ∀ k, k + 1 < T → pweight L η T (k + 1) * Φ (k + 1) ≤
      pweight L η T k * Φ k + (pweight L η T (k + 1) - pweight L η T k) * A (k + 1))
    (hD : ∀ k, k + 1 < T → pweight L η T (k + 1) * d (k + 1) ≤ pweight L η T k * e k)
    (he : ∀ k, k < T → 0 ≤ e k) (hΦ0 : Φ 0 = 0) (hd0 : d 0 ≤ D ^ 2) (hΔ : 0 ≤ Δ)
    (hA0 : A 0 ≤ Δ) :
    A T ≤ 3 * D ^ 2 / (η * T) + 7 * η * σ ^ 2 + 2 * Δ / T := by
  have hT1 : T - 1 < T := Nat.sub_lt hT one_pos
  have hrec := ppotential_recursion hL hη A Φ d e hH hJ hD (T - 1) hT1
  have hlast := hH (T - 1) hT1
  have hsucc : T - 1 + 1 = T := Nat.sub_add_cancel hT
  rw [hsucc] at hlast
  have htl := tail_last (η := η) hT
  have he' := he (T - 1) hT1
  obtain ⟨hvpos, -, hvlow⟩ := pweight_bounds hL hη hLη (T - 1) hT1
  have hS0 : tail η T 0 = η * ((T : ℝ) + 1) / 2 := tail_zero hT
  have hS0pos : 0 < tail η T 0 := tail_pos hη hT
  have hw0 : pweight L η T 0 = 1 := rfl
  have hall : ∑ k ∈ range T, step η T k ^ 2 / tail η T k ≤ 2 * η := ratio_sum hη T le_rfl
  have hfull : ∑ k ∈ range (T - 1), step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2 +
      step η T (T - 1) ^ 2 * pweight L η T (T - 1) * (1 + 2 * L * step η T (T - 1)) * σ ^ 2 ≤
      tail η T 0 * (5 / 2 * η) * σ ^ 2 := by
    have hb : ∀ k ∈ range T, step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2 ≤
        tail η T 0 * (5 / 4) * σ ^ 2 * (step η T k ^ 2 / tail η T k) := by
      intro k hk
      have hkT : k < T := mem_range.mp hk
      obtain ⟨hv, hvup, -⟩ := pweight_bounds hL hη hLη k hkT
      have ht := tail_pos hη hkT
      have hs := step_le hη.le hkT
      have hsp := step_pos hη hkT
      have hLs : L * step η T k ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left hs hL) hLη
      have hvle : pweight L η T k ≤ tail η T 0 / tail η T k := by
        rw [le_div_iff₀ ht]; exact hvup
      have h1 : pweight L η T k * (1 + 2 * L * step η T k) ≤ tail η T 0 / tail η T k * (5 / 4) :=
        mul_le_mul hvle (by linarith) (by nlinarith [mul_nonneg hL hsp.le]) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg (step η T k)) (sq_nonneg σ))
      have h4 : tail η T 0 * (5 / 4) * σ ^ 2 * (step η T k ^ 2 / tail η T k) =
          step η T k ^ 2 * σ ^ 2 * (tail η T 0 / tail η T k * (5 / 4)) := by
        field_simp
      rw [h4]
      nlinarith [h2]
    have hs1 := sum_le_sum hb
    rw [← mul_sum] at hs1
    have hrs := sum_range_succ (fun k => step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) *
      σ ^ 2) (T - 1)
    rw [hsucc] at hrs
    rw [← hrs]
    calc _ ≤ _ := hs1
      _ ≤ tail η T 0 * (5 / 4) * σ ^ 2 * (2 * η) :=
          mul_le_mul_of_nonneg_left hall (by positivity)
      _ = _ := by ring
  have hchargesum : ∑ j ∈ range (T - 1), pcharge L η T (j + 1) / tail η T (j + 1) ≤ 5 / 8 := by
    have h := pcharge_sum hL hη hLη T le_rfl
    have hsh := sum_range_succ' (fun k => pcharge L η T k / tail η T k) (T - 1)
    rw [hsucc] at hsh
    have h0 : 0 ≤ pcharge L η T 0 / tail η T 0 :=
      div_nonneg (pcharge_nonneg hL hη.le T 0 (Nat.zero_le _)) hS0pos.le
    linarith
  have hlowv : tail η T 0 * (3 / 8) ≤ pweight L η T (T - 1) * tail η T (T - 1) := by
    have := mul_le_mul_of_nonneg_left (show (3 / 8 : ℝ) ≤ 1 - ∑ j ∈ range (T - 1),
      pcharge L η T (j + 1) / tail η T (j + 1) by linarith) hS0pos.le
    linarith
  have hc0 : pcharge L η T 0 ≤ 5 / 2 * L * η ^ 2 := by
    have hs0 : step η T 0 = η := by
      have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      simp only [step, Nat.cast_zero, sub_zero]; field_simp
    unfold pcharge
    rw [hs0]
    have hLη0 : 0 ≤ L * η := mul_nonneg hL hη.le
    nlinarith [mul_nonneg hLη0 (sq_nonneg η)]
  have hc0n : 0 ≤ pcharge L η T 0 := pcharge_nonneg hL hη.le T 0 (Nat.zero_le _)
  have hA0c : pcharge L η T 0 * A 0 ≤ 5 / 2 * L * η ^ 2 * Δ := by
    have h1 := mul_le_mul_of_nonneg_left hA0 hc0n
    have h2 := mul_le_mul_of_nonneg_right hc0 hΔ
    linarith
  rw [htl] at hlowv
  have hkey : step η T (T - 1) * pweight L η T (T - 1) * A T ≤
      5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2 + tail η T 0 * (5 / 2 * η) * σ ^ 2 := by
    rw [htl] at hrec
    rw [hΦ0, hw0] at hrec
    have hwe : 0 ≤ pweight L η T (T - 1) / 2 * e (T - 1) := mul_nonneg (by positivity) he'
    linear_combination hlast + hrec + hfull + hA0c + (1 / 2 : ℝ) * hd0 + hwe
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hS0ge : η * T / 2 ≤ tail η T 0 := by
    rw [hS0]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hη.le) (by norm_num)
  have hpos : 0 < step η T (T - 1) * pweight L η T (T - 1) := by
    rw [← htl]; exact mul_pos (tail_pos hη hT1) hvpos
  have hX : 0 ≤ 5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2 + tail η T 0 * (5 / 2 * η) * σ ^ 2 := by positivity
  have hAT : A T ≤ (5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2 + tail η T 0 * (5 / 2 * η) * σ ^ 2) /
      (tail η T 0 * (3 / 8)) := by
    rw [le_div_iff₀ (by positivity)]
    rcases le_or_gt (A T) 0 with h | h
    · have : A T * (tail η T 0 * (3 / 8)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (by positivity)
      linarith
    · have h1 := mul_le_mul_of_nonneg_left hlowv h.le
      have h2 : A T * (pweight L η T (T - 1) * step η T (T - 1)) =
          step η T (T - 1) * pweight L η T (T - 1) * A T := by ring
      linarith
  have hLη' : L * η ≤ 1 / 8 := hLη
  calc A T ≤ _ := hAT
    _ = (8 / 3) * ((5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2) / tail η T 0) + (20 / 3) * η * σ ^ 2 := by
        field_simp
        ring
    _ ≤ (8 / 3) * ((5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2) / (η * T / 2)) + (20 / 3) * η * σ ^ 2 := by
        have hq : (5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2) / tail η T 0 ≤
            (5 / 2 * L * η ^ 2 * Δ + D ^ 2 / 2) / (η * T / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hS0ge
        linarith
    _ = (40 / 3) * (L * η) * Δ / T + (8 / 3) * D ^ 2 / (η * T) + (20 / 3) * η * σ ^ 2 := by
        field_simp
        ring
    _ ≤ 3 * D ^ 2 / (η * T) + 7 * η * σ ^ 2 + 2 * Δ / T := by
        have h1 : (40 / 3) * (L * η) * Δ / T ≤ 2 * Δ / T := by
          apply div_le_div_of_nonneg_right _ hTr.le
          nlinarith [mul_nonneg hL hη.le]
        have h2 : (8 / 3) * D ^ 2 / (η * T) ≤ 3 * D ^ 2 / (η * T) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [sq_nonneg D]
        have h3 : (20 / 3) * η * σ ^ 2 ≤ 7 * η * σ ^ 2 := by nlinarith [sq_nonneg σ]
        linarith

lemma ptuning_bound {L R σ Δ ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    {T : ℕ} (hT : 72 * L * R ^ 2 / ε + 900 * σ ^ 2 * R ^ 2 / ε ^ 2 + 6 * Δ / ε ≤ T) :
    0 < R / (8 * L * R + σ * Real.sqrt T) ∧ L * (R / (8 * L * R + σ * Real.sqrt T)) ≤ 1 / 8 ∧
      3 * R ^ 2 / (R / (8 * L * R + σ * Real.sqrt T) * T) +
        7 * (R / (8 * L * R + σ * Real.sqrt T)) * σ ^ 2 + 2 * Δ / T ≤ ε := by
  have hA : 0 < 72 * L * R ^ 2 / ε := by positivity
  have hB : 0 ≤ 900 * σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hC : 0 ≤ 6 * Δ / ε := by positivity
  have hTpos : (0 : ℝ) < T := by linarith
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hss : Real.sqrt T ^ 2 = T := Real.sq_sqrt hTpos.le
  set q := Real.sqrt (T : ℝ)
  have hD : 0 < 8 * L * R + σ * q := by positivity
  set η := R / (8 * L * R + σ * q)
  have hη : 0 < η := div_pos hR hD
  refine ⟨hη, ?_, ?_⟩
  · rw [show L * η = L * R / (8 * L * R + σ * q) by simp only [η]; ring, div_le_iff₀ hD]
    nlinarith [mul_nonneg hσ hsq.le]
  · have h1 : 3 * R ^ 2 / (η * T) = 24 * L * R ^ 2 / T + 3 * σ * R / q := by
      simp only [η]
      rw [← hss]
      field_simp
      ring
    have h2 : 7 * η * σ ^ 2 ≤ 7 * σ * R / q := by
      have hk : R / (8 * L * R + σ * q) * σ ≤ R / q := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hD hsq]
        nlinarith [mul_pos (mul_pos hL hR) hR]
      calc 7 * η * σ ^ 2 = 7 * σ * (R / (8 * L * R + σ * q) * σ) := by simp only [η]; ring
        _ ≤ 7 * σ * (R / q) := mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 7 * σ * R / q := by ring
    have h3 : 24 * L * R ^ 2 / T ≤ ε / 3 := by
      rw [div_le_iff₀ hTpos]
      have : 72 * L * R ^ 2 ≤ ε * T := by
        have hle : 72 * L * R ^ 2 / ε ≤ T := by linarith
        have := mul_le_mul_of_nonneg_left hle hε.le
        rwa [mul_div_cancel₀ _ hε.ne'] at this
      linarith
    have h4 : 10 * σ * R / q ≤ ε / 3 := by
      rw [div_le_iff₀ hsq]
      have hT2 : 900 * σ ^ 2 * R ^ 2 ≤ ε ^ 2 * T := by
        have hle : 900 * σ ^ 2 * R ^ 2 / ε ^ 2 ≤ T := by linarith
        have := mul_le_mul_of_nonneg_left hle (sq_nonneg ε)
        rwa [mul_div_cancel₀ _ (pow_ne_zero 2 hε.ne')] at this
      rw [← hss] at hT2
      have h5 : 30 * σ * R ≤ ε * q := by
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp
          (by nlinarith [hT2])
      linarith
    have h6 : 2 * Δ / T ≤ ε / 3 := by
      rw [div_le_iff₀ hTpos]
      have : 6 * Δ ≤ ε * T := by
        have hle : 6 * Δ / ε ≤ T := by linarith
        have := mul_le_mul_of_nonneg_left hle hε.le
        rwa [mul_div_cancel₀ _ hε.ne'] at this
      linarith
    have h7 : 3 * σ * R / q + 7 * σ * R / q = 10 * σ * R / q := by ring
    linarith

end OracleTemplate.SampledComposite
