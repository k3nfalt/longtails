import LongTails.Proofs.HiddenConvexRun
import LongTails.Proofs.MomentumLastIterateRecursion

open Set Metric InnerProductSpace MeasureTheory Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.LocalHiddenConvex

lemma sum_inv_sq_le (K : ℕ) : ∑ j ∈ range K, 1 / ((j : ℝ) + 2) ^ 2 ≤ 1 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h : 1 / ((K : ℝ) + 2) ^ 2 ≤ 1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 2) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    have e : (K : ℝ) + 1 + 1 = (K : ℝ) + 2 := by ring
    rw [e]
    linarith

lemma noise_term_le {L σ R : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) (hR : 0 < R) (j : ℕ) :
    ((j : ℝ) + 1) ^ 2 / (2 * stepScale L σ R j) * σ ^ 2 ≤ σ * R * Real.sqrt ((j : ℝ) + 1) / 2 := by
  have hD := stepScale_pos hL hσ hR j
  have hs := Real.sqrt_nonneg ((j : ℝ) + 1)
  have hss : Real.sqrt ((j : ℝ) + 1) ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hDge : σ * ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1) ≤ R * stepScale L σ R j := by
    have e : R * stepScale L σ R j = R * (4 * L) + σ * ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1) := by
      unfold stepScale; field_simp
    rw [e]
    nlinarith [mul_pos hR hL]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  have key : ((j : ℝ) + 1) ^ 2 * σ ^ 2 ≤ σ * Real.sqrt ((j : ℝ) + 1) * (R * stepScale L σ R j) := by
    have h1 := mul_le_mul_of_nonneg_left hDge (mul_nonneg hσ hs)
    have e : σ * Real.sqrt ((j : ℝ) + 1) * (σ * ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1)) =
        ((j : ℝ) + 1) ^ 2 * σ ^ 2 := by
      have : σ * Real.sqrt ((j : ℝ) + 1) * (σ * ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1)) =
          σ ^ 2 * ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1) ^ 2 := by ring
      rw [this, hss]; ring
    linarith
  nlinarith

lemma stepCost_sum_le {L σ R M : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) (hR : 0 < R) (hM : 0 ≤ M)
    (K : ℕ) :
    ∑ j ∈ range K, stepCost L σ R M j ≤
      σ * R * (K : ℝ) * Real.sqrt K / 2 +
        stepScale L σ R K * (192 * M * R ^ 3 * Real.log ((K : ℝ) + 1) + 13312 * M ^ 2 * R ^ 4) +
        (stepScale L σ R K - stepScale L σ R 0) * (171 / 32 * R ^ 2) := by
  unfold stepCost
  rw [sum_add_distrib, sum_add_distrib]
  rw [show ∑ x ∈ range K, (stepScale L σ R (x + 1) - stepScale L σ R x) * (171 / 32 * R ^ 2) =
      (stepScale L σ R K - stepScale L σ R 0) * (171 / 32 * R ^ 2) by
    rw [← sum_mul, sum_range_sub (fun j => stepScale L σ R j) K]]
  have hDK : ∀ j ∈ range K, stepScale L σ R j ≤ stepScale L σ R K :=
    fun j hj => stepScale_mono hσ hR (mem_range.mp hj).le
  have h1 : ∑ j ∈ range K, ((j : ℝ) + 1) ^ 2 / (2 * stepScale L σ R j) * σ ^ 2 ≤
      σ * R * (K : ℝ) * Real.sqrt K / 2 := by
    calc ∑ j ∈ range K, ((j : ℝ) + 1) ^ 2 / (2 * stepScale L σ R j) * σ ^ 2
        ≤ ∑ j ∈ range K, σ * R * Real.sqrt K / 2 := by
          apply sum_le_sum
          intro j hj
          have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast mem_range.mp hj
          calc _ ≤ σ * R * Real.sqrt ((j : ℝ) + 1) / 2 := noise_term_le hL hσ hR j
            _ ≤ σ * R * Real.sqrt K / 2 := by
              have := Real.sqrt_le_sqrt hjK
              have : 0 ≤ σ * R := by positivity
              gcongr
      _ = σ * R * (K : ℝ) * Real.sqrt K / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have h2 : ∑ j ∈ range K, (96 * stepScale L σ R j * M * R ^ 3 * (2 / ((j : ℝ) + 3)) +
      3328 * stepScale L σ R j * M ^ 2 * R ^ 4 * (2 / ((j : ℝ) + 2)) ^ 2) ≤
      stepScale L σ R K * (192 * M * R ^ 3 * Real.log ((K : ℝ) + 1) + 13312 * M ^ 2 * R ^ 4) := by
    have hlog := MomentumConvex.sum_inv_le_log K
    have hsq := sum_inv_sq_le K
    have hpos : 0 ≤ 1 / ((K : ℝ) + 1) := by positivity
    calc ∑ j ∈ range K, (96 * stepScale L σ R j * M * R ^ 3 * (2 / ((j : ℝ) + 3)) +
          3328 * stepScale L σ R j * M ^ 2 * R ^ 4 * (2 / ((j : ℝ) + 2)) ^ 2)
        ≤ ∑ j ∈ range K, (192 * stepScale L σ R K * M * R ^ 3 * (1 / ((j : ℝ) + 2)) +
          13312 * stepScale L σ R K * M ^ 2 * R ^ 4 * (1 / ((j : ℝ) + 2) ^ 2)) := by
          apply sum_le_sum
          intro j hj
          have hD := hDK j hj
          have hD0 : 0 ≤ stepScale L σ R j := (stepScale_pos hL hσ hR j).le
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          have ha : 2 / ((j : ℝ) + 3) ≤ 2 * (1 / ((j : ℝ) + 2)) := by
            rw [mul_one_div]
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
          have hb : (2 / ((j : ℝ) + 2)) ^ 2 = 4 * (1 / ((j : ℝ) + 2) ^ 2) := by
            field_simp; ring
          have h1 : 96 * stepScale L σ R j * M * R ^ 3 * (2 / ((j : ℝ) + 3)) ≤
              192 * stepScale L σ R K * M * R ^ 3 * (1 / ((j : ℝ) + 2)) := by
            have e1 := mul_le_mul ha hD (by positivity) (by positivity)
            have e2 : 0 ≤ 96 * M * R ^ 3 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left e1 e2]
          have h2 : 3328 * stepScale L σ R j * M ^ 2 * R ^ 4 * (2 / ((j : ℝ) + 2)) ^ 2 ≤
              13312 * stepScale L σ R K * M ^ 2 * R ^ 4 * (1 / ((j : ℝ) + 2) ^ 2) := by
            rw [hb]
            have e2 : 0 ≤ M ^ 2 * R ^ 4 * (1 / ((j : ℝ) + 2) ^ 2) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hD e2]
          linarith
      _ = 192 * stepScale L σ R K * M * R ^ 3 * ∑ j ∈ range K, 1 / ((j : ℝ) + 2) +
          13312 * stepScale L σ R K * M ^ 2 * R ^ 4 * ∑ j ∈ range K, 1 / ((j : ℝ) + 2) ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ 192 * stepScale L σ R K * M * R ^ 3 * Real.log ((K : ℝ) + 1) +
          13312 * stepScale L σ R K * M ^ 2 * R ^ 4 * 1 := by
          have hDK0 : 0 ≤ stepScale L σ R K := (stepScale_pos hL hσ hR K).le
          gcongr
          linarith
      _ = _ := by ring
  linarith

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

lemma sqrt_le_add_one {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ≤ a + 1 := by
  have h1 := Real.sq_sqrt ha
  nlinarith [Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - 1)]

set_option maxHeartbeats 4000000 in
lemma budget_sufficient {L σ R ε : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) (hR : 0 < R) (hε : 0 < ε) :
    let K := ⌈300000 * (Real.sqrt (L * R ^ 2 / ε) + σ ^ 2 * R ^ 2 / ε ^ 2) *
      Real.log (300000 * (2 + L * R ^ 2 / ε + σ ^ 2 * R ^ 2 / ε ^ 2)) ^ 2⌉₊
    0 < K ∧
    4 * (stepScale L σ R K * R ^ 2 * (20 + 6 * Real.log ((K : ℝ) + 1)) +
      σ * R * (K : ℝ) * Real.sqrt K / 2) / ((K : ℝ) * ((K : ℝ) + 1)) ≤ ε := by
  intro K
  set a := L * R ^ 2 / ε with ha
  set b := σ ^ 2 * R ^ 2 / ε ^ 2 with hb
  set Q := 2 + a + b with hQ
  set ℓ := Real.log (300000 * Q) with hℓ
  set T := Real.sqrt a + b with hT
  have ha0 : 0 < a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hQ2 : 2 ≤ Q := by linarith
  have hT0 : 0 < T := by rw [hT]; have := Real.sqrt_pos.mpr ha0; linarith
  have hℓ1 : 1 ≤ ℓ := by
    have hx : 0 < 300000 * Q := by positivity
    have h := Real.one_sub_inv_le_log_of_pos (Real.sqrt_pos.mpr hx)
    rw [Real.log_sqrt hx.le] at h
    have h2 : (2 : ℝ) ≤ Real.sqrt (300000 * Q) := by
      rw [Real.le_sqrt (by norm_num) hx.le]; nlinarith
    have h3 : (Real.sqrt (300000 * Q))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    rw [hℓ]; linarith
  have hKge : 300000 * T * ℓ ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKle : (K : ℝ) < 300000 * T * ℓ ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hKpos : 0 < K := by
    have : 0 < 300000 * T * ℓ ^ 2 := by positivity
    exact_mod_cast this.trans_le hKge
  refine ⟨hKpos, ?_⟩
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  -- logarithm of the horizon
  have hTQ : T ≤ 2 * Q := by
    have := sqrt_le_add_one ha0.le
    rw [hT, hQ]; linarith
  have hℓsq : ℓ ^ 2 ≤ 4 * (300000 * Q) := by
    have h := log_le_two_sqrt (show 0 < 300000 * Q by positivity)
    have hs := Real.sq_sqrt (show 0 ≤ 300000 * Q by positivity)
    have h0 : 0 ≤ ℓ := by linarith
    calc ℓ ^ 2 ≤ (2 * Real.sqrt (300000 * Q)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 4 * (300000 * Q) := by rw [mul_pow, hs]; ring
  have hK1le : (K : ℝ) + 1 ≤ 9 * (300000 * Q) ^ 2 := by
    have h1 : 300000 * T * ℓ ^ 2 ≤ 300000 * (2 * Q) * (4 * (300000 * Q)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hTQ (by norm_num)) hℓsq (sq_nonneg _)
        (by positivity)
    have h2 : (2 : ℝ) ≤ (300000 * Q) ^ 2 := by nlinarith
    nlinarith
  have hlogK : Real.log ((K : ℝ) + 1) ≤ 3 * ℓ := by
    have h := Real.log_le_log (by positivity) hK1le
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    have h9 : Real.log 9 ≤ ℓ := Real.log_le_log (by norm_num) (by nlinarith)
    push_cast at h
    linarith
  set B := 20 + 6 * Real.log ((K : ℝ) + 1) with hB
  have hBle : B ≤ 38 * ℓ := by rw [hB]; linarith
  have hB2 : 2 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (K : ℝ) + 1 by linarith)
    rw [hB]; linarith
  -- square root of the horizon
  set s := Real.sqrt (K : ℝ) with hs
  have hss : s ^ 2 = K := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hK1
  have hs0 : 0 < s := by linarith
  have hsK1 : Real.sqrt ((K : ℝ) + 1) ≤ 3 / 2 * s := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [hss]
  -- deterministic term
  have hsa : Real.sqrt a ≤ T := by rw [hT]; linarith
  have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hK2 : 32 * a * B ≤ (K : ℝ) ^ 2 := by
    have h1 : (300000 * Real.sqrt a * ℓ ^ 2) ^ 2 ≤ (K : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsa (by norm_num))
        (sq_nonneg _)) hKge
    have h2 : (300000 * Real.sqrt a * ℓ ^ 2) ^ 2 = 90000000000 * a * ℓ ^ 4 := by
      rw [mul_pow, mul_pow, hsa2]; ring
    have h3 : 32 * a * B ≤ 32 * a * (38 * ℓ) := mul_le_mul_of_nonneg_left hBle (by positivity)
    have h4 : ℓ ≤ ℓ ^ 4 := by
      have : 1 ≤ ℓ ^ 3 := one_le_pow₀ hℓ1
      nlinarith
    have h5 : 32 * a * (38 * ℓ) ≤ 90000000000 * a * ℓ ^ 4 := by nlinarith
    linarith
  have hLR : L * R ^ 2 = a * ε := by rw [ha]; field_simp
  have hi : 16 * L * R ^ 2 * B ≤ ε / 2 * ((K : ℝ) * ((K : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hK2 (show 0 ≤ ε / 2 by positivity)
    have e : 16 * L * R ^ 2 * B = ε / 2 * (32 * a * B) := by rw [mul_assoc 16 L, hLR]; ring
    rw [e]
    nlinarith
  -- statistical term
  have hbK : 300000 * b * ℓ ^ 2 ≤ (K : ℝ) := by
    have : 300000 * b * ℓ ^ 2 ≤ 300000 * T * ℓ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have := Real.sqrt_nonneg a
      rw [hT]; linarith
    linarith
  have hσR : σ ^ 2 * R ^ 2 = b * ε ^ 2 := by rw [hb]; field_simp
  have hseps : 532 * σ * R * ℓ ≤ ε * s := by
    have h1 : (532 * σ * R * ℓ) ^ 2 ≤ (ε * s) ^ 2 := by
      have e1 : (ε * s) ^ 2 = ε ^ 2 * K := by rw [mul_pow, hss]
      have e2 : (532 * σ * R * ℓ) ^ 2 = 283024 * (b * ε ^ 2) * ℓ ^ 2 := by
        rw [← hσR]; ring
      rw [e1, e2]
      have h := mul_le_mul_of_nonneg_left hbK (show 0 ≤ ε ^ 2 by positivity)
      have hp : 0 ≤ b * ε ^ 2 * ℓ ^ 2 := by positivity
      calc 283024 * (b * ε ^ 2) * ℓ ^ 2 ≤ 300000 * (b * ε ^ 2) * ℓ ^ 2 := by
            have := mul_le_mul_of_nonneg_right (show (283024 : ℝ) ≤ 300000 by norm_num) hp
            linarith [show 283024 * (b * ε ^ 2) * ℓ ^ 2 = 283024 * (b * ε ^ 2 * ℓ ^ 2) by ring,
              show 300000 * (b * ε ^ 2) * ℓ ^ 2 = 300000 * (b * ε ^ 2 * ℓ ^ 2) by ring]
        _ = ε ^ 2 * (300000 * b * ℓ ^ 2) := by ring
        _ ≤ ε ^ 2 * K := h
    exact (pow_le_pow_iff_left₀ (by have := hℓ1; positivity) (by positivity) (by norm_num)).mp h1
  have hii : 4 * σ * R * ((K : ℝ) + 1) * Real.sqrt ((K : ℝ) + 1) * B + 2 * σ * R * (K : ℝ) * s ≤
      ε / 2 * ((K : ℝ) * ((K : ℝ) + 1)) := by
    have hσR0 : 0 ≤ σ * R := by positivity
    have h1 : 4 * σ * R * ((K : ℝ) + 1) * Real.sqrt ((K : ℝ) + 1) * B ≤
        6 * σ * R * ((K : ℝ) + 1) * s * B := by
      have := mul_le_mul_of_nonneg_left hsK1
        (show 0 ≤ 4 * σ * R * ((K : ℝ) + 1) * B by positivity)
      nlinarith
    have h2 : 2 * σ * R * (K : ℝ) * s ≤ σ * R * ((K : ℝ) + 1) * s * B := by
      have : 2 * (K : ℝ) ≤ ((K : ℝ) + 1) * B := by nlinarith
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ σ * R * s by positivity)
      nlinarith
    have h3 : 14 * σ * R * B ≤ ε * s := by
      have := mul_le_mul_of_nonneg_left hBle (show 0 ≤ 14 * σ * R by positivity)
      linarith
    have h4 : 7 * σ * R * ((K : ℝ) + 1) * s * B ≤ ε / 2 * ((K : ℝ) * ((K : ℝ) + 1)) := by
      have := mul_le_mul_of_nonneg_left h3 (show 0 ≤ ((K : ℝ) + 1) * s / 2 by positivity)
      have e : ε / 2 * ((K : ℝ) * ((K : ℝ) + 1)) = ((K : ℝ) + 1) * s / 2 * (ε * s) := by
        rw [← hss]; ring
      rw [e]
      nlinarith
    linarith
  -- assemble
  have hexp : 4 * (stepScale L σ R K * R ^ 2 * B + σ * R * (K : ℝ) * s / 2) =
      16 * L * R ^ 2 * B + (4 * σ * R * ((K : ℝ) + 1) * Real.sqrt ((K : ℝ) + 1) * B +
        2 * σ * R * (K : ℝ) * s) := by
    unfold stepScale
    field_simp
    ring
  rw [div_le_iff₀ (by positivity), hexp]
  linarith

end OracleTemplate.LocalHiddenConvex
