import LongTails.Proofs.StagewiseSarahTuning

open scoped BigOperators

namespace OracleTemplate.StagewiseSarah

variable {L Lbar μ σ Δ ε : ℝ}

lemma cost_append (l₁ l₂ : List Epoch) : cost (l₁ ++ l₂) = cost l₁ + cost l₂ := by
  induction l₁ with
  | nil => simp [cost]
  | cons e rest ih =>
    simp only [List.cons_append, cost, ih]
    omega

lemma cost_replicate (R : ℕ) (e : Epoch) : cost (List.replicate R e) = R * (e.B + e.m) := by
  induction R with
  | zero => simp [cost]
  | succ R ih =>
    rw [List.replicate_succ]
    simp only [cost, ih]
    ring

lemma cost_stages (L Lbar μ σ Δ : ℝ) (K : ℕ) :
    cost ((List.range K).flatMap (stage L Lbar μ σ Δ)) =
      ∑ j ∈ Finset.range K, cost (stage L Lbar μ σ Δ j) := by
  induction K with
  | zero => simp [cost]
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, cost_append, ih, Finset.sum_range_succ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

lemma batch_cast_le {b : ℝ} (hb : 0 ≤ b) : ((max 1 ⌈b⌉₊ : ℕ) : ℝ) ≤ 1 + b := by
  rw [Nat.cast_max]
  apply max_le
  · simp only [Nat.cast_one]
    linarith
  · have := Nat.ceil_lt_add_one hb
    linarith

lemma cost_real_G {κ Rc Bc b : ℝ} (hκ : 1 ≤ κ) (hR : Rc ≤ 6 * κ + 1)
    (hB : Bc ≤ 1 + b) (hB0 : 0 ≤ Bc) : Rc * Bc ≤ 7 * κ + 7 * κ * b := by
  have h1 : Rc ≤ 7 * κ := by linarith
  have h2 : Rc * Bc ≤ 7 * κ * Bc := mul_le_mul_of_nonneg_right h1 hB0
  have h3 : 7 * κ * Bc ≤ 7 * κ * (1 + b) := mul_le_mul_of_nonneg_left hB (by linarith)
  linarith

lemma cost_real_V {κ Bc r Rc q : ℝ} (hκ : 1 ≤ κ) (hq : 1 < q) (hB1 : 1 ≤ Bc)
    (hBb : Bc ≤ 1 + q ^ 2) (hr : 1 ≤ r) (hsB : r ^ 2 ≤ Bc)
    (hcase : r ^ 2 = Bc ∨ κ ^ 2 ≤ 2 * r ^ 2) (hR : Rc ≤ 6 * κ / r + 1) :
    Rc * (Bc + (r ^ 2 - 1)) ≤ 17 * κ * q + 40 * q ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hsum : Bc + (r ^ 2 - 1) ≤ 2 * Bc := by linarith
  have hsum0 : 0 ≤ Bc + (r ^ 2 - 1) := by nlinarith
  have h61 : 0 ≤ 6 * κ / r + 1 := by
    have : 0 ≤ 6 * κ / r := div_nonneg (by linarith) hr0.le
    linarith
  have h1 : Rc * (Bc + (r ^ 2 - 1)) ≤ (6 * κ / r + 1) * (2 * Bc) :=
    mul_le_mul hR hsum hsum0 h61
  have hq0 : 0 < q := by linarith
  have hκ0 : 0 < κ := by linarith
  have hrne : r ≠ 0 := hr0.ne'
  rcases hcase with hc | hc
  · have h2 : (6 * κ / r + 1) * (2 * Bc) = 12 * κ * r + 2 * r ^ 2 := by
      rw [← hc]
      have hdiv : 6 * κ / r * r = 6 * κ := div_mul_cancel₀ _ hrne
      calc (6 * κ / r + 1) * (2 * r ^ 2) = 2 * r * (6 * κ / r * r) + 2 * r ^ 2 := by ring
        _ = 12 * κ * r + 2 * r ^ 2 := by rw [hdiv]; ring
    have hr2 : r ^ 2 ≤ 2 * q ^ 2 := by linarith
    have hrq : r ≤ 17 / 12 * q := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos (sub_pos.mpr hcon)
        (add_pos hr0 (mul_pos (by norm_num : (0 : ℝ) < 17 / 12) hq0))]
    have h3 : 12 * κ * r ≤ 17 * κ * q := by
      nlinarith [mul_le_mul_of_nonneg_left hrq hκ0.le]
    linarith
  · have hκr : κ ≤ 3 / 2 * r := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos (sub_pos.mpr hcon)
        (add_pos hκ0 (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hr0))]
    have h2 : 6 * κ / r ≤ 9 := by
      rw [div_le_iff₀ hr0]
      linarith
    have h3 : (6 * κ / r + 1) * (2 * Bc) ≤ 10 * (2 * Bc) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hκq : 0 ≤ 17 * κ * q := mul_nonneg (mul_nonneg (by norm_num) hκ0.le) hq0.le
    linarith

lemma stageEpoch_of_lt {j : ℕ} (h : Lbar * √(stageBatch μ σ Δ j) < L * stageBatch μ σ Δ j) :
    stageEpoch L Lbar μ σ Δ j =
      ⟨max 1 ⌈stageBatch μ σ Δ j⌉₊,
        min (max 1 ⌈stageBatch μ σ Δ j⌉₊) ⌊(Lbar / μ) ^ 2⌋₊ - 1,
        1 / (2 * Lbar * √((min (max 1 ⌈stageBatch μ σ Δ j⌉₊) ⌊(Lbar / μ) ^ 2⌋₊ : ℕ) : ℝ))⟩ := by
  simp only [stageEpoch, h, ↓reduceIte]

lemma stageEpoch_of_not_lt {j : ℕ} (h : ¬ Lbar * √(stageBatch μ σ Δ j) < L * stageBatch μ σ Δ j) :
    stageEpoch L Lbar μ σ Δ j = ⟨max 1 ⌈stageBatch μ σ Δ j⌉₊, 0, 1 / (2 * L)⟩ := by
  simp only [stageEpoch, h, ↓reduceIte]

lemma cost_stage_le (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (j : ℕ)
    (hb : 0 ≤ stageBatch μ σ Δ j) :
    (cost (stage L Lbar μ σ Δ j) : ℝ) ≤
        7 * (L / μ) + 17 * (L / μ) * stageBatch μ σ Δ j + 40 * stageBatch μ σ Δ j ∧
      (cost (stage L Lbar μ σ Δ j) : ℝ) ≤
        7 * (L / μ) + 17 * (Lbar / μ) * √(stageBatch μ σ Δ j) + 40 * stageBatch μ σ Δ j := by
  have hL0 : 0 < L := lt_of_lt_of_le hμ hL
  have hLb0 : 0 < Lbar := lt_of_lt_of_le hL0 hLbar
  have hκ : 1 ≤ L / μ := by rwa [le_div_iff₀ hμ, one_mul]
  have hκb : 1 ≤ Lbar / μ := by
    rw [le_div_iff₀ hμ, one_mul]
    exact hL.trans hLbar
  set b := stageBatch μ σ Δ j with hbdef
  have hq0 : 0 ≤ √b := Real.sqrt_nonneg b
  have hqsq : √b ^ 2 = b := Real.sq_sqrt hb
  rw [stage, cost_replicate]
  push_cast
  have hRdef : stageRepeats L Lbar μ σ Δ j =
      ⌈3 / ((((stageEpoch L Lbar μ σ Δ j).m : ℝ) + 1) *
        ((stageEpoch L Lbar μ σ Δ j).η * μ))⌉₊ := rfl
  by_cases hbr : Lbar * √b < L * b
  · have he := stageEpoch_of_lt (μ := μ) (σ := σ) (Δ := Δ) (j := j) hbr
    set B := max 1 ⌈b⌉₊ with hBdef
    set F := ⌊(Lbar / μ) ^ 2⌋₊ with hFdef
    have hF1 : 1 ≤ F := floor_sq_pos hμ (hL.trans hLbar)
    have hB1 : 1 ≤ B := le_max_left _ _
    have hs1 : 1 ≤ min B F := le_min hB1 hF1
    have hsR : (1 : ℝ) ≤ ((min B F : ℕ) : ℝ) := by exact_mod_cast hs1
    set r := √((min B F : ℕ) : ℝ) with hrdef
    have hr1 : 1 ≤ r := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt hsR
    have hrsq : r ^ 2 = ((min B F : ℕ) : ℝ) := Real.sq_sqrt (by linarith)
    have hqpos : 0 < √b := by
      rcases hq0.eq_or_lt with h0 | h0
      · exfalso
        have hb0 : b = 0 := by rw [← hqsq, ← h0]; ring
        rw [← h0, hb0] at hbr
        simp at hbr
      · exact h0
    have hq1 : 1 < √b := by
      have h1 : Lbar * √b < L * (√b * √b) := by
        rw [← sq, hqsq]
        exact hbr
      have h2 : Lbar < L * √b := by
        by_contra hcon
        push Not at hcon
        nlinarith
      by_contra hcon
      push Not at hcon
      nlinarith
    have hBR : ((B : ℕ) : ℝ) ≤ 1 + √b ^ 2 := by
      rw [hqsq]
      exact batch_cast_le hb
    have hB1R : (1 : ℝ) ≤ ((B : ℕ) : ℝ) := by exact_mod_cast hB1
    have hsB : r ^ 2 ≤ ((B : ℕ) : ℝ) := by
      rw [hrsq]
      exact_mod_cast min_le_left B F
    have hcase : r ^ 2 = ((B : ℕ) : ℝ) ∨ (Lbar / μ) ^ 2 ≤ 2 * r ^ 2 := by
      rcases min_choice B F with h | h
      · left
        rw [hrsq, h]
      · right
        rw [hrsq, h]
        have h1 : (Lbar / μ) ^ 2 < (F : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : (1 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF1
        linarith
    have hm : (((stageEpoch L Lbar μ σ Δ j).m : ℕ) : ℝ) = r ^ 2 - 1 := by
      rw [he, hrsq]
      change (((min B F - 1 : ℕ)) : ℝ) = _
      rw [Nat.cast_sub hs1]
      simp
    have hBe : (((stageEpoch L Lbar μ σ Δ j).B : ℕ) : ℝ) = ((B : ℕ) : ℝ) := by rw [he]
    have hηe : (stageEpoch L Lbar μ σ Δ j).η = 1 / (2 * Lbar * r) := by rw [he]
    have hRle : (stageRepeats L Lbar μ σ Δ j : ℝ) ≤ 6 * (Lbar / μ) / r + 1 := by
      rw [hRdef, hm, hηe]
      have harg : 3 / ((r ^ 2 - 1 + 1) * (1 / (2 * Lbar * r) * μ)) = 6 * (Lbar / μ) / r := by
        have hr0 : 0 < r := by linarith
        have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
        have h1 : (r ^ 2 - 1 + 1) * (1 / (2 * Lbar * r) * μ) = r * μ / (2 * Lbar) := by
          rw [sub_add_cancel, one_div, pow_two, mul_inv, div_eq_mul_inv]
          calc r * r * ((2 * Lbar)⁻¹ * r⁻¹ * μ) = r * (r * r⁻¹) * μ * (2 * Lbar)⁻¹ := by ring
            _ = r * μ * (2 * Lbar)⁻¹ := by rw [hrr]; ring
        rw [h1, div_div_eq_mul_div]
        ring
      rw [harg]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hmain := cost_real_V hκb hq1 hB1R hBR hr1 hsB hcase hRle
    rw [hBe, hm]
    rw [hqsq] at hmain
    have hlt : Lbar / μ * √b ≤ L / μ * b := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hbr.le hμ.le
    have hκ0 : 0 ≤ L / μ := by linarith
    constructor <;> nlinarith
  · have he := stageEpoch_of_not_lt (μ := μ) (σ := σ) (Δ := Δ) (j := j) hbr
    push Not at hbr
    have hm : (((stageEpoch L Lbar μ σ Δ j).m : ℕ) : ℝ) = 0 := by rw [he]; simp
    have hBe : (((stageEpoch L Lbar μ σ Δ j).B : ℕ) : ℝ) = ((max 1 ⌈b⌉₊ : ℕ) : ℝ) := by rw [he]
    have hηe : (stageEpoch L Lbar μ σ Δ j).η = 1 / (2 * L) := by rw [he]
    have hRle : (stageRepeats L Lbar μ σ Δ j : ℝ) ≤ 6 * (L / μ) + 1 := by
      rw [hRdef, hm, hηe]
      have harg : 3 / ((0 + 1) * (1 / (2 * L) * μ)) = 6 * (L / μ) := by
        rw [zero_add, one_mul, div_mul_eq_mul_div, one_mul, div_div_eq_mul_div]
        ring
      rw [harg]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hB0 : (0 : ℝ) ≤ ((max 1 ⌈b⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmain := cost_real_G hκ hRle (batch_cast_le hb) hB0
    rw [hBe, hm, add_zero]
    have hle : L / μ * b ≤ Lbar / μ * √b := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hbr hμ.le
    have hκ0 : 0 ≤ L / μ := by linarith
    have hκb0 : 0 ≤ L / μ * b := mul_nonneg hκ0 hb
    constructor <;> nlinarith

lemma stageBatch_eq (μ σ Δ : ℝ) (j : ℕ) : stageBatch μ σ Δ j = stageBatch μ σ Δ 0 * 2 ^ j := by
  unfold stageBatch
  ring

lemma sum_batch_le (hb : 0 ≤ stageBatch μ σ Δ 0) (K : ℕ) :
    ∑ j ∈ Finset.range K, stageBatch μ σ Δ j ≤ stageBatch μ σ Δ 0 * 2 ^ K := by
  induction K with
  | zero => simpa using hb
  | succ K ih =>
    rw [Finset.sum_range_succ, stageBatch_eq μ σ Δ K, pow_succ]
    linarith

lemma sum_sqrt_batch_le (hb : 0 ≤ stageBatch μ σ Δ 0) (K : ℕ) :
    ∑ j ∈ Finset.range K, √(stageBatch μ σ Δ j) ≤ 4 * √(stageBatch μ σ Δ 0 * 2 ^ K) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ K ih =>
    rw [Finset.sum_range_succ, stageBatch_eq μ σ Δ K, pow_succ, ← mul_assoc]
    have hX : 0 ≤ stageBatch μ σ Δ 0 * 2 ^ K := by positivity
    rw [Real.sqrt_mul hX]
    have h2 : (5 : ℝ) / 4 ≤ √2 := by
      rw [show (5 : ℝ) / 4 = √((5 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs : 0 ≤ √(stageBatch μ σ Δ 0 * 2 ^ K) := Real.sqrt_nonneg _
    nlinarith

theorem cost_schedule_le (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) :
    (cost (schedule L Lbar μ σ Δ ε) : ℝ) ≤
      640 * (L / μ * Real.logb 2 (1 + Δ / ε) + (σ / √(μ * ε)) ^ 2 +
        min (L / μ * (σ / √(μ * ε)) ^ 2) (Lbar / μ * (σ / √(μ * ε)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le hμ hL
  have hκ : 1 ≤ L / μ := by rwa [le_div_iff₀ hμ, one_mul]
  have hκb : 1 ≤ Lbar / μ := by
    rw [le_div_iff₀ hμ, one_mul]
    exact hL.trans hLbar
  have hμε : 0 < μ * ε := mul_pos hμ hε
  have hsqrt : 0 < √(μ * ε) := Real.sqrt_pos.mpr hμε
  set s := σ / √(μ * ε) with hsdef
  have hs0 : 0 ≤ s := div_nonneg hσ hsqrt.le
  have hs2 : s ^ 2 = σ ^ 2 / (μ * ε) := by
    rw [hsdef, div_pow, Real.sq_sqrt hμε.le]
  have hy0 : 0 ≤ Real.logb 2 (1 + Δ / ε) :=
    Real.logb_nonneg (by norm_num) (by have := div_nonneg hΔ hε.le; linarith)
  have hmin0 : 0 ≤ min (L / μ * s ^ 2) (Lbar / μ * s) :=
    le_min (by positivity) (by positivity)
  by_cases hΔε : Δ ≤ ε
  · have hK : ⌈Real.logb 2 (Δ / ε)⌉₊ = 0 := by
      rw [Nat.ceil_eq_zero]
      exact Real.logb_nonpos (by norm_num) (div_nonneg hΔ hε.le) ((div_le_one hε).mpr hΔε)
    simp only [schedule, hK, List.range_zero, List.flatMap_nil, cost, Nat.cast_zero]
    have : 0 ≤ L / μ * Real.logb 2 (1 + Δ / ε) := mul_nonneg (by linarith) hy0
    positivity
  · push Not at hΔε
    have hΔ0 : 0 < Δ := hε.trans hΔε
    obtain ⟨hpow1, hpow2⟩ := two_pow_stage_count hε hΔε
    set K := ⌈Real.logb 2 (Δ / ε)⌉₊ with hKdef
    have hx : 0 < Δ / ε := div_pos hΔ0 hε
    have hx1 : 1 < Δ / ε := by rwa [lt_div_iff₀ hε, one_mul]
    have hb0 : 0 ≤ stageBatch μ σ Δ 0 := by
      unfold stageBatch
      positivity
    have hbj : ∀ j, 0 ≤ stageBatch μ σ Δ j := fun j => by
      rw [stageBatch_eq]
      positivity
    have hcost : ((cost (schedule L Lbar μ σ Δ ε) : ℕ) : ℝ) =
        ∑ j ∈ Finset.range K, (cost (stage L Lbar μ σ Δ j) : ℝ) := by
      rw [schedule, cost_stages]
      push_cast
      rfl
    have hsum1 : ((cost (schedule L Lbar μ σ Δ ε) : ℕ) : ℝ) ≤
        7 * (L / μ) * K + (17 * (L / μ) + 40) * ∑ j ∈ Finset.range K, stageBatch μ σ Δ j := by
      rw [hcost, Finset.mul_sum]
      calc ∑ j ∈ Finset.range K, (cost (stage L Lbar μ σ Δ j) : ℝ)
          ≤ ∑ j ∈ Finset.range K, (7 * (L / μ) + (17 * (L / μ) + 40) * stageBatch μ σ Δ j) := by
            apply Finset.sum_le_sum
            intro j _
            have := (cost_stage_le (σ := σ) (Δ := Δ) hμ hL hLbar j (hbj j)).1
            linarith
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
            simp only [nsmul_eq_mul]
            ring
    have hsum2 : ((cost (schedule L Lbar μ σ Δ ε) : ℕ) : ℝ) ≤
        7 * (L / μ) * K + 17 * (Lbar / μ) * ∑ j ∈ Finset.range K, √(stageBatch μ σ Δ j) +
          40 * ∑ j ∈ Finset.range K, stageBatch μ σ Δ j := by
      rw [hcost, Finset.mul_sum, Finset.mul_sum]
      calc ∑ j ∈ Finset.range K, (cost (stage L Lbar μ σ Δ j) : ℝ)
          ≤ ∑ j ∈ Finset.range K, (7 * (L / μ) + 17 * (Lbar / μ) * √(stageBatch μ σ Δ j) +
              40 * stageBatch μ σ Δ j) := by
            apply Finset.sum_le_sum
            intro j _
            exact (cost_stage_le (σ := σ) (Δ := Δ) hμ hL hLbar j (hbj j)).2
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_range]
            simp only [nsmul_eq_mul]
            ring
    have hSb : ∑ j ∈ Finset.range K, stageBatch μ σ Δ j ≤ 16 * s ^ 2 := by
      refine (sum_batch_le hb0 K).trans ?_
      have h1 : stageBatch μ σ Δ 0 * 2 ^ K ≤ stageBatch μ σ Δ 0 * (2 * (Δ / ε)) :=
        mul_le_mul_of_nonneg_left hpow2 hb0
      refine h1.trans (le_of_eq ?_)
      rw [hs2]
      unfold stageBatch
      field_simp
      ring
    have hSr : ∑ j ∈ Finset.range K, √(stageBatch μ σ Δ j) ≤ 16 * s := by
      refine (sum_sqrt_batch_le hb0 K).trans ?_
      have h1 : stageBatch μ σ Δ 0 * 2 ^ K ≤ (4 * s) ^ 2 := by
        have h2 : stageBatch μ σ Δ 0 * 2 ^ K ≤ stageBatch μ σ Δ 0 * (2 * (Δ / ε)) :=
          mul_le_mul_of_nonneg_left hpow2 hb0
        refine h2.trans (le_of_eq ?_)
        rw [mul_pow, hs2]
        unfold stageBatch
        field_simp
        ring
      have h3 : √(stageBatch μ σ Δ 0 * 2 ^ K) ≤ 4 * s := by
        rw [show 4 * s = √((4 * s) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt h1
      linarith
    have hK : (K : ℝ) ≤ 2 * Real.logb 2 (1 + Δ / ε) := by
      have hlog : 0 ≤ Real.logb 2 (Δ / ε) := Real.logb_nonneg (by norm_num) hx1.le
      have h1 : (K : ℝ) < Real.logb 2 (Δ / ε) + 1 := Nat.ceil_lt_add_one hlog
      have h2 : Real.logb 2 (Δ / ε) ≤ Real.logb 2 (1 + Δ / ε) :=
        Real.logb_le_logb_of_le (by norm_num) hx (by linarith)
      have h3 : (1 : ℝ) ≤ Real.logb 2 (1 + Δ / ε) := by
        have h4 : Real.logb 2 2 ≤ Real.logb 2 (1 + Δ / ε) :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
        rwa [Real.logb_self_eq_one (by norm_num)] at h4
      linarith
    have hκ0 : 0 ≤ L / μ := by linarith
    have hκb0 : 0 ≤ Lbar / μ := by linarith
    have hs20 : 0 ≤ s ^ 2 := sq_nonneg s
    have hKκ : 7 * (L / μ) * K ≤ 14 * (L / μ) * Real.logb 2 (1 + Δ / ε) := by nlinarith
    have hSb0 : 0 ≤ ∑ j ∈ Finset.range K, stageBatch μ σ Δ j :=
      Finset.sum_nonneg (fun j _ => hbj j)
    rcases le_total (L / μ * s ^ 2) (Lbar / μ * s) with hmin | hmin
    · rw [min_eq_left hmin]
      have h1 : (17 * (L / μ) + 40) * ∑ j ∈ Finset.range K, stageBatch μ σ Δ j ≤
          (17 * (L / μ) + 40) * (16 * s ^ 2) :=
        mul_le_mul_of_nonneg_left hSb (by linarith)
      have hκs : 0 ≤ L / μ * s ^ 2 := mul_nonneg hκ0 hs20
      have hκy : 0 ≤ L / μ * Real.logb 2 (1 + Δ / ε) := mul_nonneg hκ0 hy0
      nlinarith
    · rw [min_eq_right hmin]
      have h1 : 17 * (Lbar / μ) * ∑ j ∈ Finset.range K, √(stageBatch μ σ Δ j) ≤
          17 * (Lbar / μ) * (16 * s) := mul_le_mul_of_nonneg_left hSr (by linarith)
      have hκs : 0 ≤ Lbar / μ * s := mul_nonneg hκb0 hs0
      have hκy : 0 ≤ L / μ * Real.logb 2 (1 + Δ / ε) := mul_nonneg hκ0 hy0
      nlinarith

end OracleTemplate.StagewiseSarah
