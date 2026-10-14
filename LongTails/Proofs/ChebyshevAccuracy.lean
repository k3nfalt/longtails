import LongTails.Proofs.ChebyshevBatching

open scoped BigOperators

namespace OracleTemplate.BatchedChebyshev

lemma rounded_calls_budget (L R σ ε : ℝ) :
    2 * ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ + ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊ ≤
      3 + ⌈4 * Real.sqrt (L * R ^ 2 / ε) + 65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊ := by
  have hT := (Nat.ceil_lt_add_one (Real.sqrt_nonneg (L * R ^ 2 / ε))).le
  have hv : 0 ≤ 65536 * σ ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hM := (Nat.ceil_lt_add_one hv).le
  have hB := Nat.le_ceil (4 * Real.sqrt (L * R ^ 2 / ε) + 65536 * σ ^ 2 * R ^ 2 / ε ^ 2)
  have hreal : 2 * (⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ : ℝ) +
      (⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊ : ℝ) ≤
      3 + (⌈4 * Real.sqrt (L * R ^ 2 / ε) + 65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊ : ℝ) := by
    linarith [Real.sqrt_nonneg (L * R ^ 2 / ε)]
  exact_mod_cast hreal

lemma accuracy_parameters {L R ε : ℝ} (hε : 0 < ε)
    (hfine : ε < L * R ^ 2 / 2) :
    0 < ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ ∧
    L * R ^ 2 / ε ≤ (⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ : ℝ) ^ 2 ∧
    (⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ : ℝ) ^ 2 ≤ 4 * L * R ^ 2 / ε := by
  have hq : 1 < L * R ^ 2 / ε := (lt_div_iff₀ hε).mpr (by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ L * R ^ 2 / ε by positivity)
  have hs0 := Real.sqrt_nonneg (L * R ^ 2 / ε)
  have hs1 : 1 ≤ Real.sqrt (L * R ^ 2 / ε) := by nlinarith
  have hceil := Nat.le_ceil (Real.sqrt (L * R ^ 2 / ε))
  have hceilup := (Nat.ceil_lt_add_one hs0).le
  have hT : 0 < ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ := by
    have : (0 : ℝ) < ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ := by linarith
    exact_mod_cast this
  refine ⟨hT, ?_, ?_⟩
  · nlinarith
  · have htwo : (⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ : ℝ) ≤
        2 * Real.sqrt (L * R ^ 2 / ε) := by linarith
    have hh := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity :
      0 ≤ 2 * Real.sqrt (L * R ^ 2 / ε))).mpr htwo
    calc
      _ ≤ (2 * Real.sqrt (L * R ^ 2 / ε)) ^ 2 := hh
      _ = _ := by rw [mul_pow, hs]; ring

lemma tuned_error_le {L R σ ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hfine : ε < L * R ^ 2 / 2) :
    let T := ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊
    let M := ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊
    L * R ^ 2 / (2 * (2 * (T : ℝ) + 1) ^ 2) +
      (σ ^ 2 / (2 * L)) * (∑ i ∈ Finset.range T,
        weight T (i + 1) ^ 2 / (batch T M (i + 1) : ℝ)) ≤ ε := by
  dsimp only
  let T := ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊
  let M := ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊
  obtain ⟨hT, hlo, hup⟩ := accuracy_parameters hε hfine
  change 0 < T at hT
  change L * R ^ 2 / ε ≤ (T : ℝ) ^ 2 at hlo
  change (T : ℝ) ^ 2 ≤ 4 * L * R ^ 2 / ε at hup
  change L * R ^ 2 / (2 * (2 * (T : ℝ) + 1) ^ 2) +
    (σ ^ 2 / (2 * L)) * (∑ i ∈ Finset.range T,
      weight T (i + 1) ^ 2 / (batch T M (i + 1) : ℝ)) ≤ ε
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hR : 0 < R ^ 2 := by nlinarith
  have hbias : L * R ^ 2 / (2 * (2 * (T : ℝ) + 1) ^ 2) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hl := (div_le_iff₀ hε).mp hlo
    nlinarith [mul_pos hε (sq_pos_of_pos hT0)]
  have hnoise : (σ ^ 2 / (2 * L)) * (∑ i ∈ Finset.range T,
      weight T (i + 1) ^ 2 / (batch T M (i + 1) : ℝ)) ≤ ε / 2 := by
    by_cases hM : M = 0
    · have hm : 65536 * σ ^ 2 * R ^ 2 / ε ^ 2 ≤ 0 := by
        have hc := Nat.le_ceil (65536 * σ ^ 2 * R ^ 2 / ε ^ 2)
        change 65536 * σ ^ 2 * R ^ 2 / ε ^ 2 ≤ (M : ℝ) at hc
        simpa only [hM, Nat.cast_zero] using hc
      have hz : σ ^ 2 = 0 := by
        have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hm
        nlinarith [mul_pos hR (show 0 < (65536 : ℝ) by norm_num), sq_nonneg σ]
      simp only [hz, zero_div, zero_mul]
      positivity
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
      have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
      have hv := allocated_variance_sum_le hT hMpos
      have hceil : 65536 * σ ^ 2 * R ^ 2 / ε ^ 2 ≤ (M : ℝ) := Nat.le_ceil _
      calc
        _ ≤ (σ ^ 2 / (2 * L)) * (16384 * (T : ℝ) ^ 2 / M) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
        _ ≤ (σ ^ 2 / (2 * L)) * (16384 * (4 * L * R ^ 2 / ε) / M) := by
          gcongr
        _ = 32768 * σ ^ 2 * R ^ 2 / (ε * (M : ℝ)) := by field_simp; ring
        _ ≤ ε / 2 := by
          apply (div_le_iff₀ (mul_pos hε hM')).mpr
          have hc := (div_le_iff₀ (sq_pos_of_pos hε)).mp hceil
          nlinarith
  linarith

end OracleTemplate.BatchedChebyshev
