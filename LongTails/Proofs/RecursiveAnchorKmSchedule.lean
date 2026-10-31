import LongTails.Algorithms.RecursiveAnchorKm
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic

namespace OracleTemplate.RecursiveAnchorKm

section Generic

lemma noise_generic {η Λ K σ α a : ℝ} (hη : 0 < η) (hΛ : 0 < Λ) (hK : 0 ≤ K)
    (ha : a = η ^ 2 * Λ * (1 + Λ)) (hα : α = a / (a + 2 * K * σ ^ 2)) :
    (1 - α * Λ / (1 + Λ)) ^ 2 * (η ^ 2 / 2) + K * (α / (1 + Λ)) ^ 2 * σ ^ 2 ≤ η ^ 2 / 2 := by
  have hpos : 0 < 1 + Λ := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have hs : 0 ≤ 2 * K * σ ^ 2 := by positivity
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hα1 : α ≤ 1 := by rw [hα, div_le_one (by linarith)]; linarith
  have hαs : α * (2 * K * σ ^ 2) ≤ a := by
    rw [hα, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  set x := α * Λ / (1 + Λ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    simp only [x]
    rw [div_le_one hpos]
    nlinarith
  have key : K * (α / (1 + Λ)) ^ 2 * σ ^ 2 = α * (α * (2 * K * σ ^ 2)) / (2 * (1 + Λ) ^ 2) := by
    field_simp
  have key2 : x * (η ^ 2 / 2) = α * a / (2 * (1 + Λ) ^ 2) := by
    simp only [x]
    rw [ha]
    field_simp
  have h1 : K * (α / (1 + Λ)) ^ 2 * σ ^ 2 ≤ x * (η ^ 2 / 2) := by
    rw [key, key2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hαs hα0) (by positivity)
  have h2 : (1 - x) ^ 2 * (η ^ 2 / 2) ≤ (1 - x) * (η ^ 2 / 2) := by
    have : (1 - x) ^ 2 ≤ 1 - x := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  nlinarith

lemma count_generic {η Λ K σ α a : ℝ} (hη : 0 < η) (hΛ : 0 < Λ) (hK : 0 ≤ K)
    (ha : a = η ^ 2 * Λ * (1 + Λ)) (hα : α = a / (a + 2 * K * σ ^ 2)) (M : ℕ) :
    (1 - α * Λ / (1 + Λ)) ^ (2 * (M * ⌈(1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2⌉₊)) ≤
      (1 / 4) ^ M := by
  have hpos : 0 < 1 + Λ := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have hs : 0 ≤ 2 * K * σ ^ 2 := by positivity
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : α ≤ 1 := by rw [hα, div_le_one (by linarith)]; linarith
  set m := ⌈(1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2⌉₊
  set x := α * Λ / (1 + Λ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    simp only [x]
    rw [div_le_one hpos]
    nlinarith
  have hinv : x * ((1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2) = 1 := by
    simp only [x]
    rw [hα, ha]
    field_simp
  have hmx : 1 ≤ (m : ℝ) * x := by
    have := Nat.le_ceil ((1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2)
    nlinarith
  have hb : 2 ≤ (1 + x) ^ m := le_trans (by linarith) (one_add_mul_le_pow (by linarith) m)
  have hprod : (1 - x) ^ m * (1 + x) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hm : (1 - x) ^ m ≤ 1 / 2 := by
    have := pow_nonneg (show 0 ≤ 1 - x by linarith) m
    nlinarith
  rw [show 2 * (M * m) = m * (2 * M) by ring, pow_mul]
  calc ((1 - x) ^ m) ^ (2 * M) ≤ (1 / 2) ^ (2 * M) :=
        pow_le_pow_left₀ (pow_nonneg (by linarith) m) hm _
    _ = (1 / 4) ^ M := by rw [pow_mul]; norm_num

end Generic

variable {D ε : ℝ}

lemma anchorWeight_pos (hD : 0 < D) (hε : 0 < ε) (t : ℕ) : 0 < anchorWeight D ε t := by
  unfold anchorWeight; positivity

lemma totalWeight_zero : totalWeight D ε 0 = anchorWeight D ε 0 := by
  norm_num [totalWeight, anchorWeight]

lemma totalWeight_succ (u : ℕ) :
    totalWeight D ε (u + 1) = totalWeight D ε u + anchorWeight D ε (u + 1) := by
  simp only [totalWeight, anchorWeight]; ring

lemma pow_le_totalWeight (hD : 0 < D) (hε : 0 < ε) (u : ℕ) :
    2 ^ u * (ε / (4 * D)) ≤ totalWeight D ε u := by
  unfold totalWeight
  have h1 : (1 : ℝ) ≤ 2 ^ u := one_le_pow₀ (by norm_num)
  have h2 : (2 : ℝ) ^ u ≤ 2 ^ (u + 1) - 1 := by rw [pow_succ]; linarith
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

lemma totalWeight_pos (hD : 0 < D) (hε : 0 < ε) (u : ℕ) : 0 < totalWeight D ε u :=
  lt_of_lt_of_le (by positivity) (pow_le_totalWeight hD hε u)

lemma one_le_anchorWeight_lastStage (hD : 0 < D) (hε : 0 < ε) :
    1 ≤ anchorWeight D ε (lastStage D ε) := by
  unfold anchorWeight lastStage
  have h1 : ((⌈4 * D / ε⌉₊ : ℕ) : ℝ) ≤ 2 ^ Nat.clog 2 ⌈4 * D / ε⌉₊ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h2 : 4 * D / ε ≤ ⌈4 * D / ε⌉₊ := Nat.le_ceil _
  have h3 : 4 * D / ε ≤ 2 ^ Nat.clog 2 ⌈4 * D / ε⌉₊ := le_trans h2 h1
  rw [div_le_iff₀ hε] at h3
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  linarith

lemma lastStage_le (hD : 0 < D) (hε : 0 < ε) :
    (lastStage D ε : ℝ) + 1 ≤ Real.logb 2 (1 + D / ε) + 4 := by
  set S := lastStage D ε
  have hDε : 0 ≤ D / ε := by positivity
  have hlog0 : 0 ≤ Real.logb 2 (1 + D / ε) := Real.logb_nonneg (by norm_num) (by linarith)
  rcases Nat.eq_zero_or_pos S with h0 | hpos
  · rw [h0]; push_cast; linarith
  · have hn : 1 < ⌈4 * D / ε⌉₊ := by
      by_contra hc
      push Not at hc
      have : S = 0 := Nat.clog_of_right_le_one hc 2
      omega
    have h1 : 2 ^ (Nat.clog 2 ⌈4 * D / ε⌉₊).pred < ⌈4 * D / ε⌉₊ :=
      Nat.pow_pred_clog_lt_self (by norm_num) hn
    have h2 : ((⌈4 * D / ε⌉₊ : ℕ) : ℝ) < 4 * D / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : (2 : ℝ) ^ (S - 1) < 4 * (1 + D / ε) := by
      have h4 : ((2 ^ (S - 1) : ℕ) : ℝ) < ((⌈4 * D / ε⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4
      have : 4 * D / ε = 4 * (D / ε) := by ring
      linarith
    have h4 : ((S - 1 : ℕ) : ℝ) < Real.logb 2 (4 * (1 + D / ε)) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]
      exact h3
    rw [Real.logb_mul (by norm_num) (by positivity)] at h4
    have h5 : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [h5] at h4
    have h6 : ((S - 1 : ℕ) : ℝ) = (S : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    linarith

lemma stageTarget_pos (hD : 0 < D) (hε : 0 < ε) (u : ℕ) : 0 < stageTarget D ε u := by
  unfold stageTarget
  have := anchorWeight_pos hD hε (u + 1)
  split_ifs <;> positivity

lemma stageTarget_last :
    stageTarget D ε (lastStage D ε) = ε / (4 * (lastStage D ε + 1)) := by
  unfold stageTarget
  rw [ite_eq_right (lt_irrefl _)]

lemma stageTarget_of_lt {u : ℕ} (hu : u < lastStage D ε) :
    stageTarget D ε u = ε / (6 * (lastStage D ε + 1) * anchorWeight D ε (u + 1)) := by
  unfold stageTarget
  rw [ite_eq_left hu]

lemma stageTarget_le_two_mul (hD : 0 < D) (hε : 0 < ε) {u : ℕ} (hu : u < lastStage D ε) :
    stageTarget D ε u ≤ 2 * stageTarget D ε (u + 1) := by
  rw [stageTarget_of_lt hu]
  have ha := anchorWeight_pos hD hε (u + 1)
  by_cases h : u + 1 < lastStage D ε
  · rw [stageTarget_of_lt h]
    have : anchorWeight D ε (u + 1 + 1) = 2 * anchorWeight D ε (u + 1) := by
      simp only [anchorWeight]; ring
    rw [this]
    apply le_of_eq
    field_simp
  · have hS : u + 1 = lastStage D ε := by omega
    have h1 : 1 ≤ anchorWeight D ε (u + 1) := by
      rw [hS]; exact one_le_anchorWeight_lastStage hD hε
    have hlast : stageTarget D ε (u + 1) = ε / (4 * ((lastStage D ε : ℝ) + 1)) := by
      rw [hS]; exact stageTarget_last
    rw [hlast, div_le_iff₀ (by positivity)]
    have he : 2 * (ε / (4 * ((lastStage D ε : ℝ) + 1))) *
        (6 * ((lastStage D ε : ℝ) + 1) * anchorWeight D ε (u + 1)) =
        3 * ε * anchorWeight D ε (u + 1) := by
      field_simp
      ring
    rw [he]
    nlinarith

lemma target_mul_total (hD : 0 < D) (hε : 0 < ε) {u : ℕ} (hu : u ≤ lastStage D ε) :
    ε / (12 * (lastStage D ε + 1)) ≤ stageTarget D ε u * totalWeight D ε u := by
  set S := lastStage D ε
  have hΛ := pow_le_totalWeight hD hε u
  by_cases h : u < S
  · rw [stageTarget_of_lt h]
    have ha := anchorWeight_pos hD hε (u + 1)
    calc ε / (12 * (S + 1)) =
          ε / (6 * (S + 1) * anchorWeight D ε (u + 1)) * (2 ^ u * (ε / (4 * D))) := by
          simp only [anchorWeight]
          field_simp
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hΛ (by positivity)
  · have hS : u = S := by omega
    rw [hS, stageTarget_last]
    have h1 := one_le_anchorWeight_lastStage hD hε
    have h2 : 1 ≤ totalWeight D ε S := by
      have := pow_le_totalWeight hD hε S
      simp only [anchorWeight] at h1
      linarith
    calc ε / (12 * (S + 1)) ≤ ε / (4 * (S + 1)) :=
          div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
      _ = ε / (4 * (S + 1)) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma stageStep_mem (hD : 0 < D) (hε : 0 < ε) {K σ : ℝ} (hK : 0 ≤ K) (u : ℕ) :
    0 ≤ stageStep K σ D ε u ∧ stageStep K σ D ε u ≤ 1 := by
  unfold stageStep
  have h1 := stageTarget_pos hD hε u
  have h2 := totalWeight_pos hD hε u
  have ha : 0 < stageTarget D ε u ^ 2 * totalWeight D ε u * (1 + totalWeight D ε u) := by positivity
  have hs : 0 ≤ 2 * K * σ ^ 2 := by positivity
  exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩

lemma stage_noise (hD : 0 < D) (hε : 0 < ε) {K σ : ℝ} (hK : 0 ≤ K) (u : ℕ) :
    (1 - stageStep K σ D ε u * totalWeight D ε u / (1 + totalWeight D ε u)) ^ 2 *
        (stageTarget D ε u ^ 2 / 2) +
      K * (stageStep K σ D ε u / (1 + totalWeight D ε u)) ^ 2 * σ ^ 2 ≤
      stageTarget D ε u ^ 2 / 2 :=
  noise_generic (stageTarget_pos hD hε u) (totalWeight_pos hD hε u) hK rfl rfl

lemma stage_count (hD : 0 < D) (hε : 0 < ε) {K σ : ℝ} (hK : 0 ≤ K) (u : ℕ) :
    (1 - stageStep K σ D ε u * totalWeight D ε u / (1 + totalWeight D ε u)) ^
        (2 * stageLength K σ D ε u) ≤
      (1 / 4) ^ (if u = 0 then 2 * lastStage D ε + 7 else 5) :=
  count_generic (stageTarget_pos hD hε u) (totalWeight_pos hD hε u) hK rfl rfl _

lemma stageLength_pos (hD : 0 < D) (hε : 0 < ε) {K σ : ℝ} (hK : 0 ≤ K) (u : ℕ) :
    0 < stageLength K σ D ε u := by
  unfold stageLength
  have h2 := totalWeight_pos hD hε u
  have hx : 0 < (1 + totalWeight D ε u) / totalWeight D ε u +
      2 * K * σ ^ 2 / (stageTarget D ε u * totalWeight D ε u) ^ 2 := by
    have : 0 ≤ 2 * K * σ ^ 2 / (stageTarget D ε u * totalWeight D ε u) ^ 2 := by positivity
    have : 0 < (1 + totalWeight D ε u) / totalWeight D ε u := by positivity
    linarith
  apply Nat.mul_pos
  · split_ifs <;> omega
  · exact Nat.ceil_pos.mpr hx

lemma initial_contraction (hD : 0 < D) (hε : 0 < ε) :
    (1 / 4 : ℝ) ^ (2 * lastStage D ε + 7) * (4 * D ^ 2) ≤ stageTarget D ε 0 ^ 2 / 2 := by
  set S := lastStage D ε
  rcases Nat.eq_zero_or_pos S with h0 | hpos
  · have hη : stageTarget D ε 0 = ε / 4 := by
      have := stageTarget_last (D := D) (ε := ε)
      rw [← show S = lastStage D ε from rfl, h0] at this
      rw [this]; norm_num
    have h1 := one_le_anchorWeight_lastStage hD hε
    rw [← show S = lastStage D ε from rfl, h0] at h1
    simp only [anchorWeight, pow_zero, one_mul] at h1
    rw [le_div_iff₀ (by positivity)] at h1
    rw [hη, h0]
    have hD2 : D ^ 2 ≤ ε ^ 2 / 16 := by nlinarith
    norm_num
    nlinarith
  · have hη : stageTarget D ε 0 = D / (3 * (S + 1)) := by
      rw [stageTarget_of_lt hpos]
      simp only [anchorWeight]
      field_simp
      ring
    rw [hη]
    have hS1 : ((S : ℝ) + 1) ≤ 2 ^ S := by
      have : S + 1 ≤ 2 ^ S := Nat.lt_two_pow_self
      exact_mod_cast this
    have hS2 : ((S : ℝ) + 1) ^ 2 ≤ 4 ^ S := by
      calc ((S : ℝ) + 1) ^ 2 ≤ (2 ^ S) ^ 2 := pow_le_pow_left₀ (by positivity) hS1 2
        _ = 4 ^ S := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h4 : (4 : ℝ) ^ (2 * S + 7) = 4 ^ S * 4 ^ S * 4 ^ 7 := by
      rw [show 2 * S + 7 = S + S + 7 by ring, pow_add, pow_add]
    have h4S : (1 : ℝ) ≤ 4 ^ S := one_le_pow₀ (by norm_num)
    have h72 : 72 * ((S : ℝ) + 1) ^ 2 ≤ 4 ^ (2 * S + 7) := by
      rw [h4]; nlinarith
    rw [one_div_pow, div_pow, div_mul_eq_mul_div, one_mul, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hD0 : 0 ≤ D ^ 2 := sq_nonneg D
    nlinarith

lemma later_contraction (hD : 0 < D) (hε : 0 < ε) {u : ℕ} (hu : u < lastStage D ε) :
    (1 / 4 : ℝ) ^ 5 * (4 * stageTarget D ε u ^ 2) ≤ stageTarget D ε (u + 1) ^ 2 / 2 := by
  have h1 := stageTarget_le_two_mul hD hε hu
  have h0 := (stageTarget_pos hD hε u).le
  have h2 : stageTarget D ε u ^ 2 ≤ (2 * stageTarget D ε (u + 1)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith

lemma accuracy_step (hD : 0 < D) (hε : 0 < ε) {u : ℕ} (hu : u < lastStage D ε) :
    3 * anchorWeight D ε (u + 1) * stageTarget D ε u ≤ ε / (2 * (lastStage D ε + 1)) := by
  rw [stageTarget_of_lt hu]
  have := anchorWeight_pos hD hε (u + 1)
  apply le_of_eq
  field_simp
  ring

lemma accuracy_total (hD : 0 < D) (hε : 0 < ε) :
    2 * stageTarget D ε (lastStage D ε) + 2 * anchorWeight D ε 0 * D +
      lastStage D ε * (ε / (2 * (lastStage D ε + 1))) ≤ ε := by
  rw [stageTarget_last]
  simp only [anchorWeight, pow_zero, one_mul]
  apply le_of_eq
  field_simp
  ring

lemma stageLength_le (hD : 0 < D) (hε : 0 < ε) {K σ : ℝ} (hK : 0 ≤ K) {u : ℕ}
    (hu : u ≤ lastStage D ε) :
    (stageLength K σ D ε u : ℝ) ≤ ((if u = 0 then 2 * lastStage D ε + 7 else 5 : ℕ) : ℝ) *
      (2 + (1 / 2) ^ u * (4 * D / ε) + 288 * K * σ ^ 2 * (lastStage D ε + 1) ^ 2 / ε ^ 2) := by
  set S := lastStage D ε
  set Λ := totalWeight D ε u
  set η := stageTarget D ε u
  have hΛ := totalWeight_pos hD hε u
  have hη := stageTarget_pos hD hε u
  have hs : 0 ≤ 2 * K * σ ^ 2 := by positivity
  have hx : 0 ≤ (1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2 := by positivity
  have hc := Nat.ceil_lt_add_one hx
  have hinvΛ : 1 / Λ ≤ (1 / 2) ^ u * (4 * D / ε) := by
    calc 1 / Λ ≤ 1 / (2 ^ u * (ε / (4 * D))) :=
          one_div_le_one_div_of_le (by positivity) (pow_le_totalWeight hD hε u)
      _ = (1 / 2) ^ u * (4 * D / ε) := by
          rw [one_div_pow]; field_simp
  have hηΛ := target_mul_total hD hε hu
  have hsq : (ε / (12 * (S + 1))) ^ 2 ≤ (η * Λ) ^ 2 := pow_le_pow_left₀ (by positivity) hηΛ 2
  have hnoise : 2 * K * σ ^ 2 / (η * Λ) ^ 2 ≤ 288 * K * σ ^ 2 * (S + 1) ^ 2 / ε ^ 2 := by
    calc 2 * K * σ ^ 2 / (η * Λ) ^ 2 ≤ 2 * K * σ ^ 2 / (ε / (12 * (S + 1))) ^ 2 :=
          div_le_div_of_nonneg_left hs (by positivity) hsq
      _ = 288 * K * σ ^ 2 * (S + 1) ^ 2 / ε ^ 2 := by field_simp; ring
  have hfirst : (1 + Λ) / Λ = 1 + 1 / Λ := by
    rw [add_div, div_self (ne_of_gt hΛ)]; ring
  have hX : (1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2 ≤
      1 + (1 / 2) ^ u * (4 * D / ε) + 288 * K * σ ^ 2 * (S + 1) ^ 2 / ε ^ 2 := by
    rw [hfirst]; linarith
  have hm : (⌈(1 + Λ) / Λ + 2 * K * σ ^ 2 / (η * Λ) ^ 2⌉₊ : ℝ) ≤
      2 + (1 / 2) ^ u * (4 * D / ε) + 288 * K * σ ^ 2 * (S + 1) ^ 2 / ε ^ 2 := by
    linarith
  unfold stageLength
  push_cast
  exact mul_le_mul_of_nonneg_left hm (by split_ifs <;> positivity)

lemma budget_le (hD : 0 < D) (hε : 0 < ε) {K σ : ℝ} (hK : 0 ≤ K) :
    (∑ u ∈ Finset.range (lastStage D ε + 1), (stageLength K σ D ε u : ℝ)) ≤
      (Real.logb 2 (1 + D / ε) + 4) * (16 + 20 * D / ε +
        2048 * K * σ ^ 2 * (Real.logb 2 (1 + D / ε) + 4) ^ 2 / ε ^ 2) := by
  set S := lastStage D ε
  set ℓ := Real.logb 2 (1 + D / ε) + 4
  set B := 4 * D / ε
  set C := 288 * K * σ ^ 2 * (S + 1) ^ 2 / ε ^ 2
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := by positivity
  have hℓ : (S : ℝ) + 1 ≤ ℓ := lastStage_le hD hε
  have hlog0 : 0 ≤ Real.logb 2 (1 + D / ε) :=
    Real.logb_nonneg (by norm_num) (by have h0 : 0 ≤ D / ε := (by positivity); linarith)
  have hℓ4 : 4 ≤ ℓ := by simp only [ℓ]; linarith
  have hterm : ∀ u, u ≤ S → (stageLength K σ D ε u : ℝ) ≤
      ((if u = 0 then 2 * S + 7 else 5 : ℕ) : ℝ) * (2 + (1 / 2) ^ u * B + C) :=
    fun u hu => stageLength_le hD hε hK hu
  have hsum : (∑ u ∈ Finset.range (S + 1), (stageLength K σ D ε u : ℝ)) ≤
      (7 * S + 7) * (2 + C) + (2 * S + 12) * B := by
    rw [Finset.sum_range_succ']
    have hrest : (∑ u ∈ Finset.range S, (stageLength K σ D ε (u + 1) : ℝ)) ≤
        ∑ u ∈ Finset.range S, (5 * (2 + C) + 5 * B * (1 / 2) ^ (u + 1)) := by
      apply Finset.sum_le_sum
      intro u hu
      have h := hterm (u + 1) (by simp at hu; omega)
      simp only [Nat.add_one_ne_zero, ite_false, Nat.cast_ofNat] at h
      linarith
    have hgeo : (∑ u ∈ Finset.range S, ((1 : ℝ) / 2) ^ (u + 1)) ≤ 1 := by
      have := sum_geometric_two_le S
      have he : (∑ u ∈ Finset.range S, ((1 : ℝ) / 2) ^ (u + 1)) =
          (1 / 2) * ∑ u ∈ Finset.range S, ((1 : ℝ) / 2) ^ u := by
        rw [Finset.mul_sum]; congr 1; funext u; ring
      rw [he]; linarith
    have hsplit : (∑ u ∈ Finset.range S, (5 * (2 + C) + 5 * B * (1 / 2) ^ (u + 1))) =
        S * (5 * (2 + C)) + 5 * B * ∑ u ∈ Finset.range S, ((1 : ℝ) / 2) ^ (u + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    have h0 := hterm 0 (Nat.zero_le _)
    simp only [ite_true, pow_zero, one_mul] at h0
    push_cast at h0
    have h5B : 5 * B * ∑ u ∈ Finset.range S, ((1 : ℝ) / 2) ^ (u + 1) ≤ 5 * B :=
      by nlinarith
    nlinarith
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hcube : ((S : ℝ) + 1) ^ 3 ≤ ℓ ^ 3 := pow_le_pow_left₀ (by positivity) hℓ 3
  have hKσ : 0 ≤ K * σ ^ 2 / ε ^ 2 := by positivity
  have hC' : (7 * S + 7) * C = 2016 * (K * σ ^ 2 / ε ^ 2) * ((S : ℝ) + 1) ^ 3 := by
    simp only [C]; ring
  have hgoal : (Real.logb 2 (1 + D / ε) + 4) * (16 + 20 * D / ε +
      2048 * K * σ ^ 2 * (Real.logb 2 (1 + D / ε) + 4) ^ 2 / ε ^ 2) =
      16 * ℓ + 5 * ℓ * B + 2048 * (K * σ ^ 2 / ε ^ 2) * ℓ ^ 3 := by
    simp only [ℓ, B]; ring
  rw [hgoal]
  have hB' : (2 * S + 12) * B ≤ 5 * ℓ * B := by
    apply mul_le_mul_of_nonneg_right _ hB
    linarith
  have hC'' : 2016 * (K * σ ^ 2 / ε ^ 2) * ((S : ℝ) + 1) ^ 3 ≤ 2048 * (K * σ ^ 2 / ε ^ 2) * ℓ ^ 3 := by
    have := mul_le_mul_of_nonneg_left hcube hKσ
    nlinarith
  nlinarith

end OracleTemplate.RecursiveAnchorKm
