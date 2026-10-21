import LongTails.Proofs.UntiedReverseFisherBranches
import Mathlib.Tactic

namespace LongTails.Proofs.UntiedReverseFisherBudget

open LongTails.Proofs.UntiedReverseFisherPhases
open LongTails.Proofs.UntiedReverseFisherBranches
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory

noncomputable def logArgument (d B δ ε : ℝ) : ℝ := 10 ^ 20 * d * (1 + B) / (δ * ε)

noncomputable def iterations (d s B δ ε : ℝ) : ℕ :=
  ⌈10 ^ 16 / max (s ^ 2) ε * Real.log (logArgument d B δ ε)⌉₊

section

variable {d B δ ε : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hε : 0 < ε) (hε1 : ε ≤ 1)

include hd hB hδ hδ1 hε hε1

omit hε1 in
lemma logArgument_ge : 10 ^ 20 * (1 + B) / ε ≤ logArgument d B δ ε := by
  unfold logArgument
  rw [div_le_div_iff₀ hε (by positivity)]
  have h1 : 10 ^ 20 * (1 + B) * (δ * ε) ≤ 10 ^ 20 * (1 + B) * ε := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  have h2 : 10 ^ 20 * (1 + B) * ε ≤ 10 ^ 20 * d * (1 + B) * ε := by
    have : 0 ≤ 10 ^ 20 * (1 + B) * ε := by positivity
    nlinarith
  linarith

omit hδ1 hε1 in
lemma logArgument_pos : 0 < logArgument d B δ ε := by unfold logArgument; positivity

lemma logArgument_ge_dδ : d / δ ≤ logArgument d B δ ε := by
  unfold logArgument
  rw [div_le_div_iff₀ hδ (by positivity)]
  have hd0 : 0 ≤ d := by linarith
  have : d * (δ * ε) ≤ d * 1 := mul_le_mul_of_nonneg_left (by nlinarith) hd0
  nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 10 ^ 20 * (1 + B) by nlinarith) (mul_nonneg hd0 hδ.le)]

lemma log_main_ge : 12 ≤ Real.log (logArgument d B δ ε) := by
  rw [Real.le_log_iff_exp_le (logArgument_pos hd hB hδ hε)]
  have h1 : Real.exp 12 ≤ 10 ^ 20 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc Real.exp 1 ^ 12 ≤ 2.7182818286 ^ 12 := pow_le_pow_left₀ (Real.exp_pos 1).le this.le 12
      _ ≤ 10 ^ 20 := by norm_num
  have h3 : (10 : ℝ) ^ 20 ≤ 10 ^ 20 * (1 + B) / ε := by
    rw [le_div_iff₀ hε]; nlinarith
  linarith [logArgument_ge hd hB hδ hδ1 hε]

omit hd hB hδ hδ1 hε hε1 in
lemma log_le_main {x : ℝ} (hx : 0 < x) (hle : x ≤ logArgument d B δ ε) :
    Real.log x ≤ Real.log (logArgument d B δ ε) :=
  Real.log_le_log hx hle

omit hd hB hδ hδ1 hε hε1 in
lemma log_le_main_two {x : ℝ} (hx : 0 < x) (hle : x ≤ logArgument d B δ ε ^ 2) :
    Real.log x ≤ 2 * Real.log (logArgument d B δ ε) := by
  have h := Real.log_le_log hx hle
  rw [Real.log_pow] at h
  push_cast at h
  linarith

end

lemma ceil_le_of_le {x c : ℝ} (hc : 0 ≤ c) (h : x ≤ c) : (⌈x⌉₊ : ℝ) ≤ c + 1 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [Nat.ceil_eq_zero.mpr hx]; simp; linarith
  · exact (Nat.ceil_lt_add_one hx.le).le.trans (by linarith)

lemma log_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have := Real.add_one_le_exp x
  rw [Real.log_le_iff_le_exp (by linarith)]
  linarith

section Bounds

variable {d s B δ ε a : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hε : 0 < ε) (hε1 : ε ≤ 1)

include hd hB hδ hδ1 hε hε1

lemma warm_le : (warmIterations B : ℝ) ≤ 74 * Real.log (logArgument d B δ ε) := by
  have hΛ := log_main_ge hd hB hδ hδ1 hε hε1
  have harg : 1 + B / centreThreshold ≤ logArgument d B δ ε := by
    refine le_trans ?_ (logArgument_ge hd hB hδ hδ1 hε)
    unfold centreThreshold
    rw [le_div_iff₀ hε]
    nlinarith
  have hl := log_le_main (by unfold centreThreshold; positivity) harg
  have h := ceil_le_of_le (x := 512 / 7 * Real.log (1 + B / centreThreshold))
    (c := 512 / 7 * Real.log (logArgument d B δ ε)) (by positivity) (by linarith)
  unfold warmIterations
  linarith

lemma centre_le : (centreIterations B ε : ℝ) ≤ 74 * Real.log (logArgument d B δ ε) := by
  have hΛ := log_main_ge hd hB hδ hδ1 hε hε1
  have hs := Real.sqrt_pos.mpr hε
  have hse : ε ≤ Real.sqrt ε := by
    rw [Real.le_sqrt hε.le hε.le]; nlinarith
  have harg : 1 + 2 * B / Real.sqrt ε ≤ logArgument d B δ ε := by
    refine le_trans ?_ (logArgument_ge hd hB hδ hδ1 hε)
    have h1 : 2 * B / Real.sqrt ε ≤ 2 * B / ε := div_le_div_of_nonneg_left (by positivity) hε hse
    have h2 : 1 + 2 * B / ε ≤ 10 ^ 20 * (1 + B) / ε := by
      rw [show 1 + 2 * B / ε = (ε + 2 * B) / ε by field_simp]
      exact div_le_div_of_nonneg_right (by nlinarith) hε.le
    linarith
  have hl := log_le_main (by positivity) harg
  have h := ceil_le_of_le (x := 512 / 7 * Real.log (1 + 2 * B / Real.sqrt ε))
    (c := 512 / 7 * Real.log (logArgument d B δ ε)) (by positivity) (by linarith)
  unfold centreIterations
  linarith

lemma small_le (hs : 0 ≤ s) (hsa : s ≤ 2 * a) (haε : a ^ 2 ≤ ε / 10 ^ 5) :
    (smallIterations ε : ℝ) ≤ 10 ^ 16 / max (s ^ 2) ε * Real.log (logArgument d B δ ε) := by
  have hΛ := log_main_ge hd hB hδ hδ1 hε hε1
  have hM : max (s ^ 2) ε = ε := by
    apply max_eq_right; nlinarith [mul_self_le_mul_self hs hsa]
  rw [hM]
  have harg : 16 / ε ≤ logArgument d B δ ε := by
    refine le_trans ?_ (logArgument_ge hd hB hδ hδ1 hε)
    exact div_le_div_of_nonneg_right (by nlinarith) hε.le
  have hl := log_le_main (by positivity) harg
  have h := ceil_le_of_le (x := 204800 / ε * Real.log (16 / ε))
    (c := 204800 / ε * Real.log (logArgument d B δ ε)) (by positivity)
    (mul_le_mul_of_nonneg_left hl (by positivity))
  unfold smallIterations
  have h2 : 204800 / ε * Real.log (logArgument d B δ ε) + 1 ≤
      10 ^ 16 / ε * Real.log (logArgument d B δ ε) := by
    have h3 : 1 ≤ 1 / ε * Real.log (logArgument d B δ ε) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hε]; nlinarith
    have : 10 ^ 16 / ε * Real.log (logArgument d B δ ε) =
        204800 / ε * Real.log (logArgument d B δ ε) +
          (10 ^ 16 - 204800) * (1 / ε * Real.log (logArgument d B δ ε)) := by ring
    nlinarith
  linarith

omit hd hB hδ hδ1 hε1 in
lemma inv_strength_le (hs : 0 ≤ s) (hsa : s ≤ 2 * a) (ha1 : a ≤ 1 / 2)
    (haε : ε / 10 ^ 5 < a ^ 2) : 1 / signalStrength a ≤ 125 * 10 ^ 8 / max (s ^ 2) ε := by
  have ha2 : 0 < a ^ 2 := lt_of_le_of_lt (by positivity) haε
  have hM : max (s ^ 2) ε ≤ 10 ^ 5 * a ^ 2 := by
    apply max_le
    · nlinarith [mul_self_le_mul_self hs hsa]
    · nlinarith
  have hMpos : 0 < max (s ^ 2) ε := lt_of_lt_of_le hε (le_max_right _ _)
  have ha4 : a ^ 2 ≤ 1 / 4 := by nlinarith
  unfold signalStrength
  rw [one_div_div, div_le_div_iff₀ ha2 hMpos]
  nlinarith

set_option maxHeartbeats 1000000 in
lemma positive_le (hs : 0 ≤ s) (hsa : s ≤ 2 * a) (ha1 : a ≤ 1 / 2)
    (haε : ε / 10 ^ 5 < a ^ 2) :
    (positiveIterations a ε (δ / d) B : ℝ) ≤
      10 ^ 16 / max (s ^ 2) ε * Real.log (logArgument d B δ ε) := by
  have hΛ := log_main_ge hd hB hδ hδ1 hε hε1
  set Λ := Real.log (logArgument d B δ ε) with hΛdef
  have ha2 : 0 < a ^ 2 := lt_of_le_of_lt (by positivity) haε
  have ha : 0 < a := by nlinarith [sq_nonneg a]
  have hm := strength_pos ha
  have hm1 := (strength_le ha).2
  set m := signalStrength a with hmdef
  have hinv := inv_strength_le hε hs hsa ha1 haε
  set M := max (s ^ 2) ε with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le hε (le_max_right _ _)
  have hM1 : M ≤ 1 := max_le (by nlinarith [mul_self_le_mul_self hs hsa]) hε1
  have hT0 := warm_le hd hB hδ hδ1 hε hε1
  set T0 := warmIterations B with hT0def
  have hd0 : 0 < d := by linarith
  have hdδ : 0 < d / δ := by positivity
  have hlogdδ : Real.log (d / δ) ≤ Λ :=
    log_le_main hdδ (logArgument_ge_dδ hd hB hδ hδ1 hε hε1)
  have hdδ1 : 1 ≤ d / δ := by rw [le_div_iff₀ hδ]; linarith
  set P := 1 / (δ / d) * (16 / 15) ^ T0 with hP
  have hPeq : P = d / δ * (16 / 15) ^ T0 := by rw [hP, one_div_div]
  have hP1 : 1 ≤ P := by
    rw [hPeq]; nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 16 / 15 by norm_num) (n := T0)]
  have hlogP : Real.log P ≤ 6 * Λ := by
    rw [hPeq, Real.log_mul hdδ.ne' (by positivity), Real.log_pow]
    have h1 : Real.log (16 / 15) ≤ 1 / 15 := by
      have := log_one_add_le (x := 1 / 15) (by norm_num); norm_num at this ⊢; linarith
    have h2 : (T0 : ℝ) * Real.log (16 / 15) ≤ 74 * Λ * (1 / 15) :=
      mul_le_mul hT0 h1 (Real.log_nonneg (by norm_num)) (by positivity)
    linarith
  set u1 := (29 / 32) ^ T0 * (δ / d) with hu1
  have hu10 : 0 < u1 := by positivity
  have hu1le : u1 ≤ 1 := by
    rw [hu1]
    have h1 : (29 / 32 : ℝ) ^ T0 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : δ / d ≤ 1 := by rw [div_le_one hd0]; linarith
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 29 / 32 by norm_num) T0]
  have hlogu1 : Real.log (1 / u1) ≤ 9 * Λ := by
    have he : 1 / u1 = (32 / 29) ^ T0 * (d / δ) := by
      rw [hu1]; field_simp; rw [← mul_pow]; norm_num
    rw [he, Real.log_mul (by positivity) hdδ.ne', Real.log_pow]
    have h1 : Real.log (32 / 29) ≤ 3 / 29 := by
      have := log_one_add_le (x := 3 / 29) (by norm_num); norm_num at this ⊢; linarith
    have h2 : (T0 : ℝ) * Real.log (32 / 29) ≤ 74 * Λ * (3 / 29) :=
      mul_le_mul hT0 h1 (Real.log_nonneg (by norm_num)) (by positivity)
    nlinarith
  have hn1 : (phaseOne a P : ℝ) ≤ 1024 * Λ / m + 1 := by
    unfold phaseOne
    have h := ceil_le_of_le (x := 8 / (3 * (1 / 64) * m) * Real.log P) (c := 1024 * Λ / m)
      (by positivity) (by
        rw [show 8 / (3 * (1 / 64) * m) = 512 / 3 / m by field_simp; ring]
        rw [show 1024 * Λ / m = 512 / 3 / m * (6 * Λ) by field_simp; ring]
        exact mul_le_mul_of_nonneg_left hlogP (by positivity))
    exact h
  have hsqm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsqm1 : Real.sqrt m ≤ 1 := by rw [Real.sqrt_le_one]; exact hm1
  have hL0 : 0 < floorLevel a u1 P := by unfold floorLevel; positivity
  have harg2 : Real.sqrt m / (8 * floorLevel a u1 P) ≤ 1 / u1 * (1 + P) := by
    have h1u : 1 ≤ 1 / u1 := by rw [le_div_iff₀ hu10]; linarith
    unfold floorLevel
    rcases min_cases u1 (Real.sqrt m / (6 * (1 + P))) with ⟨hmin, -⟩ | ⟨hmin, -⟩
    · rw [hmin, div_le_iff₀ (by positivity)]
      have : 1 / u1 * (1 + P) * (8 * u1) = 8 * (1 + P) := by field_simp
      rw [this]; linarith
    · rw [hmin, div_le_iff₀ (by positivity)]
      have : 1 / u1 * (1 + P) * (8 * (Real.sqrt m / (6 * (1 + P)))) =
          1 / u1 * (8 * Real.sqrt m / 6) := by field_simp
      rw [this]
      have h7 := mul_le_mul_of_nonneg_right h1u (show 0 ≤ 8 * Real.sqrt m / 6 by positivity)
      linarith
  have hlog2 : Real.log (Real.sqrt m / (8 * floorLevel a u1 P)) ≤ 16 * Λ := by
    have h1 := Real.log_le_log (by positivity) harg2
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    have h2 : Real.log (1 + P) ≤ 1 + 6 * Λ := by
      have h3 : Real.log (1 + P) ≤ Real.log (2 * P) := Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul (by norm_num) (by positivity)] at h3
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    linarith
  have hn2 : (phaseTwo a u1 P : ℝ) ≤ 8192 * Λ / m + 1 := by
    unfold phaseTwo
    exact ceil_le_of_le (by positivity) (by
      rw [show 8 / (1 / 64 * m) = 512 / m by field_simp; ring]
      rw [show 8192 * Λ / m = 512 / m * (16 * Λ) by field_simp; ring]
      exact mul_le_mul_of_nonneg_left hlog2 (by positivity))
  have hsε := Real.sqrt_pos.mpr hε
  have hse : ε ≤ Real.sqrt ε := by rw [Real.le_sqrt hε.le hε.le]; nlinarith
  have harg3 : 300 * (1 + 600 * a) / (m * Real.sqrt ε) ≤ logArgument d B δ ε ^ 2 := by
    have hX := logArgument_ge hd hB hδ hδ1 hε
    have hX2 : (10 ^ 20 / ε) ^ 2 ≤ logArgument d B δ ε ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      refine le_trans ?_ hX
      exact div_le_div_of_nonneg_right (by nlinarith) hε.le
    refine le_trans ?_ hX2
    have hinvε : 1 / m ≤ 125 * 10 ^ 8 / ε := by
      refine hinv.trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) hε (le_max_right _ _)
    have h1 : 300 * (1 + 600 * a) ≤ 90300 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have h2 : 1 ≤ 125 * 10 ^ 8 / ε * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]
      rw [div_le_div_iff₀ hm hε] at hinvε; linarith
    have h3 : (10 ^ 20 / ε) ^ 2 * (m * Real.sqrt ε) ≥ (10 ^ 20 / ε) ^ 2 * (m * ε) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hse hm.le) (by positivity)
    have h4 : (10 ^ 20 / ε) ^ 2 * (m * ε) = 10 ^ 40 / ε * m := by field_simp
    have h5 : 10 ^ 40 / ε * m ≥ 90300 := by
      have : 10 ^ 40 / ε * m = (10 ^ 40 / (125 * 10 ^ 8)) * (125 * 10 ^ 8 / ε * m) := by
        field_simp
      rw [this]; nlinarith
    linarith
  have hlog3 := log_le_main_two (by positivity) harg3
  have hn3 : (phaseThree a ε : ℝ) ≤ 122880 * Λ / m + 1 := by
    unfold phaseThree
    exact ceil_le_of_le (by positivity) (by
      rw [show 960 / (1 / 64 * m) = 61440 / m by field_simp; ring]
      rw [show 122880 * Λ / m = 61440 / m * (2 * Λ) by field_simp; ring]
      exact mul_le_mul_of_nonneg_left hlog3 (by positivity))
  unfold positiveIterations postIterations
  push_cast
  rw [← hT0def]
  have hΛm : Λ ≤ Λ / m := by rw [le_div_iff₀ hm]; nlinarith
  have htot : (T0 : ℝ) + phaseOne a P + phaseTwo a u1 P + phaseThree a ε ≤ 132200 * Λ / m := by
    have : 132200 * Λ / m = 1024 * Λ / m + 8192 * Λ / m + 122880 * Λ / m + 104 * (Λ / m) := by ring
    nlinarith
  have hfin : 132200 * Λ / m ≤ 10 ^ 16 / M * Λ := by
    have : 132200 * Λ / m = 132200 * Λ * (1 / m) := by ring
    rw [this]
    calc 132200 * Λ * (1 / m) ≤ 132200 * Λ * (125 * 10 ^ 8 / M) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ 10 ^ 16 / M * Λ := by
        rw [show 132200 * Λ * (125 * 10 ^ 8 / M) = (132200 * 125 * 10 ^ 8) / M * Λ by ring]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (by norm_num) hMpos.le
  have hu1' : (29 / 32) ^ T0 * (δ / d) = u1 := rfl
  rw [hu1', ← hP]
  linarith

end Bounds

end LongTails.Proofs.UntiedReverseFisherBudget
