import LongTails.Proofs.StochasticEnvelopeExecution
import LongTails.Proofs.StochasticEnvelopeDebiasing
import LongTails.Proofs.StochasticEnvelopeSampling

namespace LongTails.Proofs.StochasticEnvelopeWork

lemma log_one_add_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log (1 + x) ≤ 1 + Real.log x := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma confidence_count_upper {η H A B : ℝ} (K : ℕ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlog : Real.log (K + 1 : ℝ) ≤ A * H) (hinv : -Real.log η ≤ B * H) :
    ((7 + ⌈2 * Real.log (1 + (K + 1 : ℝ) / η)⌉₊ + 1 : ℕ) : ℝ) ≤
      11 + 2 * A * H + 2 * B * H := by
  have hx : 1 ≤ (K + 1 : ℝ) / η := (le_div_iff₀ hη).2 (by linarith [Nat.cast_nonneg (α := ℝ) K])
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (1 + (K + 1 : ℝ) / η) by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
  have hl := log_one_add_le ((K + 1 : ℝ) / η) hx
  rw [Real.log_div (by positivity) hη.ne'] at hl
  push_cast
  linarith

lemma approximation_log_bounds {κ a m : ℝ} (hκ : 2 ≤ κ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hm : 1 ≤ m) (ell : ℕ) :
    let W := 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m
    let H := W * ((ell : ℝ) + 1)
    let n := m * (2 : ℝ) ^ ell
    1 ≤ W ∧ W ≤ H ∧ 1 ≤ n ∧ Real.log κ ≤ H ∧ Real.log (1 / a) ≤ H ∧
      Real.log m ≤ W ∧ Real.log n ≤ H := by
  dsimp only
  have hk0 : 0 < κ := by linarith
  have hm0 : 0 < m := by linarith
  have hk : 0 ≤ Real.log (1025 * κ) := Real.log_nonneg (by nlinarith)
  have ha' : 0 ≤ Real.log (1 / a) := Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using ha1))
  have hm' : 0 ≤ Real.log m := Real.log_nonneg hm
  have hpow : 1 ≤ (2 : ℝ) ^ ell := one_le_pow₀ (by norm_num)
  have hw : 1 ≤ 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m := by linarith
  have hwh : 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m ≤
      (1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m) * ((ell : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) ell]
  have hkl := Real.log_le_log hk0 (show κ ≤ 1025 * κ by linarith)
  refine ⟨hw, hwh, ?_, by linarith, by linarith, by linarith, ?_⟩
  · nlinarith
  · rw [Real.log_mul hm0.ne' (by positivity), Real.log_pow]
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α := ℝ) ell)]

lemma approximation_confidence_counts {κ a m p : ℝ} (hκ : 2 ≤ κ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hm : 1 ≤ m) (hsm : Real.sqrt κ ≤ m) (hp : 1 < p) (hp2 : p ≤ 2)
    (ell : ℕ) :
    let n := m * (2 : ℝ) ^ ell
    let W := 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m
    let H := W * ((ell : ℝ) + 1)
    let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
    let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
    let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    (N + 1 : ℝ) ≤ 20 * m * W ∧ (J : ℝ) ≤ 8 * H ∧
      ((7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊ + 1 : ℕ) : ℝ) ≤ 512 * H ∧
      ((7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊ + 1 : ℕ) : ℝ) ≤ 128 * H := by
  let n := m * (2 : ℝ) ^ ell
  let W := 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m
  let H := W * ((ell : ℝ) + 1)
  let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
  let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
  let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  obtain ⟨hW, hWH, hn, hkH, haH, hmW, hnH⟩ := approximation_log_bounds hκ ha ha1 hm ell
  change 1 ≤ W at hW
  change W ≤ H at hWH
  change 1 ≤ n at hn
  change Real.log κ ≤ H at hkH
  change Real.log (1 / a) ≤ H at haH
  change Real.log m ≤ W at hmW
  change Real.log n ≤ H at hnH
  have hH : 1 ≤ H := hW.trans hWH
  have hk0 : 0 < κ := by linarith
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := by linarith
  have hla : -Real.log a = Real.log (1 / a) := by simp
  have hla0 : 0 ≤ -Real.log a := by rw [hla]; exact Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using ha1))
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlk0 : 0 ≤ Real.log κ := Real.log_nonneg (by linarith)
  have hN : (N + 1 : ℝ) ≤ 20 * m * W := by
    have hlog0 : 0 ≤ Real.log (1 + 1024 * κ) := Real.log_nonneg (by nlinarith)
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 17 * Real.sqrt κ * Real.log (1 + 1024 * κ) by positivity)
    have hl := Real.log_le_log (show 0 < 1 + 1024 * κ by positivity)
      (show 1 + 1024 * κ ≤ 1025 * κ by linarith)
    have hlW : Real.log (1025 * κ) ≤ W := by
      dsimp [W]; linarith [Real.log_nonneg hm, hla0]
    have hb := mul_le_mul_of_nonneg_right hsm hlog0
    have hb' := mul_le_mul_of_nonneg_left (hl.trans hlW) hm0.le
    have hmw : 1 ≤ m * W := by nlinarith
    change (N : ℝ) < _ at hc
    nlinarith
  have hJ : (J : ℝ) ≤ 8 * H := by
    have hx : 1 ≤ n / a := (le_div_iff₀ ha).2 (by linarith)
    have hl := log_one_add_le (n / a) hx
    rw [Real.log_div hn0.ne' ha.ne'] at hl
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (1 + n / a) by
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
    change (J : ℝ) < _ at hc
    rw [← hla] at haH
    linarith
  have hη₀0 : 0 < η₀ := by dsimp [η₀]; positivity
  have hη₁0 : 0 < η₁ := by dsimp [η₁]; positivity
  have he0 : -Real.log η₀ = 128 * Real.log 2 + 12 * Real.log κ +
      (2 * p) * (-Real.log a) + (2 * (p - 1)) * Real.log n := by
    dsimp [η₀]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_rpow hk0,
      Real.log_rpow ha, Real.log_rpow hn0]
    ring
  have he1 : -Real.log η₁ = 32 * Real.log 2 + p * (-Real.log a) + (p - 1) * Real.log n := by
    dsimp [η₁]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_rpow ha, Real.log_rpow hn0]
    ring
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hη₀1 : η₀ ≤ 1 := by
    apply (Real.log_le_log_iff hη₀0 (by norm_num : (0 : ℝ) < 1)).mp
    rw [Real.log_one]; nlinarith only [he0, hl20, hlk0, mul_nonneg (show 0 ≤ p by linarith) hla0,
      mul_nonneg (show 0 ≤ p - 1 by linarith) hln0]
  have hη₁1 : η₁ ≤ 1 := by
    apply (Real.log_le_log_iff hη₁0 (by norm_num : (0 : ℝ) < 1)).mp
    rw [Real.log_one]; nlinarith only [he1, hl20, mul_nonneg (show 0 ≤ p by linarith) hla0,
      mul_nonneg (show 0 ≤ p - 1 by linarith) hln0]
  have he0H : -Real.log η₀ ≤ 146 * H := by
    rw [he0]
    rw [← hla] at haH
    nlinarith only [hH, hkH, haH, hnH, hl21, mul_nonneg (show 0 ≤ 2 - p by linarith) hla0,
      mul_nonneg (show 0 ≤ 2 - p by linarith) hln0]
  have he1H : -Real.log η₁ ≤ 35 * H := by
    rw [he1]
    rw [← hla] at haH
    nlinarith only [hH, hkH, haH, hnH, hl21, mul_nonneg (show 0 ≤ 2 - p by linarith) hla0,
      mul_nonneg (show 0 ≤ 2 - p by linarith) hln0]
  have hlN : Real.log (N + 1 : ℝ) ≤ 22 * H := by
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    rw [Real.log_mul (by positivity) hW0.ne', Real.log_mul (by norm_num) hm0.ne'] at hl
    linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 20), Real.log_le_self hW0.le]
  have hlJ : Real.log (J + 1 : ℝ) ≤ 10 * H := by
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < J + 1)
      (show (J + 1 : ℝ) ≤ 9 * H by linarith)
    rw [Real.log_mul (by norm_num) hH0.ne'] at hl
    linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 9), Real.log_le_self hH0.le]
  exact ⟨hN, hJ, (confidence_count_upper N hη₀0 hη₀1 hlN he0H).trans (by linarith),
    (confidence_count_upper J hη₁0 hη₁1 hlJ he1H).trans (by linarith)⟩

lemma approximation_work_bound {κ a m p : ℝ} (hκ : 2 ≤ κ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hm : 1 ≤ m) (hsm : Real.sqrt κ ≤ m) (hp : 1 < p) (hp2 : p ≤ 2)
    (ell : ℕ) :
    let q := p / (p - 1)
    let n := m * (2 : ℝ) ^ ell
    let W := 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m
    let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
    let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
    let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
    let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
    let b := ⌈(1073741824 : ℝ) ^ q⌉₊
    let K := ⌈(268435456 : ℝ) ^ q * (Real.sqrt κ + n + 1)⌉₊
    8 * (b + 1 : ℝ) * (pilotReplicas + 1 : ℝ) * (N + 1 : ℝ) +
      (K : ℝ) * (innerReplicas + 1 : ℝ) * J ≤
      (2 : ℝ) ^ (30 * q + 20) * m * W ^ 2 * (2 : ℝ) ^ ell * ((ell : ℝ) + 1) ^ 2 := by
  let q := p / (p - 1)
  let n := m * (2 : ℝ) ^ ell
  let W := 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m
  let H := W * ((ell : ℝ) + 1)
  let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
  let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
  let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
  let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
  let b := ⌈(1073741824 : ℝ) ^ q⌉₊
  let K := ⌈(268435456 : ℝ) ^ q * (Real.sqrt κ + n + 1)⌉₊
  let C := (1073741824 : ℝ) ^ q
  obtain ⟨hN, hJ, hP, hI⟩ := approximation_confidence_counts hκ ha ha1 hm hsm hp hp2 ell
  change (N + 1 : ℝ) ≤ 20 * m * W at hN
  change (J : ℝ) ≤ 8 * H at hJ
  change ((pilotReplicas + 1 : ℕ) : ℝ) ≤ 512 * H at hP
  change ((innerReplicas + 1 : ℕ) : ℝ) ≤ 128 * H at hI
  push_cast at hP hI
  obtain ⟨hW, hWH, hn, _, _, _, _⟩ := approximation_log_bounds hκ ha ha1 hm ell
  change 1 ≤ W at hW
  change W ≤ H at hWH
  change 1 ≤ n at hn
  have hH : 1 ≤ H := hW.trans hWH
  have hq : 1 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hC : 1 ≤ C := Real.one_le_rpow (by norm_num) (by linarith)
  have hC0 : 0 ≤ C := by linarith
  have hmn : m ≤ n := by
    dsimp [n]
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := ell)]
  have hb : (b + 1 : ℝ) ≤ 3 * C := by
    have hh := Nat.ceil_lt_add_one hC0
    change (b : ℝ) < C + 1 at hh
    linarith
  have hK : (K : ℝ) ≤ 4 * C * n := by
    let C' := (268435456 : ℝ) ^ q
    have hC' : 1 ≤ C' := Real.one_le_rpow (by norm_num) (by linarith)
    have hcmp : C' ≤ C := Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
    have hpos : 0 ≤ C' * (Real.sqrt κ + n + 1) := by positivity
    have hh := Nat.ceil_lt_add_one hpos
    change (K : ℝ) < C' * (Real.sqrt κ + n + 1) + 1 at hh
    have hb' : C' * (Real.sqrt κ + n + 1) ≤ C * (3 * n) := by
      apply mul_le_mul hcmp ?_ (by positivity) hC0
      linarith
    nlinarith only [hh, hb', hC, hn, mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hn)]
  have hfirst : 8 * (b + 1 : ℝ) * (pilotReplicas + 1 : ℝ) * (N + 1 : ℝ) ≤
      245760 * C * n * H ^ 2 := by
    calc
      _ ≤ 8 * (3 * C) * (512 * H) * (20 * m * W) := by gcongr
      _ = 245760 * C * m * W * H := by ring
      _ ≤ 245760 * C * n * H * H := by gcongr
      _ = _ := by ring
  have hsecond : (K : ℝ) * (innerReplicas + 1 : ℝ) * J ≤ 4096 * C * n * H ^ 2 := by
    calc
      _ ≤ (4 * C * n) * (128 * H) * (8 * H) := by gcongr
      _ = _ := by ring
  have htotal : 8 * (b + 1 : ℝ) * (pilotReplicas + 1 : ℝ) * (N + 1 : ℝ) +
      (K : ℝ) * (innerReplicas + 1 : ℝ) * J ≤ 1048576 * C * n * H ^ 2 := by
    nlinarith only [hfirst, hsecond, mul_nonneg (mul_nonneg hC0 (by linarith : 0 ≤ n)) (sq_nonneg H)]
  change _ ≤ (2 : ℝ) ^ (30 * q + 20) * m * W ^ 2 * (2 : ℝ) ^ ell * ((ell : ℝ) + 1) ^ 2
  refine htotal.trans_eq ?_
  have he : C = (2 : ℝ) ^ (30 * q) := by
    dsimp [C]
    rw [show (1073741824 : ℝ) = (2 : ℝ) ^ (30 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), he]
  norm_num only [Real.rpow_ofNat, Real.rpow_natCast, Nat.reducePow]
  dsimp [n, H]
  ring

open MeasureTheory ProbabilityTheory in
lemma three_level_work {v : unitInterval} {t C : ℝ} (ht : 0 < t)
    (hv : (v : ℝ) = 1 / 2 + t / 16) (hC : 0 ≤ C) (work : ℕ → ℝ)
    (hw0 : ∀ n, 0 ≤ work n)
    (hw : ∀ n, work n ≤ C * (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2) :
    Integrable (fun n => work 0 + work (n + 1) + work n) (geometricMeasure v) ∧
      (∫ n, work 0 + work (n + 1) + work n ∂geometricMeasure v) ≤ 10240 * C / t ^ 3 := by
  have hh (n : ℕ) : work 0 + work (n + 1) + work n ≤
      (10 * C) * (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2 := by
    have hs := StochasticEnvelopeDebiasing.shifted_quadratic_work n
    have hn1 : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hn2 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hn : 1 ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2 := by nlinarith
    have hwzero : work 0 ≤ C := by simpa using hw 0
    have hwshift := hw (n + 1)
    push_cast at hwshift
    have hshift := mul_le_mul_of_nonneg_left hs hC
    have hbase := mul_le_mul_of_nonneg_left hn hC
    nlinarith [hw n]
  obtain ⟨hi, hb⟩ := StochasticEnvelopeDebiasing.linear_level_work ht hv (10 * C) (by positivity)
    (fun n => work 0 + work (n + 1) + work n) (fun n => add_nonneg (add_nonneg (hw0 0) (hw0 (n + 1))) (hw0 n)) hh
  refine ⟨hi, hb.trans_eq ?_⟩
  ring

open MeasureTheory ProbabilityTheory
open LongTails.Algorithms.StochasticEnvelopeProgram
lemma tuned_approximation_work {κ a m p : ℝ} (hκ : 2 ≤ κ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hm : 1 ≤ m) (hsm : Real.sqrt κ ≤ m) (hp : 1 < p) (hp2 : p ≤ 2)
    (ell : ℕ) :
    ((approximationTuning κ p a (m * (2 : ℝ) ^ ell)).calls : ℝ) ≤
      (2 : ℝ) ^ (30 * (p / (p - 1)) + 20) * m *
        (1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m) ^ 2 *
          (2 : ℝ) ^ ell * ((ell : ℝ) + 1) ^ 2 := by
  have hh := approximation_work_bound hκ ha ha1 hm hsm hp hp2 ell
  convert hh using 1
  simp only [approximationTuning, ApproximationTuning.calls, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat]
  ring

lemma tuned_envelope_work {κ a m p t : ℝ} (hκ : 2 ≤ κ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hm : 1 ≤ m) (hsm : Real.sqrt κ ≤ m) (hp : 1 < p) (hp2 : p ≤ 2)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    let cost := fun ell => (approximationTuning κ p a (m * (2 : ℝ) ^ ell)).calls
    let P := geometricMeasure (levelProbability t ht.le ht1)
    Integrable (fun n => ((cost 0 + cost (n + 1) + cost n : ℕ) : ℝ)) P ∧
      (∫ n, ((cost 0 + cost (n + 1) + cost n : ℕ) : ℝ) ∂P) ≤
        10240 * ((2 : ℝ) ^ (30 * (p / (p - 1)) + 20) * m *
          (1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m) ^ 2) / t ^ 3 := by
  have hh := three_level_work ht (v := levelProbability t ht.le ht1) rfl
    (show 0 ≤ (2 : ℝ) ^ (30 * (p / (p - 1)) + 20) * m *
      (1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m) ^ 2 by positivity)
    (fun ell => ((approximationTuning κ p a (m * (2 : ℝ) ^ ell)).calls : ℝ))
    (fun _ => Nat.cast_nonneg _) (tuned_approximation_work hκ ha ha1 hm hsm hp hp2)
  simpa only [Nat.cast_add] using hh

lemma affine_scale_attenuation {q Q t r m H : ℝ} (hq : 0 < q) (hqQ : q ≤ Q)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hH : 1 ≤ H)
    (hc : (2 : ℝ) ^ (28 : ℝ) * q / t ≤ H) :
    (2 : ℝ) ^ (28 : ℝ) * q / t * m ^ (-(r / q)) ≤
      (H * m ^ (-(1 / Q))) ^ r := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hHr : H ≤ H ^ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH hr
  have hfrac : r / Q ≤ r / q := div_le_div_of_nonneg_left (zero_le_one.trans hr) hq hqQ
  have hpow : m ^ (-(r / q)) ≤ m ^ (-(r / Q)) :=
    Real.rpow_le_rpow_of_exponent_le hm (neg_le_neg hfrac)
  calc
    _ ≤ H ^ r * m ^ (-(r / Q)) := mul_le_mul (hc.trans hHr) hpow (by positivity) (by positivity)
    _ = (H * m ^ (-(1 / Q))) ^ r := by
      rw [Real.mul_rpow hH0 (by positivity), ← Real.rpow_mul hm0]
      congr 2
      ring
lemma attenuation_positive {H m Q : ℝ} (hH : 0 < H) (hm : 0 < m) :
    0 < H * m ^ (-(1 / Q)) := by positivity

lemma attenuation_le_one {H m Q : ℝ} (hm : 0 < m)
    (hH : H ≤ m ^ (1 / Q)) : H * m ^ (-(1 / Q)) ≤ 1 := by
  rw [Real.rpow_neg hm.le]
  exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos hm _)).2 (by simpa using hH)

lemma one_step_noise_work_cancellation {H m Q : ℝ} (hH : 0 < H) (hm : 0 < m) (hQ : 0 < Q) :
    (m * H) * (H * m ^ (-(1 / Q))) ^ Q = H ^ (1 + Q) := by
  rw [Real.mul_rpow hH.le (by positivity), ← Real.rpow_mul hm.le,
    show -(1 / Q) * Q = -1 by field_simp, Real.rpow_neg_one,
    Real.rpow_add hH, Real.rpow_one]
  field_simp

lemma initial_batch_noise_cancellation {B q Q S : ℝ} (hB : 1 ≤ B) (hq : 0 < q)
    (hqQ : q ≤ Q) (hS : 0 ≤ S) :
    B * (S / B ^ (1 / q)) ^ Q ≤ S ^ Q := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hQ : 0 < Q := hq.trans_le hqQ
  have he : 1 ≤ Q / q := (le_div_iff₀ hq).2 (by simpa using hqQ)
  have hp : B ≤ B ^ (Q / q) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB he
  rw [Real.div_rpow hS (by positivity), ← Real.rpow_mul hB0.le,
    show 1 / q * Q = Q / q by ring]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (Q / q))).2
  convert mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hS Q) using 1
  ring

lemma iterated_noise_work_cancellation {B S H m Q : ℝ} (hS : 0 ≤ S)
    (hH : 0 < H) (hm : 0 < m) (hQ : 0 < Q) (i : ℕ) :
    (B * (m * H) ^ i) * (S * (H * m ^ (-(1 / Q))) ^ i) ^ Q =
      B * S ^ Q * (H ^ (1 + Q)) ^ i := by
  have hrho : 0 ≤ H * m ^ (-(1 / Q)) := by positivity
  calc
    _ = B * S ^ Q * ((m * H) * (H * m ^ (-(1 / Q))) ^ Q) ^ i := by
      rw [Real.mul_rpow hS (pow_nonneg hrho i), ← Real.rpow_pow_comm hrho, mul_pow]
      ring
    _ = _ := by rw [one_step_noise_work_cancellation hH hm hQ]


lemma depth_exponent_drift (d : ℕ) (hd : 1 ≤ d) :
    (1 + 1 / (d : ℝ) ^ 2) ^ d ≤ 2 ∧
      (1 + 1 / (d : ℝ) ^ 2) ^ d ≤ 1 + 2 / d := by
  by_cases hd1 : d = 1
  · subst d; norm_num
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hd0 : 0 < (d : ℝ) := by linarith
  let x := 1 / (d : ℝ) ^ 2
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) ^ 2)).2
    nlinarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) d
  have hbase : (1 + x) * (1 - x) ≤ 1 := by nlinarith
  have hpow : ((1 + x) * (1 - x)) ^ d ≤ 1 :=
    pow_le_one₀ (mul_nonneg (by positivity) (by linarith)) hbase
  rw [mul_pow] at hpow
  have hh := (mul_le_mul_of_nonneg_left hb (pow_nonneg (by positivity : 0 ≤ 1 + x) d)).trans hpow
  have hx : (d : ℝ) * x = 1 / d := by dsimp [x]; field_simp
  have hh' : (1 + x) ^ d * (1 - 1 / d) ≤ 1 := by
    rw [mul_neg, hx] at hh
    simpa only [sub_eq_add_neg] using hh
  have hratio : (1 + x) ^ d ≤ (d : ℝ) / (d - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)).2
    have hm := mul_le_mul_of_nonneg_right hh' hd0.le
    have he : (1 - 1 / (d : ℝ)) * d = d - 1 := by field_simp
    rw [mul_assoc, he] at hm
    simpa only [one_mul] using hm
  refine ⟨hratio.trans ?_, hratio.trans ?_⟩
  · apply (div_le_iff₀ (by linarith : 0 < (d : ℝ) - 1)).2
    linarith
  · apply (div_le_iff₀ (by linarith : 0 < (d : ℝ) - 1)).2
    apply (mul_le_mul_iff_left₀ hd0).mp
    field_simp
    nlinarith
lemma level_conjugate_range {q t : ℝ} (hq : 2 ≤ q) (ht : 0 ≤ t)
    (i d : ℕ) (hi : i ≤ d) :
    2 ≤ q * (1 + t) ^ i ∧ q ≤ q * (1 + t) ^ i ∧
      q * (1 + t) ^ i ≤ q * (1 + t) ^ d := by
  have hpow : 1 ≤ (1 + t) ^ i := one_le_pow₀ (by linarith)
  have hq0 : 0 ≤ q := by linarith
  have hqi : q ≤ q * (1 + t) ^ i := by nlinarith
  exact ⟨hq.trans hqi, hqi, mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + t) hi) hq0⟩

lemma conjugate_moment_range {q : ℝ} (hq : 2 ≤ q) :
    1 < q / (q - 1) ∧ q / (q - 1) ≤ 2 ∧
      (q / (q - 1)) / (q / (q - 1) - 1) = q := by
  have hd : 0 < q - 1 := by linarith
  refine ⟨(lt_div_iff₀ hd).2 (by linarith), (div_le_iff₀ hd).2 (by linarith), ?_⟩
  field_simp
  ring

lemma level_smoothness_ratio {L k : ℝ} (hL : 0 < L) (hk : 0 < k) (i : ℕ) :
    (L / k ^ i + L / k ^ (i + 1)) / (L / k ^ (i + 1)) = k + 1 := by
  rw [pow_succ]
  field_simp


lemma initial_batch_relative {σ κ H q : ℝ} (hσ : 0 ≤ σ) (hκ : 2 ≤ κ)
    (hH : 1 ≤ H) (hq : 0 < q) :
    let B := ⌈(4 * (1 + σ) * κ ^ 2 * H) ^ q⌉₊
    0 < B ∧ 4 * (B : ℝ) ^ (-(1 / q)) * σ ≤ κ ^ (-2 : ℝ) / H ∧
      (B : ℝ) ≤ 2 * (4 * (1 + σ) * κ ^ 2 * H) ^ q := by
  let A := 4 * (1 + σ) * κ ^ 2 * H
  let B := ⌈A ^ q⌉₊
  have hk0 : 0 < κ := by linarith
  have hH0 : 0 < H := by linarith
  have hA1 : 1 ≤ A := by dsimp [A]; nlinarith [mul_nonneg hσ (sq_nonneg κ), mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg κ)]
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hpow : 1 ≤ A ^ q := Real.one_le_rpow hA1 hq.le
  have hceil : A ^ q ≤ (B : ℝ) := Nat.le_ceil _
  have hB0 : 0 < (B : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < A ^ q) hceil
  have hB : 0 < B := by exact_mod_cast hB0
  have hc := Real.rpow_le_rpow (by positivity : 0 ≤ A ^ q) hceil (by positivity : 0 ≤ 1 / q)
  rw [← Real.rpow_mul hA.le, mul_one_div_cancel hq.ne', Real.rpow_one] at hc
  refine ⟨hB, ?_, ?_⟩
  · rw [Real.rpow_neg hB0.le, Real.rpow_neg hk0.le, Real.rpow_two]
    apply (le_div_iff₀ hH0).2
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hk0)).mp
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hB0 (1 / q))).mp
    have ht : 4 * σ * κ ^ 2 * H ≤ (B : ℝ) ^ (1 / q) := by
      apply le_trans ?_ hc
      dsimp [A]
      nlinarith [mul_nonneg (sq_nonneg κ) hH0.le]
    convert ht using 1 <;> field_simp
  · have hu := Nat.ceil_lt_add_one (show 0 ≤ A ^ q by positivity)
    change (B : ℝ) < A ^ q + 1 at hu
    linarith

lemma overhead_work_domination {q W : ℝ} (hq : 2 ≤ q) (hW : 2 + q ≤ W) :
    let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
    (2 : ℝ) ^ (60 * q + 50) * q ^ 2 * A ^ 2 * W ^ 12 ≤ W ^ A := by
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  have hW4 : 4 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hqp : 0 ≤ 1 + q := by linarith
  have hcub : 1 + q ≤ (1 + q) ^ 3 := by
    calc
      _ = (1 + q) * 1 := by ring
      _ ≤ (1 + q) * (1 + q) ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) hqp
      _ = _ := by ring
  have hA : 30 * q + 65 ≤ A := by dsimp [A]; norm_num; nlinarith
  have hpower : (2 : ℝ) ^ (60 * q + 90) ≤ W ^ (30 * q + 45) := by
    calc
      _ = ((2 : ℝ) ^ (2 : ℝ)) ^ (30 * q + 45) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) (by norm_num; exact hW4) (by linarith)
  have hpoly : q ^ 2 * A ^ 2 * W ^ 12 ≤ (2 : ℝ) ^ (40 : ℝ) * W ^ (20 : ℝ) := by
    dsimp [A]
    simp only [mul_pow, ← pow_mul, Nat.reduceMul, Real.rpow_ofNat]
    calc
      _ ≤ W ^ 2 * (1099511627776 * W ^ 6) * W ^ 12 := by gcongr <;> linarith
      _ = _ := by ring
  calc
    _ = (2 : ℝ) ^ (60 * q + 50) * (q ^ 2 * A ^ 2 * W ^ 12) := by ring
    _ ≤ (2 : ℝ) ^ (60 * q + 50) * ((2 : ℝ) ^ (40 : ℝ) * W ^ (20 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (2 : ℝ) ^ (60 * q + 90) * W ^ (20 : ℝ) := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ W ^ (30 * q + 45) * W ^ (20 : ℝ) := mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = W ^ (30 * q + 65) := by rw [← Real.rpow_add hW0]; congr 1; ring
    _ ≤ W ^ A := Real.rpow_le_rpow_of_exponent_le (by linarith) hA

section SlotWork
open LongTails.Algorithms.StochasticEnvelopeProgram StochasticEnvelopeExecution
variable {S : Type*} [MeasurableSpace S]
lemma slot_work_integral (P : Measure S) [IsProbabilityMeasure P]
    {cost : S → ℕ} (hi : Integrable (fun s => (cost s : ℝ)) P)
    (n : ℕ) :
    let R := Measure.infinitePi fun _ : ℕ => P
    Integrable (fun ξ : ℕ → S => (slotCalls (fun j => cost (ξ j)) n 0 : ℝ)) R ∧
      (∫ ξ : ℕ → S, (slotCalls (fun j => cost (ξ j)) n 0 : ℝ) ∂R) =
        (n : ℝ) * ∫ s, (cost s : ℝ) ∂P := by
  have hcoord (j : ℕ) : Integrable (fun ξ : ℕ → S => (cost (ξ j) : ℝ))
      (Measure.infinitePi fun _ : ℕ => P) := (measurePreserving_eval_infinitePi (fun _ : ℕ => P) j).integrable_comp_of_integrable hi
  have hmean (j : ℕ) : (∫ ξ : ℕ → S, (cost (ξ j) : ℝ) ∂Measure.infinitePi fun _ : ℕ => P) =
      ∫ s, (cost s : ℝ) ∂P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => P) j).hasLaw.integral_comp hi.aestronglyMeasurable
  simp only [slotCalls_sum, Nat.zero_add, Nat.cast_sum]
  refine ⟨integrable_finsetSum _ (fun j _ => hcoord j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hcoord j)]
  simp only [hmean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma random_slot_work (P : Measure S) [IsProbabilityMeasure P]
    (Q : Measure ℕ) {cost : S → ℕ}
    (hc : Measurable cost) (hi : Integrable (fun s => (cost s : ℝ)) P)
    (count : ℕ → ℕ) (hn : Integrable (fun n => (count n : ℝ)) Q) :
    let R := Measure.infinitePi fun _ : ℕ => P
    let W := fun w : ℕ × (ℕ → S) => (slotCalls (fun j => cost (w.2 j)) (count w.1) 0 : ℝ)
    Integrable W (Q.prod R) ∧
      (∫ w, W w ∂Q.prod R) = (∫ n, (count n : ℝ) ∂Q) * (∫ s, (cost s : ℝ) ∂P) := by
  let R := Measure.infinitePi fun _ : ℕ => P
  let W := fun w : ℕ × (ℕ → S) => (slotCalls (fun j => cost (w.2 j)) (count w.1) 0 : ℝ)
  have hW : Measurable W := by
    apply measurable_from_prod_countable_right
    intro n
    simp only [W, slotCalls_sum, Nat.zero_add, Nat.cast_sum]
    apply Finset.measurable_sum
    intro j hj
    fun_prop
  have hsection (n : ℕ) : Integrable (fun ξ => W (n, ξ)) R := (slot_work_integral P hi (count n)).1
  have hnorm (n : ℕ) : (∫ ξ, ‖W (n, ξ)‖ ∂R) = (count n : ℝ) * ∫ s, (cost s : ℝ) ∂P := by
    have hnonneg (ξ : ℕ → S) : 0 ≤ W (n, ξ) := Nat.cast_nonneg _
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
    exact (slot_work_integral P hi (count n)).2
  have hWi : Integrable W (Q.prod R) := (integrable_prod_iff hW.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall hsection, by simpa only [hnorm] using hn.mul_const (∫ s, (cost s : ℝ) ∂P)⟩
  refine ⟨hWi, ?_⟩
  rw [integral_prod W hWi]
  have hsectionMean (n : ℕ) : (∫ ξ, W (n, ξ) ∂R) =
      (count n : ℝ) * ∫ s, (cost s : ℝ) ∂P := (slot_work_integral P hi (count n)).2
  simp_rw [hsectionMean]
  exact integral_mul_const _ _

end SlotWork

lemma recovery_work_bound {κ n a η q : ℝ} (hn : 1 ≤ n)
    (ha : 0 < a) (ha1 : a ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hq : 0 ≤ q) :
    let W := 1 + Real.log n + Real.log (1 / a) + Real.log (1 / η)
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    let K := ⌈(268435456 : ℝ) ^ q * (Real.sqrt κ + n + 1)⌉₊
    ((K * (7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η)⌉₊ + 1) * J : ℕ) : ℝ) ≤
      128 * (268435456 : ℝ) ^ q * (Real.sqrt κ + n + 1) * W ^ 2 := by
  let W := 1 + Real.log n + Real.log (1 / a) + Real.log (1 / η)
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  let C := (268435456 : ℝ) ^ q
  let K := ⌈C * (Real.sqrt κ + n + 1)⌉₊
  dsimp only
  simp only [Nat.cast_mul]
  change (K : ℝ) * ((7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η)⌉₊ + 1 : ℕ) : ℝ) * J ≤
    128 * C * (Real.sqrt κ + n + 1) * W ^ 2
  have hln := Real.log_nonneg hn
  have hla := Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using ha1) : 1 ≤ 1 / a)
  have hle := Real.log_nonneg ((le_div_iff₀ hη).2 (by simpa using hη1) : 1 ≤ 1 / η)
  have hW : 1 ≤ W := by dsimp [W]; linarith
  have hJ : (J : ℝ) ≤ 3 * W := by
    have hx : 1 ≤ n / a := (le_div_iff₀ ha).2 (by linarith)
    have hl := log_one_add_le (n / a) hx
    rw [Real.log_div (by linarith : n ≠ 0) ha.ne'] at hl
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (1 + n / a) by
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
    change (J : ℝ) < _ at hc
    simp only [one_div, Real.log_inv] at hla hle ⊢
    dsimp [W]
    simp only [one_div, Real.log_inv]
    linarith
  have hlog : Real.log (J + 1 : ℝ) ≤ 3 * W := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < (J : ℝ) + 1 by positivity)
    linarith
  have hinv : -Real.log η ≤ 1 * W := by
    dsimp [W]; simp only [one_div, Real.log_inv] at *; linarith
  have hrep := confidence_count_upper J hη hη1 hlog hinv
  have hrep' : ((7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η)⌉₊ + 1 : ℕ) : ℝ) ≤ 19 * W := by
    linarith
  have hC : 1 ≤ C := Real.one_le_rpow (by norm_num) hq
  have hsize : 1 ≤ Real.sqrt κ + n + 1 := by linarith [Real.sqrt_nonneg κ]
  have hprod : 1 ≤ C * (Real.sqrt κ + n + 1) := by nlinarith
  have hK : (K : ℝ) ≤ 2 * C * (Real.sqrt κ + n + 1) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ C * (Real.sqrt κ + n + 1) by positivity)
    change (K : ℝ) < _ at hh
    nlinarith
  calc
    _ ≤ (2 * C * (Real.sqrt κ + n + 1)) * (19 * W) * (3 * W) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ C * (Real.sqrt κ + n + 1) by positivity) (sq_nonneg W)]

lemma geometric_depth_tuning {T : ℝ} (hT : 1 ≤ T) (d : ℕ) (hd : 1 ≤ d) :
    let k := (2 * T) ^ (1 / (d : ℝ))
    1 < k ∧ k ^ d = 2 * T ∧ (k + 1) ^ d ≤ (2 : ℝ) ^ d * (2 * T) := by
  let k := (2 * T) ^ (1 / (d : ℝ))
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hk : 1 < k := Real.one_lt_rpow (by linarith) (by positivity)
  have he : k ^ d = 2 * T := by
    dsimp [k]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 2 * T)]
    rw [one_div_mul_cancel hd'.ne', Real.rpow_one]
  refine ⟨hk, he, ?_⟩
  calc
    (k + 1) ^ d ≤ (2 * k) ^ d := by gcongr; linarith
    _ = (2 : ℝ) ^ d * (2 * T) := by rw [mul_pow, he]

lemma depth_smoothness_endpoint {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hT : 1 ≤ L * R ^ 2 / ε) (d : ℕ) (hd : 1 ≤ d) :
    L / (((2 * (L * R ^ 2 / ε)) ^ (1 / (d : ℝ))) ^ d) = ε / (2 * R ^ 2) := by
  rw [(geometric_depth_tuning hT d hd).2.1]
  field_simp

lemma depth_conjugates {q : ℝ} (hq : 2 ≤ q) (d : ℕ) (hd : 1 ≤ d) (i : ℕ) (hi : i ≤ d) :
    2 ≤ q * (1 + 1 / (d : ℝ) ^ 2) ^ i ∧
      q * (1 + 1 / (d : ℝ) ^ 2) ^ i ≤ 2 * q := by
  have hbase : 1 ≤ 1 + 1 / (d : ℝ) ^ 2 := by
    have := one_div_nonneg.mpr (sq_nonneg (d : ℝ)); linarith
  have hp : 1 ≤ (1 + 1 / (d : ℝ) ^ 2) ^ i := one_le_pow₀ hbase
  have hp' : (1 + 1 / (d : ℝ) ^ 2) ^ i ≤ 2 :=
    (pow_le_pow_right₀ hbase hi).trans (depth_exponent_drift d hd).1
  constructor <;> nlinarith

lemma rpow_le_one_add_rpow {x r Q : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hrQ : r ≤ Q) :
    x ^ r ≤ 1 + x ^ Q := by
  by_cases hx1 : x ≤ 1
  · have hh : x ^ r ≤ 1 := Real.rpow_le_one hx hx1 hr
    linarith [Real.rpow_nonneg hx Q]
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hrQ
    linarith

lemma variable_moment_work {B S H m Q r D : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hH : 0 < H) (hm : 0 < m) (hQ : 0 < Q) (hr : 0 ≤ r) (hrQ : r ≤ Q)
    (hD : 0 < D) (i : ℕ) :
    (B * (m * H) ^ i) * ((S * (H * m ^ (-(1 / Q))) ^ i) / D) ^ r ≤
      B * (m * H) ^ i + (B * S ^ Q * (H ^ (1 + Q)) ^ i) / D ^ Q := by
  have hscale : 0 ≤ S * (H * m ^ (-(1 / Q))) ^ i := by positivity
  have hh := mul_le_mul_of_nonneg_left
    (rpow_le_one_add_rpow (div_nonneg hscale hD.le) hr hrQ)
    (show 0 ≤ B * (m * H) ^ i by positivity)
  calc
    _ ≤ (B * (m * H) ^ i) * (1 + ((S * (H * m ^ (-(1 / Q))) ^ i) / D) ^ Q) := hh
    _ = _ := by
      rw [Real.div_rpow hscale hD.le, mul_add, mul_one, ← mul_div_assoc,
        iterated_noise_work_cancellation hS hH hm hQ i]

lemma base_work_tuning {κ H q Q : ℝ} (hκ : 2 ≤ κ) (hH : 1 ≤ H)
    (hq : 2 ≤ q) (hQ : 0 < Q) (hQq : Q ≤ 2 * q) :
    let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
    1 ≤ m ∧ Real.sqrt κ ≤ m ∧ m ≤ 2 * Real.sqrt κ * H ^ (4 * q) ∧
      0 < H * m ^ (-(1 / Q)) ∧ H * m ^ (-(1 / Q)) ≤ 1 := by
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  have hk : 1 ≤ Real.sqrt κ := (Real.le_sqrt (by norm_num) (by linarith)).2 (by norm_num; linarith)
  have hpow : 1 ≤ H ^ (4 * q) := Real.one_le_rpow hH (by linarith)
  have hsize : 1 ≤ Real.sqrt κ * H ^ (4 * q) := by nlinarith
  have hm : Real.sqrt κ * H ^ (4 * q) ≤ m := Nat.le_ceil _
  have hm1 : 1 ≤ m := hsize.trans hm
  have hms : Real.sqrt κ ≤ m := le_trans (by nlinarith) hm
  have hmupper : m ≤ 2 * Real.sqrt κ * H ^ (4 * q) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt κ * H ^ (4 * q) by positivity)
    change m < _ at hh
    nlinarith
  have hmH : H ^ (4 * q) ≤ m := le_trans (by nlinarith) hm
  have hHpow : H ≤ m ^ (1 / Q) := by
    calc
      H = H ^ (1 : ℝ) := (Real.rpow_one H).symm
      _ ≤ H ^ (4 * q / Q) := Real.rpow_le_rpow_of_exponent_le hH
        ((le_div_iff₀ hQ).2 (by nlinarith))
      _ = (H ^ (4 * q)) ^ (1 / Q) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ H)]; congr 1; ring
      _ ≤ m ^ (1 / Q) := Real.rpow_le_rpow (by positivity) hmH (by positivity)
  exact ⟨hm1, hms, hmupper, attenuation_positive (by linarith) (by linarith),
    attenuation_le_one (by linarith) hHpow⟩

lemma attenuated_sequence_moment {q Q t r m H S : ℝ} (hq : 0 < q) (hqQ : q ≤ Q)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hH : 1 ≤ H) (hS : 0 ≤ S)
    (hc : (2 : ℝ) ^ (28 : ℝ) * q / t ≤ H) (i : ℕ) :
    let ρ := H * m ^ (-(1 / Q))
    (2 : ℝ) ^ (28 : ℝ) * q / t * m ^ (-(r / q)) * (S * ρ ^ i) ^ r ≤
      (S * ρ ^ (i + 1)) ^ r := by
  let ρ := H * m ^ (-(1 / Q))
  have hρ : 0 ≤ ρ := by positivity
  have hh := mul_le_mul_of_nonneg_right (affine_scale_attenuation hq hqQ hr hm hH hc)
    (Real.rpow_nonneg (show 0 ≤ S * ρ ^ i by positivity) r)
  refine hh.trans_eq ?_
  change ρ ^ r * (S * ρ ^ i) ^ r = (S * ρ ^ (i + 1)) ^ r
  rw [← Real.mul_rpow hρ (by positivity), pow_succ]
  congr 1
  ring

lemma depth_choice {M q : ℝ} (hM : 4 ≤ M) (hq : 2 ≤ q) :
    let d := ⌈Real.sqrt (Real.log M)⌉₊
    1 ≤ d ∧ (d : ℝ) ≤ 2 + q + Real.log M ∧
      Real.log M / (d : ℝ) ≤ Real.sqrt (Real.log M) ∧
      (d : ℝ) ≤ 1 + Real.sqrt (Real.log M) := by
  let d := ⌈Real.sqrt (Real.log M)⌉₊
  have hl : 0 < Real.log M := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (Real.log M) := Real.sqrt_pos.2 hl
  have hd : 1 ≤ d := Nat.ceil_pos.2 hs
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlow : Real.sqrt (Real.log M) ≤ (d : ℝ) := Nat.le_ceil _
  have hu := Nat.ceil_lt_add_one (Real.sqrt_nonneg (Real.log M))
  change (d : ℝ) < _ at hu
  have hsq := Real.sq_sqrt hl.le
  have hsupper : Real.sqrt (Real.log M) ≤ 1 + Real.log M := by nlinarith [sq_nonneg (Real.sqrt (Real.log M) - 1)]
  refine ⟨hd, by linarith, ?_, by linarith⟩
  apply (div_le_iff₀ hd').2
  nlinarith

lemma conjugate_involution {q : ℝ} (hq : 1 < q) :
    (q / (q - 1)) / (q / (q - 1) - 1) = q := by
  have hne : q - 1 ≠ 0 := by linarith
  have hden : q / (q - 1) - 1 = 1 / (q - 1) := by field_simp; ring
  rw [hden]
  field_simp

lemma geometric_moment_recurrence {q t : ℝ} (hq : 2 ≤ q) (ht : 0 ≤ t) (i : ℕ) :
    let Q := fun j : ℕ => q * (1 + t) ^ j
    let p := fun j : ℕ => Q j / (Q j - 1)
    p (i + 1) = (p i / (p i - 1) * (1 + t)) / (p i / (p i - 1) * (1 + t) - 1) := by
  let Q := fun j : ℕ => q * (1 + t) ^ j
  have hQi : 1 < Q i := by
    have hh : 1 ≤ (1 + t) ^ i := one_le_pow₀ (by linarith)
    dsimp [Q]
    nlinarith
  dsimp only
  rw [conjugate_involution hQi]
  simp only [pow_succ]
  congr 1 <;> ring

lemma attenuated_relative_bound {κ H ρ : ℝ} (hκ : 0 < κ) (hH : 1 ≤ H)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (i : ℕ) :
    0 < (κ ^ (-2 : ℝ) / H) * ρ ^ i ∧
      (κ ^ (-2 : ℝ) / H) * ρ ^ i ≤ κ ^ (-2 : ℝ) := by
  have hH0 : 0 < H := by linarith
  have ha : 0 < κ ^ (-2 : ℝ) / H := by positivity
  have ha' : κ ^ (-2 : ℝ) / H ≤ κ ^ (-2 : ℝ) := div_le_self (by positivity) hH
  have hp : ρ ^ i ≤ 1 := pow_le_one₀ hρ.le hρ1
  exact ⟨mul_pos ha (pow_pos hρ i), (mul_le_of_le_one_right ha.le hp).trans ha'⟩

lemma overhead_moment_domination {q Q W : ℝ} (hq : 2 ≤ q) (hW : 2 + q ≤ W)
    (hQq : Q ≤ 2 * q) (d : ℕ) (hdW : (d : ℝ) ≤ W) :
    (2 : ℝ) ^ (28 : ℝ) * Q / (1 / (d : ℝ) ^ 2) ≤
      W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ (3 : ℕ)) := by
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ (3 : ℕ)
  have hW4 : 4 ≤ W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hA : 18 ≤ A := by
    have hh : 1 ≤ (1 + q) ^ 3 := one_le_pow₀ (by linarith)
    dsimp [A]
    norm_num
    nlinarith
  have hconst : (2 : ℝ) ^ (29 : ℕ) ≤ W ^ 15 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hW4 15
    norm_num at hh ⊢
    linarith
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  calc
    _ = (2 : ℝ) ^ (28 : ℕ) * Q * (d : ℝ) ^ 2 := by norm_num
    _ ≤ (2 : ℝ) ^ (29 : ℕ) * q * W ^ 2 := by
      have hsq := pow_le_pow_left₀ hd0 hdW 2
      norm_num
      nlinarith [mul_le_mul hQq hsq (sq_nonneg (d : ℝ)) (by linarith : 0 ≤ 2 * q)]
    _ ≤ W ^ 15 * W * W ^ 2 := by gcongr; linarith
    _ = W ^ (18 : ℝ) := by norm_num; ring
    _ ≤ W ^ A := Real.rpow_le_rpow_of_exponent_le hW1 hA

lemma relative_log_identity {κ H m Q : ℝ} (hκ : 0 < κ) (hH : 0 < H) (hm : 0 < m) (i : ℕ) :
    Real.log (1 / ((κ ^ (-2 : ℝ) / H) * (H * m ^ (-(1 / Q))) ^ i)) =
      2 * Real.log κ + (1 - (i : ℝ)) * Real.log H + ((i : ℝ) / Q) * Real.log m := by
  rw [one_div, Real.log_inv,
    Real.log_mul (by positivity : κ ^ (-2 : ℝ) / H ≠ 0) (by positivity),
    Real.log_div (by positivity : κ ^ (-2 : ℝ) ≠ 0) hH.ne',
    Real.log_rpow hκ, Real.log_pow,
    Real.log_mul hH.ne' (by positivity : m ^ (-(1 / Q)) ≠ 0), Real.log_rpow hm]
  ring
lemma tuning_log_bound {κ H m Q q A W : ℝ} (hκ : 2 ≤ κ) (hH : 1 ≤ H)
    (hm : 1 ≤ m) (hQ : 1 ≤ Q) (hq : 2 ≤ q) (hA : 1024 ≤ A) (hW : 4 ≤ W)
    (hklog : Real.log κ ≤ W) (hHlog : Real.log H ≤ A * W)
    (hmlog : Real.log m ≤ 6 * q * A * W) (i : ℕ) (hi : (i : ℝ) ≤ W) :
    1 + Real.log (1025 * κ) +
      Real.log (1 / ((κ ^ (-2 : ℝ) / H) * (H * m ^ (-(1 / Q))) ^ i)) + Real.log m ≤
      32 * q * A * W ^ 2 := by
  rw [relative_log_identity (by linarith) (by linarith) (by linarith),
    Real.log_mul (by norm_num : (1025 : ℝ) ≠ 0) (by linarith : κ ≠ 0)]
  have hconst : Real.log 1025 ≤ 1024 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1025)]
  have hlogH := Real.log_nonneg hH
  have hlogm := Real.log_nonneg hm
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have hiQ : (i : ℝ) / Q ≤ W :=
    (div_le_self hi0 hQ).trans hi
  have hterm := mul_le_mul hiQ hmlog hlogm (by positivity : 0 ≤ W)
  have hHterm : (1 - (i : ℝ)) * Real.log H ≤ A * W := by
    nlinarith
  have hqA : 2048 ≤ q * A := by nlinarith
  have hqAW : 8192 ≤ q * A * W := by nlinarith
  have hmulW := mul_le_mul_of_nonneg_left (show 1 ≤ W by linarith) (show 0 ≤ q * A * W by positivity)
  have hmulA := mul_le_mul_of_nonneg_right (show 1 ≤ q by linarith) (show 0 ≤ A * W by positivity)
  have hmul3 := mul_le_mul_of_nonneg_right (show 3 ≤ q * A * W by linarith) (show 0 ≤ W by positivity)
  nlinarith

lemma base_work_log_bound {κ H m q A W : ℝ} (hκ : 0 < κ) (hH : 0 < H)
    (hm : 1 ≤ m) (hq : 2 ≤ q) (hA : 1 ≤ A) (hW : 1 ≤ W)
    (hklog : Real.log κ ≤ W) (hHlog : Real.log H ≤ A * W)
    (hmupper : m ≤ 2 * Real.sqrt κ * H ^ (4 * q)) :
    Real.log m ≤ 6 * q * A * W := by
  have hl := Real.log_le_log (by linarith : 0 < m) hmupper
  rw [Real.log_mul (by positivity : 2 * Real.sqrt κ ≠ 0) (by positivity),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
    Real.log_sqrt hκ.le, Real.log_rpow hH] at hl
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_left hHlog (show 0 ≤ 4 * q by linarith)
  have hqA : 2 ≤ q * A := by nlinarith
  have hqAW : 2 * W ≤ q * A * W := mul_le_mul_of_nonneg_right hqA (by linarith)
  nlinarith

lemma overhead_log_bound {W A : ℝ} (hW : 1 ≤ W) (hA : 0 ≤ A) :
    Real.log (W ^ A) ≤ A * W := by
  rw [Real.log_rpow (by linarith : 0 < W)]
  apply mul_le_mul_of_nonneg_left _ hA
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < W)]

lemma envelope_work_domination {q qi W m X : ℝ} (hq : 2 ≤ q) (hqi : qi ≤ 2 * q)
    (hW : 2 + q ≤ W) (hm : 0 ≤ m) (hX : 0 ≤ X) (d : ℕ) (hd : (d : ℝ) ≤ W)
    (hXW : X ≤ 32 * q * ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3) * W ^ 2) :
    10240 * ((2 : ℝ) ^ (30 * qi + 20) * m * X ^ 2) / (1 / (d : ℝ) ^ 2) ^ 3 ≤
      m * W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3) := by
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  have hA : 0 ≤ A := by positivity
  have hW1 : 1 ≤ W := by linarith
  have hp : (2 : ℝ) ^ (30 * qi + 20) ≤ (2 : ℝ) ^ (60 * q + 20) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hWpow : W ^ 10 ≤ W ^ 12 := pow_le_pow_right₀ hW1 (by omega)
  have he : (2 : ℝ) ^ (60 * q + 50) = 1073741824 * (2 : ℝ) ^ (60 * q + 20) := by
    rw [show 60 * q + 50 = (30 : ℝ) + (60 * q + 20) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hh : 10240 * ((2 : ℝ) ^ (30 * qi + 20) * m * X ^ 2) / (1 / (d : ℝ) ^ 2) ^ 3 ≤
      m * ((2 : ℝ) ^ (60 * q + 50) * q ^ 2 * A ^ 2 * W ^ 12) := by
    calc
      _ = 10240 * ((2 : ℝ) ^ (30 * qi + 20) * m * X ^ 2) * (d : ℝ) ^ 6 := by
        simp only [one_div, inv_pow, div_inv_eq_mul, ← pow_mul, Nat.reduceMul]
      _ ≤ 10240 * ((2 : ℝ) ^ (60 * q + 20) * m * (32 * q * A * W ^ 2) ^ 2) * W ^ 6 := by
        gcongr
      _ = 10485760 * (2 : ℝ) ^ (60 * q + 20) * m * q ^ 2 * A ^ 2 * W ^ 10 := by ring
      _ ≤ 1073741824 * (2 : ℝ) ^ (60 * q + 20) * m * q ^ 2 * A ^ 2 * W ^ 12 := by gcongr; norm_num
      _ = _ := by rw [he]; ring
  refine hh.trans ?_
  exact mul_le_mul_of_nonneg_left (overhead_work_domination hq hW) hm

lemma condition_log_bound {T M : ℝ} (hT : 1 ≤ T) (hTM : T ≤ M)
    (d : ℕ) (hd : 1 ≤ d) :
    Real.log ((2 * T) ^ (1 / (d : ℝ)) + 1) ≤ 2 + Real.log M := by
  let k := (2 * T) ^ (1 / (d : ℝ))
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hk := (geometric_depth_tuning hT d hd).1
  change 1 < k at hk
  have hklog : Real.log k ≤ Real.log (2 * T) := by
    dsimp [k]
    rw [Real.log_rpow (by linarith : 0 < 2 * T)]
    exact mul_le_of_le_one_left (Real.log_nonneg (by linarith)) (by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd')
  have hlog := Real.log_le_log (by linarith : 0 < k + 1) (show k + 1 ≤ 2 * k by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : k ≠ 0)] at hlog
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)] at hklog
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlT := Real.log_le_log (by linarith : 0 < T) hTM
  change Real.log (k + 1) ≤ _
  linarith

lemma geometric_level_work {q W κ : ℝ} (hq : 2 ≤ q) (hW : 2 + q ≤ W)
    (hκ : 2 ≤ κ) (hklog : Real.log κ ≤ W) (d : ℕ) (hd : 1 ≤ d) (hdW : (d : ℝ) ≤ W)
    (i : ℕ) (hi : i ≤ d) :
    let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
    let H := W ^ A
    let t := 1 / (d : ℝ) ^ 2
    let Q := fun j : ℕ => q * (1 + t) ^ j
    let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
    let ρ := H * m ^ (-(1 / Q d))
    let a := (κ ^ (-2 : ℝ) / H) * ρ ^ i
    let p := Q i / (Q i - 1)
    let cost := fun ell => (approximationTuning κ p a (m * (2 : ℝ) ^ ell)).calls
    ∃ ht : 0 < t, ∃ ht1 : t ≤ 1,
      Integrable (fun n => ((cost 0 + cost (n + 1) + cost n : ℕ) : ℝ))
        (geometricMeasure (levelProbability t ht.le ht1)) ∧
      (∫ n, ((cost 0 + cost (n + 1) + cost n : ℕ) : ℝ)
        ∂geometricMeasure (levelProbability t ht.le ht1)) ≤ m * H := by
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  let H := W ^ A
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun j : ℕ => q * (1 + t) ^ j
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  let a := (κ ^ (-2 : ℝ) / H) * ρ ^ i
  let p := Q i / (Q i - 1)
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity : 0 < (d : ℝ) ^ 2)).2
    nlinarith
  have hA : 1024 ≤ A := by
    have hh : 1 ≤ (1 + q) ^ 3 := one_le_pow₀ (by linarith)
    dsimp [A]; norm_num; nlinarith
  have hW1 : 1 ≤ W := by linarith
  have hH : 1 ≤ H := Real.one_le_rpow hW1 (by linarith)
  have hQd := depth_conjugates hq d hd d le_rfl
  have hQi := depth_conjugates hq d hd i hi
  change 2 ≤ Q d ∧ Q d ≤ 2 * q at hQd
  change 2 ≤ Q i ∧ Q i ≤ 2 * q at hQi
  obtain ⟨hm, hms, hmu, hρ, hρ1⟩ := base_work_tuning hκ hH hq (by linarith : 0 < Q d) hQd.2
  change 1 ≤ m at hm
  change Real.sqrt κ ≤ m at hms
  change m ≤ 2 * Real.sqrt κ * H ^ (4 * q) at hmu
  change 0 < ρ at hρ
  change ρ ≤ 1 at hρ1
  have ha := attenuated_relative_bound (by linarith : 0 < κ) hH hρ hρ1 i
  change 0 < a ∧ a ≤ κ ^ (-2 : ℝ) at ha
  have ha1 : a ≤ 1 := ha.2.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
  have hp : 1 < p ∧ p ≤ 2 := ⟨(conjugate_moment_range hQi.1).1, (conjugate_moment_range hQi.1).2.1⟩
  have hHlog : Real.log H ≤ A * W := overhead_log_bound hW1 (by linarith)
  have hmlog := base_work_log_bound (by linarith : 0 < κ) (by linarith : 0 < H)
    hm hq (by linarith : 1 ≤ A) hW1 hklog hHlog hmu
  have hiW : (i : ℝ) ≤ W := (by exact_mod_cast hi : (i : ℝ) ≤ d).trans hdW
  have hlog := tuning_log_bound hκ hH hm (by linarith : 1 ≤ Q d) hq hA (by linarith : 4 ≤ W)
    hklog hHlog hmlog i hiW
  let X := 1 + Real.log (1025 * κ) + Real.log (1 / a) + Real.log m
  change X ≤ 32 * q * A * W ^ 2 at hlog
  have hX : 0 ≤ X := by
    have h1 := Real.log_nonneg (show 1 ≤ 1025 * κ by linarith)
    have h2 := Real.log_nonneg ((le_div_iff₀ ha.1).2 (by simpa using ha1) : 1 ≤ 1 / a)
    have h3 := Real.log_nonneg hm
    dsimp [X]; linarith
  have hw := tuned_envelope_work hκ ha.1 ha1 hm hms hp.1 hp.2 ht ht1
  refine ⟨ht, ht1, hw.1, hw.2.trans ?_⟩
  have hconj : p / (p - 1) = Q i := conjugate_involution (by linarith : 1 < Q i)
  rw [hconj]
  exact envelope_work_domination hq hQi.2 hW (by linarith) hX d hdW hlog

lemma recovery_distance_ratios {ε μ d κ R : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμlower : ε / (2 * R ^ 2) ≤ μ) :
    let U := Real.sqrt (2 * ε / μ)
    let D := Real.sqrt (ε / (2 * d * μ * κ))
    0 < D ∧ U / D = 2 * Real.sqrt (d * κ) ∧
      1 / (μ * D) ≤ 2 * (R / ε) * Real.sqrt (d * κ) := by
  let U := Real.sqrt (2 * ε / μ)
  let D := Real.sqrt (ε / (2 * d * μ * κ))
  let b := Real.sqrt (d * κ)
  have hD : 0 < D := Real.sqrt_pos.2 (by positivity)
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hDsq : D ^ 2 = ε / (2 * d * μ * κ) := Real.sq_sqrt (by positivity)
  have hUsq : U ^ 2 = 2 * ε / μ := Real.sq_sqrt (by positivity)
  have hbsq : b ^ 2 = d * κ := Real.sq_sqrt (by positivity)
  have heq : (2 * b * D) ^ 2 = U ^ 2 := by
    calc
      _ = 4 * b ^ 2 * D ^ 2 := by ring
      _ = 2 * ε / μ := by rw [hbsq, hDsq]; field_simp; ring
      _ = _ := hUsq.symm
  have hUD : U = 2 * b * D := (sq_eq_sq₀ hU (by positivity)).1 heq.symm
  have hμbound : ε ≤ 2 * R ^ 2 * μ := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * R ^ 2)).1 hμlower
    nlinarith
  have hsecond : (2 * R * μ * D * b) ^ 2 = 2 * R ^ 2 * μ * ε := by
    calc
      _ = 4 * R ^ 2 * μ ^ 2 * D ^ 2 * b ^ 2 := by ring
      _ = _ := by rw [hDsq, hbsq]; field_simp; ring
  have hlin : ε ≤ 2 * R * μ * D * b := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * R ^ 2 * μ - ε by linarith) hε.le,
      show 0 ≤ 2 * R * μ * D * b by positivity]
  refine ⟨hD, ?_, ?_⟩
  · change U / D = 2 * b
    rw [hUD, mul_div_cancel_right₀ _ hD.ne']
  · change 1 / (μ * D) ≤ 2 * (R / ε) * b
    apply (div_le_iff₀ (mul_pos hμ hD)).2
    calc
      (1 : ℝ) = ε / ε := (div_self hε.ne').symm
      _ ≤ (2 * R * μ * D * b) / ε := (div_le_div_iff_of_pos_right hε).2 hlin
      _ = _ := by ring

lemma rpow_add_bound {x y Q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hQ : 1 ≤ Q) :
    (x + y) ^ Q ≤ (2 : ℝ) ^ Q * (x ^ Q + y ^ Q) := by
  have hh : (x + y) ^ Q ≤ (2 : ℝ) ^ (Q - 1) * (x ^ Q + y ^ Q) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow (⟨x, hx⟩ : NNReal) (⟨y, hy⟩ : NNReal) hQ
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma weighted_recovery_scale {C b x y r Q : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 0 ≤ r) (hrQ : r ≤ Q) (hQ : 1 ≤ Q) :
    C * (1 + (b * (x + y)) ^ r) ≤
      2 * C + (2 * b) ^ Q * (C * x ^ Q + C * y ^ Q) := by
  have hcomp := rpow_le_one_add_rpow (mul_nonneg hb (add_nonneg hx hy)) hr hrQ
  have hsplit : (b * (x + y)) ^ Q ≤ (2 * b) ^ Q * (x ^ Q + y ^ Q) := by
    rw [Real.mul_rpow hb (add_nonneg hx hy), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hb]
    have hh := mul_le_mul_of_nonneg_left (rpow_add_bound hx hy hQ) (Real.rpow_nonneg hb Q)
    nlinarith
  calc
    _ ≤ C * (2 + (2 * b) ^ Q * (x ^ Q + y ^ Q)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _ = _ := by ring

lemma normalized_noise_work {B σ Z H m q Q : ℝ} (hB : 1 ≤ B) (hσ : 0 ≤ σ)
    (hZ : 0 ≤ Z) (hH : 0 < H) (hm : 0 < m) (hq : 0 < q) (hqQ : q ≤ Q) (i : ℕ) :
    let ρ := H * m ^ (-(1 / Q))
    (B * (m * H) ^ i) * ((4 * σ * B ^ (-(1 / q)) * ρ ^ i) * Z) ^ Q ≤
      (4 * σ * Z) ^ Q * (H ^ (1 + Q)) ^ i := by
  let ρ := H * m ^ (-(1 / Q))
  have hB0 : 0 < B := by linarith
  have hS : 0 ≤ (4 * σ * Z) / B ^ (1 / q) := by positivity
  have he : (4 * σ * B ^ (-(1 / q)) * ρ ^ i) * Z =
      ((4 * σ * Z) / B ^ (1 / q)) * ρ ^ i := by
    rw [Real.rpow_neg hB0.le]
    ring
  change (B * (m * H) ^ i) * ((4 * σ * B ^ (-(1 / q)) * ρ ^ i) * Z) ^ Q ≤ _
  rw [he, iterated_noise_work_cancellation hS hH hm (hq.trans_le hqQ) i]
  exact mul_le_mul_of_nonneg_right
    (initial_batch_noise_cancellation hB hq hqQ (show 0 ≤ 4 * σ * Z by positivity)) (by positivity)

lemma noise_exponent_overhead {V M e d S : ℝ} (hV : 0 ≤ V) (hVM : V ≤ M)
    (he : 0 ≤ e) (hed : e ≤ 1 + 2 / d) (hd : 0 < d) (hS : 0 ≤ S)
    (hlog : Real.log M / d ≤ S) :
    V ^ e ≤ (1 + V) * Real.exp (2 * S) := by
  have hexp : 1 ≤ Real.exp (2 * S) := Real.one_le_exp (by positivity)
  by_cases hV1 : V ≤ 1
  · have hh := Real.rpow_le_one hV hV1 he
    nlinarith
  · have hVp : 0 < V := by linarith
    have hlV := Real.log_le_log hVp hVM
    have hratio : Real.log V / d ≤ S := ((div_le_div_iff_of_pos_right hd).2 hlV).trans hlog
    have hpow : V ^ (2 / d) ≤ Real.exp (2 * S) := by
      rw [Real.rpow_def_of_pos hVp]
      apply Real.exp_le_exp.mpr
      calc
        Real.log V * (2 / d) = 2 * (Real.log V / d) := by ring
        _ ≤ 2 * S := mul_le_mul_of_nonneg_left hratio (by norm_num)
    calc
      _ ≤ V ^ (1 + 2 / d) := Real.rpow_le_rpow_of_exponent_le (by linarith) hed
      _ = V * V ^ (2 / d) := by rw [Real.rpow_add hVp, Real.rpow_one]
      _ ≤ V * Real.exp (2 * S) := mul_le_mul_of_nonneg_left hpow hV
      _ ≤ _ := by gcongr; linarith

lemma geometric_scale_moment {q W κ : ℝ} (hq : 2 ≤ q) (hW : 2 + q ≤ W)
    (hκ : 2 ≤ κ) (d : ℕ) (hd : 1 ≤ d) (hdW : (d : ℝ) ≤ W) (i : ℕ) (hi : i < d)
    (S : ℝ) (hS : 0 ≤ S) :
    let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
    let H := W ^ A
    let t := 1 / (d : ℝ) ^ 2
    let Q := fun j : ℕ => q * (1 + t) ^ j
    let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
    let ρ := H * m ^ (-(1 / Q d))
    let r := Q (i + 1) / (Q (i + 1) - 1)
    (2 : ℝ) ^ (28 : ℝ) * Q i / t * m ^ (-(r / Q i)) * (S * ρ ^ i) ^ r ≤
      (S * ρ ^ (i + 1)) ^ r := by
  let A := (2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3
  let H := W ^ A
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun j : ℕ => q * (1 + t) ^ j
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let r := Q (i + 1) / (Q (i + 1) - 1)
  have hA : 0 ≤ A := by positivity
  have hH : 1 ≤ H := Real.one_le_rpow (by linarith) hA
  have hQd := depth_conjugates hq d hd d le_rfl
  have hQi := depth_conjugates hq d hd i (by omega)
  have hQn := depth_conjugates hq d hd (i + 1) (by omega)
  change 2 ≤ Q d ∧ Q d ≤ 2 * q at hQd
  change 2 ≤ Q i ∧ Q i ≤ 2 * q at hQi
  change 2 ≤ Q (i + 1) ∧ Q (i + 1) ≤ 2 * q at hQn
  have hqd : Q i ≤ Q d := by
    dsimp [Q]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply pow_le_pow_right₀ _ (by omega)
    have : 0 ≤ t := by dsimp [t]; positivity
    linarith
  have hm : 1 ≤ m := (base_work_tuning hκ hH hq (by linarith : 0 < Q d) hQd.2).1
  have hr : 1 ≤ r := (conjugate_moment_range hQn.1).1.le
  have hc : (2 : ℝ) ^ (28 : ℝ) * Q i / t ≤ H := overhead_moment_domination hq hW hQi.2 d hdW
  exact attenuated_sequence_moment (by linarith) hqd hr hm hH hS hc i

lemma condition_depth_log {T M S : ℝ} (hT : 1 ≤ T) (hTM : T ≤ M)
    (d : ℕ) (hd : 1 ≤ d) (hlog : Real.log M / (d : ℝ) ≤ S) :
    Real.log ((2 * T) ^ (1 / (d : ℝ)) + 1) ≤ 2 + S := by
  let k := (2 * T) ^ (1 / (d : ℝ))
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hdp : 0 < (d : ℝ) := by linarith
  have hk := (geometric_depth_tuning hT d hd).1
  change 1 < k at hk
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlT := Real.log_le_log (by linarith : 0 < T) hTM
  have hinv : 1 / (d : ℝ) ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd'
  have hklog : Real.log k ≤ 1 + S := by
    have hquot : Real.log (2 * T) / (d : ℝ) ≤ (1 + Real.log M) / (d : ℝ) := by
      apply (div_le_div_iff_of_pos_right hdp).2
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)]
      linarith
    rw [add_div] at hquot
    have he : Real.log k = Real.log (2 * T) / (d : ℝ) := by
      dsimp [k]
      rw [Real.log_rpow (by linarith : 0 < 2 * T)]
      ring
    rw [he]
    linarith
  have hbound := Real.log_le_log (by linarith : 0 < k + 1) (show k + 1 ≤ 2 * k by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : k ≠ 0)] at hbound
  change Real.log (k + 1) ≤ _
  linarith

lemma recovery_sample_log {n M d κ q qi W : ℝ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    (hd : 1 ≤ d) (hκ : 2 ≤ κ) (hq : 2 ≤ q) (hqi : 0 ≤ qi) (hqiq : qi ≤ 2 * q)
    (hW : 4 ≤ W) (hlogM : Real.log M ≤ W) (hlogκ : Real.log κ ≤ W) (hdW : d ≤ W)
    (hnupper : n ≤ 1 + (10 * M * Real.sqrt (d * κ)) ^ qi) :
    Real.log n ≤ 12 * q * W := by
  let Y := 10 * M * Real.sqrt (d * κ)
  have hsqrt : 1 ≤ Real.sqrt (d * κ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hY : 1 ≤ Y := by dsimp [Y]; nlinarith
  have hYpow : 1 ≤ Y ^ qi := Real.one_le_rpow hY hqi
  have hnY : n ≤ 2 * Y ^ qi := by change n ≤ 1 + Y ^ qi at hnupper; linarith
  have hlogd : Real.log d ≤ W := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < d)]
  have hlog10 : Real.log 10 ≤ 9 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogY : Real.log Y ≤ 5 * W := by
    dsimp [Y]
    rw [Real.log_mul (by positivity : 10 * M ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) (by linarith : M ≠ 0),
      Real.log_sqrt (by positivity : 0 ≤ d * κ),
      Real.log_mul (by linarith : d ≠ 0) (by linarith : κ ≠ 0)]
    linarith
  have hh := Real.log_le_log (by linarith : 0 < n) hnY
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
    Real.log_rpow (by linarith : 0 < Y)] at hh
  have hprod := mul_le_mul hqiq hlogY (Real.log_nonneg hY) (by linarith : 0 ≤ 2 * q)
  nlinarith

lemma recovery_work_domination {q qi W Z X : ℝ} (hq : 2 ≤ q) (hqi0 : 0 ≤ qi)
    (hqi : qi ≤ 2 * q) (hW : 2 + q ≤ W) (hZ : 0 ≤ Z) (hX : 0 ≤ X)
    (hXW : X ≤ 64 * q * ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3) * W ^ 2) :
    128 * (268435456 : ℝ) ^ qi * Z * X ^ 2 ≤
      Z * W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3) := by
  have hh := envelope_work_domination hq hqi hW hZ (show 0 ≤ X / 2 by positivity)
    1 (by norm_num; linarith) (show X / 2 ≤
      32 * q * ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3) * W ^ 2 by linarith)
  simp only [Nat.cast_one, one_pow, div_one] at hh
  have hp : (268435456 : ℝ) ^ qi ≤ (2 : ℝ) ^ (30 * qi + 20) := by
    rw [show (268435456 : ℝ) = (2 : ℝ) ^ (28 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine le_trans ?_ hh
  calc
    _ ≤ 128 * (2 : ℝ) ^ (30 * qi + 20) * Z * X ^ 2 := by gcongr
    _ ≤ _ := by nlinarith [show 0 ≤ (2 : ℝ) ^ (30 * qi + 20) * Z * X ^ 2 by positivity]

lemma attenuated_additive_le {B σ H m q Q : ℝ} (hB : 1 ≤ B) (hσ : 0 ≤ σ)
    (hq : 0 < q) (hρ : 0 ≤ H * m ^ (-(1 / Q)))
    (hρ1 : H * m ^ (-(1 / Q)) ≤ 1) (i : ℕ) :
    4 * σ * B ^ (-(1 / q)) * (H * m ^ (-(1 / Q))) ^ i ≤ 4 * σ := by
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hB (neg_nonpos.mpr (one_div_nonneg.mpr hq.le))
  have hp := pow_le_one₀ hρ hρ1 (n := i)
  calc
    _ ≤ (4 * σ) * 1 * 1 := by gcongr
    _ = _ := by ring

lemma recovery_argument_bound {ε μ d κ R s a σ M : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hμlower : ε / (2 * R ^ 2) ≤ μ)
    (hs : 0 ≤ s) (hsσ : s ≤ 4 * σ) (ha1 : a ≤ 1)
    (hM : 1 ≤ M) (hσM : σ * R / ε ≤ M) :
    let U := Real.sqrt (2 * ε / μ)
    let D := Real.sqrt (ε / (2 * d * μ * κ))
    (s / μ + a * U) / D ≤ 10 * M * Real.sqrt (d * κ) := by
  let U := Real.sqrt (2 * ε / μ)
  let D := Real.sqrt (ε / (2 * d * μ * κ))
  let b := Real.sqrt (d * κ)
  obtain ⟨hD, hUD, hinv⟩ := recovery_distance_ratios hε hμ hd hκ hR hμlower
  change U / D = 2 * b at hUD
  change 1 / (μ * D) ≤ 2 * (R / ε) * b at hinv
  change (s / μ + a * U) / D ≤ 10 * M * b
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hratio : 0 ≤ 2 * (R / ε) * b := by positivity
  calc
    _ = s * (1 / (μ * D)) + a * (U / D) := by field_simp
    _ ≤ s * (2 * (R / ε) * b) + a * (2 * b) := by rw [hUD]; gcongr
    _ ≤ (4 * σ) * (2 * (R / ε) * b) + 1 * (2 * b) := by gcongr
    _ = (8 * (σ * R / ε) + 2) * b := by ring
    _ ≤ 10 * M * b := by gcongr; linarith

lemma recovery_sample_work {B σ Z H m q Q qi b a κ : ℝ} (hB : 1 ≤ B) (hσ : 0 ≤ σ)
    (hZ : 0 ≤ Z) (hH : 0 < H) (hm : 0 < m) (hq : 0 < q) (hqQ : q ≤ Q)
    (hQ : 1 ≤ Q) (hqi : 0 ≤ qi) (hqiQ : qi ≤ Q) (hb : 0 ≤ b)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hρ1 : H * m ^ (-(1 / Q)) ≤ 1) (i : ℕ) :
    let ρ := H * m ^ (-(1 / Q))
    let C := B * (m * H) ^ i
    let s := 4 * σ * B ^ (-(1 / q)) * ρ ^ i
    let ai := a * ρ ^ i
    C * (Real.sqrt κ + (1 + (b * (s * Z + ai)) ^ qi) + 1) ≤
      C * (Real.sqrt κ + 3 + (2 * b) ^ Q) +
        (2 * b) ^ Q * ((4 * σ * Z) ^ Q * (H ^ (1 + Q)) ^ i) := by
  let ρ := H * m ^ (-(1 / Q))
  let C := B * (m * H) ^ i
  let s := 4 * σ * B ^ (-(1 / q)) * ρ ^ i
  let ai := a * ρ ^ i
  have hB0 : 0 ≤ B := by linarith
  have hρ : 0 ≤ ρ := by positivity
  have hC : 0 ≤ C := by positivity
  have hs : 0 ≤ s := by positivity
  have hai : 0 ≤ ai := by positivity
  have hai1 : ai ≤ 1 := by
    have hp := pow_le_one₀ hρ hρ1 (n := i)
    dsimp [ai]
    nlinarith
  have hh := weighted_recovery_scale hC hb (mul_nonneg hs hZ) hai hqi hqiQ hQ
  have hnoise := normalized_noise_work hB hσ hZ hH hm hq hqQ i
  change C * (s * Z) ^ Q ≤ (4 * σ * Z) ^ Q * (H ^ (1 + Q)) ^ i at hnoise
  have hrel : C * ai ^ Q ≤ C := mul_le_of_le_one_right hC (Real.rpow_le_one hai hai1 (by linarith))
  have hF : 0 ≤ (2 * b) ^ Q := by positivity
  have hnF := mul_le_mul_of_nonneg_left hnoise hF
  have hrF := mul_le_mul_of_nonneg_left hrel hF
  change C * (Real.sqrt κ + (1 + (b * (s * Z + ai)) ^ qi) + 1) ≤ _
  nlinarith

lemma recovery_confidence_log {δ d W : ℝ} (hδ : 0 < δ) (hd : 1 ≤ d)
    (hW : 4 ≤ W) (hdW : d ≤ W) (hδlog : Real.log (1 / δ) ≤ W) :
    Real.log (1 / (δ / (4 * d))) ≤ 3 * W := by
  have he : 1 / (δ / (4 * d)) = 4 * d / δ := by field_simp
  rw [he, Real.log_div (by positivity : 4 * d ≠ 0) hδ.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by linarith : d ≠ 0)]
  have hl4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hld : Real.log d ≤ W := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < d)]
  simp only [one_div, Real.log_inv] at hδlog
  linarith

lemma recovery_total_log {n a η q A W : ℝ} (hq : 2 ≤ q) (hA : 1 ≤ A) (hW : 4 ≤ W)
    (hn : Real.log n ≤ 12 * q * W) (ha : Real.log (1 / a) ≤ 32 * q * A * W ^ 2)
    (hη : Real.log (1 / η) ≤ 3 * W) :
    1 + Real.log n + Real.log (1 / a) + Real.log (1 / η) ≤ 64 * q * A * W ^ 2 := by
  have hqA : q ≤ q * A := by nlinarith
  have hqAW : q * W ≤ q * A * W := mul_le_mul_of_nonneg_right hqA (by linarith)
  have hmulW := mul_le_mul_of_nonneg_left hW (show 0 ≤ q * A * W by positivity)
  have hqW : 2 * W ≤ q * W := mul_le_mul_of_nonneg_right hq (by linarith)
  nlinarith

lemma recovery_sum_work {B σ Z H m q Q b a κ : ℝ} (hB : 1 ≤ B) (hσ : 0 ≤ σ)
    (hZ : 0 ≤ Z) (hH : 1 ≤ H) (hm : 1 ≤ m) (hq : 0 < q) (hqQ : q ≤ Q)
    (hQ : 1 ≤ Q) (hb : 0 ≤ b) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hρ1 : H * m ^ (-(1 / Q)) ≤ 1) (qi : ℕ → ℝ) (d : ℕ)
    (hqi : ∀ i < d, 0 ≤ qi i ∧ qi i ≤ Q) :
    let ρ := H * m ^ (-(1 / Q))
    let C := fun i : ℕ => B * (m * H) ^ i
    let s := fun i : ℕ => 4 * σ * B ^ (-(1 / q)) * ρ ^ i
    let ai := fun i : ℕ => a * ρ ^ i
    (∑ i ∈ Finset.range d, C i * (Real.sqrt κ + (1 + (b * (s i * Z + ai i)) ^ qi i) + 1)) ≤
      (d : ℝ) * ((Real.sqrt κ + 3 + (2 * b) ^ Q) * (B * (m * H) ^ d) +
        (2 * b) ^ Q * ((4 * σ * Z) ^ Q * (H ^ (1 + Q)) ^ d)) := by
  let ρ := H * m ^ (-(1 / Q))
  let C := fun i : ℕ => B * (m * H) ^ i
  let s := fun i : ℕ => 4 * σ * B ^ (-(1 / q)) * ρ ^ i
  let ai := fun i : ℕ => a * ρ ^ i
  let U := (Real.sqrt κ + 3 + (2 * b) ^ Q) * (B * (m * H) ^ d) +
    (2 * b) ^ Q * ((4 * σ * Z) ^ Q * (H ^ (1 + Q)) ^ d)
  have hbase : 1 ≤ m * H := by nlinarith
  have hnoisebase : 1 ≤ H ^ (1 + Q) := Real.one_le_rpow hH (by linarith)
  have hnode (i : ℕ) (hi : i ∈ Finset.range d) :
      C i * (Real.sqrt κ + (1 + (b * (s i * Z + ai i)) ^ qi i) + 1) ≤ U := by
    have hid := Finset.mem_range.mp hi
    have hh := recovery_sample_work hB hσ hZ (by linarith : 0 < H) (by linarith : 0 < m)
      hq hqQ hQ (hqi i hid).1 (hqi i hid).2 hb ha ha1 hρ1 i (κ := κ)
    change C i * (Real.sqrt κ + (1 + (b * (s i * Z + ai i)) ^ qi i) + 1) ≤ _ at hh
    refine hh.trans ?_
    change C i * (Real.sqrt κ + 3 + (2 * b) ^ Q) +
      (2 * b) ^ Q * ((4 * σ * Z) ^ Q * (H ^ (1 + Q)) ^ i) ≤ U
    dsimp [C, U]
    rw [mul_comm (B * (m * H) ^ i)]
    gcongr
  calc
    _ ≤ ∑ _i ∈ Finset.range d, U := Finset.sum_le_sum hnode
    _ = (d : ℝ) * U := by simp

lemma deterministic_work_bound {B m H κ T σ q : ℝ} (hm : 0 ≤ m)
    (hH : 0 < H) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hσ : 0 ≤ σ)
    (d : ℕ) (hκd : κ ^ d ≤ (2 : ℝ) ^ d * (2 * T))
    (hBu : B ≤ 2 * (4 * (1 + σ) * κ ^ 2 * H) ^ q)
    (hmu : m ≤ 2 * Real.sqrt κ * H ^ (4 * q)) :
    B * (m * H) ^ d ≤ ((1 + σ) ^ q * Real.sqrt T) *
      ((2 : ℝ) ^ (2 * d + 2) * (4 : ℝ) ^ q * κ ^ (2 * q) *
        H ^ (q + (4 * q + 1) * (d : ℝ))) := by
  have hroot : (Real.sqrt κ) ^ d ≤ (2 : ℝ) ^ (d + 1) * Real.sqrt T := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    have hs : ((Real.sqrt κ) ^ d) ^ 2 = κ ^ d := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul, Real.sq_sqrt hκ]
    rw [hs, mul_pow, Real.sq_sqrt hT]
    have ht : (2 : ℝ) ^ d * 2 ≤ ((2 : ℝ) ^ (d + 1)) ^ 2 := by
      have hh : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
      simp only [pow_succ, pow_zero]
      nlinarith
    have htT := mul_le_mul_of_nonneg_right ht hT
    nlinarith
  have hBform : 2 * (4 * (1 + σ) * κ ^ 2 * H) ^ q =
      2 * (4 : ℝ) ^ q * (1 + σ) ^ q * κ ^ (2 * q) * H ^ q := by
    rw [Real.mul_rpow (by positivity) hH.le,
      Real.mul_rpow (by positivity) (sq_nonneg κ),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
      ← Real.rpow_natCast κ 2, ← Real.rpow_mul hκ]
    norm_num only [Nat.cast_ofNat]
    ring
  have hmform : (2 * Real.sqrt κ * H ^ (4 * q)) * H =
      2 * Real.sqrt κ * H ^ (4 * q + 1) := by
    rw [Real.rpow_add hH, Real.rpow_one]
    ring
  have hHp : (H ^ (4 * q + 1)) ^ d = H ^ ((4 * q + 1) * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH.le]
  calc
    _ ≤ (2 * (4 * (1 + σ) * κ ^ 2 * H) ^ q) *
        ((2 * Real.sqrt κ * H ^ (4 * q)) * H) ^ d := by gcongr
    _ = (2 * (4 : ℝ) ^ q * (1 + σ) ^ q * κ ^ (2 * q) * H ^ q) *
        ((2 : ℝ) ^ d * (Real.sqrt κ) ^ d * H ^ ((4 * q + 1) * (d : ℝ))) := by
      rw [hBform, hmform, mul_pow, mul_pow, hHp]
    _ ≤ (2 * (4 : ℝ) ^ q * (1 + σ) ^ q * κ ^ (2 * q) * H ^ q) *
        ((2 : ℝ) ^ d * ((2 : ℝ) ^ (d + 1) * Real.sqrt T) * H ^ ((4 * q + 1) * (d : ℝ))) := by gcongr
    _ = _ := by
      rw [Real.rpow_add hH]
      rw [show 2 * d + 2 = (d + 1) + (d + 1) by omega, pow_add, pow_succ]
      ring

lemma recovery_normalized_argument {ε μ d κ R s a : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hd : 0 < d) (hκ : 0 < κ) (hR : 0 < R) (hs : 0 ≤ s)
    (hμlower : ε / (2 * R ^ 2) ≤ μ) :
    (s / μ + a * Real.sqrt (2 * ε / μ)) / Real.sqrt (ε / (2 * d * μ * κ)) ≤
      (2 * Real.sqrt (d * κ)) * (s * (R / ε) + a) := by
  obtain ⟨hD, hUD, hinv⟩ := recovery_distance_ratios hε hμ hd hκ hR hμlower
  have hh := mul_le_mul_of_nonneg_left hinv hs
  calc
    _ = s * (1 / (μ * Real.sqrt (ε / (2 * d * μ * κ)))) +
        a * (Real.sqrt (2 * ε / μ) / Real.sqrt (ε / (2 * d * μ * κ))) := by ring
    _ ≤ s * (2 * (R / ε) * Real.sqrt (d * κ)) + a * (2 * Real.sqrt (d * κ)) := by rw [hUD]; linarith
    _ = _ := by ring
lemma recovery_factor_domination {d κ Q : ℝ} (hd : 1 ≤ d) (hκ : 2 ≤ κ) (hQ : 2 ≤ Q) :
    Real.sqrt κ + 3 ≤ (4 * Real.sqrt (d * κ)) ^ Q := by
  have hκ0 : 0 ≤ κ := by linarith
  have hdκ : κ ≤ d * κ := by nlinarith
  have hs : Real.sqrt κ ≤ Real.sqrt (d * κ) := Real.sqrt_le_sqrt hdκ
  have hs2 := Real.sq_sqrt hκ0
  have hs0 := Real.sqrt_nonneg κ
  have hs1 : 1 ≤ Real.sqrt (d * κ) := (Real.one_le_sqrt).2 (by nlinarith)
  have hr : (4 * Real.sqrt (d * κ)) ^ (2 : ℝ) ≤ (4 * Real.sqrt (d * κ)) ^ Q :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hQ
  rw [Real.rpow_two] at hr
  have hss := Real.sq_sqrt (show 0 ≤ d * κ by positivity)
  nlinarith

lemma scalar_overhead_logs {q A W S d κ Q : ℝ}
    (hq : 2 ≤ q) (hA : 16 ≤ A) (hW : 4 ≤ W) (hw : 1 ≤ Real.log W)
    (hS : 0 ≤ S) (hd : 1 ≤ d) (hdS : d ≤ 1 + S)
    (hκ : 2 ≤ κ) (hk : Real.log κ ≤ 2 + S) (hQ : 2 ≤ Q) (hQq : Q ≤ 2*q) :
    let H := W ^ A
    let G := 2*d*H*(4*Real.sqrt (d*κ))^Q
    let D := (2:ℝ)^(2*d+2)*4^q*κ^(2*q)*H^(q+(4*q+1)*d)
    let N := (4:ℝ)^Q*Real.exp (2*S)*H^((1+Q)*d)
    Real.log G ≤ 4*A*q*(1+S)*Real.log W ∧
    Real.log D ≤ 12*A*q*(1+S)*Real.log W ∧
    Real.log N ≤ 8*A*q*(1+S)*Real.log W := by
  let u := 1+S
  let w := Real.log W
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hw' : 1 ≤ w := hw
  have hdlog : Real.log d ≤ u := (Real.log_le_sub_one_of_pos (by linarith)).trans (by dsimp [u]; linarith)
  have hk' : Real.log κ ≤ 2*u := hk.trans (by dsimp [u]; linarith)
  have hl2 : Real.log (2:ℝ) ≤ 1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
  have hl4 : Real.log (4:ℝ) ≤ 3 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4) using 1; norm_num
  have haw : 0 ≤ A*w := by positivity
  have hqu : 0 ≤ q*u := by positivity
  have hquw : q*u ≤ q*u*w := le_mul_of_one_le_right hqu hw'
  have hauw : A*w ≤ A*q*u*w := by nlinarith [mul_nonneg (by linarith : 0 ≤ A*w) (by nlinarith : 0 ≤ q*u-1)]
  have hquwA : q*u*w ≤ A*q*u*w := by nlinarith [mul_nonneg (by positivity : 0 ≤ q*u*w) (by linarith : 0 ≤ A-1)]
  have hbase : Real.log (4*Real.sqrt (d*κ)) ≤ 5*u := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity), Real.log_mul (by linarith) (by linarith)]
    nlinarith
  have hG : Real.log (2*d*W^A*(4*Real.sqrt (d*κ))^Q) ≤ A*w+11*q*u := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by linarith), Real.log_rpow (by linarith), Real.log_rpow (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hbase (by linarith : 0 ≤ Q)
    have hh' := mul_le_mul_of_nonneg_right hQq (by positivity : 0 ≤ 5*u)
    dsimp [w] at *
    nlinarith
  have hD : Real.log ((2:ℝ)^(2*d+2)*4^q*κ^(2*q)*(W^A)^(q+(4*q+1)*d)) ≤
      12*q*u + 6*A*q*u*w := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow (by norm_num), Real.log_rpow (by linarith), Real.log_rpow (by positivity), Real.log_rpow (by linarith)]
    have h1 := mul_le_mul_of_nonneg_left hl2 (by linarith : 0 ≤ 2*d+2)
    have h2 := mul_le_mul_of_nonneg_left hl4 (by linarith : 0 ≤ q)
    have h3 := mul_le_mul_of_nonneg_left hk' (by linarith : 0 ≤ 2*q)
    have hcoef : q+(4*q+1)*d ≤ 6*q*u := by
      have hh := mul_le_mul_of_nonneg_left hdS (by linarith : 0 ≤ 4*q+1)
      change (4*q+1)*d ≤ (4*q+1)*u at hh
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right hcoef haw
    dsimp [w] at *
    nlinarith
  have hN : Real.log ((4:ℝ)^Q*Real.exp (2*S)*(W^A)^((1+Q)*d)) ≤
      8*q*u + 3*A*q*u*w := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by norm_num), Real.log_exp, Real.log_rpow (by positivity), Real.log_rpow (by linarith)]
    have h1 := mul_le_mul_of_nonneg_left hl4 (by linarith : 0 ≤ Q)
    have hcoef : (1+Q)*d ≤ 3*q*u := by
      have hh := mul_le_mul_of_nonneg_left hdS (by linarith : 0 ≤ 1+Q)
      have hh' := mul_le_mul_of_nonneg_right hQq (by positivity : 0 ≤ u)
      change (1+Q)*d ≤ (1+Q)*u at hh
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right hcoef haw
    dsimp [w,u] at *
    nlinarith
  dsimp only
  change _ ≤ 4*A*q*u*w ∧ _ ≤ 12*A*q*u*w ∧ _ ≤ 8*A*q*u*w
  have hlarge : 16*(q*u*w) ≤ A*q*u*w := by nlinarith [mul_nonneg (by positivity : 0 ≤ q*u*w) (by linarith : 0 ≤ A-16)]
  constructor
  · nlinarith
  constructor <;> nlinarith
lemma scalar_overhead_products {q A W S d κ Q : ℝ}
    (hq : 2 ≤ q) (hA : 16 ≤ A) (hW : 4 ≤ W) (hw : 1 ≤ Real.log W)
    (hS : 0 ≤ S) (hd : 1 ≤ d) (hdS : d ≤ 1 + S)
    (hκ : 2 ≤ κ) (hk : Real.log κ ≤ 2 + S) (hQ : 2 ≤ Q) (hQq : Q ≤ 2*q) :
    let H := W ^ A
    let G := 2*d*H*(4*Real.sqrt (d*κ))^Q
    let D := (2:ℝ)^(2*d+2)*4^q*κ^(2*q)*H^(q+(4*q+1)*d)
    let N := (4:ℝ)^Q*Real.exp (2*S)*H^((1+Q)*d)
    4*G*D ≤ Real.exp (32*A*q*(1+S)*Real.log W) ∧
    4*G*N ≤ Real.exp (32*A*q*(1+S)*Real.log W) := by
  let H := W ^ A
  let G := 2*d*H*(4*Real.sqrt (d*κ))^Q
  let D := (2:ℝ)^(2*d+2)*4^q*κ^(2*q)*H^(q+(4*q+1)*d)
  let N := (4:ℝ)^Q*Real.exp (2*S)*H^((1+Q)*d)
  have hG : 0 < G := by dsimp [G,H]; positivity
  have hD : 0 < D := by dsimp [D,H]; positivity
  have hN : 0 < N := by dsimp [N,H]; positivity
  obtain ⟨hg,hdn,hn⟩ := scalar_overhead_logs hq hA hW hw hS hd hdS hκ hk hQ hQq
  change Real.log G ≤ _ at hg
  change Real.log D ≤ _ at hdn
  change Real.log N ≤ _ at hn
  have hlarge : 1 ≤ A*q*(1+S)*Real.log W := by
    have h1 : 1 ≤ A*q := by nlinarith [mul_nonneg (by linarith : 0 ≤ A-1) (by linarith : 0 ≤ q-1)]
    have h2 : 1 ≤ A*q*(1+S) := by nlinarith [mul_nonneg (by linarith : 0 ≤ A*q) hS]
    nlinarith [mul_nonneg (by linarith : 0 ≤ A*q*(1+S)) (by linarith : 0 ≤ Real.log W-1)]
  have hl4 : Real.log (4:ℝ) ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4) using 1; norm_num
  dsimp only
  constructor
  · apply (Real.log_le_iff_le_exp (by change 0 < 4*G*D; positivity)).1
    change Real.log (4*G*D) ≤ _
    rw [Real.log_mul (by positivity) hD.ne', Real.log_mul (by norm_num) hG.ne']
    nlinarith
  · apply (Real.log_le_iff_le_exp (by change 0 < 4*G*N; positivity)).1
    change Real.log (4*G*N) ≤ _
    rw [Real.log_mul (by positivity) hN.ne', Real.log_mul (by norm_num) hG.ne']
    nlinarith

lemma public_overhead_coefficient {q : ℝ} (hq : 2 ≤ q) :
    32 * ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ 3) * q ≤ (2 : ℝ) ^ (32 : ℕ) * q ^ 4 := by
  have hq0 : 0 ≤ q := by linarith
  have hc : (1 + q) ^ 3 ≤ (2 * q) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := mul_le_mul_of_nonneg_right hc hq0
  norm_num at *
  nlinarith [sq_nonneg (q ^ 2)]
lemma log_four_lower {W : ℝ} (hW : 4 ≤ W) : 1 ≤ Real.log W := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hW
  rw [h4] at hh
  norm_num at h2
  linarith

end LongTails.Proofs.StochasticEnvelopeWork
