import LongTails.Proofs.TailObliviousExecution
import LongTails.Proofs.TailObliviousAccuracy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.TailObliviousBudget

open LongTails.Setups.TailObliviousMonotoneRootFinding
open LongTails.Algorithms.TailObliviousExtragradient
open TailObliviousExecution TailObliviousAccuracy TailObliviousProcess TailObliviousStage

lemma epochOffset_lower (n : ℕ) : (2 : ℝ) ^ n ≤ epochOffset (n + 1) := by
  simp only [epochOffset]
  push_cast
  unfold innerSteps
  push_cast
  have h0 : (0 : ℝ) ≤ epochOffset n := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ n + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

lemma epochOffset_upper (n : ℕ) : (epochOffset n : ℝ) ≤ 96 * n * 2 ^ n := by
  induction n with
  | zero => simp [epochOffset]
  | succ n ih =>
    simp only [epochOffset]
    push_cast
    unfold innerSteps
    push_cast
    rw [pow_succ]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

lemma epochOffset_strict (n : ℕ) : epochOffset n < epochOffset (n + 1) := by
  simp only [epochOffset]
  have : 0 < (n + 1) * innerSteps n := by unfold innerSteps; positivity
  omega

lemma exists_epoch (M : ℕ) (hM : 192 ≤ M) :
    ∃ K, 2 * epochOffset (K + 1) ≤ M ∧ M < 2 * epochOffset (K + 2) := by
  have hex : ∃ n, M < 2 * epochOffset (n + 1) := by
    refine ⟨M, ?_⟩
    have h := epochOffset_lower M
    have hpow : (M : ℝ) < 2 ^ M := by
      exact_mod_cast Nat.lt_two_pow_self
    have : (M : ℝ) < 2 * epochOffset (M + 1) := by linarith [hpow, h]
    exact_mod_cast this
  classical
  let n0 := Nat.find hex
  have hn0 : M < 2 * epochOffset (n0 + 1) := Nat.find_spec hex
  have h1 : epochOffset 1 = 96 := by simp [epochOffset, innerSteps]
  have hpos : 1 ≤ n0 := by
    by_contra h
    have h0 : n0 = 0 := by omega
    rw [h0, h1] at hn0
    omega
  refine ⟨n0 - 1, ?_, ?_⟩
  · have hmin := Nat.find_min hex (show n0 - 1 < n0 by omega)
    rw [show n0 - 1 + 1 = n0 by omega]
    have : ¬ M < 2 * epochOffset (n0 - 1 + 1) := hmin
    rw [show n0 - 1 + 1 = n0 by omega] at this
    omega
  · rw [show n0 - 1 + 2 = n0 + 1 by omega]
    exact hn0

lemma sum_rpow_le (a b β : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ : 1 ≤ β) :
    1 + a + b ^ β ≤ (1 + a + b) ^ β := by
  have h1 : (1 + a) ^ β + b ^ β ≤ (1 + a + b) ^ β := by
    have h := NNReal.add_rpow_le_rpow_add (⟨1 + a, by positivity⟩ : NNReal) ⟨b, hb⟩ hβ
    exact_mod_cast h
  have h2 : 1 + a ≤ (1 + a) ^ β := by
    have := one_add_mul_self_le_rpow_one_add (s := a) (by linarith) hβ
    nlinarith
  linarith

lemma log_count_bound (α M A Z ℓ : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hA : 1 ≤ A) (hℓ : 0 ≤ ℓ) (hAℓ : Real.log A ≤ α / (α - 1) * ℓ)
    (hZ : Z = 64 * (α / (α - 1)) ^ 2 * (1 + ℓ))
    (hM0 : 0 < M) (hM : M ≤ 2 * (2 ^ (20 / (α - 1)) * A * Z ^ (2 * α / (α - 1)))) :
    Real.log M + 2 * Real.log 2 ≤ Z * Real.log 2 := by
  set β := α / (α - 1) with hβ
  have hα0 : 0 < α - 1 := by linarith
  have hβ2 : 2 ≤ β := by rw [hβ, le_div_iff₀ hα0]; linarith
  have hβ1 : β - 1 = 1 / (α - 1) := by rw [hβ]; field_simp; ring
  have hZpos : 0 < Z := by rw [hZ]; positivity
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hP : 0 < 2 ^ (20 / (α - 1)) * A * Z ^ (2 * α / (α - 1)) := by positivity
  have hlogM : Real.log M ≤ Real.log 2 + (20 / (α - 1)) * Real.log 2 + Real.log A +
      (2 * β) * Real.log Z := by
    have h := Real.log_le_log hM0 hM
    rw [Real.log_mul (by norm_num) hP.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
      Real.log_rpow hZpos] at h
    have h2b : 2 * α / (α - 1) = 2 * β := by rw [hβ]; ring
    rw [h2b] at h
    linarith
  have hlogZ : Real.log Z ≤ 6 * Real.log 2 + 2 * (β - 1) + ℓ := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
    have hb : Real.log (β ^ 2) ≤ 2 * (β - 1) := by
      rw [Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show 0 < β by linarith)
      push_cast; linarith
    have hl : Real.log (1 + ℓ) ≤ ℓ := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + ℓ by linarith); linarith
    linarith
  have h20 : 20 / (α - 1) = 20 * (β - 1) := by rw [hβ1]; ring
  rw [h20] at hlogM
  have hmain : Real.log M + 2 * Real.log 2 ≤
      3 * Real.log 2 + 20 * (β - 1) * Real.log 2 + β * ℓ +
        2 * β * (6 * Real.log 2 + 2 * (β - 1) + ℓ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlogZ (by linarith : (0 : ℝ) ≤ 2 * β)]
  refine hmain.trans ?_
  rw [hZ]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ β) (by linarith : (0 : ℝ) ≤ β)) hℓ,
    mul_nonneg (by linarith : (0 : ℝ) ≤ β) hℓ]


lemma term_bias (α Λ c ε : ℝ) (hα1 : 1 < α) (hΛ : 0 ≤ Λ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hb : Λ * c ≤ ε / 34) : 17 * Λ ^ α * c ^ α ≤ ε ^ α / 2 := by
  have h1 : Λ ^ α * c ^ α = (Λ * c) ^ α := (Real.mul_rpow hΛ hc).symm
  have h2 : (Λ * c) ^ α ≤ (ε / 34) ^ α := Real.rpow_le_rpow (by positivity) hb (by linarith)
  have h3 : (ε / 34) ^ α = ε ^ α / 34 ^ α := Real.div_rpow hε.le (by norm_num) α
  have h4 : (34 : ℝ) ≤ 34 ^ α := by
    calc (34 : ℝ) = 34 ^ (1 : ℝ) := (Real.rpow_one 34).symm
      _ ≤ 34 ^ α := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
  have hεα : 0 < ε ^ α := Real.rpow_pos_of_pos hε α
  have h5 : ε ^ α / 34 ^ α ≤ ε ^ α / 34 := div_le_div_of_nonneg_left hεα.le (by norm_num) h4
  calc 17 * Λ ^ α * c ^ α = 17 * (Λ * c) ^ α := by rw [mul_assoc, h1]
    _ ≤ 17 * (ε ^ α / 34) := by
      have h6 := (h2.trans (le_of_eq h3)).trans h5
      linarith
    _ = ε ^ α / 2 := by ring

lemma term_noise (α Λ σ ε M v : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hΛ : 2 ≤ Λ) (hσ : 0 < σ)
    (hε : 0 < ε) (hM0 : 0 < M)
    (hM : 2 ^ (20 / (α - 1)) * (σ / ε) ^ (α / (α - 1)) * Λ ^ (2 * α / (α - 1)) ≤ M)
    (hv0 : 0 ≤ v) (hv : v ≤ 48 * Λ / M) :
    17 * Λ ^ α * (324 * (σ ^ α * v ^ (α - 1))) ≤ ε ^ α / 2 := by
  have hα0 : 0 < α - 1 := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hr : 0 < σ / ε := div_pos hσ hε
  have hMpow : (2 ^ (20 / (α - 1)) * (σ / ε) ^ (α / (α - 1)) * Λ ^ (2 * α / (α - 1))) ^ (α - 1) ≤
      M ^ (α - 1) := Real.rpow_le_rpow (by positivity) hM hα0.le
  have hsplit : (2 ^ (20 / (α - 1)) * (σ / ε) ^ (α / (α - 1)) * Λ ^ (2 * α / (α - 1))) ^ (α - 1) =
      2 ^ (20 : ℝ) * (σ / ε) ^ α * Λ ^ (2 * α) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hr.le, ← Real.rpow_mul hΛ0.le]
    have hne : α - 1 ≠ 0 := hα0.ne'
    have e1 : 20 / (α - 1) * (α - 1) = 20 := by field_simp
    have e2 : α / (α - 1) * (α - 1) = α := by field_simp
    have e3 : 2 * α / (α - 1) * (α - 1) = 2 * α := by field_simp
    rw [e1, e2, e3]
  rw [hsplit] at hMpow
  have hvpow : v ^ (α - 1) ≤ (48 * Λ / M) ^ (α - 1) := Real.rpow_le_rpow hv0 hv hα0.le
  have hq : (48 * Λ / M) ^ (α - 1) = 48 ^ (α - 1) * Λ ^ (α - 1) / M ^ (α - 1) := by
    rw [Real.div_rpow (by positivity) hM0.le, Real.mul_rpow (by norm_num) hΛ0.le]
  have h48 : (48 : ℝ) ^ (α - 1) ≤ 48 := by
    calc (48 : ℝ) ^ (α - 1) ≤ 48 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 48 := Real.rpow_one 48
  have hMa : 0 < M ^ (α - 1) := Real.rpow_pos_of_pos hM0 _
  have hσε : (σ / ε) ^ α = σ ^ α / ε ^ α := Real.div_rpow hσ.le hε.le α
  have hεα : 0 < ε ^ α := Real.rpow_pos_of_pos hε α
  have hσα : 0 < σ ^ α := Real.rpow_pos_of_pos hσ α
  have hΛα : Λ ^ α * Λ ^ (α - 1) = Λ ^ (2 * α) / Λ := by
    rw [← Real.rpow_add hΛ0, eq_div_iff hΛ0.ne', ← Real.rpow_add_one hΛ0.ne']
    congr 1; ring
  have h2pow : (2 : ℝ) ^ (20 : ℝ) = 1048576 := by norm_num
  rw [h2pow, hσε] at hMpow
  have hΛ2 : 0 < Λ ^ (2 * α) := Real.rpow_pos_of_pos hΛ0 _
  have key : σ ^ α * Λ ^ (2 * α) ≤ M ^ (α - 1) * ε ^ α / 1048576 := by
    rw [le_div_iff₀ (by norm_num)]
    have := hMpow
    rw [show 1048576 * (σ ^ α / ε ^ α) * Λ ^ (2 * α) =
      (1048576 * σ ^ α * Λ ^ (2 * α)) / ε ^ α by ring, div_le_iff₀ hεα] at this
    linarith
  calc 17 * Λ ^ α * (324 * (σ ^ α * v ^ (α - 1)))
      ≤ 17 * Λ ^ α * (324 * (σ ^ α * (48 ^ (α - 1) * Λ ^ (α - 1) / M ^ (α - 1)))) := by
        rw [← hq]
        have := Real.rpow_nonneg hΛ0.le α
        gcongr
    _ = 5508 * 48 ^ (α - 1) * (σ ^ α * (Λ ^ α * Λ ^ (α - 1))) / M ^ (α - 1) := by ring
    _ = 5508 * 48 ^ (α - 1) * (σ ^ α * Λ ^ (2 * α)) / (Λ * M ^ (α - 1)) := by
        rw [hΛα]
        have h1 : Λ ≠ 0 := hΛ0.ne'
        have h2 : M ^ (α - 1) ≠ 0 := hMa.ne'
        field_simp
    _ ≤ 5508 * 48 * (M ^ (α - 1) * ε ^ α / 1048576) / (Λ * M ^ (α - 1)) := by
        gcongr
    _ = 264384 * ε ^ α / (1048576 * Λ) := by
        have h1 : Λ ≠ 0 := hΛ0.ne'
        have h2 : M ^ (α - 1) ≠ 0 := hMa.ne'
        field_simp
        norm_num
    _ ≤ ε ^ α / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith


set_option maxHeartbeats 4000000 in
lemma budget_accuracy (d : Public) (hL : 0 < d.L) (R σ α ε : ℝ) (hR : 0 ≤ R) (hσ : 0 ≤ σ)
    (hα1 : 1 < α) (hα2 : α ≤ 2) (hε : 0 < ε) (M K : ℕ)
    (hlow : 2 * epochOffset (K + 1) ≤ M) (hhigh : M < 2 * epochOffset (K + 2))
    (hX : 2 ^ 20 * (1 + d.L * R / ε) *
      (64 * (α / (α - 1)) ^ 2 * (1 + Real.log (1 + d.L * R / ε + σ / ε))) ^ 2 +
      2 ^ (20 / (α - 1)) * (σ / ε) ^ (α / (α - 1)) *
      (64 * (α / (α - 1)) ^ 2 * (1 + Real.log (1 + d.L * R / ε + σ / ε))) ^ (2 * α / (α - 1))
        ≤ (M : ℝ))
    (hX2 : (M : ℝ) ≤ 2 * (2 ^ 20 * (1 + d.L * R / ε) *
      (64 * (α / (α - 1)) ^ 2 * (1 + Real.log (1 + d.L * R / ε + σ / ε))) ^ 2 +
      2 ^ (20 / (α - 1)) * (σ / ε) ^ (α / (α - 1)) *
      (64 * (α / (α - 1)) ^ 2 * (1 + Real.log (1 + d.L * R / ε + σ / ε))) ^ (2 * α / (α - 1)))) :
    accuracyBound d R σ α K ≤ ε ^ α := by
  set β := α / (α - 1) with hβ
  set A := 1 + d.L * R / ε + (σ / ε) ^ β with hA
  set t := 1 + d.L * R / ε + σ / ε with ht
  set ℓ := Real.log t with hℓ
  set Z := 64 * β ^ 2 * (1 + ℓ) with hZ
  have hα0 : 0 < α - 1 := by linarith
  have hβ2 : 2 ≤ β := by rw [hβ, le_div_iff₀ hα0]; linarith
  have hLR : 0 ≤ d.L * R / ε := by positivity
  have hσε : 0 ≤ σ / ε := by positivity
  have hσβ : 0 ≤ (σ / ε) ^ β := Real.rpow_nonneg hσε _
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg ht1
  have hA1 : 1 ≤ A := by rw [hA]; linarith
  have hAt : A ≤ t ^ β := sum_rpow_le _ _ β hLR hσε (by linarith)
  have hAℓ : Real.log A ≤ β * ℓ := by
    have h := Real.log_le_log (by linarith) hAt
    rwa [Real.log_rpow (by linarith)] at h
  have hZpos : 0 < Z := by rw [hZ]; positivity
  have hZ1 : 1 ≤ Z := by
    rw [hZ]; nlinarith
  have h2big : (2 : ℝ) ^ (20 : ℝ) ≤ 2 ^ (20 / (α - 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [le_div_iff₀ hα0]; linarith
  have h2n : (2 : ℝ) ^ (20 : ℝ) = 2 ^ 20 := by norm_num
  rw [h2n] at h2big
  have hZsq : Z ^ 2 ≤ Z ^ (2 * α / (α - 1)) := by
    have : Z ^ (2 : ℝ) ≤ Z ^ (2 * α / (α - 1)) := by
      apply Real.rpow_le_rpow_of_exponent_le hZ1
      rw [le_div_iff₀ hα0]; linarith
    simpa using this
  have hnew_old : 2 ^ 20 * (1 + d.L * R / ε) * Z ^ 2 + 2 ^ (20 / (α - 1)) * (σ / ε) ^ β *
      Z ^ (2 * α / (α - 1)) ≤ 2 ^ (20 / (α - 1)) * A * Z ^ (2 * α / (α - 1)) := by
    rw [hA]
    have hZ0 : 0 ≤ Z ^ 2 := sq_nonneg _
    have : (2 : ℝ) ^ 20 * (1 + d.L * R / ε) * Z ^ 2 ≤
        2 ^ (20 / (α - 1)) * (1 + d.L * R / ε) * Z ^ (2 * α / (α - 1)) := by
      gcongr
    nlinarith
  have hXpos : 0 < 2 ^ 20 * (1 + d.L * R / ε) * Z ^ 2 + 2 ^ (20 / (α - 1)) * (σ / ε) ^ β *
      Z ^ (2 * α / (α - 1)) := by positivity
  have hM0 : 0 < (M : ℝ) := hXpos.trans_le hX
  have hcount := log_count_bound α M A Z ℓ hα1 hα2 hA1 hℓ0 hAℓ hZ hM0 (by linarith)
  have h2K : (2 : ℝ) ^ K ≤ M := by
    have h1 := epochOffset_lower K
    have h2 : (2 * epochOffset (K + 1) : ℝ) ≤ M := by exact_mod_cast hlow
    have h3 : (0 : ℝ) ≤ epochOffset (K + 1) := Nat.cast_nonneg _
    linarith
  have hKlog : (K : ℝ) * Real.log 2 ≤ Real.log M := by
    have h := Real.log_le_log (by positivity) h2K
    rwa [Real.log_pow] at h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Λ : ℝ := (K : ℝ) + 2 with hΛdef
  have hΛ2 : 2 ≤ Λ := by have := (Nat.cast_nonneg K : (0 : ℝ) ≤ K); linarith
  have hΛZ : Λ ≤ Z := by
    have : Λ * Real.log 2 ≤ Z * Real.log 2 := by rw [hΛdef]; nlinarith
    exact le_of_mul_le_mul_right this hlog2
  have hupper : (M : ℝ) < 768 * Λ * 2 ^ K := by
    have h1 := epochOffset_upper (K + 2)
    have h2 : (M : ℝ) < 2 * epochOffset (K + 2) := by exact_mod_cast hhigh
    have h3 : (2 : ℝ) ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; norm_num; ring
    rw [h3] at h1
    push_cast at h1
    rw [hΛdef]
    nlinarith
  have h2Kpos : (0 : ℝ) < 2 ^ K := by positivity
  have hu : 1 / (2 : ℝ) ^ K ≤ 768 * Λ / M := by
    rw [div_le_div_iff₀ h2Kpos hM0]; linarith
  have hΛpow : Λ ^ (2 * α / (α - 1)) ≤ Z ^ (2 * α / (α - 1)) :=
    Real.rpow_le_rpow (by linarith) hΛZ (by positivity)
  have hMΛ : 2 ^ (20 / (α - 1)) * (σ / ε) ^ β * Λ ^ (2 * α / (α - 1)) ≤ M := by
    refine le_trans ?_ hX
    have h0 : 0 ≤ 2 ^ (20 / (α - 1)) * (σ / ε) ^ β := by positivity
    have h1 := mul_le_mul_of_nonneg_left hΛpow h0
    have h2 : 0 ≤ (2 : ℝ) ^ 20 * (1 + d.L * R / ε) * Z ^ 2 := by positivity
    linarith
  have hstr : strength d K 0 = d.L * (1 / 2 ^ K) := by
    rw [strength_zero]; ring
  have hc0 : 0 ≤ 2 * strength d K 0 * R := by
    have := strength_pos d hL K 0; positivity
  have hbias : 17 * Λ ^ α * (2 * strength d K 0 * R) ^ α ≤ ε ^ α / 2 := by
    apply term_bias α Λ _ ε hα1 (by linarith) hc0 hε
    have hMb : 1048576 * (d.L * R / ε) * Λ ^ 2 ≤ M := by
      have hΛsq : Λ ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (by linarith) hΛZ 2
      have h3 : 0 ≤ 2 ^ (20 / (α - 1)) * (σ / ε) ^ β * Z ^ (2 * α / (α - 1)) := by positivity
      calc (1048576 : ℝ) * (d.L * R / ε) * Λ ^ 2 ≤ 2 ^ 20 * (1 + d.L * R / ε) * Z ^ 2 := by
            have h4 : (1048576 : ℝ) * (d.L * R / ε) ≤ 2 ^ 20 * (1 + d.L * R / ε) := by
              norm_num
            exact mul_le_mul h4 hΛsq (by positivity) (by positivity)
        _ ≤ (M : ℝ) := by linarith
    rw [hstr]
    have hLRε : d.L * R = (d.L * R / ε) * ε := by field_simp
    calc Λ * (2 * (d.L * (1 / 2 ^ K)) * R) = 2 * Λ * (d.L * R) * (1 / 2 ^ K) := by ring
      _ ≤ 2 * Λ * (d.L * R) * (768 * Λ / M) := by
          gcongr
      _ = 1536 * ((d.L * R / ε) * Λ ^ 2) * ε / M := by rw [hLRε]; field_simp; ring
      _ ≤ 1536 * (M / 1048576) * ε / M := by
          gcongr
          linarith
      _ ≤ ε / 34 := by
          rw [div_le_div_iff₀ hM0 (by norm_num)]
          nlinarith
  have hnoise : 17 * Λ ^ α * (324 * floorTerm σ α K) ≤ ε ^ α / 2 := by
    rcases hσ.eq_or_lt with h0 | hpos
    · rw [← h0]
      unfold floorTerm
      rw [Real.zero_rpow (by linarith)]
      simp
      exact div_nonneg (Real.rpow_pos_of_pos hε α).le (by norm_num)
    · unfold floorTerm
      apply term_noise α Λ σ ε M (relaxation K) hα1 hα2 hΛ2 hpos hε hM0 _
        (relaxation_pos K).le
      · have : relaxation K = (1 / 2 ^ K) / 16 := by unfold relaxation; field_simp
        rw [this]
        have h768 := hu
        calc (1 / 2 ^ K) / 16 ≤ (768 * Λ / M) / 16 := by gcongr
          _ ≤ 48 * Λ / M := by rw [div_div]; rw [div_le_div_iff₀ (by positivity) hM0]; nlinarith
      · exact hMΛ
  unfold accuracyBound envelope
  rw [← hΛdef]
  nlinarith [hbias, hnoise]

end LongTails.Proofs.TailObliviousBudget
