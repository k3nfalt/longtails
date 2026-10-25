import LongTails.Proofs.HeavyTailedSospSpectralCost
import LongTails.Proofs.HeavyTailedSospConfigured

namespace LongTails.Proofs.HeavyTailedSospBudget

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSospTuned
open HeavyTailedSospTuning HeavyTailedSospCost HeavyTailedSospDetectorCost HeavyTailedSospSpectralCost
open HeavyTailedSospWork

lemma probe_calls_envelope (p : Params) (hd : 0 < p.d) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    let D := Real.log (2 + (p.d : ℝ))
    let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
    let V := (p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)
    let X := p.σh / Real.sqrt (p.ρ * p.ε)
    ((max 1 (repeatCount p) * max 1 (probeSteps p) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (17 * conjugate p ^ 2) * (J * D * V + J * D ^ conjugate p * X ^ conjugate p) := by
  intro D J V X
  have hD := dimension_log_ge_one p hd
  have hJ := public_log_ge_one p hL hρ hε
  have hR := repeatCount_envelope p hp hp2 hL hρ hε
  have ht := probeSteps_public_upper p hd hp hp2 hL hρ hσ hε
  have hm := mul_le_mul hR ht (Nat.cast_nonneg (probeSteps p))
    (by positivity : 0 ≤ (2 : ℝ) ^ (4 * conjugate p ^ 2) * J)
  change (repeatCount p : ℝ) * probeSteps p ≤
    ((2 : ℝ) ^ (4 * conjugate p ^ 2) * J) *
      ((2 : ℝ) ^ (13 * conjugate p ^ 2) * (D * V + D ^ conjugate p * X ^ conjugate p)) at hm
  have hid : ((2 : ℝ) ^ (4 * conjugate p ^ 2) * J) *
      ((2 : ℝ) ^ (13 * conjugate p ^ 2) * (D * V + D ^ conjugate p * X ^ conjugate p)) =
      (2 : ℝ) ^ (17 * conjugate p ^ 2) * (J * D * V + J * D ^ conjugate p * X ^ conjugate p) := by
    calc
      _ = ((2 : ℝ) ^ (4 * conjugate p ^ 2) * (2 : ℝ) ^ (13 * conjugate p ^ 2)) *
          (J * D * V + J * D ^ conjugate p * X ^ conjugate p) := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 2; ring
  have hRp : 1 ≤ repeatCount p := repeatCount_pos p hL hρ hε
  have htp : 1 ≤ probeSteps p := (spectral_tuning_bounds p hd hp hL hρ hσ hε).2.2.1
  rw [max_eq_right hRp, max_eq_right htp, Nat.cast_mul]
  simpa only [hid] using hm

lemma detector_calls_envelope (p : Params) (hvalid : spec.valid p) :
    let D := Real.log (2 + (p.d : ℝ))
    let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
    let V := (p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)
    let X := p.σh / Real.sqrt (p.ρ * p.ε)
    (detectorCalls (config p) : ℝ) ≤ (2 : ℝ) ^ (18 * conjugate p ^ 2) *
      (J * D * V + J * D ^ conjugate p * X ^ conjugate p + J ^ 2 * (1 + X ^ conjugate p)) := by
  intro D J V X
  rcases hvalid with ⟨hd, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  have hD : 0 ≤ D := le_trans (by norm_num) (dimension_log_ge_one p hd)
  have hJ : 0 ≤ J := le_trans (by norm_num) (public_log_ge_one p hL hρ hε)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have h1 := probe_calls_envelope p hd hp hp2 hL hρ hσh hε
  have h2 := validation_calls_envelope p hp hp2 hL hρ hσh hε
  have he1 : (2 : ℝ) ^ (17 * conjugate p ^ 2) ≤ (2 : ℝ) ^ (18 * conjugate p ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [sq_nonneg (conjugate p)])
  have he2 : (2 : ℝ) ^ (11 * conjugate p ^ 2) ≤ (2 : ℝ) ^ (18 * conjugate p ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [sq_nonneg (conjugate p)])
  have hh1 := mul_le_mul_of_nonneg_right he1
    (by positivity : 0 ≤ J * D * V + J * D ^ conjugate p * X ^ conjugate p)
  have hh2 := mul_le_mul_of_nonneg_right he2 (by positivity : 0 ≤ J ^ 2 * (1 + X ^ conjugate p))
  change ((max 1 (repeatCount p) * max 1 (probeSteps p) : ℕ) : ℝ) ≤
    (2 : ℝ) ^ (17 * conjugate p ^ 2) * (J * D * V + J * D ^ conjugate p * X ^ conjugate p) at h1
  change ((max 1 (repeatCount p) * max 1 (validationBatch p) * max 1 (validationGroups p) : ℕ) : ℝ) ≤
    (2 : ℝ) ^ (11 * conjugate p ^ 2) * J ^ 2 * (1 + X ^ conjugate p) at h2
  have hid : (detectorCalls (config p) : ℝ) =
      ((max 1 (repeatCount p) * max 1 (probeSteps p) : ℕ) : ℝ) +
      ((max 1 (repeatCount p) * max 1 (validationBatch p) * max 1 (validationGroups p) : ℕ) : ℝ) := by
    simp only [detectorCalls, trialCalls, config, Nat.cast_mul, Nat.cast_add]
    ring
  rw [hid]
  nlinarith

lemma detector_cap_constant {r : ℝ} (hr : 2 ≤ r) :
    10 * (2 : ℝ) ^ 23 * (2 : ℝ) ^ (18 * r ^ 2) ≤ (2 : ℝ) ^ (25 * r ^ 2) := by
  have h10 : (10 : ℝ) ≤ 16 := by norm_num
  have hb := mul_le_mul_of_nonneg_right h10 (by positivity : 0 ≤ (2 : ℝ) ^ 23 * (2 : ℝ) ^ (18 * r ^ 2))
  have hid : 16 * ((2 : ℝ) ^ 23 * (2 : ℝ) ^ (18 * r ^ 2)) = (2 : ℝ) ^ (27 + 18 * r ^ 2) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  rw [hid] at hb
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by nlinarith [sq_nonneg (r - 2)] : 27 + 18 * r ^ 2 ≤ 25 * r ^ 2)
  nlinarith

lemma detector_cap_envelope (p : Params) (hvalid : spec.valid p) :
    let D := Real.log (2 + (p.d : ℝ))
    let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
    let V := (p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)
    let X := p.σh / Real.sqrt (p.ρ * p.ε)
    let U := 1 + p.Δ * (p.L + Real.sqrt (p.ρ * p.ε)) / p.ε ^ 2
    10 * cycleCount p * (detectorCalls (config p) : ℝ) ≤ (2 : ℝ) ^ (25 * conjugate p ^ 2) * U *
      (J * D * V + J * D ^ conjugate p * X ^ conjugate p + J ^ 2 * (1 + X ^ conjugate p)) := by
  intro D J V X U
  have hdet := detector_calls_envelope p hvalid
  rcases hvalid with ⟨hd, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  have hD : 0 ≤ D := le_trans (by norm_num) (dimension_log_ge_one p hd)
  have hJ : 0 ≤ J := le_trans (by norm_num) (public_log_ge_one p hL hρ hε)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  let Y := J * D * V + J * D ^ conjugate p * X ^ conjugate p + J ^ 2 * (1 + X ^ conjugate p)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  change (detectorCalls (config p) : ℝ) ≤ (2 : ℝ) ^ (18 * conjugate p ^ 2) * Y at hdet
  have hT := cycleCount_public_upper p hL hρ hΔ hε
  change (cycleCount p : ℝ) ≤ (2 : ℝ) ^ 23 * U at hT
  have hm := mul_le_mul hT hdet (Nat.cast_nonneg (detectorCalls (config p)))
    (by positivity : 0 ≤ (2 : ℝ) ^ 23 * U)
  have hc := mul_le_mul_of_nonneg_right (detector_cap_constant (conjugate_ge_two p hp hp2))
    (mul_nonneg hU hY)
  change _ ≤ (2 : ℝ) ^ (25 * conjugate p ^ 2) * U * Y
  nlinarith

noncomputable def publicEnvelope (p : Params) : ℝ :=
  let r := conjugate p
  let S := p.L + Real.sqrt (p.ρ * p.ε)
  let A := 1 + p.σg / p.ε
  let Z := p.σh / S + p.ρ * p.ε / S ^ 2
  let U := 1 + p.Δ * S / p.ε ^ 2
  let D := Real.log (2 + (p.d : ℝ))
  let J := Real.log (2 + S ^ 2 / (p.ρ * p.ε))
  let V := S / Real.sqrt (p.ρ * p.ε)
  let X := p.σh / Real.sqrt (p.ρ * p.ε)
  (2 : ℝ) ^ (64 * r ^ 2) * (A ^ r + U *
    (1 + A ^ (r - 1) * Z + Z ^ r + J * D * V + J * D ^ r * X ^ r + J ^ 2 * (1 + X ^ r)))

lemma publicEnvelope_bounds (p : Params) (hvalid : spec.valid p) :
    0 < publicEnvelope p ∧
      10 * ((2 * (cycleCount p : ℝ) / (max 1 (epochCount p) : ℕ) + 1) * (max 1 (resetBatch p) : ℕ) +
        2 * cycleCount p * (max 1 (transportBatch p) : ℕ) +
          cycleCount p * (detectorCalls (config p) : ℝ)) ≤ publicEnvelope p := by
  have hg := estimator_public_envelope p hvalid
  have hd := detector_cap_envelope p hvalid
  rcases hvalid with ⟨hdim, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  let r := conjugate p
  let S := p.L + Real.sqrt (p.ρ * p.ε)
  let A := 1 + p.σg / p.ε
  let Z := p.σh / S + p.ρ * p.ε / S ^ 2
  let U := 1 + p.Δ * S / p.ε ^ 2
  let D := Real.log (2 + (p.d : ℝ))
  let J := Real.log (2 + S ^ 2 / (p.ρ * p.ε))
  let V := S / Real.sqrt (p.ρ * p.ε)
  let X := p.σh / Real.sqrt (p.ρ * p.ε)
  have hS : 0 < S := by dsimp [S]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hD : 0 ≤ D := le_trans (by norm_num) (dimension_log_ge_one p hdim)
  have hJ : 0 ≤ J := le_trans (by norm_num) (public_log_ge_one p hL hρ hε)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let G := A ^ r + U * (1 + A ^ (r - 1) * Z + Z ^ r)
  let H := U * (J * D * V + J * D ^ r * X ^ r + J ^ 2 * (1 + X ^ r))
  have hG : 0 < G := by dsimp [G]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have heq : publicEnvelope p = (2 : ℝ) ^ (64 * r ^ 2) * (G + H) := by
    unfold publicEnvelope
    dsimp only [r, S, A, Z, U, D, J, V, X, G, H]
    ring
  rw [heq]
  constructor
  · positivity
  have heG := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by nlinarith [sq_nonneg r] : 32 * r ^ 2 ≤ 64 * r ^ 2)) hG.le
  have heH := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by nlinarith [sq_nonneg r] : 25 * r ^ 2 ≤ 64 * r ^ 2)) hH
  change _ ≤ (2 : ℝ) ^ (32 * r ^ 2) * G at hg
  change _ ≤ (2 : ℝ) ^ (25 * r ^ 2) * U *
    (J * D * V + J * D ^ r * X ^ r + J ^ 2 * (1 + X ^ r)) at hd
  have hd' : 10 * cycleCount p * (detectorCalls (config p) : ℝ) ≤ (2 : ℝ) ^ (25 * r ^ 2) * H := by
    dsimp only [H]
    simpa only [mul_assoc] using hd
  calc
    _ = 10 * ((2 * (cycleCount p : ℝ) / (max 1 (epochCount p) : ℕ) + 1) *
        (max 1 (resetBatch p) : ℕ) + 2 * cycleCount p * (max 1 (transportBatch p) : ℕ)) +
        10 * cycleCount p * (detectorCalls (config p) : ℝ) := by ring
    _ ≤ (2 : ℝ) ^ (64 * r ^ 2) * G + (2 : ℝ) ^ (64 * r ^ 2) * H :=
      add_le_add (hg.trans heG) (hd'.trans heH)
    _ = _ := by ring

end LongTails.Proofs.HeavyTailedSospBudget
