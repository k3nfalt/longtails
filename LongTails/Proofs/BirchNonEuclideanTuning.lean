import LongTails.Algorithms.BirchNonEuclideanFramework
import LongTails.Proofs.BirchNonEuclideanCertificate
import LongTails.Proofs.BirchMeasurableLmoAudit

namespace LongTails.Proofs.BirchNonEuclideanTuning

open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (IsBallLMO)
open LongTails.Algorithms.BirchNonEuclideanFramework

lemma batch_minimum (p : Params) : p.profile.minimumBatch ≤ batchSize p := by
  unfold batchSize
  omega

lemma batch_positive (p : Params) (hp : spec.valid p) : 0 < batchSize p :=
  lt_of_lt_of_le hp.2.2.2.2.2.2.2.2.1.1 (batch_minimum p)

lemma horizon_positive (p : Params) : 0 < horizon p := by
  unfold horizon
  omega

lemma regularity_nonneg (p : Params) (hp : spec.valid p) : 0 ≤ p.κ := by
  obtain ⟨w⟩ := hp.2.2.2.2.2.2.2.1
  exact (show (0 : ℝ) ≤ 1 by norm_num).trans (w.smoothness_lower.trans w.smoothness_upper)

lemma drift_nonneg (p : Params) (hp : spec.valid p) :
    0 ≤ p.profile.driftConstant + p.profile.driftLinear * batchSize p := by
  obtain ⟨_, hd, hl, _, _⟩ := hp.2.2.2.2.2.2.2.2.1
  positivity

lemma step_positive (p : Params) (hp : spec.valid p) : 0 < stepSize p := by
  have hL := hp.2.2.1
  have hd := drift_nonneg p hp
  unfold stepSize
  have : 0 < 1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p := by linarith
  positivity

lemma tuning_valid (p : Params) (hp : spec.valid p) :
    (canonicalTuning (stepSize p) (batchSize p)).Valid := by
  have hB : (1 : ℝ) ≤ batchSize p := by exact_mod_cast batch_positive p hp
  change (∀ _ : ℕ, 0 ≤ stepSize p) ∧ ∀ _ : ℕ,
    0 ≤ 1 / (batchSize p : ℝ) ∧ 1 / (batchSize p : ℝ) ≤ 1
  refine ⟨fun _ => (step_positive p hp).le, fun _ => ⟨by positivity, ?_⟩⟩
  simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hB

lemma chosenLMO_valid (p : Params) (hp : spec.valid p) : IsBallLMO p.N 1 (chosenLMO p) := by
  have hh := LongTails.Proofs.BirchLmoExistence.exists_measurable_lmo p.N hp.1 hp.2.1
  unfold chosenLMO
  rw [dite_eq_left hh]
  exact Classical.choose_spec hh

lemma step_conditions (p : Params) (hp : spec.valid p) :
    stepSize p * p.L ≤ 1 / 2 ∧
    stepSize p * p.L * (p.profile.driftConstant + p.profile.driftLinear * batchSize p) ≤ 1 / 4 := by
  have hL := hp.2.2.1
  have hd := drift_nonneg p hp
  have hu : 0 < 1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p := by linarith
  have he : stepSize p * p.L =
      1 / (4 * (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p)) := by
    unfold stepSize
    field_simp
  rw [he]
  constructor
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith
  · rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith

lemma batch_noise_bound (p : Params) (hp : spec.valid p) :
    16 * p.κ * p.σ ^ 2 *
      (p.profile.noiseLinear / batchSize p + p.profile.noiseQuadratic / (batchSize p : ℝ) ^ 2) ≤
        p.ε / 2 := by
  have hε := hp.2.2.2.2.1
  have hκ := regularity_nonneg p hp
  obtain ⟨_, _, _, hv1, hv2⟩ := hp.2.2.2.2.2.2.2.2.1
  have hB : (0 : ℝ) < batchSize p := Nat.cast_pos.mpr (batch_positive p hp)
  have hY : 0 ≤ p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε := by positivity
  have hsum : 64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / p.ε +
      8 * Real.sqrt (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε) ≤ (batchSize p : ℝ) := by
    have hc := Nat.le_ceil (64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / p.ε +
      8 * Real.sqrt (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε))
    unfold batchSize
    push_cast
    exact hc.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hl : 64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear ≤ p.ε * (batchSize p : ℝ) := by
    have hh : 64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / p.ε ≤ (batchSize p : ℝ) :=
      (le_add_of_nonneg_right (by positivity)).trans hsum
    exact (div_le_iff₀ hε).mp hh |>.trans_eq (mul_comm _ _)
  have hq : 64 * p.κ * p.σ ^ 2 * p.profile.noiseQuadratic ≤ p.ε * (batchSize p : ℝ) ^ 2 := by
    have hh : 8 * Real.sqrt (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε) ≤
        (batchSize p : ℝ) := (le_add_of_nonneg_left (by positivity)).trans hsum
    have hs := (sq_le_sq₀ (by positivity) hB.le).mpr hh
    rw [mul_pow, Real.sq_sqrt hY] at hs
    have ht : 64 * p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε ≤
        (batchSize p : ℝ) ^ 2 := by
      calc
        _ = 8 ^ 2 * (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε) := by ring
        _ ≤ _ := hs
    exact (div_le_iff₀ hε).mp ht |>.trans_eq (mul_comm _ _)
  have hl' : 16 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / batchSize p ≤ p.ε / 4 := by
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hq' : 16 * p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / (batchSize p : ℝ) ^ 2 ≤ p.ε / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    nlinarith
  calc
    _ = 16 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / batchSize p +
        16 * p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / (batchSize p : ℝ) ^ 2 := by ring
    _ ≤ p.ε / 2 := by linarith

lemma horizon_bound (p : Params) (hp : spec.valid p) :
    6 * p.Δ / (stepSize p * horizon p) ≤ p.ε / 2 := by
  have hε := hp.2.2.2.2.1
  have hL := hp.2.2.1
  have hη := step_positive p hp
  have hK : (0 : ℝ) < horizon p := Nat.cast_pos.mpr (horizon_positive p)
  have hd := drift_nonneg p hp
  have hu : 0 < 1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p := by linarith
  have hb : 48 * p.L * p.Δ *
      (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p) ≤ p.ε * horizon p := by
    have hc := Nat.le_ceil (48 * p.L * p.Δ *
      (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p) / p.ε)
    have hh : 48 * p.L * p.Δ *
        (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p) / p.ε ≤
          (horizon p : ℝ) := by
      unfold horizon
      push_cast
      exact hc.trans (le_add_of_nonneg_left (by norm_num))
    exact (div_le_iff₀ hε).mp hh |>.trans_eq (mul_comm _ _)
  have he : 6 * p.Δ / (stepSize p * horizon p) =
      24 * p.L * p.Δ *
        (1 + p.profile.driftConstant + p.profile.driftLinear * batchSize p) / horizon p := by
    unfold stepSize
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ hK).mpr
  nlinarith

lemma accuracy_bound (p : Params) (hp : spec.valid p) :
    6 * p.Δ / (stepSize p * horizon p) +
      16 * p.κ * p.σ ^ 2 *
        (p.profile.noiseLinear / batchSize p + p.profile.noiseQuadratic / (batchSize p : ℝ) ^ 2) ≤
          p.ε := by
  linarith [horizon_bound p hp, batch_noise_bound p hp]

lemma program_certificate (p : Params) (hp : spec.valid p) :
    (program p).Legal p.workers ∧ (program p).oracleCalls = p.callCount (horizon p) (batchSize p) ∧
      Nonempty (ProgramCertificate (program p) (horizon p) (stepSize p)
        (p.profile.driftConstant + p.profile.driftLinear * batchSize p)
        (p.profile.noiseLinear / batchSize p + p.profile.noiseQuadratic / (batchSize p : ℝ) ^ 2)) :=
  hp.2.2.2.2.2.2.2.2.2 (horizon p) (batchSize p) (horizon_positive p) (batch_minimum p)
    (stepSize p) (step_positive p hp)

lemma algorithm_allowed (p : Params) (hp : spec.valid p) : spec.allowedAlgorithm p (algorithm p) :=
  ⟨horizon p, batchSize p, canonicalTuning (stepSize p) (batchSize p), batch_positive p hp,
    tuning_valid p hp, (program_certificate p hp).1, chosenLMO p, chosenLMO_valid p hp, rfl⟩

end LongTails.Proofs.BirchNonEuclideanTuning
