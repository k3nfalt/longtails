import LongTails.Algorithms.AffineHeavyTailedAdam
import LongTails.Proofs.AffineAdamDescent
import LongTails.Proofs.AffineAdamBiasCorrection

namespace LongTails.Proofs.AffineAdamTrajectory

open OracleTemplate LongTails.Setups.AffineHeavyTailedAdam
open LongTails.Algorithms.AffineHeavyTailedAdam AdaptiveHistoryAlgebra

lemma trajectory_time {d : ℕ} (cfg : Config) (x0 : Point d) (k : ℕ)
    (z : ℕ → Point d) (t : ℕ) : (trajectory cfg x0 k z t).time = t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [trajectory, coreStep] using congrArg Nat.succ ih

lemma default_invariants {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) :
    0 ≤ (trajectory cfg x0 k z t).secondMoment i ∧
      ((trajectory cfg x0 k z t).momentum i) ^ 2 ≤
        64 * (trajectory cfg x0 k z t).secondMoment i := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
    have he : (trajectory cfg x0 k z (t + 1)).secondMoment i =
        (999 / 1000 : ℝ) * (trajectory cfg x0 k z t).secondMoment i +
          (1 - 999 / 1000) * (z t i) ^ 2 := by
      simp only [trajectory, coreStep, Adam.secondMomentStep, hb2]
      ring
    have hm : (trajectory cfg x0 k z (t + 1)).momentum i =
        (9 / 10 : ℝ) * (trajectory cfg x0 k z t).momentum i + (1 - 9 / 10) * z t i := by
      simp [trajectory, coreStep, hb1]
    rw [he, hm]
    have hv := ih.1
    exact ⟨by positivity, default_momentum_invariant ih.1 ih.2⟩

lemma corrected_direction_bound {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000) (hδ : 0 < cfg.δ)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) :
    |(trajectory cfg x0 k z (t + 1)).momentum i / (1 - cfg.β₁ ^ (t + 1)) /
      (Real.sqrt ((trajectory cfg x0 k z (t + 1)).secondMoment i /
        (1 - cfg.β₂ ^ (t + 1))) + cfg.δ)| ≤ 80 := by
  obtain ⟨hv, hm⟩ := default_invariants cfg hb1 hb2 x0 k z (t + 1) i
  have h1 : (1 / 10 : ℝ) ≤ 1 - cfg.β₁ ^ (t + 1) := by
    rw [hb1, pow_succ]
    have h := pow_le_one₀ (n := t) (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num)
    nlinarith
  have h2 := AffineAdamBiasCorrection.correction_pos (β := cfg.β₂)
    (by rw [hb2]; norm_num) (by rw [hb2]; norm_num) t
  have h3 : 1 - cfg.β₂ ^ (t + 1) ≤ 1 := by rw [hb2]; have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 999 / 1000) (t + 1); linarith
  simpa only [add_comm cfg.δ] using bias_corrected_direction_bound hv hm h1 h2 h3 hδ

lemma coordinate_move {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (hη : 0 ≤ cfg.η) (hδ : 0 < cfg.δ)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) :
    |(trajectory cfg x0 k z (t + 1)).point i - (trajectory cfg x0 k z t).point i| ≤
      80 * cfg.η := by
  have h := corrected_direction_bound cfg hb1 hb2 hδ x0 k z t i
  have he : (trajectory cfg x0 k z (t + 1)).point i - (trajectory cfg x0 k z t).point i =
      -cfg.η * ((trajectory cfg x0 k z (t + 1)).momentum i / (1 - cfg.β₁ ^ (t + 1)) /
        (Real.sqrt ((trajectory cfg x0 k z (t + 1)).secondMoment i /
          (1 - cfg.β₂ ^ (t + 1))) + cfg.δ)) := by
    simp only [trajectory, coreStep, Adam.direction, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.add_apply, smul_eq_mul, trajectory_time]
    simp only [div_eq_mul_inv]
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg hη]
  simpa only [mul_comm cfg.η] using mul_le_mul_of_nonneg_left h hη

noncomputable def correctedM {d : ℕ} (cfg : Config) (x0 : Point d) (k : ℕ)
    (z : ℕ → Point d) (t : ℕ) (i : Fin d) : ℝ :=
  (trajectory cfg x0 k z t).momentum i / (1 - cfg.β₁ ^ t)

noncomputable def correctedV {d : ℕ} (cfg : Config) (x0 : Point d) (k : ℕ)
    (z : ℕ → Point d) (t : ℕ) (i : Fin d) : ℝ :=
  (trajectory cfg x0 k z t).secondMoment i / (1 - cfg.β₂ ^ t)

lemma correctedM_recurrence {d : ℕ} (cfg : Config)
    (hβ : 0 ≤ cfg.β₁) (hβ1 : cfg.β₁ < 1)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) :
    correctedM cfg x0 k z (t + 1) i =
      AffineAdamBiasCorrection.memory cfg.β₁ t * correctedM cfg x0 k z t i +
        (1 - AffineAdamBiasCorrection.memory cfg.β₁ t) * z t i := by
  have h := AffineAdamBiasCorrection.corrected_recurrence
    (u := (trajectory cfg x0 k z t).momentum i) (z := z t i) hβ hβ1 t
    (by intro ht; subst t; rfl)
  simpa only [correctedM, trajectory, coreStep, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] using h

lemma correctedV_recurrence {d : ℕ} (cfg : Config)
    (hβ : 0 ≤ cfg.β₂) (hβ1 : cfg.β₂ < 1)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) :
    correctedV cfg x0 k z (t + 1) i =
      AffineAdamBiasCorrection.memory cfg.β₂ t * correctedV cfg x0 k z t i +
        (1 - AffineAdamBiasCorrection.memory cfg.β₂ t) * (z t i) ^ 2 := by
  have h := AffineAdamBiasCorrection.corrected_recurrence
    (u := (trajectory cfg x0 k z t).secondMoment i) (z := (z t i) ^ 2) hβ hβ1 t
    (by intro ht; subst t; rfl)
  simpa only [correctedV, trajectory, coreStep, Adam.secondMomentStep, sub_sub_cancel] using h

lemma correctedV_nonneg {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) :
    0 ≤ correctedV cfg x0 k z t i := by
  cases t with
  | zero => simp [correctedV]
  | succ t =>
    exact div_nonneg (default_invariants cfg hb1 hb2 x0 k z (t + 1) i).1
      (AffineAdamBiasCorrection.correction_pos (by rw [hb2]; norm_num)
        (by rw [hb2]; norm_num) t).le

noncomputable def momentumError {d : ℕ} (cfg : Config) (x0 : Point d) (k : ℕ)
    (z h : ℕ → Point d) : ℕ → ℝ
  | 0 => 0
  | t + 1 => ∑ i, |correctedM cfg x0 k z (t + 1) i - h t i|

noncomputable def normalizerError {d : ℕ} (cfg : Config) (x0 : Point d) (k : ℕ)
    (z h : ℕ → Point d) : ℕ → ℝ
  | 0 => 0
  | t + 1 => ∑ i, |Real.sqrt (correctedV cfg x0 k z (t + 1) i) - (|h t i|)|

noncomputable def drift {d : ℕ} (h : ℕ → Point d) : ℕ → ℝ
  | 0 => 0
  | t + 1 => sumNorm (h (t + 1) - h t)

lemma momentum_error_recurrence {d : ℕ} (cfg : Config) (hb1 : cfg.β₁ = 9 / 10)
    (x0 : Point d) (k : ℕ) (z h : ℕ → Point d) (t : ℕ) :
    momentumError cfg x0 k z h (t + 1) ≤
      (9 / 10 : ℝ) * momentumError cfg x0 k z h t +
        (9 / 10 : ℝ) * drift h t + sumNorm (z t - h t) := by
  have hb : 0 ≤ cfg.β₁ := by rw [hb1]; norm_num
  have hb' : cfg.β₁ < 1 := by rw [hb1]; norm_num
  cases t with
  | zero =>
    simp only [momentumError, drift, mul_zero, zero_add, sumNorm, PiLp.sub_apply]
    apply Finset.sum_le_sum
    intro i _
    rw [correctedM_recurrence cfg hb hb']
    simp [AffineAdamBiasCorrection.memory]
  | succ t =>
    simp only [momentumError, drift, sumNorm, PiLp.sub_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [correctedM_recurrence cfg hb hb']
    obtain ⟨h0, h1⟩ := AffineAdamBiasCorrection.memory_bounds hb hb' (t + 1)
    have h2 : AffineAdamBiasCorrection.memory cfg.β₁ (t + 1) ≤ (9 / 10 : ℝ) := by simpa [hb1] using h1
    exact AffineAdamBiasCorrection.corrected_momentum_transport h0 (by linarith) h2

lemma normalizer_error_recurrence {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (x0 : Point d) (k : ℕ) (z h : ℕ → Point d) (t : ℕ) :
    normalizerError cfg x0 k z h (t + 1) ≤
      (1999 / 2000 : ℝ) * normalizerError cfg x0 k z h t +
        (1999 / 2000 : ℝ) * drift h t + sumNorm (z t - h t) := by
  have hb : 0 ≤ cfg.β₂ := by rw [hb2]; norm_num
  have hb' : cfg.β₂ < 1 := by rw [hb2]; norm_num
  cases t with
  | zero =>
    simp only [normalizerError, drift, mul_zero, zero_add, sumNorm, PiLp.sub_apply]
    apply Finset.sum_le_sum
    intro i _
    rw [correctedV_recurrence cfg hb hb']
    simp only [AffineAdamBiasCorrection.memory, pow_zero, sub_self, mul_zero,
      zero_div, zero_mul, sub_zero, one_mul, zero_add, Real.sqrt_sq_eq_abs]
    exact abs_abs_sub_abs_le_abs_sub _ _
  | succ t =>
    simp only [normalizerError, drift, sumNorm, PiLp.sub_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [correctedV_recurrence cfg hb hb']
    obtain ⟨h0, h1⟩ := AffineAdamBiasCorrection.memory_bounds hb hb' (t + 1)
    have h2 : Real.sqrt (AffineAdamBiasCorrection.memory cfg.β₂ (t + 1)) ≤ (1999 / 2000 : ℝ) := by
      apply (Real.sqrt_le_left (by norm_num)).mpr
      rw [hb2] at h1 ⊢
      norm_num at *
      linarith
    exact AffineAdamHistory.rms_transport (correctedV_nonneg cfg hb1 hb2 x0 k z (t + 1) i)
      h0 (by linarith) h2

lemma maxNorm_move {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (hη : 0 ≤ cfg.η) (hδ : 0 < cfg.δ)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) :
    maxNorm ((trajectory cfg x0 k z (t + 1)).point - (trajectory cfg x0 k z t).point) ≤
      80 * cfg.η := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 80 * cfg.η)).mpr
  intro i
  exact coordinate_move cfg hb1 hb2 hη hδ x0 k z t i

lemma coordinate_alignment {d : ℕ} (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000) (hδ : 0 < cfg.δ)
    (x0 : Point d) (k : ℕ) (z : ℕ → Point d) (t : ℕ) (i : Fin d) (g : ℝ) :
    |g| - 82 * |correctedM cfg x0 k z (t + 1) i - g| -
      (|Real.sqrt (correctedV cfg x0 k z (t + 1) i) - (|g|)| + cfg.δ) ≤
      g * correctedM cfg x0 k z (t + 1) i /
        (Real.sqrt (correctedV cfg x0 k z (t + 1) i) + cfg.δ) := by
  have hs : 0 < Real.sqrt (correctedV cfg x0 k z (t + 1) i) + cfg.δ := by positivity
  have h := corrected_direction_bound cfg hb1 hb2 hδ x0 k z t i
  change |correctedM cfg x0 k z (t + 1) i /
    (Real.sqrt (correctedV cfg x0 k z (t + 1) i) + cfg.δ)| ≤ 80 at h
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs] at h
  have hv : Real.sqrt (correctedV cfg x0 k z (t + 1) i) + cfg.δ ≤
      |g| + (|Real.sqrt (correctedV cfg x0 k z (t + 1) i) - (|g|)| + cfg.δ) := by
    linarith [le_abs_self (Real.sqrt (correctedV cfg x0 k z (t + 1) i) - |g|)]
  simpa only [show (80 : ℝ) + 2 = 82 by norm_num] using
    AffineAdamHistory.scalar_alignment hs (abs_nonneg _) le_rfl hv h

end LongTails.Proofs.AffineAdamTrajectory
