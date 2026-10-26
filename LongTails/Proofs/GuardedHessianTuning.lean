import LongTails.Proofs.GuardedGradientMoments
import LongTails.Algorithms.GuardedHessianTransport
import LongTails.Proofs.GuardedGeneralizedGeometry

open MeasureTheory

namespace LongTails.Proofs.GuardedHessianTuning

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport

lemma batch_root_tuning {r p B : ℝ} (hr : 0 ≤ r) (hp : 1 < p) (hB : 0 < B)
    (hsize : r ^ (p / (p - 1)) ≤ B) :
    r * (B ^ (p - 1))⁻¹ ^ p⁻¹ ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hsize hp1.le
  rw [← Real.rpow_mul hr, div_mul_cancel₀ p hp1.ne'] at hh
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hr p) hh (inv_nonneg.mpr hp0.le)
  rw [Real.rpow_rpow_inv hr hp0.ne'] at hroot
  have hden : 0 < (B ^ (p - 1)) ^ p⁻¹ := by positivity
  rw [Real.inv_rpow (Real.rpow_nonneg hB.le _)]
  exact (mul_le_mul_of_nonneg_right hroot (inv_nonneg.mpr hden.le)).trans_eq
    (mul_inv_cancel₀ hden.ne')

lemma reset_error_tuning {S ε p B : ℝ} (hS : 0 ≤ S) (hε : 0 < ε)
    (hp : 1 < p) (hB : 0 < B)
    (hsize : (65536 * S / ε) ^ (p / (p - 1)) ≤ B) :
    54 * S * (B ^ (p - 1))⁻¹ ^ p⁻¹ ≤ 54 * ε / 65536 := by
  have hh := batch_root_tuning (show 0 ≤ 65536 * S / ε by positivity) hp hB hsize
  have he := (mul_le_mul_of_nonneg_right hh hε.le)
  field_simp at he
  simp only [one_div] at he
  nlinarith

lemma transport_error_tuning {K η B q ε : ℝ} (hB : 0 < B) (hK : 0 < K)
    (hη : η = ε / (1048576 * K * B ^ q⁻¹)) :
    3840 * (K * η) * B ^ q⁻¹ = 3840 * ε / 1048576 := by
  rw [hη]
  have hpow : 0 < B ^ q⁻¹ := by positivity
  field_simp

lemma combined_error_small {r s ε : ℝ} (hε : 0 ≤ ε)
    (hr : r ≤ 54 * ε / 65536) (hs : s ≤ 3840 * ε / 1048576) :
    r + s ≤ ε / 128 := by linarith

lemma gradient_sum_tuning {η T ε Δ L δ G : ℝ}
    (hη : 0 < η) (hT : 0 < T) (hε : 0 ≤ ε)
    (hδ : δ ≤ ε / 128) (hcurv : L * η ≤ ε / 1048576)
    (hsteps : 1024 * Δ ≤ η * T * ε)
    (hdescent : η * G / 2 ≤ Δ + 2 * η * T * δ + T * (L * η ^ 2)) :
    G / T ≤ ε / 16 := by
  apply (div_le_iff₀ hT).mpr
  have ht : 0 ≤ η * T := by positivity
  have hd := mul_le_mul_of_nonneg_left hδ ht
  have hc := mul_le_mul_of_nonneg_left hcurv ht
  apply (mul_le_mul_iff_of_pos_left hη).mp
  nlinarith [mul_nonneg ht hε]

lemma stopped_gap_tuning {η T ε Δ L δ D : ℝ}
    (hη : 0 < η) (hT : 0 ≤ T) (hε : 0 < ε)
    (hδ : δ ≤ ε / 128) (hcurv : L * η ≤ ε / 1048576)
    (hsteps : T ≤ 1024 * Δ / (η * ε) + 2)
    (hdescent : D ≤ Δ + 2 * η * T * δ + T * (L * η ^ 2)) :
    D ≤ 33 * Δ + η * ε / 16 := by
  have ht : 0 ≤ η * T := by positivity
  have hd := mul_le_mul_of_nonneg_left hδ ht
  have hc := mul_le_mul_of_nonneg_left hcurv ht
  have hN := mul_le_mul_of_nonneg_right hsteps (mul_pos hη hε).le
  have he : (1024 * Δ / (η * ε) + 2) * (η * ε) = 1024 * Δ + 2 * η * ε := by
    field_simp
  rw [he] at hN
  nlinarith

lemma true_abort_tuning {L0 L1 M Δ ε η D : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hM : 0 < M) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (h0 : L0 * Δ ≤ M ^ 2 / 4294967296) (h1 : L1 * Δ ≤ M / 65536)
    (hstep : (L0 + L1 * M) * η * ε ≤ ε ^ 2 / 1048576)
    (hD : D ≤ 33 * Δ + η * ε / 16) :
    8 * (L0 + L1 * M) * D / M ^ 2 ≤ 1 / 128 := by
  apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ 8 * (L0 + L1 * M) by positivity)
  have hm := mul_le_mul_of_nonneg_right h1 hM.le
  have hs := (sq_le_sq₀ hε hM.le).mpr hεM
  nlinarith

lemma radius_estimates (p : LongTails.Setups.GeneralizedAffineHessianVector.Params)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    let M := LongTails.Algorithms.GuardedHessianTransport.guardRadius p
    0 < M ∧ p.ε ≤ M ∧ p.L0 * p.Δ ≤ M ^ 2 / 4294967296 ∧
      p.L1 * p.Δ ≤ M / 65536 := by
  dsimp only [LongTails.Algorithms.GuardedHessianTransport.guardRadius]
  have hs := Real.sqrt_nonneg (p.L0 * p.Δ)
  have he := Real.sq_sqrt (mul_nonneg hL0 hΔ)
  have hb := mul_nonneg hL1 hΔ
  refine ⟨by positivity, by nlinarith, ?_, by nlinarith⟩
  have hn : Real.sqrt (p.L0 * p.Δ) ≤ Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε := by linarith
  have hh := (sq_le_sq₀ hs (by positivity)).mpr hn
  nlinarith

lemma step_scale_bounds {L0 L1 H η M ε : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hη : 0 ≤ η) (hM : 0 < M)
    (hε : 0 ≤ ε) (hεM : ε ≤ M) (hH : L0 + L1 * M ≤ H)
    (hscale : H * η ≤ ε / 1048576) :
    L1 * η ≤ 1 / 4 ∧ L0 * η ≤ M / 4 ∧ L0 * η ≤ ε / 1048576 ∧
      (L0 + L1 * M) * η * ε ≤ ε ^ 2 / 1048576 := by
  have hh := mul_le_mul_of_nonneg_right hH hη
  have h0 := mul_nonneg hL0 hη
  have h1 := mul_nonneg hL1 hη
  have hcurv : L0 * η ≤ ε / 1048576 := by nlinarith [mul_nonneg h1 hM.le]
  have hlin : L1 * η ≤ 1 / 4 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith
  refine ⟨hlin, by linarith, hcurv, ?_⟩
  have he := mul_le_mul_of_nonneg_right (hh.trans hscale) hε
  nlinarith

lemma batchCount_pos (p : Params) : 0 < batchCount p := by unfold batchCount; omega
lemma stepCount_pos (p : Params) : 0 < stepCount p := by unfold stepCount; omega
lemma guardBatchCount_pos (p : Params) : 0 < guardBatchCount p := by unfold guardBatchCount; omega
lemma guardGroupCount_pos (p : Params) : 0 < guardGroupCount p := by unfold guardGroupCount; omega

@[simp] lemma tuned_steps (p : Params) : (tunedConfig p).steps + 1 = stepCount p := by
  dsimp only [tunedConfig]
  have := stepCount_pos p
  omega

@[simp] lemma tuned_epoch (p : Params) : (tunedConfig p).epoch + 1 = batchCount p := by
  dsimp only [tunedConfig]
  have := batchCount_pos p
  omega

@[simp] lemma tuned_resetBatch (p : Params) : (tunedConfig p).resetBatch + 1 = batchCount p := by
  dsimp only [tunedConfig]
  have := batchCount_pos p
  omega

@[simp] lemma tuned_guardBatch (p : Params) : (tunedConfig p).guardBatch + 1 = guardBatchCount p := by
  dsimp only [tunedConfig]
  have := guardBatchCount_pos p
  omega

@[simp] lemma tuned_groups (p : Params) : (tunedConfig p).groups + 1 = guardGroupCount p := by
  dsimp only [tunedConfig]
  have := guardGroupCount_pos p
  omega

lemma transportScale_pos (p : Params) (hv : spec.valid p) : 0 < transportScale p := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := (radius_estimates p hL0 hL1 hΔ hε).1
  unfold transportScale
  positivity

lemma stepSize_pos (p : Params) (hv : spec.valid p) : 0 < stepSize p := by
  have hH := transportScale_pos p hv
  have hB := batchCount_pos p
  have hε := hv.2.2.2.2.2.2.2.2.2.2.2
  unfold stepSize
  positivity

lemma stepSize_scale (p : Params) (hv : spec.valid p) :
    transportScale p * stepSize p ≤ p.ε / 1048576 := by
  have hH := transportScale_pos p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hB : (1 : ℝ) ≤ batchCount p := by exact_mod_cast batchCount_pos p
  have hpow : 1 ≤ (batchCount p : ℝ) ^ p.q⁻¹ :=
    Real.one_le_rpow hB (inv_nonneg.mpr (by linarith))
  have hpowpos : 0 < (batchCount p : ℝ) ^ p.q⁻¹ := by linarith
  unfold stepSize
  have he : transportScale p *
      (p.ε / (1048576 * transportScale p * (batchCount p : ℝ) ^ p.q⁻¹)) =
        p.ε / (1048576 * (batchCount p : ℝ) ^ p.q⁻¹) := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)

lemma batchCount_size (p : Params) :
    (65536 * (p.σg + p.αg * guardRadius p) / p.ε) ^ (p.p / (p.p - 1)) ≤ (batchCount p : ℝ) := by
  have hh := Nat.le_ceil ((65536 * (p.σg + p.αg * guardRadius p) / p.ε) ^ (p.p / (p.p - 1)))
  unfold batchCount
  push_cast
  linarith

lemma guardBatchCount_size (p : Params) :
    (1048576 * (p.σg / guardRadius p + p.αg)) ^ (p.p / (p.p - 1)) ≤ (guardBatchCount p : ℝ) := by
  have hh := Nat.le_ceil ((1048576 * (p.σg / guardRadius p + p.αg)) ^ (p.p / (p.p - 1)))
  unfold guardBatchCount
  push_cast
  linarith

lemma stepCount_bounds (p : Params) (hv : spec.valid p) :
    1024 * p.Δ ≤ stepSize p * (stepCount p : ℝ) * p.ε ∧
      (stepCount p : ℝ) ≤ 1024 * p.Δ / (stepSize p * p.ε) + 2 := by
  have hη := stepSize_pos p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hlo := Nat.le_ceil (1024 * p.Δ / (stepSize p * p.ε))
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 1024 * p.Δ / (stepSize p * p.ε) by positivity)
  have hden : 0 < stepSize p * p.ε := mul_pos hη hε
  have hmul := (div_le_iff₀ hden).mp hlo
  unfold stepCount
  push_cast
  constructor <;> nlinarith

lemma dyadic_log_bound {x : ℝ} (hx : 0 < x) (n : ℕ)
    (hn : Real.log x / Real.log 2 ≤ (n : ℝ)) : (1 / 2 : ℝ) ^ n ≤ 1 / x := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := (div_le_iff₀ hlog).mp hn
  have hp := Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2) hh
  simpa only [one_div_pow] using one_div_le_one_div_of_le hx hp

lemma guardGroupCount_bound (p : Params) :
    (1 / 2 : ℝ) ^ guardGroupCount p ≤ 1 / (128 * (stepCount p : ℝ)) := by
  have ht := stepCount_pos p
  apply dyadic_log_bound (by positivity)
  have hh := Nat.le_ceil (Real.log (128 * (stepCount p : ℝ)) / Real.log 2)
  unfold guardGroupCount
  push_cast
  linarith

lemma guardGroupCount_small (p : Params) : (1 / 2 : ℝ) ^ guardGroupCount p ≤ 1 / 16 := by
  have ht : (1 : ℝ) ≤ stepCount p := by exact_mod_cast stepCount_pos p
  exact (guardGroupCount_bound p).trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))

lemma tuned_estimator_small (p : Params) (hv : spec.valid p) :
    54 * (p.σg + p.αg * guardRadius p) *
      (((batchCount p : ℝ) ^ (p.p - 1))⁻¹ ^ p.p⁻¹) +
      3840 * (transportScale p * stepSize p) * (batchCount p : ℝ) ^ p.q⁻¹ ≤ p.ε / 128 := by
  have hH := transportScale_pos p hv
  have hB : (0 : ℝ) < batchCount p := by exact_mod_cast batchCount_pos p
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := (radius_estimates p hL0 hL1 hΔ hε).1
  apply combined_error_small hε.le
  · exact reset_error_tuning (by positivity) hε hp hB (batchCount_size p)
  · exact (transport_error_tuning hB hH (rfl : stepSize p = _)).le

lemma tuned_guard_batch (p : Params) (hv : spec.valid p) :
    6 * (p.σg / guardRadius p + p.αg) ^ p.p /
      (guardBatchCount p : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := (radius_estimates p hL0 hL1 hΔ hε).1
  exact GuardedGradientMoments.guard_batch_size_suffices (by positivity) hp
    (guardBatchCount p) (guardBatchCount_pos p) (guardBatchCount_size p)

lemma tuned_step_conditions (p : Params) (hv : spec.valid p) :
    p.L1 * stepSize p ≤ 1 / 4 ∧ p.L0 * stepSize p ≤ guardRadius p / 4 ∧
      p.L0 * stepSize p ≤ p.ε / 1048576 ∧
      (p.L0 + p.L1 * guardRadius p) * stepSize p * p.ε ≤ p.ε ^ 2 / 1048576 := by
  have hη := stepSize_pos p hv
  have hscale := stepSize_scale p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := radius_estimates p hL0 hL1 hΔ hε
  apply step_scale_bounds hL0 hL1 hη.le hM.1 hε.le hM.2.1 _ hscale
  unfold transportScale
  have := div_nonneg hε.le hM.1.le
  have := mul_nonneg hαh hM.1.le
  linarith

lemma initial_gradient_bound (p : Params) (hv : spec.valid p)
    (f : Space p → ℝ) (g : Space p → Space p) {m : ℝ}
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ) : ‖g p.x0‖ ≤ guardRadius p := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := radius_estimates p hL0 hL1 hΔ hε
  have hh := GuardedGeneralizedGeometry.gradient_gap_exact hL0 hL1 hf hg hH hm p.x0
  have hb := mul_le_mul_of_nonneg_left hgap
    (show 0 ≤ 8 * (p.L0 + p.L1 * ‖g p.x0‖) by positivity)
  apply GuardedGeneralizedGeometry.norm_bound_of_gap (norm_nonneg _) hM.1.le (hh.trans hb)
  · nlinarith [hM.2.2.2]
  · nlinarith [hM.2.2.1, sq_nonneg (guardRadius p)]

end LongTails.Proofs.GuardedHessianTuning
