import LongTails.Proofs.CovarianceAcceleratedMixture

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.CovarianceAcceleratedEntropy

lemma entropy_scalar {p q W : ℝ} (hp : 0 < p) (hq : 0 < q) (hW : 0 < W) (F : ℝ) :
    q * (F - Real.log (q / p) - Real.log W) ≤ p * Real.exp F / W - q := by
  have h := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp (F - Real.log (q / p) - Real.log W)) hq.le
  have he : q * Real.exp (F - Real.log (q / p) - Real.log W) = p * Real.exp F / W := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (div_pos hq hp), Real.exp_log hW]
    field_simp
  rw [he] at h
  nlinarith

lemma integral_entropy_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p q F : Ω → ℝ) (hp : ∀ ω, 0 < p ω) (hq : ∀ ω, 0 < q ω)
    (hqi : Integrable q μ) (hqn : (∫ ω, q ω ∂μ) = 1)
    (hF : Integrable (fun ω => q ω * F ω) μ)
    (hKL : Integrable (fun ω => q ω * Real.log (q ω / p ω)) μ)
    (hExp : Integrable (fun ω => p ω * Real.exp (F ω)) μ)
    (hW : 0 < ∫ ω, p ω * Real.exp (F ω) ∂μ) :
    (∫ ω, q ω * F ω ∂μ) - (∫ ω, q ω * Real.log (q ω / p ω) ∂μ) ≤
      Real.log (∫ ω, p ω * Real.exp (F ω) ∂μ) := by
  let W := ∫ ω, p ω * Real.exp (F ω) ∂μ
  have hL : Integrable (fun ω => q ω * (F ω - Real.log (q ω / p ω) - Real.log W)) μ := by
    have h := (hF.sub hKL).sub (hqi.mul_const (Real.log W))
    apply h.congr
    filter_upwards [] with ω
    dsimp only [Pi.sub_apply]
    ring
  have hR : Integrable (fun ω => p ω * Real.exp (F ω) / W - q ω) μ :=
    (hExp.div_const W).sub hqi
  have h := integral_mono hL hR (fun ω => entropy_scalar (hp ω) (hq ω) hW (F ω))
  have hLi : (∫ ω, q ω * (F ω - Real.log (q ω / p ω) - Real.log W) ∂μ) =
      (∫ ω, q ω * F ω ∂μ) - (∫ ω, q ω * Real.log (q ω / p ω) ∂μ) - Real.log W := by
    simp_rw [mul_sub]
    rw [integral_sub (show Integrable (fun ω => q ω * F ω - q ω * Real.log (q ω / p ω)) μ
      from hF.sub hKL) (hqi.mul_const (Real.log W)), integral_sub hF hKL,
      integral_mul_const, hqn, one_mul]
  have hRi : (∫ ω, p ω * Real.exp (F ω) / W - q ω ∂μ) = 0 := by
    rw [integral_sub (hExp.div_const W) hqi, integral_div, hqn]
    change W / W - 1 = 0
    rw [div_self hW.ne', sub_self]
  rw [hLi, hRi] at h
  linarith

end LongTails.Proofs.CovarianceAcceleratedEntropy
