import LongTails.Proofs.MonotoneHessianParameters
import LongTails.Proofs.ReusedCurvatureCorrection

namespace LongTails.Proofs.MonotoneHessianLedger

lemma ordinary_charge {ε γ τ d drop : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hscale : γ * τ = ε / 2 ^ 30) (hd : d ≤ 160 * τ) (hdrop : γ * τ ^ 2 ≤ drop) :
    ε / 2 ^ 40 * d ≤ drop := by
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ ε / 2 ^ 40 by positivity)
  have he := congrArg (fun x : ℝ => x * τ) hscale
  have hp := mul_nonneg hε hτ
  nlinarith

lemma curvature_charge {ε γ τ η : ℝ} (hγ : 0 ≤ γ) (_hτ : 0 ≤ τ)
    (hscale : γ * τ = ε / 2 ^ 30) (hη : η = 2 ^ 20 * τ) :
    γ * τ ^ 2 ≤ (7 * γ / 1024) * η ^ 2 / 3 ∧
    ε / 2 ^ 40 * (4 * τ + η) ≤ (7 * γ / 1024) * η ^ 2 / 3 := by
  rw [hη]
  have hp := mul_nonneg hγ (sq_nonneg τ)
  have he := congrArg (fun x : ℝ => x * τ) hscale
  constructor <;> nlinarith

lemma coarse_curvature_charge {ε γ δ H : ℝ} (hH : 0 < H) (hγ : 0 ≤ γ)
    (hδ : γ ≤ δ) (hscale : γ ^ 2 = H * ε) :
    ε / 2 ^ 40 * (δ / H) ≤ δ * (δ / H) ^ 2 / 3 := by
  have hδ0 : 0 ≤ δ := hγ.trans hδ
  have he : ε = γ ^ 2 / H := (eq_div_iff hH.ne').mpr (by nlinarith only [hscale])
  rw [he]
  have hs : γ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hγ hδ 2
  have hh := mul_le_mul_of_nonneg_right hs hδ0
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hH)).mp
  field_simp
  nlinarith [mul_nonneg hδ0 (sq_nonneg δ)]

lemma coarse_progress (p : LongTails.Setups.HessianLipschitzSecondOrder.Params)
    (hp : LongTails.Setups.HessianLipschitzSecondOrder.spec.valid p) :
    LongTails.Algorithms.MonotoneHessianReuse.progress p ≤
      LongTails.Algorithms.MonotoneHessianReuse.delta p *
        (LongTails.Algorithms.MonotoneHessianReuse.delta p / p.H) ^ 2 / 3 := by
  have hH := hp.1
  have hγ := MonotoneHessianParameters.gamma_pos p hp
  have hδ := MonotoneHessianParameters.delta_pos p hp
  have hle := MonotoneHessianParameters.gamma_le_delta p hp
  have hh := mul_le_mul hle (pow_le_pow_left₀ hγ.le hle 2) (sq_nonneg _ ) hδ.le
  unfold LongTails.Algorithms.MonotoneHessianReuse.progress
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hH)).mp
  field_simp
  nlinarith [mul_nonneg hγ.le (sq_nonneg (LongTails.Algorithms.MonotoneHessianReuse.gamma p))]

lemma charged_path {ℓ : ℝ} (value distance : ℕ → ℝ)
    (hstep : ∀ k, ℓ * distance k ≤ value k - value (k + 1)) (n : ℕ) :
    ℓ * ∑ k ∈ Finset.range n, distance k ≤ value 0 - value n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hh := hstep n
    nlinarith

lemma refresh_potential {R : ℝ} (potential distance : ℕ → ℝ) (fresh coarse : ℕ → ℕ)
    (hstep : ∀ k, R * fresh k + potential (k + 1) ≤
      potential k + distance k + R * coarse k) (n : ℕ) :
    R * (∑ k ∈ Finset.range n, fresh k : ℕ) + potential n ≤
      potential 0 + ∑ k ∈ Finset.range n, distance k + R * (∑ k ∈ Finset.range n, coarse k : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add]
    have hh := hstep n
    nlinarith

end LongTails.Proofs.MonotoneHessianLedger
