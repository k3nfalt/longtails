import LongTails.Proofs.SpectralGradientWindow
import LongTails.Proofs.SpectralGradientTuning
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

lemma minimizer_gradient_zero (p : Params) {f : p.E → ℝ} (u : p.E)
    (hu : IsMinOn f Set.univ u) : gradient f u = 0 := by
  have hh := (hu.isLocalMin (Filter.univ_mem)).fderiv_eq_zero
  simp [gradient, hh]

lemma spectral_accuracy (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hM : 0 ≤ p.M) (hR : 0 < p.R) (hε : 0 < p.ε)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hu : IsMinOn f Set.univ u) (hinit : ‖p.x0 - u‖ ≤ p.R)
    (hH : ∀ z, ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) u‖ ≤ p.M * ‖z - u‖) :
    f ((window p (gradient f))^[windowCount p] (probePoint p (gradient f) p.x0 (warmupCount p))) -
      f u ≤ p.ε := by
  let B := p.L * p.R
  let c := curvatureFactor p
  let H := 1 + c * B
  let a := p.μ / (2 * p.L)
  let x := probePoint p (gradient f) p.x0 (warmupCount p)
  let v := fun n => ‖gradient f ((window p (gradient f))^[n] x)‖
  have hL : 0 < p.L := hμ.trans_le hμL
  have hB : 0 < B := mul_pos hL hR
  have hc : 0 ≤ c := by dsimp [c, curvatureFactor]; positivity
  have hH1 : 1 ≤ H := by dsimp [H]; linarith [mul_nonneg hc hB.le]
  have hH0 : 0 < H := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * p.L)).mpr
    linarith
  have hzero : gradient f u = 0 := minimizer_gradient_zero p u hu
  have hg0 : ‖gradient f p.x0‖ ≤ B := by
    have hh := hlip p.x0 u
    rw [hzero, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hinit hL.le)
  have hw : warmupCount p = ⌈Real.log (2 * H) / a⌉₊ := by
    have he : 2 + 2 * curvatureFactor p * p.L * p.R = 2 * H := by dsimp [H, c, B]; ring
    unfold warmupCount
    rw [he]
    congr 1
    dsimp [a]
    field_simp

  have hwarm : (1 - a) ^ warmupCount p ≤ 1 / (2 * H) := by
    rw [hw]
    exact scalar_warmup ha ha1 hH1
  have hstart : v 0 ≤ B / (2 * H) := by
    have hh := probe_gradient_rate p hμ hμL hf hg hs hlip p.x0 (warmupCount p)
    change ‖gradient f x‖ ≤ (1 - a) ^ warmupCount p * ‖gradient f p.x0‖ at hh
    change ‖gradient f x‖ ≤ _
    calc
      _ ≤ (1 - a) ^ warmupCount p * ‖gradient f p.x0‖ := hh
      _ ≤ (1 / (2 * H)) * B := mul_le_mul hwarm hg0 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hstep (n : ℕ) : v (n + 1) ≤ c * (v n) ^ 2 := by
    change ‖gradient f ((window p (gradient f))^[n + 1] x)‖ ≤
      c * ‖gradient f ((window p (gradient f))^[n] x)‖ ^ 2
    rw [Function.iterate_succ_apply']
    exact window_gradient_bound p hμ hμL hM hf hg hs hlip u hzero hH _
  have hseq := quadratic_sequence_bound v hB hH0 hc
    (by dsimp [H]; linarith : c * B ≤ H) (fun n => norm_nonneg _) hstart hstep (windowCount p)
  have hacc : (v (windowCount p)) ^ 2 / (2 * p.μ) ≤ p.ε :=
    terminal_accuracy hB hH1 hμ hε (norm_nonneg _) hseq
  exact (gap_from_gradient hμ hs u _).trans hacc

end OracleTemplate.SpectralGradient
