import LongTails.Proofs.PLMinimaxNewton
import LongTails.Proofs.PLMinimaxTuning
import LongTails.Proofs.PLMinimaxJet

open LongTails.Setups.NonconvexPLSecondOrder
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

lemma setup_fixed_refinement {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (u : ℕ → Space p)
    (hu : ∀ n, u (n + 1) = u n + residualNewtonStep
      (regularizedGradient (gradient f) p.L z (u n))
      (regularizedHessian (fderiv ℝ (gradient f) (u n)) p.L) p.ρ)
    (hstart : ∃ q, regularizedGradient (gradient f) p.L z q = 0 ∧
      ‖q - u 0‖ ≤ p.μ / (64 * p.ρ)) :
    ‖regularizedGradient (gradient f) p.L z (u (tuning p).refinementSteps)‖ ≤
      (tuning p).residualTolerance := by
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hp := tuning_positive hv
  have hτ := hp.2.2.2.2.2.2.2.2.2
  have hr : 0 ≤ p.μ / (64 * p.ρ) := by positivity
  have he : p.ρ * (p.μ / (64 * p.ρ)) = p.μ / 64 := by field_simp [hρ.ne']
  have hs : p.ρ * (p.μ / (64 * p.ρ)) ≤ p.μ / 16 := by rw [he]; linarith only [hμ]
  have hb := (setup_refinement hv hf z u hu hr hs hstart).2
  let n := ⌈Real.log (1 + p.ρ * (p.μ / (64 * p.ρ)) ^ 2 / (tuning p).residualTolerance) / Real.log 2⌉₊
  have hN : (tuning p).refinementSteps = n + 1 := rfl
  rw [hN]
  have hn := refinement_iterations_suffice (B := p.ρ * (p.μ / (64 * p.ρ)) ^ 2)
    (by positivity) hτ n (Nat.le_ceil _)
  apply (hb n).trans
  convert hn using 1
  ring

lemma setup_residual_certificate {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (w : Space p)
    (hr : ‖regularizedGradient (gradient f) p.L z w‖ ≤ (tuning p).residualTolerance) :
    ∃ y, (∀ v, f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, v)) ≤
      f (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))) ∧
      ‖w - WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y)‖ ≤
        (tuning p).distanceTolerance := by
  have H := setup_hyp hv hf
  obtain ⟨q, hq, hd⟩ := regularized_root_error H z w
  obtain ⟨hx, hy⟩ := regularized_zero_saddle H z q hq
  have he : (tuning p).residualTolerance = p.μ * (tuning p).distanceTolerance / 8 := rfl
  have hb : ‖q - w‖ ≤ (tuning p).distanceTolerance := by
    apply (mul_le_mul_iff_right₀ (show 0 < p.μ / 8 from div_pos hv.1 (by norm_num))).mp
    calc
      (p.μ / 8) * ‖q - w‖ ≤ ‖regularizedGradient (gradient f) p.L z w‖ := hd
      _ ≤ (tuning p).residualTolerance := hr
      _ = (p.μ / 8) * (tuning p).distanceTolerance := by rw [he]; ring
  refine ⟨q.snd, hy, ?_⟩
  have hpair : WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, q.snd) = q := by
    rw [← hx]
    exact (WithLp.equiv 2 (p.E × p.F)).left_inv q
  rw [hpair, norm_sub_rev]
  exact hb

lemma setup_tracking_start {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z h : p.E) (w : Space p)
    (hr : ‖regularizedGradient (gradient f) p.L z w‖ ≤ (tuning p).residualTolerance)
    (hh : ‖h‖ ≤ (tuning p).mesh) :
    ∃ q, regularizedGradient (gradient f) p.L (z + h) q = 0 ∧ ‖q - w‖ ≤ p.μ / (64 * p.ρ) := by
  have H := setup_hyp hv hf
  obtain ⟨y, hy, hd⟩ := setup_residual_certificate hv hf z w hr
  obtain ⟨q, hq, hdist⟩ := regularized_roots_move H z y hy h
  refine ⟨q, ?_, ?_⟩
  · rw [regularizedGradient_center_shift (gradient f) p.L z h q] at hq
    exact add_eq_right.mp hq
  · have hC : 0 < 4 + 32 * p.L / p.μ := by have := H.hL; have := H.hμ; positivity
    have hs : 0 < Real.sqrt (4 + 32 * p.L / p.μ) := Real.sqrt_pos.mpr hC
    have hmesh : Real.sqrt (4 + 32 * p.L / p.μ) * (tuning p).mesh = p.μ / (128 * p.ρ) := by
      change Real.sqrt (4 + 32 * p.L / p.μ) *
        (p.μ / (128 * p.ρ * Real.sqrt (4 + 32 * (p.L / p.μ)))) = _
      rw [show 4 + 32 * (p.L / p.μ) = 4 + 32 * p.L / p.μ by ring]
      field_simp [hs.ne', hv.2.2.1.ne']
    have hm := mul_le_mul_of_nonneg_left hh hs.le
    rw [hmesh] at hm
    have he := (tuning_distance_bounds p).1
    have hn := dist_triangle q
      (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y)) w
    simp only [dist_eq_norm] at hn
    rw [norm_sub_rev (WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y)) w] at hn
    calc
      ‖q - w‖ ≤ _ := hn
      _ ≤ p.μ / (128 * p.ρ) + p.μ / (128 * p.ρ) :=
        add_le_add (hdist.trans hm) (hd.trans he)
      _ = p.μ / (64 * p.ρ) := by ring

lemma setup_jet_certificate {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (w : Space p)
    (hr : ‖regularizedGradient (gradient f) p.L z w‖ ≤ (tuning p).residualTolerance) :
    ‖(2 * p.L) • (z - w.fst) - gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z‖ ≤
      (tuning p).gradientTolerance ∧
    ‖envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L) (tuning p).regularization -
      fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z‖ ≤
        (tuning p).hessianTolerance := by
  have H := setup_hyp hv hf
  have hp := tuning_positive hv
  have hb := hp.2.2.2.2.2.2.1
  have hθ := hp.2.2.2.2.2.2.2.1
  obtain ⟨y, hy, hd⟩ := setup_residual_certificate hv hf z w hr
  let q : Space p := WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y)
  have hd' : ‖w - q‖ ≤ (tuning p).distanceTolerance := hd
  have hdists := tuning_distance_bounds p
  constructor
  · have hx := WithLp.norm_fst_le p.E (w - q)
    change ‖w.fst - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z‖ ≤ ‖w - q‖ at hx
    have hx' := hx.trans hd'
    rw [setup_envelope_gradient hv hf]
    have he : (2 * p.L) • (z - w.fst) -
        (2 * p.L) • (z - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) =
        -(2 * p.L) • (w.fst - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z) := by
      simp only [smul_sub, neg_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (show 0 < 2 * p.L by linarith [H.hL])]
    have ha := (le_div_iff₀ (show 0 < 2 * p.L by linarith [H.hL])).mp hdists.2.1
    have hh := mul_le_mul_of_nonneg_left hx' (show 0 ≤ 2 * p.L by linarith [H.hL])
    nlinarith only [ha, hh]
  · have hroot := setup_envelopeHessianApprox_norm hv hf z y hy hθ
      (show 0 ≤ (tuning p).hessianTolerance / 2 by positivity) (tuning_hessian_bias hv).le
    have hpert := setup_envelopeHessianApprox_difference hv hf w q hθ
    have hC : 0 < (tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2 := by positivity
    have hden : 0 < 8 * p.L ^ 2 * p.ρ *
        ((tuning p).regularization⁻¹ + 18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2) := by
      have := H.hL; have := hv.2.2.1; positivity
    have ht := (le_div_iff₀ hden).mp hdists.2.2.1
    have hdscaled := mul_le_mul_of_nonneg_left hd'
      (show 0 ≤ 4 * p.L ^ 2 * ((tuning p).regularization⁻¹ +
        18 * p.L ^ 2 * (tuning p).regularization⁻¹ ^ 2) * p.ρ by have := hv.2.2.1; positivity)
    have htri := dist_triangle
      (envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) w) p.L) (tuning p).regularization)
      (envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) q) p.L) (tuning p).regularization)
      (fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z)
    simp only [dist_eq_norm] at htri
    change ‖envelopeHessianApprox p.L (regularizedHessian (fderiv ℝ (gradient f) q) p.L) (tuning p).regularization -
      fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z‖ ≤ (tuning p).hessianTolerance / 2 at hroot
    nlinarith only [hroot, hpert, ht, hdscaled, htri]

lemma setup_output_certificate {p : Params} {f : Space p → ℝ} {oracle}
    (hv : spec.valid p) (hf : spec.admissible p f oracle) (z : p.E) (w : Space p)
    (hr : ‖regularizedGradient (gradient f) p.L z w‖ ≤ (tuning p).residualTolerance)
    (hg : ‖gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L) z‖ ≤ p.ε / 8)
    (hc : ∀ v, -((25 / 96 : ℝ) * (tuning p).curvature) * ‖v‖ ^ 2 ≤
      ⟪fderiv ℝ (gradient (envelope (fun x y => f (WithLp.toLp 2 (x, y))) p.L)) z v, v⟫) :
    ‖gradient (value f) w.fst‖ ≤ p.ε ∧
      ∀ v, -(tuning p).curvature * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient (value f)) w.fst v⟫ := by
  have hp := tuning_positive hv
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hε := hv.2.2.2.2.2
  have hη := hp.2.1
  obtain ⟨y, hy, hd⟩ := setup_residual_certificate hv hf z w hr
  have hd' : ‖w.fst - primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z‖ ≤
      (tuning p).distanceTolerance := by
    exact (WithLp.norm_fst_le p.E
      (w - WithLp.toLp 2 (primal (fun x y => f (WithLp.toLp 2 (x, y))) p.L z, y))).trans hd
  have hb := tuning_distance_bounds p
  constructor
  · have htransfer := setup_approximate_gradient_transfer hv hf z w.fst
    have hs := mul_le_mul_of_nonneg_left (hd'.trans hb.2.2.2.1)
      (show 0 ≤ 4 * p.L ^ 2 / p.μ by positivity)
    have he : (4 * p.L ^ 2 / p.μ) * (p.ε / (8 * p.L * (p.L / p.μ))) = p.ε / 2 := by
      field_simp
      ring
    rw [he] at hs
    linarith only [htransfer, hg, hs, hε]
  · intro v
    have htransfer := setup_approximate_curvature_transfer hv hf z w.fst
      (show 0 ≤ (25 / 96 : ℝ) * (tuning p).curvature by positivity) hc v
    have hA : 0 < (1 + 2 * p.L / p.μ) ^ 3 := by positivity
    have hM := hp.1
    have hs := mul_le_mul_of_nonneg_left (hd'.trans hb.2.2.2.2)
      (mul_pos hM hA).le
    have he : ((tuning p).smoothness * (1 + 2 * p.L / p.μ) ^ 3) *
        ((tuning p).curvature / (2 * (tuning p).smoothness * (1 + 2 * p.L / p.μ) ^ 3)) =
          (tuning p).curvature / 2 := by field_simp
    rw [he] at hs
    have hcoef : 6 * ((2 * p.L) * (p.ρ * (4 + 32 * p.L / p.μ) / (2 * Real.sqrt (p.L * p.μ))) *
        (1 + 2 * p.L / p.μ) ^ 3) = (tuning p).smoothness * (1 + 2 * p.L / p.μ) ^ 3 := by
      change _ = (6 * ((2 * p.L) * (p.ρ * (4 + 32 * (p.L / p.μ)) /
        (2 * Real.sqrt (p.L * p.μ))))) * _
      ring
    rw [hcoef, real_inner_comm] at htransfer
    have hs' := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖v‖)
    have hη' := mul_nonneg hη.le (sq_nonneg ‖v‖)
    nlinarith only [htransfer, hs', hη']

end OracleTemplate.PLMinimax
