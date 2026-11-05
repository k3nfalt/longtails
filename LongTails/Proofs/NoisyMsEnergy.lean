import LongTails.Proofs.GdConvex
import LongTails.Proofs.DampedGeneralizedDynamics
import LongTails.Algorithms.NoisyDampedNewton
import LongTails.Proofs.NoisyNewtonTuning

namespace LongTails.Proofs.NoisyMsEnergy

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma update_error_identity (z u g e : E) (a : ℝ) :
    ‖z - a • (g + e) - u‖ ^ 2 / 2 =
      ‖z - a • g - u‖ ^ 2 / 2 - a * ⟪e, z - a • g - u⟫ +
        a ^ 2 * ‖e‖ ^ 2 / 2 := by
  rw [show z - a • (g + e) - u = (z - a • g - u) - a • e by module,
    norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm (z - a • g - u) e]
  ring

omit [CompleteSpace E] in
lemma damped_mix {f : E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    (A p γ : ℝ) (hA : 0 ≤ A) (hp : 0 ≤ p)
    (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hden : 0 < A + γ * p) (x y : E) :
    (A + γ * p) * f (((1 - γ) * A / (A + γ * p)) • x +
      (γ * (A + p) / (A + γ * p)) • y) ≤
        (1 - γ) * A * f x + γ * (A + p) * f y := by
  have hsum : (1 - γ) * A / (A + γ * p) + γ * (A + p) / (A + γ * p) = 1 := by
    field_simp
    ring
  have hh := hc.2 (Set.mem_univ x) (Set.mem_univ y)
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hγ₁) hA) hden.le)
    (div_nonneg (mul_nonneg hγ (add_nonneg hA hp)) hden.le) hsum
  have hm := mul_le_mul_of_nonneg_left hh hden.le
  simp only [smul_eq_mul] at hm
  convert hm using 1
  field_simp

lemma damped_step {f : E → ℝ} {g : E → E} (A p γ a τ : ℝ)
    (hA : 0 ≤ A) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (ha : a = γ * p) (hscale : a ^ 2 * τ = γ * (A + p))
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (x z v y s xn u e : E)
    (hv : (A + p) • v = A • x + p • z) (hy : y = v + s)
    (hmix : (A + a) * f xn ≤ (1 - γ) * A * f x + γ * (A + p) * f y) :
    (A + a) * (f xn - f u) + ‖z - a • (g y + e) - u‖ ^ 2 / 2 ≤
      A * (f x - f u) + ‖z - u‖ ^ 2 / 2 +
        a ^ 2 / 2 * (‖g y + τ • s‖ ^ 2 - τ ^ 2 * ‖s‖ ^ 2) -
        a * ⟪e, z - a • g y - u⟫ + a ^ 2 * ‖e‖ ^ 2 / 2 := by
  have hx := OracleTemplate.Gradient.convex_support hc hg y x
  have hu := OracleTemplate.Gradient.convex_support hc hg y u
  have hvec : A • (x - y) + p • (u - y) =
      -(p • (z - u)) - (A + p) • s := by
    calc
      _ = A • x + p • u - (A + p) • v - (A + p) • s := by rw [hy]; module
      _ = _ := by rw [hv]; module
  have hi := congrArg (fun w => ⟪g y, w⟫) hvec
  simp only [inner_add_right, inner_sub_right, inner_neg_right, inner_smul_right] at hi
  have hx' := mul_le_mul_of_nonneg_left hx (mul_nonneg hγ hA)
  have hu' := mul_le_mul_of_nonneg_left hu (mul_nonneg hγ hp)
  have hi' := congrArg (fun t : ℝ => γ * t) hi
  have hobj : (A + a) * (f xn - f u) ≤ A * (f x - f u) +
      a * ⟪g y, z - u⟫ + γ * (A + p) * ⟪g y, s⟫ := by
    simp only [inner_sub_right] at hx' hu' ⊢
    rw [ha] at *
    nlinarith only [hmix, hx', hu', hi']
  have hn : ‖z - a • g y - u‖ ^ 2 =
      ‖z - u‖ ^ 2 - 2 * a * ⟪g y, z - u⟫ + a ^ 2 * ‖g y‖ ^ 2 := by
    rw [show z - a • g y - u = (z - u) - a • g y by abel, norm_sub_sq_real]
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (z - u) (g y)]
    ring
  have hr : ‖g y + τ • s‖ ^ 2 =
      ‖g y‖ ^ 2 + 2 * τ * ⟪g y, s⟫ + τ ^ 2 * ‖s‖ ^ 2 := by
    rw [norm_add_sq_real]
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [update_error_identity, hn, hr]
  have hs := congrArg (fun t : ℝ => t * ⟪g y, s⟫) hscale
  nlinarith only [hobj, hs]

lemma residual_dissipation (before after noise a t r e : ℝ)
    (hstep : after ≤ before + a ^ 2 / 2 * (r ^ 2 - t ^ 2) + noise)
    (hres : r ^ 2 ≤ t ^ 2 / 4 + 8 * e ^ 2) :
    after + 3 / 8 * a ^ 2 * t ^ 2 ≤
      before + 4 * a ^ 2 * e ^ 2 + noise := by
  have hh := mul_le_mul_of_nonneg_left hres (sq_nonneg a)
  nlinarith only [hstep, hh]

open OracleTemplate.GeneralizedAccelerated (tentativeWeight coupling)
open LongTails.Algorithms.NoisyDampedNewton (Trial actualWeight trialPoint finish)

lemma finish_energy {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (t : Trial E) (hA : 0 ≤ t.previous.A) (hη : 0 < t.previous.guess)
    (hτ : t.previous.guess ≤ t.curvature) (floor : ℝ) (u e : E) :
    let a := actualWeight t
    let next := finish floor t (g (trialPoint t) + e)
    next.A * (f next.x - f u) + ‖next.z - u‖ ^ 2 / 2 ≤
      t.previous.A * (f t.previous.x - f u) + ‖t.previous.z - u‖ ^ 2 / 2 +
      a ^ 2 / 2 * (‖g (trialPoint t) + t.curvature • t.displacement‖ ^ 2 -
        t.curvature ^ 2 * ‖t.displacement‖ ^ 2) -
      a * ⟪e, t.previous.z - a • g (trialPoint t) - u⟫ + a ^ 2 * ‖e‖ ^ 2 / 2 := by
  have ht : 0 < t.curvature := hη.trans_le hτ
  have hp := OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos t.previous hη
  have he := OracleTemplate.GeneralizedAccelerated.tentativeWeight_equation t.previous hA hη
  have hγ : 0 < t.previous.guess / t.curvature := div_pos hη ht
  have hγ₁ : t.previous.guess / t.curvature ≤ 1 := (div_le_one ht).mpr hτ
  have hden : 0 < t.previous.A + t.previous.guess / t.curvature * tentativeWeight t.previous :=
    add_pos_of_nonneg_of_pos hA (mul_pos hγ hp)
  have hscale : actualWeight t ^ 2 * t.curvature =
      t.previous.guess / t.curvature * (t.previous.A + tentativeWeight t.previous) := by
    calc
      _ = t.previous.guess / t.curvature *
          (t.previous.guess * tentativeWeight t.previous ^ 2) := by
        unfold actualWeight
        field_simp
      _ = _ := by rw [he]
  have hv : (t.previous.A + tentativeWeight t.previous) • coupling t.previous =
      t.previous.A • t.previous.x + tentativeWeight t.previous • t.previous.z := by
    have hn : t.previous.A + tentativeWeight t.previous ≠ 0 := ne_of_gt (by linarith)
    simp only [coupling, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> field_simp
  have hm := damped_mix hc t.previous.A (tentativeWeight t.previous)
    (t.previous.guess / t.curvature) hA hp.le hγ.le hγ₁ hden t.previous.x (trialPoint t)
  exact damped_step t.previous.A (tentativeWeight t.previous)
    (t.previous.guess / t.curvature) (actualWeight t) t.curvature hA hp.le hγ.le rfl hscale hc hg
    t.previous.x t.previous.z (coupling t.previous) (trialPoint t) t.displacement
    (finish floor t (g (trialPoint t) + e)).x u e hv rfl hm

lemma residual_square (α r movement error : ℝ) (hα : α ≤ 1 / 4)
    (hr : 0 ≤ r) (ht : 0 ≤ movement)
    (hres : r ≤ α * movement + 2 * error) :
    r ^ 2 ≤ movement ^ 2 / 4 + 8 * error ^ 2 := by
  have hh := mul_le_mul_of_nonneg_right hα ht
  have hb : r ≤ movement / 4 + 2 * error := by linarith
  have hs := pow_le_pow_left₀ hr hb 2
  nlinarith only [hs, sq_nonneg (movement / 4 - 2 * error), sq_nonneg movement]

lemma finish_dissipation {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (t : Trial E) (hA : 0 ≤ t.previous.A) (hη : 0 < t.previous.guess)
    (hτ : t.previous.guess ≤ t.curvature) (floor : ℝ) (u e : E)
    (α modelError : ℝ) (hα : α ≤ 1 / 4)
    (hres : ‖g (trialPoint t) + t.curvature • t.displacement‖ ≤
      α * (t.curvature * ‖t.displacement‖) + 2 * modelError) :
    let a := actualWeight t
    let next := finish floor t (g (trialPoint t) + e)
    next.A * (f next.x - f u) + ‖next.z - u‖ ^ 2 / 2 +
      3 / 8 * a ^ 2 * (t.curvature * ‖t.displacement‖) ^ 2 ≤
      t.previous.A * (f t.previous.x - f u) + ‖t.previous.z - u‖ ^ 2 / 2 +
        4 * a ^ 2 * modelError ^ 2 - a * ⟪e, t.previous.z - a • g (trialPoint t) - u⟫ +
          a ^ 2 * ‖e‖ ^ 2 / 2 := by
  have hs := finish_energy hc hg t hA hη hτ floor u e
  have hr := residual_square α ‖g (trialPoint t) + t.curvature • t.displacement‖
    (t.curvature * ‖t.displacement‖) modelError hα (norm_nonneg _)
    (mul_nonneg (hη.le.trans hτ) (norm_nonneg _)) hres
  have hh := mul_le_mul_of_nonneg_left hr (sq_nonneg (actualWeight t))
  dsimp only at hs ⊢
  nlinarith only [hs, hh]

lemma exact_step_bounds (R before after D z model : ℝ) (hR : 0 ≤ R) (hz : 0 ≤ z)
    (hbefore : before ≤ 8 * R ^ 2) (hmodel : model ≤ R ^ 2) (hD : 0 ≤ D)
    (hafter : z ^ 2 / 2 ≤ after) (hstep : after + 3 / 8 * D ≤ before + model) :
    D ≤ 24 * R ^ 2 ∧ z ≤ 5 * R := by
  constructor
  · nlinarith only [hbefore, hmodel, hafter, hstep, sq_nonneg z]
  · have hs : z ^ 2 ≤ (5 * R) ^ 2 := by nlinarith only [hbefore, hmodel, hafter, hstep, hD]
    exact (sq_le_sq₀ hz (by positivity)).mp hs

lemma model_error_scaled (R ε ℓ p a e : ℝ) (hR : 0 ≤ R) (hℓ : 0 < ℓ)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hap : a ≤ p) (hcap : a * ε ≤ 32 * R ^ 2)
    (hnoise : p * e ^ 2 ≤ ε / (1073741824 * ℓ ^ 2)) :
    a * e ≤ R / (4096 * ℓ) := by
  have hn := (le_div_iff₀ (by positivity : 0 < 1073741824 * ℓ ^ 2)).mp hnoise
  have hm := mul_le_mul_of_nonneg_right hap (sq_nonneg e)
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ 1073741824 * ℓ ^ 2 by positivity)
  have hscaled : (a * e ^ 2) * (1073741824 * ℓ ^ 2) ≤ ε := hh.trans hn
  have hmul := mul_le_mul_of_nonneg_left hscaled ha
  have hs : (4096 * ℓ * (a * e)) ^ 2 ≤ R ^ 2 := by nlinarith only [hmul, hcap, sq_nonneg R]
  have hb := (sq_le_sq₀ (by positivity : 0 ≤ 4096 * ℓ * (a * e)) hR).mp hs
  exact (le_div_iff₀ (by positivity : 0 < 4096 * ℓ)).mpr (by nlinarith only [hb])

lemma clipping_center_bound (R ℓ a residual movement error : ℝ) (hR : 0 ≤ R) (hℓ : 0 < ℓ)
    (ha : 0 ≤ a) (hmovement : a * movement ≤ 5 * R)
    (herror : a * error ≤ R / (4096 * ℓ))
    (hresidual : residual ≤ movement / (262144 * ℓ) + 2 * error) :
    a * residual ≤ R / (512 * ℓ) := by
  have hh := mul_le_mul_of_nonneg_left hresidual ha
  have hm := div_le_div_of_nonneg_right hmovement (show 0 ≤ 262144 * ℓ by positivity)
  have he : a * (movement / (262144 * ℓ) + 2 * error) =
      a * movement / (262144 * ℓ) + 2 * (a * error) := by ring
  rw [he] at hh
  have hn : 5 * R / (262144 * ℓ) + 2 * (R / (4096 * ℓ)) ≤ R / (512 * ℓ) := by
    field_simp
    nlinarith
  linarith

open LongTails.Setups.StochasticLocalHessianConvex (Params spec)
open LongTails.Algorithms.NoisyDampedNewton (target curvatureFloor tolerance confidence modelRadius updateRadius)
open LongTails.Proofs.NoisyNewtonTuning

lemma correction_ready (p : Params) (hp : spec.valid p) {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (u : E) (hmin : ∀ x, f u ≤ f x) (t : Trial E)
    (hA : 0 ≤ t.previous.A) (hcap : t.previous.A ≤ target p / 2)
    (hfloor : curvatureFloor p ≤ t.previous.guess) (hτ : t.previous.guess ≤ t.curvature)
    (error : ℝ) (he : 0 ≤ error)
    (hmodel : error ≤ modelRadius p (tentativeWeight t.previous) / 2)
    (henergy : t.previous.A * (f t.previous.x - f u) + ‖t.previous.z - u‖ ^ 2 / 2 ≤ 8 * p.R ^ 2)
    (hres : ‖g (trialPoint t) + t.curvature • t.displacement‖ ≤
      tolerance p * (t.curvature * ‖t.displacement‖) + 2 * error) :
    ‖t.previous.z - actualWeight t • g (trialPoint t) - u‖ ≤ 5 * p.R ∧
      ‖g (trialPoint t) + t.curvature • t.displacement‖ ≤ updateRadius p (actualWeight t) / 2 := by
  have hR := hp.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.1
  have hW := target_pos p hp
  have hl := confidence_lower p hp
  have hlp : 0 < confidence p := by linarith
  have hη : 0 < t.previous.guess := lt_of_lt_of_le (by unfold curvatureFloor; positivity) hfloor
  have ht : 0 < t.curvature := hη.trans_le hτ
  have hw := OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos t.previous hη
  have ha := actualWeight_bounds t hη hτ
  have hap := ha.1
  have hpcap := tentativeWeight_cap t.previous (target p) hW hA hcap hfloor
  have hacap : actualWeight t * p.ε ≤ 32 * p.R ^ 2 :=
    (le_div_iff₀ hε).mp (ha.2.trans hpcap)
  have hnoise : tentativeWeight t.previous * error ^ 2 ≤ p.ε / (1073741824 * confidence p ^ 2) := by
    have hh := pow_le_pow_left₀ he hmodel 2
    rw [modelRadius_half_square p hp _ hw] at hh
    have hm := mul_le_mul_of_nonneg_left hh hw.le
    exact hm.trans_eq (by field_simp)
  have heScaled := model_error_scaled p.R p.ε (confidence p) (tentativeWeight t.previous)
    (actualWeight t) error hR.le hlp ha.1.le he ha.2 hacap hnoise
  have hcharge : 4 * actualWeight t ^ 2 * error ^ 2 ≤ p.R ^ 2 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4096 * confidence p)).mp heScaled
    have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 4096 * confidence p by linarith)
      (mul_nonneg ha.1.le he)
    have hs := pow_le_pow_left₀ (show 0 ≤ 2 * (actualWeight t * error) by positivity)
      (show 2 * (actualWeight t * error) ≤ p.R by nlinarith only [hb, hh]) 2
    nlinarith only [hs]
  let xn := finish (curvatureFloor p) t (g (trialPoint t))
  have hAn : 0 ≤ xn.A := by change 0 ≤ t.previous.A + actualWeight t; positivity
  have hgap := mul_nonneg hAn (sub_nonneg.mpr (hmin xn.x))
  have hs := finish_dissipation hc hg t hA hη hτ (curvatureFloor p) u 0
    (tolerance p) error (tolerance_bounds p hp).2 hres
  simp only [add_zero, inner_zero_left, mul_zero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hs
  have hb := exact_step_bounds p.R
    (t.previous.A * (f t.previous.x - f u) + ‖t.previous.z - u‖ ^ 2 / 2)
    (xn.A * (f xn.x - f u) + ‖xn.z - u‖ ^ 2 / 2)
    (actualWeight t ^ 2 * (t.curvature * ‖t.displacement‖) ^ 2) ‖xn.z - u‖
    (4 * actualWeight t ^ 2 * error ^ 2) hR.le (norm_nonneg _) henergy hcharge
    (by positivity) (by linarith only [hgap]) (by simpa only [mul_assoc] using hs)
  refine ⟨hb.2, ?_⟩
  have hmovement : actualWeight t * (t.curvature * ‖t.displacement‖) ≤ 5 * p.R := by
    have hs : (actualWeight t * (t.curvature * ‖t.displacement‖)) ^ 2 ≤ (5 * p.R) ^ 2 := by
      nlinarith only [hb.1, sq_nonneg p.R]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  have hr := clipping_center_bound p.R (confidence p) (actualWeight t)
    ‖g (trialPoint t) + t.curvature • t.displacement‖ (t.curvature * ‖t.displacement‖) error
    hR.le hlp ha.1.le hmovement heScaled (by simpa only [tolerance, div_mul_eq_mul_div, one_mul] using hres)
  have hh : ‖g (trialPoint t) + t.curvature • t.displacement‖ ≤
      (p.R / (512 * confidence p)) / actualWeight t :=
    (le_div_iff₀ ha.1).mpr (by simpa only [mul_comm] using hr)
  exact hh.trans_eq (by unfold updateRadius; ring)

end LongTails.Proofs.NoisyMsEnergy
