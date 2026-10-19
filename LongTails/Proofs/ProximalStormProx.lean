import LongTails.Proofs.GdConvex
import LongTails.Proofs.NormalizedStormMoments
import LongTails.Proofs.TerminalClippingEnergy
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] {Ω : Type} [MeasurableSpace Ω]

structure Hyp (p : Measure Ω) (f : E → ℝ) (g : E → Ω → E) (Lbar Γ : ℝ) (xstar : E) :
    Prop where
  convex : ConvexOn ℝ univ f
  grad : ∀ x, HasGradientAt f (gradient f x) x
  min : IsMinOn f univ xstar
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  var_int : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  sgc : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ Γ ^ 2 * ‖gradient f x‖ ^ 2
  diff_int : ∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) p
  mss : ∀ x y, ∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p ≤ Lbar ^ 2 * ‖x - y‖ ^ 2
  Lbar_pos : 0 < Lbar
  Γ_nn : 0 ≤ Γ

noncomputable def phiGrad (f : E → ℝ) (lam : ℝ) (xt x : E) : E :=
  gradient f x + (1 / lam) • (x - xt)

noncomputable def phi (f : E → ℝ) (lam : ℝ) (xt x : E) : ℝ :=
  f x + ‖x - xt‖ ^ 2 / (2 * lam)

noncomputable def prox (f : E → ℝ) (lam : ℝ) (xt : E) : E :=
  Classical.epsilon fun x => phiGrad f lam xt x = 0

section Deterministic

variable {p : Measure Ω} {f : E → ℝ} {g : E → Ω → E} {Lbar Γ : ℝ} {xstar : E}

lemma Hyp.grad_lip [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) (x y : E) :
    ‖gradient f x - gradient f y‖ ≤ Lbar * ‖x - y‖ := by
  have he : gradient f x - gradient f y = ∫ ω, (g x ω - g y ω) ∂p := by
    rw [integral_sub (H.int x) (H.int y), H.mean, H.mean]
  have hm : AEStronglyMeasurable (fun ω => g x ω - g y ω) p :=
    ((H.int x).sub (H.int y)).aestronglyMeasurable
  have h1 := norm_integral_le_integral_norm (μ := p) (fun ω => g x ω - g y ω)
  have h2 := NormalizedStorm.integral_norm_le_sqrt hm (H.diff_int x y)
  have h3 : Real.sqrt (∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p) ≤ Lbar * ‖x - y‖ := by
    rw [show Lbar * ‖x - y‖ = Real.sqrt ((Lbar * ‖x - y‖) ^ 2) by
      rw [Real.sqrt_sq (by have := H.Lbar_pos; positivity)]]
    exact Real.sqrt_le_sqrt (by rw [mul_pow]; exact H.mss x y)
  rw [he]
  linarith

lemma Hyp.grad_star (H : Hyp p f g Lbar Γ xstar) : gradient f xstar = 0 := by
  have hloc : IsLocalMin f xstar := H.min.isLocalMin Filter.univ_mem
  have hd := (H.grad xstar).hasFDerivAt
  have h0 := hloc.hasFDerivAt_eq_zero hd
  have : (InnerProductSpace.toDual ℝ E) (gradient f xstar) = 0 := h0
  exact (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.mp this

lemma Hyp.monotone (H : Hyp p f g Lbar Γ xstar) (x y : E) :
    0 ≤ ⟪gradient f x - gradient f y, x - y⟫ := by
  have h1 := Gradient.convex_support H.convex H.grad x y
  have h2 := Gradient.convex_support H.convex H.grad y x
  have he : ⟪gradient f x - gradient f y, x - y⟫ =
      -⟪gradient f x, y - x⟫ - ⟪gradient f y, x - y⟫ := by
    rw [inner_sub_left, ← inner_neg_right, neg_sub]
  linarith

lemma Hyp.phiGrad_mono (H : Hyp p f g Lbar Γ xstar) (lam : ℝ) (xt x y : E) :
    ‖x - y‖ ^ 2 / lam ≤ ⟪phiGrad f lam xt x - phiGrad f lam xt y, x - y⟫ := by
  have hm := H.monotone x y
  have he : phiGrad f lam xt x - phiGrad f lam xt y =
      (gradient f x - gradient f y) + (1 / lam) • (x - y) := by
    simp only [phiGrad]; module
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have : ‖x - y‖ ^ 2 / lam = 1 / lam * ‖x - y‖ ^ 2 := by ring
  linarith

lemma Hyp.phiGrad_lip [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt x y : E) :
    ‖phiGrad f lam xt x - phiGrad f lam xt y‖ ≤ (Lbar + 1 / lam) * ‖x - y‖ := by
  have he : phiGrad f lam xt x - phiGrad f lam xt y =
      (gradient f x - gradient f y) + (1 / lam) • (x - y) := by
    simp only [phiGrad]; module
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlam), add_mul]
  exact add_le_add_left (H.grad_lip x y) _

lemma Hyp.exists_prox [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt : E) : ∃ x, phiGrad f lam xt x = 0 := by
  set M := Lbar + 1 / lam
  have hM : 0 < M := by have := H.Lbar_pos; positivity
  set s := 1 / (lam * M ^ 2)
  have hs : 0 < s := by positivity
  set q := 1 - 1 / (lam * M) ^ 2
  have hlM : 1 ≤ lam * M := by
    have : lam * M = lam * Lbar + 1 := by
      simp only [M]; field_simp
    have := H.Lbar_pos; nlinarith
  have hq0 : 0 ≤ q := by
    have : 1 / (lam * M) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    simp only [q]; linarith
  have hq1 : q < 1 := by
    have : 0 < 1 / (lam * M) ^ 2 := by positivity
    simp only [q]; linarith
  let T : E → E := fun x => x - s • phiGrad f lam xt x
  have hT : ∀ x y, ‖T x - T y‖ ^ 2 ≤ q * ‖x - y‖ ^ 2 := by
    intro x y
    have he : T x - T y = (x - y) - s • (phiGrad f lam xt x - phiGrad f lam xt y) := by
      simp only [T]; module
    rw [he, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hmono := H.phiGrad_mono lam xt x y
    have hlip := H.phiGrad_lip hlam xt x y
    have hip : ⟪x - y, phiGrad f lam xt x - phiGrad f lam xt y⟫ =
        ⟪phiGrad f lam xt x - phiGrad f lam xt y, x - y⟫ := real_inner_comm _ _
    rw [hip]
    have hl2 : ‖phiGrad f lam xt x - phiGrad f lam xt y‖ ^ 2 ≤ M ^ 2 * ‖x - y‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hlip 2
    have hsM : s ^ 2 * M ^ 2 = s / lam := by
      simp only [s]; field_simp
    have hq : q = 1 - 2 * s / lam + s / lam := by
      simp only [q, s]; field_simp; ring
    have h1 : 2 * s * ⟪phiGrad f lam xt x - phiGrad f lam xt y, x - y⟫ ≥
        2 * s * (‖x - y‖ ^ 2 / lam) := by
      have := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 2 * s); linarith
    have h2 : (s * ‖phiGrad f lam xt x - phiGrad f lam xt y‖) ^ 2 ≤
        s ^ 2 * (M ^ 2 * ‖x - y‖ ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hl2 (by positivity)
    rw [hq]
    have : s ^ 2 * (M ^ 2 * ‖x - y‖ ^ 2) = s / lam * ‖x - y‖ ^ 2 := by
      rw [← mul_assoc, hsM]
    have h3 : 2 * s * (‖x - y‖ ^ 2 / lam) = 2 * s / lam * ‖x - y‖ ^ 2 := by ring
    nlinarith
  let K : NNReal := ⟨Real.sqrt q, Real.sqrt_nonneg _⟩
  have hK : LipschitzWith K T := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    change ‖T x - T y‖ ≤ Real.sqrt q * ‖x - y‖
    rw [← Real.sqrt_sq (norm_nonneg (T x - T y)), ← Real.sqrt_sq (norm_nonneg (x - y)),
      ← Real.sqrt_mul hq0]
    exact Real.sqrt_le_sqrt (hT x y)
  have hc : ContractingWith K T := by
    refine ⟨?_, hK⟩
    have : Real.sqrt q < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hq1
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    exact this
  have : Nonempty E := ⟨0⟩
  refine ⟨ContractingWith.fixedPoint T hc, ?_⟩
  have hfix := ContractingWith.fixedPoint_isFixedPt (f := T) hc
  have : s • phiGrad f lam xt (ContractingWith.fixedPoint T hc) = 0 := by
    have h' : T (ContractingWith.fixedPoint T hc) = ContractingWith.fixedPoint T hc := hfix
    simp only [T] at h'
    have := congrArg (fun z => ContractingWith.fixedPoint T hc - z) h'
    simpa using this
  exact (smul_eq_zero.mp this).resolve_left hs.ne'

lemma Hyp.prox_spec [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt : E) : phiGrad f lam xt (prox f lam xt) = 0 :=
  Classical.epsilon_spec (H.exists_prox hlam xt)

lemma Hyp.grad_prox [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt : E) :
    gradient f (prox f lam xt) = (1 / lam) • (xt - prox f lam xt) := by
  have h := H.prox_spec hlam xt
  simp only [phiGrad] at h
  have : gradient f (prox f lam xt) = -((1 / lam) • (prox f lam xt - xt)) :=
    eq_neg_of_add_eq_zero_left h
  rw [this, ← smul_neg, neg_sub]

lemma Hyp.dist_prox_le [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt x : E) :
    ‖x - prox f lam xt‖ ≤ lam * ‖phiGrad f lam xt x‖ := by
  have hm := H.phiGrad_mono lam xt x (prox f lam xt)
  rw [H.prox_spec hlam xt, sub_zero] at hm
  have hc := real_inner_le_norm (phiGrad f lam xt x) (x - prox f lam xt)
  have hn := norm_nonneg (x - prox f lam xt)
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hlam.le (norm_nonneg _)
  · have : ‖x - prox f lam xt‖ ^ 2 / lam ≤ ‖phiGrad f lam xt x‖ * ‖x - prox f lam xt‖ :=
      hm.trans hc
    rw [div_le_iff₀ hlam] at this
    have h2 : ‖x - prox f lam xt‖ * ‖x - prox f lam xt‖ ≤
        (lam * ‖phiGrad f lam xt x‖) * ‖x - prox f lam xt‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 hpos

lemma Hyp.prox_nonexpansive [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (a b : E) : ‖prox f lam a - prox f lam b‖ ≤ ‖a - b‖ := by
  set u := prox f lam a
  set w := prox f lam b
  have hm := H.monotone u w
  rw [H.grad_prox hlam a, H.grad_prox hlam b] at hm
  have he : (1 / lam) • (a - u) - (1 / lam) • (b - w) = (1 / lam) • ((a - b) - (u - w)) := by
    module
  rw [he, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hpos : 0 < 1 / lam := one_div_pos.mpr hlam
  have h1 : ‖u - w‖ ^ 2 ≤ ⟪a - b, u - w⟫ := by
    have := (mul_nonneg_iff_of_pos_left hpos).mp hm; linarith
  have h2 := real_inner_le_norm (a - b) (u - w)
  rcases (norm_nonneg (u - w)).eq_or_lt with h0 | hp
  · rw [← h0]; exact norm_nonneg _
  · have : ‖u - w‖ * ‖u - w‖ ≤ ‖a - b‖ * ‖u - w‖ := by nlinarith
    exact le_of_mul_le_mul_right this hp

lemma Hyp.continuous_prox [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) : Continuous (prox f lam) :=
  (LipschitzWith.of_dist_le_mul fun a b => by
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    exact H.prox_nonexpansive hlam a b : LipschitzWith 1 (prox f lam)).continuous

lemma Hyp.grad_continuous [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) :
    Continuous (gradient f) :=
  (LipschitzWith.of_dist_le_mul fun x y => by
    simp only [dist_eq_norm]
    exact H.grad_lip x y : LipschitzWith ⟨Lbar, H.Lbar_pos.le⟩ (gradient f)).continuous

lemma Hyp.phi_hasGradient (H : Hyp p f g Lbar Γ xstar) (lam : ℝ) (xt x : E) :
    HasGradientAt (phi f lam xt) (phiGrad f lam xt x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := (H.grad x).hasFDerivAt
  have h2 := (((hasStrictFDerivAt_norm_sq (x - xt)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const xt)).const_mul (1 / (2 * lam))
  have h3 := h1.add h2
  have hfun : phi f lam xt = fun z => f z + 1 / (2 * lam) * ((fun z : E => ‖z‖ ^ 2) ∘
      fun z => id z - xt) z := by
    funext z; simp only [phi, Function.comp, id]; ring
  rw [hfun]
  convert h3 using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, phiGrad, inner_add_left, real_inner_smul_left,
    add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  field_simp

lemma Hyp.phi_strong (H : Hyp p f g Lbar Γ xstar) {lam : ℝ} (hlam : 0 < lam) (xt x y : E) :
    phi f lam xt x + ⟪phiGrad f lam xt x, y - x⟫ + ‖y - x‖ ^ 2 / (2 * lam) ≤
      phi f lam xt y := by
  have h := Gradient.convex_support H.convex H.grad x y
  simp only [phi, phiGrad]
  have he : ‖y - xt‖ ^ 2 = ‖x - xt‖ ^ 2 + 2 * ⟪x - xt, y - x⟫ + ‖y - x‖ ^ 2 := by
    have : y - xt = (x - xt) + (y - x) := by abel
    rw [this, norm_add_sq_real]
  rw [inner_add_left, real_inner_smul_left, he]
  field_simp
  nlinarith

lemma Hyp.phi_prox_le [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt x : E) : phi f lam xt (prox f lam xt) ≤ phi f lam xt x := by
  have h := H.phi_strong hlam xt (prox f lam xt) x
  rw [H.prox_spec hlam xt, inner_zero_left, add_zero] at h
  have : 0 ≤ ‖x - prox f lam xt‖ ^ 2 / (2 * lam) := by positivity
  linarith

lemma Hyp.phi_pl (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt x : E) :
    phi f lam xt x - phi f lam xt (prox f lam xt) ≤ lam / 2 * ‖phiGrad f lam xt x‖ ^ 2 := by
  have h := H.phi_strong hlam xt x (prox f lam xt)
  set u := prox f lam xt - x
  have hq : -⟪phiGrad f lam xt x, u⟫ ≤ lam / 2 * ‖phiGrad f lam xt x‖ ^ 2 + ‖u‖ ^ 2 / (2 * lam) := by
    have hc := real_inner_le_norm (-phiGrad f lam xt x) u
    rw [inner_neg_left, norm_neg] at hc
    have : ‖phiGrad f lam xt x‖ * ‖u‖ ≤ lam / 2 * ‖phiGrad f lam xt x‖ ^ 2 + ‖u‖ ^ 2 / (2 * lam) := by
      have h0 : 0 ≤ (lam * ‖phiGrad f lam xt x‖ - ‖u‖) ^ 2 := sq_nonneg _
      rw [show lam / 2 * ‖phiGrad f lam xt x‖ ^ 2 + ‖u‖ ^ 2 / (2 * lam) =
        ((lam * ‖phiGrad f lam xt x‖) ^ 2 + ‖u‖ ^ 2) / (2 * lam) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith

lemma Hyp.phi_smooth [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt x y : E) :
    phi f lam xt y ≤ phi f lam xt x + ⟪phiGrad f lam xt x, y - x⟫ +
      (Lbar + 1 / lam) / 2 * ‖y - x‖ ^ 2 :=
  Gradient.smooth_upper_bound (fun z => H.phi_hasGradient lam xt z)
    (fun a b => H.phiGrad_lip hlam xt a b) x y

lemma Hyp.phiGrad_sq_le [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt x : E) :
    ‖phiGrad f lam xt x‖ ^ 2 ≤
      2 * (Lbar + 1 / lam) * (phi f lam xt x - phi f lam xt (prox f lam xt)) := by
  have hM : 0 < Lbar + 1 / lam := by have := H.Lbar_pos; positivity
  have hd := Gradient.descent hM (fun z => H.phi_hasGradient lam xt z)
    (fun a b => H.phiGrad_lip hlam xt a b) x
  have hl := H.phi_prox_le hlam xt (x - (1 / (Lbar + 1 / lam)) • phiGrad f lam xt x)
  have h1 : ‖phiGrad f lam xt x‖ ^ 2 / (2 * (Lbar + 1 / lam)) ≤
      phi f lam xt x - phi f lam xt (prox f lam xt) := by linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at h1

lemma Hyp.phi_start_le [IsProbabilityMeasure p] (H : Hyp p f g Lbar Γ xstar) {lam : ℝ}
    (hlam : 0 < lam) (xt : E) :
    phi f lam xt xt - phi f lam xt (prox f lam xt) ≤
      (Lbar + 1 / lam) * ‖xt - prox f lam xt‖ ^ 2 := by
  have h := H.phi_strong hlam xt xt (prox f lam xt)
  have hc := real_inner_le_norm (phiGrad f lam xt xt) (prox f lam xt - xt)
  have hg : ‖phiGrad f lam xt xt‖ ≤ (Lbar + 1 / lam) * ‖xt - prox f lam xt‖ := by
    have := H.phiGrad_lip hlam xt xt (prox f lam xt)
    rwa [H.prox_spec hlam xt, sub_zero] at this
  have hn : ‖prox f lam xt - xt‖ = ‖xt - prox f lam xt‖ := norm_sub_rev _ _
  have : 0 ≤ ‖prox f lam xt - xt‖ ^ 2 / (2 * lam) := by positivity
  have hm : ‖phiGrad f lam xt xt‖ * ‖prox f lam xt - xt‖ ≤
      (Lbar + 1 / lam) * ‖xt - prox f lam xt‖ ^ 2 := by
    rw [hn, sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hg (norm_nonneg _)
  have hi : -⟪phiGrad f lam xt xt, prox f lam xt - xt⟫ ≤
      ‖phiGrad f lam xt xt‖ * ‖prox f lam xt - xt‖ := by
    have := real_inner_le_norm (-phiGrad f lam xt xt) (prox f lam xt - xt)
    rwa [inner_neg_left, norm_neg] at this
  linarith

end Deterministic

section Noise

variable {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

lemma Hyp.centered_diff (H : Hyp p f g Lbar Γ xstar) (x y : E) :
    Integrable (fun ω => ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ^ 2) p ∧
      ∫ ω, ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ^ 2 ∂p ≤
        Lbar ^ 2 * ‖x - y‖ ^ 2 := by
  have hX : Integrable (fun ω => g x ω - g y ω) p := (H.int x).sub (H.int y)
  have hm : ∫ ω, (g x ω - g y ω) ∂p = gradient f x - gradient f y := by
    rw [integral_sub (H.int x) (H.int y), H.mean, H.mean]
  have h := TerminalClipping.centered_second_moment hX (H.diff_int x y)
  rw [hm] at h
  have he : ∀ ω, (g x ω - gradient f x) - (g y ω - gradient f y) =
      (g x ω - g y ω) - (gradient f x - gradient f y) := fun ω => by abel
  simp_rw [he]
  exact ⟨h.1, h.2.trans (H.mss x y)⟩

lemma Hyp.noise_bound (H : Hyp p f g Lbar Γ xstar) {lam : ℝ} (hlam : 0 < lam) (xt x : E) :
    ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤
      2 * Γ ^ 2 * ‖xt - prox f lam xt‖ ^ 2 / lam ^ 2 +
        2 * Lbar ^ 2 * lam ^ 2 * ‖phiGrad f lam xt x‖ ^ 2 := by
  set u := prox f lam xt
  have hpt : ∀ ω, ‖g x ω - gradient f x‖ ^ 2 ≤
      2 * ‖g u ω - gradient f u‖ ^ 2 +
        2 * ‖(g x ω - gradient f x) - (g u ω - gradient f u)‖ ^ 2 := by
    intro ω
    have := NormalizedStorm.sq_norm_add_le (g u ω - gradient f u)
      ((g x ω - gradient f x) - (g u ω - gradient f u))
    simpa using this
  obtain ⟨hci, hc⟩ := H.centered_diff x u
  have hint : Integrable (fun ω => 2 * ‖g u ω - gradient f u‖ ^ 2 +
      2 * ‖(g x ω - gradient f x) - (g u ω - gradient f u)‖ ^ 2) p :=
    ((H.var_int u).const_mul 2).add (hci.const_mul 2)
  have h1 := integral_mono (H.var_int x) hint hpt
  rw [integral_add ((H.var_int u).const_mul 2) (hci.const_mul 2), integral_const_mul,
    integral_const_mul] at h1
  have hs := H.sgc u
  have hgu : ‖gradient f u‖ = ‖xt - u‖ / lam := by
    rw [H.grad_prox hlam xt, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlam)]
    ring
  have hd := H.dist_prox_le hlam xt x
  have hd2 : ‖x - u‖ ^ 2 ≤ lam ^ 2 * ‖phiGrad f lam xt x‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [hgu, div_pow] at hs
  have hL2 : Lbar ^ 2 * ‖x - u‖ ^ 2 ≤ Lbar ^ 2 * (lam ^ 2 * ‖phiGrad f lam xt x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
  have : 2 * Γ ^ 2 * ‖xt - u‖ ^ 2 / lam ^ 2 = 2 * (Γ ^ 2 * (‖xt - u‖ ^ 2 / lam ^ 2)) := by ring
  rw [this]
  nlinarith

lemma Hyp.start_noise (H : Hyp p f g Lbar Γ xstar) {lam : ℝ} (hlam : 0 < lam) (xt : E) :
    ∫ ω, ‖g xt ω - gradient f xt‖ ^ 2 ∂p ≤
      Γ ^ 2 * (Lbar + 1 / lam) ^ 2 * ‖xt - prox f lam xt‖ ^ 2 := by
  have hs := H.sgc xt
  have hg : ‖gradient f xt‖ ≤ (Lbar + 1 / lam) * ‖xt - prox f lam xt‖ := by
    have := H.phiGrad_lip hlam xt xt (prox f lam xt)
    rw [H.prox_spec hlam xt, sub_zero] at this
    simpa [phiGrad] using this
  have hg2 : ‖gradient f xt‖ ^ 2 ≤ ((Lbar + 1 / lam) * ‖xt - prox f lam xt‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg 2
  calc _ ≤ Γ ^ 2 * ‖gradient f xt‖ ^ 2 := hs
    _ ≤ Γ ^ 2 * ((Lbar + 1 / lam) * ‖xt - prox f lam xt‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hg2 (sq_nonneg _)
    _ = _ := by ring

end Noise

end OracleTemplate.ProximalStorm
