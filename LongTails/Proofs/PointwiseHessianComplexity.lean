import LongTails.Proofs.PointwiseHessianTrialCount
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.PointwiseHessianComplexity

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianCounting

noncomputable def dataScale (p : Params) : ℝ :=
  2 + (p.Δ + p.H₀ * p.R ^ 2 + p.M₀ * p.R ^ 3 + p.M₁ ^ 2 * p.R ^ 4 * p.Δ) / p.ε + p.M₁ * p.R ^ 2

lemma dataScale_bounds (p : Params) (hv : spec.valid p) :
    2 ≤ dataScale p ∧ p.Δ / p.ε ≤ dataScale p ∧ p.M₀ * p.R ^ 3 / p.ε ≤ dataScale p ∧
      p.M₁ * p.R ^ 2 ≤ dataScale p ∧
      (4 * p.H₀ + 12 * p.M₀ * p.R + 34 * p.M₁ ^ 2 * p.R ^ 2 * p.Δ) * p.R ^ 2 / p.ε ≤ 34 * dataScale p := by
  rcases hv with ⟨hM₀, hM₁, hR, hΔ, hH, hε⟩
  have h1 : 0 ≤ p.H₀ * p.R ^ 2 := by positivity
  have h2 : 0 ≤ p.M₀ * p.R ^ 3 := by positivity
  have h3 : 0 ≤ p.M₁ ^ 2 * p.R ^ 4 * p.Δ := by positivity
  have h4 : 0 ≤ p.M₁ * p.R ^ 2 := by positivity
  have hz : dataScale p * p.ε = 2 * p.ε + p.Δ + p.H₀ * p.R ^ 2 + p.M₀ * p.R ^ 3 +
      p.M₁ ^ 2 * p.R ^ 4 * p.Δ + p.M₁ * p.R ^ 2 * p.ε := by
    unfold dataScale
    field_simp
    ring
  constructor
  · unfold dataScale
    have : 0 ≤ (p.Δ + p.H₀ * p.R ^ 2 + p.M₀ * p.R ^ 3 + p.M₁ ^ 2 * p.R ^ 4 * p.Δ) / p.ε := by positivity
    linarith
  constructor
  · apply (div_le_iff₀ hε).mpr
    nlinarith [mul_nonneg h4 hε.le]
  constructor
  · apply (div_le_iff₀ hε).mpr
    nlinarith [mul_nonneg h4 hε.le]
  constructor
  · unfold dataScale
    have : 0 ≤ (p.Δ + p.H₀ * p.R ^ 2 + p.M₀ * p.R ^ 3 + p.M₁ ^ 2 * p.R ^ 4 * p.Δ) / p.ε := by positivity
    linarith
  · apply (div_le_iff₀ hε).mpr
    nlinarith [mul_nonneg h4 hε.le]

lemma numeric_level_power : (16384 : ℝ) ^ (2 / 7 : ℝ) = 16 := by
  rw [show (16384 : ℝ) = (2 : ℝ) ^ (14 : ℕ) by norm_num,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma quantitative_level {D A B : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : D * A ≤ 6144 * B + 3) : level D A ≤ 16 * (1 + B ^ (2 / 7 : ℝ)) := by
  have hpow : 0 ≤ B ^ (2 / 7 : ℝ) := Real.rpow_nonneg hB _
  unfold level
  apply max_le (by linarith)
  by_cases hB1 : B ≤ 1
  · have hh := Real.rpow_le_rpow (mul_nonneg hD hA)
      (show D * A ≤ 16384 by linarith) (show (0 : ℝ) ≤ 2 / 7 by norm_num)
    rw [numeric_level_power] at hh
    linarith
  · have hh := Real.rpow_le_rpow (mul_nonneg hD hA)
      (show D * A ≤ 16384 * B by linarith) (show (0 : ℝ) ≤ 2 / 7 by norm_num)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16384) hB, numeric_level_power] at hh
    linarith

lemma log_six_bound {Z x : ℝ} (hZ : 2 ≤ Z) (hx : 0 < x) (hxZ : x ≤ Z) :
    Real.log (6 * x) ≤ 6 * (1 + Real.log Z) := by
  have hZp : 0 < Z := by linarith
  have hlZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hl6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hx.ne']
  have hh := Real.log_le_log hx hxZ
  linarith

lemma initial_potential_bound {D A Z B : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hZ : 2 ≤ Z) (hB : B ≤ Z) (hb : D * A ≤ 6144 * B + 3) :
    |Real.log (1 / A) - Real.log (threshold D A)| ≤ 8 * (1 + Real.log Z) := by
  have hZp : 0 < Z := by linarith
  have hLZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hh := Real.log_le_log (show 0 < 1 + D * A by positivity)
    (show 1 + D * A ≤ 8192 * Z by linarith)
  have hnum : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = (2 : ℝ) ^ (13 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (8192 : ℝ) ≠ 0) hZp.ne', hnum] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hp := initial_log_potential hD hA
  nlinarith

lemma accepted_count_scalar {n F L P V B Z : ℝ}
    (hB : 0 ≤ B) (hZ : 2 ≤ Z) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hFb : F ≤ 16 * (1 + B ^ (2 / 7 : ℝ)))
    (hLb : L ≤ 6 * (1 + Real.log Z)) (hPb : P ≤ 8 * (1 + Real.log Z)) (hVb : V ≤ L)
    (hn : n * Real.log 2 ≤ 2 * Real.log 2 * (3 * F * L + 8 * F) + P + V) :
    n ≤ 1024 * (1 + B ^ (2 / 7 : ℝ)) * (1 + Real.log Z) := by
  have hl2 := PointwiseHessianTrialCount.half_le_log_two
  have hl2p : 0 < Real.log 2 := by linarith
  have hZlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hpow := Real.rpow_nonneg hB (2 / 7 : ℝ)
  have hprod' : F * L ≤ 96 * (1 + B ^ (2 / 7 : ℝ)) * (1 + Real.log Z) := by
    nlinarith [mul_le_mul hFb hLb hL (by positivity : 0 ≤ 16 * (1 + B ^ (2 / 7 : ℝ)))]
  have hF' : F ≤ 16 * (1 + B ^ (2 / 7 : ℝ)) * (1 + Real.log Z) := by
    nlinarith [mul_nonneg hpow hZlog]
  have hPV : P + V ≤ 28 * (1 + Real.log Z) * Real.log 2 := by
    nlinarith [mul_nonneg hZlog (sub_nonneg.mpr hl2)]
  have ht : n * Real.log 2 ≤ 860 * (1 + B ^ (2 / 7 : ℝ)) * (1 + Real.log Z) * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hprod' hl2p.le,
      mul_le_mul_of_nonneg_right hF' hl2p.le, mul_nonneg hpow hZlog,
      mul_nonneg hpow hl2p.le, mul_nonneg (mul_nonneg hpow hZlog) hl2p.le]
  have hn' := (mul_le_mul_iff_left₀ hl2p).mp ht
  nlinarith [mul_nonneg hpow hZlog]

lemma center_displacement_bound {p : Public} {f : p.E → ℝ} {xs : p.E} (s : State p)
    (hR : 0 < p.R) (hmin : IsMinOn f Set.univ xs)
    (hi : PointwiseHessianOuter.Invariant f xs s) : ‖s.center - s.w‖ ≤ 6 * p.R := by
  have hz := PointwiseHessianOuter.energy_radius s xs hR.le hi.A_pos.le
    (fun x => hmin (Set.mem_univ x)) hi.energy_le
  have hh := PointwiseHessianOuter.center_displacement s xs hi.A_pos.le hi.η_pos hi.radius hz
  have ha : 0 < s.a := PointwiseHessianTuning.weight_pos hi.A_pos.le hi.η_pos
  have hf : s.a / (s.A + s.a) ≤ 1 := (div_le_one (by linarith [hi.A_pos])).mpr (by linarith [hi.A_pos])
  exact hh.trans (by nlinarith)

lemma center_gradient_budget (p : Params) (hv : spec.valid p) {f : p.E → ℝ}
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f) {xs : p.E}
    (hmin : IsMinOn f Set.univ xs)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hH : ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.H₀)
    (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (s : State p.toPublic) (hi : PointwiseHessianOuter.Invariant f xs s) :
    ‖gradient f s.center‖ * p.R / p.ε ≤
      1024 * dataScale p * Real.exp (Real.sqrt p.M₁ * ‖s.center - s.w‖) := by
  rcases hv with ⟨hM₀, hM₁, hR, hΔ, hH₀, hε⟩
  let K := 4 * p.H₀ + 12 * p.M₀ * p.R + 34 * p.M₁ ^ 2 * p.R ^ 2 * p.Δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (gradient f) (xs + t • (s.w - xs))‖ ≤ K :=
    PointwiseHessianBounds.sublevel_hessian_bound hf hc hmin hM₀ hM₁ hT p.x0 s.w
      hH hx hgap hi.radius (PointwiseHessianBounds.stored_gap hR hΔ hi) ht
  have hHw : ‖fderiv ℝ (gradient f) s.w‖ ≤ K := by
    simpa using hseg 1 (by simp)
  have hgw : ‖gradient f s.w‖ ≤ 4 * K * p.R := by
    have hh := PointwiseHessianBounds.ray_gradient_bound hf hmin s.w hK hseg
    have hh' := mul_le_mul_of_nonneg_left hi.radius hK
    nlinarith
  have hd := center_displacement_bound s hR hmin hi
  have hgrowth := PointwiseHessianGrowth.gradient_growth hf hM₀ hM₁ hT s.w (s.center - s.w)
  simp only [add_sub_cancel] at hgrowth
  have hbase : (‖gradient f s.w‖ + ‖fderiv ℝ (gradient f) s.w‖ * ‖s.center - s.w‖ +
      p.M₀ * ‖s.center - s.w‖ ^ 2) * p.R ≤ 340 * dataScale p * p.ε := by
    have hcross := mul_le_mul hHw hd (norm_nonneg _) hK
    have hsq := pow_le_pow_left₀ (norm_nonneg (s.center - s.w)) hd 2
    have hnoise := mul_le_mul_of_nonneg_left hsq hM₀
    have hraw : ‖gradient f s.w‖ + ‖fderiv ℝ (gradient f) s.w‖ * ‖s.center - s.w‖ +
        p.M₀ * ‖s.center - s.w‖ ^ 2 ≤ 10 * K * p.R + 36 * p.M₀ * p.R ^ 2 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hraw hR.le
    have hid : dataScale p * p.ε = 2 * p.ε + p.Δ + p.H₀ * p.R ^ 2 + p.M₀ * p.R ^ 3 +
        p.M₁ ^ 2 * p.R ^ 4 * p.Δ + p.M₁ * p.R ^ 2 * p.ε := by
      unfold dataScale
      field_simp
      ring
    dsimp only [K] at hscaled
    nlinarith [mul_nonneg hH₀ (sq_nonneg p.R), mul_nonneg hM₀ (pow_nonneg hR.le 3),
      mul_nonneg (mul_nonneg hM₁ (sq_nonneg p.R)) hε.le]
  have hexp := Real.exp_pos (Real.sqrt p.M₁ * ‖s.center - s.w‖)
  have hZ := (dataScale_bounds p ⟨hM₀,hM₁,hR,hΔ,hH₀,hε⟩).1
  have hscale := mul_le_mul_of_nonneg_right hgrowth hR.le
  have hscaled := mul_le_mul_of_nonneg_right hbase
    (Real.exp_nonneg (1 + Real.sqrt p.M₁ * ‖s.center - s.w‖))
  rw [Real.exp_add] at hscale hscaled
  apply (div_le_iff₀ hε).mpr
  have h3 := Real.exp_one_lt_three
  have hprod := mul_nonneg (show 0 ≤ dataScale p * p.ε by positivity) hexp.le
  nlinarith

lemma cold_regularization_log {lam a r G R ε Z x : ℝ}
    (hlam : 0 < lam) (ha : 0 < a) (hr : 0 < r) (hG : 0 < G) (hR : 0 < R) (hε : 0 < ε)
    (hZ : 2 ≤ Z) (hx : 0 ≤ x) (hlamb : lam ≤ R ^ 2 / ε)
    (hab : 1 / a ≤ 32768 * Z) (hrb : R / r ≤ 1048576 * Z)
    (hGb : G * R / ε ≤ 1024 * Z * Real.exp x) :
    Real.log (lam / min lam (a * r / (4 * G))) ≤ 64 * (1 + Real.log Z) + x := by
  have hZp : 0 < Z := by linarith
  have hZlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hsmall : 0 < a * r / (4 * G) := by positivity
  by_cases hh : lam ≤ a * r / (4 * G)
  · rw [min_eq_left hh, div_self hlam.ne', Real.log_one]
    positivity
  · rw [min_eq_right (le_of_not_ge hh)]
    have hratio : lam / (a * r / (4 * G)) ≤ 140737488355328 * Z ^ 3 * Real.exp x := by
      calc
        _ = 4 * lam * G / (a * r) := by field_simp
        _ ≤ 4 * (R ^ 2 / ε) * G / (a * r) := by gcongr
        _ = 4 * (G * R / ε) * (1 / a) * (R / r) := by field_simp
        _ ≤ 4 * (1024 * Z * Real.exp x) * (32768 * Z) * (1048576 * Z) := by gcongr
        _ = _ := by ring
    have hl := Real.log_le_log (div_pos hlam hsmall) hratio
    have hc : Real.log (140737488355328 : ℝ) = 47 * Real.log 2 := by
      rw [show (140737488355328 : ℝ) = (2 : ℝ) ^ (47 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_mul (by positivity : (140737488355328 : ℝ) * Z ^ 3 ≠ 0) (Real.exp_ne_zero x),
      Real.log_mul (by norm_num : (140737488355328 : ℝ) ≠ 0) (pow_ne_zero 3 hZp.ne'),
      Real.log_pow, Real.log_exp, hc] at hl
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

lemma inverse_continuation_scale {p : Public} {τ r Z : ℝ}
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hτ : 0 < τ)
    (hr : 0 ≤ r) (hrc : r ≤ radiusCap p τ) (hZ : 2 ≤ Z) (hU : p.M₁ * p.R ^ 2 ≤ Z) :
    1 / continuationRatio p τ r ≤ 32768 * Z := by
  have hh := PointwiseHessianEpisodes.continuation_inverse_bound hM₀ hM₁ hτ hrc
  have hrR := hrc.trans (PointwiseHessianTuning.radiusCap_le p τ)
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrR 2) hM₁
  nlinarith

lemma started_regularization {p : Public} (s : State p)
    (reply : p.E ⊕ (p.E →L[ℝ] p.E))
    (hs : PointwiseHessianEpisodes.RadiusStart s (update s reply)) :
    (update s reply).b = initialRegularization p (update s reply).τ (update s reply).r (update s reply).centerG := by
  rcases hs with ⟨hsrc, hdst⟩
  rcases hsrc with hsrc | hsrc
  · by_cases hg : ‖readGradient reply‖ ≤ gradientThreshold p
    · simp [update, hsrc, hg, finish] at hdst
    · simp only [update, hsrc, ite_eq_right hg, startTrial]
  · by_cases hh : ‖newtonPoint p s.b s.center s.x s.g (readHessian reply) - s.center‖ ≤ 2 * s.r
    · simp [update, hsrc, hh] at hdst
    · simp only [update, hsrc, ite_eq_right hh]
      unfold failedTrial
      split_ifs <;> rfl

lemma refinement_ratio_bound {p : Public} {τ r Z : ℝ}
    (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hτ : 0 < τ) (hr : 0 < r) (hrc : r ≤ radiusCap p τ)
    (hτZ : τ * p.R ^ 2 / p.ε ≤ 1024 * Z) :
    2 * continuationRatio p τ r * r / (4 * (1 / τ) * gradientThreshold p / 3) ≤ 384000 * Z := by
  have ha := PointwiseHessianTuning.continuationRatio_le p hM₀ hM₁ hτ hr.le
  have hap := PointwiseHessianTuning.continuationRatio_pos p hM₀ hM₁ hτ hr.le
  have hrR := hrc.trans (PointwiseHessianTuning.radiusCap_le p τ)
  have har : continuationRatio p τ r * r ≤ p.R / 4 := by
    have hh := mul_le_mul ha hrR hr.le (by norm_num : (0 : ℝ) ≤ 1 / 64)
    nlinarith
  have he : 2 * continuationRatio p τ r * r / (4 * (1 / τ) * gradientThreshold p / 3) =
      1500 * (continuationRatio p τ r * r) * τ * p.R / p.ε := by
    unfold gradientThreshold
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ hε).mpr
  have hτZ' := (div_le_iff₀ hε).mp hτZ
  have hmul := mul_le_mul_of_nonneg_right har (show 0 ≤ 1500 * τ * p.R by positivity)
  nlinarith

lemma allowance_scalar {a L U Z x y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hU : 1 ≤ U) (hZ : 2 ≤ Z) (hx : 0 ≤ x) (hy : 0 ≤ y) (hyZ : y ≤ 384000 * Z)
    (hL : 0 ≤ L) (hLb : L ≤ 64 * (1 + Real.log Z) + x) (haU : 1 / a ≤ 65 * U) :
    L / Real.log (1 + a / 8) + Real.log (1 + y) / Real.log 4 + 3 ≤
      1048576 * U * (1 + Real.log Z + x) := by
  have hcont := PointwiseHessianEpisodes.continuation_count_log_bound ha ha1 hL
  have href := PointwiseHessianEpisodes.refinement_log_bound hy hZ hyZ
  have hlogZ := Real.log_nonneg (show 1 ≤ Z by linarith)
  have hlog4 : 1 ≤ Real.log 4 := by
    have hh := PointwiseHessianTrialCount.half_le_log_two
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have href' : 22 * Real.log Z / Real.log 4 ≤ 22 * Real.log Z :=
    (div_le_iff₀ (by linarith : 0 < Real.log 4)).mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left haU (show 0 ≤ 16 * L by positivity)
  have he : 16 * L * (1 / a) = 16 * L / a := by ring
  rw [he] at hmul
  have hLb' := mul_le_mul_of_nonneg_right hLb (show 0 ≤ 1040 * U by positivity)
  nlinarith [mul_nonneg (sub_nonneg.mpr hU) hlogZ, mul_nonneg (sub_nonneg.mpr hU) hx]

lemma relative_power_bounds {v : ℝ} (hv : 0 ≤ v) : v ≤ 1 + v ^ 3 ∧ v ^ 2 ≤ 1 + v ^ 3 := by
  by_cases h : v ≤ 1
  · have hc : 0 ≤ v ^ 3 := by positivity
    constructor <;> nlinarith [mul_nonneg hv (sub_nonneg.mpr h)]
  · have hh : 0 ≤ v ^ 2 * (v - 1) := mul_nonneg (sq_nonneg v) (by linarith)
    constructor <;> nlinarith [sq_nonneg (v - 1)]

lemma aggregate_allowance_scalar {W v ell P S T V G A Q : ℝ}
    (hW : 1 ≤ W) (hv : 0 ≤ v) (hell : 1 ≤ ell)
    (hP : P ≤ 2097152 * W * ell ^ 3) (hS : S ≤ 2464)
    (hT : T ≤ 262144 * ell ^ 3) (hV : V ≤ 14784)
    (hG : G ≤ 1048576 * (ell * P + v ^ 2 * ell * S + v * T + v ^ 3 * V))
    (hA : A ≤ 1024 * W * ell) (hQ : Q ≤ A + 2 * G + P + 2) :
    Q ≤ 17592186044416 * (W + v ^ 3) * ell ^ 4 := by
  have hellp : 0 ≤ ell := by linarith
  have hell3 : 1 ≤ ell ^ 3 := one_le_pow₀ hell
  have hell4 : 1 ≤ ell ^ 4 := one_le_pow₀ hell
  have hell14 : ell ≤ ell ^ 4 := by nlinarith [mul_nonneg hellp (sub_nonneg.mpr hell3)]
  have hell34 : ell ^ 3 ≤ ell ^ 4 := by nlinarith [mul_nonneg (pow_nonneg hellp 3) (sub_nonneg.mpr hell)]
  have hv3 : 0 ≤ v ^ 3 := by positivity
  have hvb := relative_power_bounds hv
  have hmass : 1 ≤ W + v ^ 3 := by linarith
  have hWmass : W ≤ W + v ^ 3 := by linarith
  have hvmass : v ≤ W + v ^ 3 := by linarith [hvb.1]
  have hv2mass : v ^ 2 ≤ W + v ^ 3 := by linarith [hvb.2]
  have hv3mass : v ^ 3 ≤ W + v ^ 3 := by linarith
  have hP' : ell * P ≤ 2097152 * (W + v ^ 3) * ell ^ 4 := by
    calc
      _ ≤ ell * (2097152 * W * ell ^ 3) := mul_le_mul_of_nonneg_left hP hellp
      _ ≤ ell * (2097152 * (W + v ^ 3) * ell ^ 3) := by gcongr
      _ = _ := by ring
  have hS' : v ^ 2 * ell * S ≤ 2464 * (W + v ^ 3) * ell ^ 4 := by
    calc
      _ ≤ v ^ 2 * ell * 2464 := mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ (W + v ^ 3) * ell ^ 4 * 2464 := by gcongr
      _ = _ := by ring
  have hT' : v * T ≤ 262144 * (W + v ^ 3) * ell ^ 4 := by
    calc
      _ ≤ v * (262144 * ell ^ 3) := mul_le_mul_of_nonneg_left hT hv
      _ ≤ (W + v ^ 3) * (262144 * ell ^ 4) := by gcongr
      _ = _ := by ring
  have hV' : v ^ 3 * V ≤ 14784 * (W + v ^ 3) * ell ^ 4 := by
    calc
      _ ≤ v ^ 3 * 14784 := mul_le_mul_of_nonneg_left hV hv3
      _ ≤ (W + v ^ 3) * 14784 := by gcongr
      _ ≤ ((W + v ^ 3) * 14784) * ell ^ 4 := le_mul_of_one_le_right (by positivity) hell4
      _ = _ := by ring
  have hA' : A ≤ 1024 * (W + v ^ 3) * ell ^ 4 := by
    apply hA.trans
    gcongr
  have hP'' : P ≤ 2097152 * (W + v ^ 3) * ell ^ 4 := by
    apply hP.trans
    gcongr
  have hmass' : 1 ≤ (W + v ^ 3) * ell ^ 4 := one_le_mul_of_one_le_of_one_le hmass hell4
  nlinarith

lemma started_allowance_bound (p : Params) (hv : spec.valid p) {f : p.E → ℝ}
    (s : State p.toPublic) (hi : PointwiseHessianExecution.InnerParameters f s)
    (hb : s.b = initialRegularization p.toPublic s.τ s.r s.centerG)
    (hτlo : p.ε / p.R ^ 2 ≤ s.τ)
    (hτZ : s.τ * p.R ^ 2 / p.ε ≤ 1024 * dataScale p)
    (hrho : p.R / (1048576 * dataScale p) ≤ s.r)
    (hg : ‖gradient f s.center‖ * p.R / p.ε ≤
      1024 * dataScale p * Real.exp (Real.sqrt p.M₁ * ‖s.center - s.w‖)) :
    PointwiseHessianEpisodePartition.gradientAllowance s ≤
      1048576 * (1 + p.M₁ * s.r ^ 2) * (1 + Real.log (dataScale p) + Real.sqrt p.M₁ * ‖s.center - s.w‖) := by
  obtain ⟨hZ, hΔZ, hMZ, hUZ, hKZ⟩ := dataScale_bounds p hv
  rcases hv with ⟨hM₀,hM₁,hR,hΔ,hH,hε⟩
  have hZp : 0 < dataScale p := by linarith
  have ha := PointwiseHessianTuning.continuationRatio_pos p.toPublic hM₀ hM₁ hi.τ_pos hi.r_pos.le
  have ha1 := PointwiseHessianTuning.continuationRatio_le p.toPublic hM₀ hM₁ hi.τ_pos hi.r_pos.le
  have hlam := one_div_pos.mpr hi.τ_pos
  have hlamb : 1 / s.τ ≤ p.R ^ 2 / p.ε := by
    have hh := one_div_le_one_div_of_le (show 0 < p.ε / p.R ^ 2 by positivity) hτlo
    simpa only [one_div_div] using hh
  have hrb : p.R / s.r ≤ 1048576 * dataScale p := by
    apply (div_le_iff₀ hi.r_pos).mpr
    have hh := (div_le_iff₀ (show 0 < 1048576 * dataScale p by positivity)).mp hrho
    nlinarith
  have hgpos : 0 < ‖gradient f s.center‖ := by
    rw [← hi.cached_gradient]
    exact norm_pos_iff.mpr hi.cached_nonzero
  have hx : 0 ≤ Real.sqrt p.M₁ * ‖s.center - s.w‖ := by positivity
  have hab := inverse_continuation_scale hM₀ hM₁ hi.τ_pos hi.r_pos.le hi.r_le hZ hUZ
  have hlog := cold_regularization_log hlam ha hi.r_pos hgpos hR hε hZ hx hlamb hab hrb hg
  have hblog : Real.log ((1 / s.τ) / s.b) ≤
      64 * (1 + Real.log (dataScale p)) + Real.sqrt p.M₁ * ‖s.center - s.w‖ := by
    simpa only [hb, initialRegularization, hi.cached_gradient] using hlog
  have hlognonneg : 0 ≤ Real.log ((1 / s.τ) / s.b) :=
    Real.log_nonneg ((one_le_div hi.b_pos).mpr hi.b_le)
  let t := 4 * (1 / s.τ) * gradientThreshold p.toPublic / 3
  have ht : 0 < t := by dsimp [t, gradientThreshold]; positivity
  have hy : 0 ≤ 2 * continuationRatio p.toPublic s.τ s.r * s.r / t :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.le) hi.r_pos.le) ht.le
  have hyZ := refinement_ratio_bound hM₀ hM₁ hR hε hi.τ_pos hi.r_pos hi.r_le hτZ
  have hU : 1 ≤ 1 + p.M₁ * s.r ^ 2 := by nlinarith [mul_nonneg hM₁ (sq_nonneg s.r)]
  have haU := PointwiseHessianEpisodes.continuation_inverse_bound hM₀ hM₁ hi.τ_pos hi.r_le
  have hh := allowance_scalar ha (show continuationRatio p.toPublic s.τ s.r ≤ 1 by linarith)
    hU hZ hx hy hyZ hlognonneg hblog haU
  have hid : (2 * continuationRatio p.toPublic s.τ s.r * s.r + t) / t =
      1 + 2 * continuationRatio p.toPublic s.τ s.r * s.r / t := by field_simp; ring
  change Real.log ((1 / s.τ) / s.b) / Real.log (1 + continuationRatio p.toPublic s.τ s.r / 8) +
    Real.log ((2 * continuationRatio p.toPublic s.τ s.r * s.r + t) / t) / Real.log 4 + 3 ≤ _
  rw [hid]
  exact hh

lemma quantitative_outer_count (p : Params) (hv : spec.valid p) {f : p.E → ℝ}
    (s : ℕ → State p.toPublic) (xs : p.E) (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hmin : IsMinOn f Set.univ xs) (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) (N : ℕ)
    (hi : ∀ k ≤ N, PointwiseHessianExecution.StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hcert : ∀ k < N, PointwiseHessianLedger.CertificateInvariant f (s k))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x))
    (hloss : (∑ k ∈ Finset.range N, PointwiseHessianLedger.loss (s k) (reply k)) ≤ p.R ^ 2)
    (h0 : s 0 = initial p.toPublic) (hcap : (s N).A ≤ 3 * targetWeight p.toPublic) :
    ((PointwiseHessianEvents.acceptedIndices s reply N).card : ℝ) ≤
      1024 * (1 + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ)) * (1 + Real.log (dataScale p)) := by
  obtain ⟨hZ,hΔZ,hBZ,hUZ,hKZ⟩ := dataScale_bounds p hv
  rcases hv with ⟨hM₀,hM₁,hR,hΔ,hH,hε⟩
  let D := 2048 * p.M₀ * p.R + p.ε / p.R ^ 2
  let B := p.M₀ * p.R ^ 3 / p.ε
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA0 := (hi 0 (Nat.zero_le N)).outer.A_pos
  have hAN := (hi N le_rfl).outer.A_pos
  have hmono := PointwiseHessianLedger.path_weight_mono s reply N (fun k hk => hi k hk.le) hs (Nat.zero_le N) le_rfl
  have hDA : D * (s N).A ≤ 6144 * B + 3 := by
    calc
      _ ≤ D * (3 * targetWeight p.toPublic) := mul_le_mul_of_nonneg_left hcap hD.le
      _ = _ := by dsimp [D,B,targetWeight]; field_simp; ring
  have hDA0 : D * (s 0).A ≤ 6144 * B + 3 :=
    (mul_le_mul_of_nonneg_left hmono hD.le).trans hDA
  have hF := quantitative_level hD.le hAN.le hB hDA
  have hL : 0 ≤ Real.log (s N).A - Real.log (s 0).A :=
    sub_nonneg.mpr (Real.log_le_log hA0 hmono)
  have hLcap := PointwiseHessianBounds.weight_log_bound p.toPublic hR hΔ hε hAN hcap
  have hAinit : (s 0).A = initialWeight p.toPublic := by rw [h0]; rfl
  have hηinit : (s 0).η = 1 / (s 0).A := by rw [h0]; rfl
  have hLb : Real.log (s N).A - Real.log (s 0).A ≤ 6 * (1 + Real.log (dataScale p)) := by
    rw [hAinit]
    apply hLcap.trans
    have hh := log_six_bound hZ (div_pos hΔ hε) hΔZ
    simpa only [mul_div_assoc] using hh
  have hP := initial_potential_bound hD.le hA0 hZ hBZ hDA0
  rw [← hηinit] at hP
  have hV := (threshold_log_variation hD.le hA0 hmono).2
  have hcount := PointwiseHessianEvents.accepted_path_count s xs hf hc hM₀ hR hmin reply N hi hs hcert hg hloss
    hD (show 2048 * p.M₀ * p.R ≤ D by
      have hh : 0 ≤ p.ε / p.R ^ 2 := by positivity
      dsimp [D]
      linarith)
  dsimp only at hcount
  apply accepted_count_scalar hB hZ hL (level_pos D (s N).A).le hF hLb hP hV
  linarith

lemma finite_allowance_sum {ι : Type*} (I : Finset ι) (P : ι → Prop) [DecidablePred P]
    (r d F : ι → ℝ) {M ell : ℝ}
    (hF : ∀ i ∈ I, P i → F i ≤ 1048576 * (1 + M * r i ^ 2) * (ell + Real.sqrt M * d i)) :
    (∑ i ∈ I, if P i then F i else 0) ≤
      1048576 * (ell * (∑ i ∈ I, if P i then (1 : ℝ) else 0) +
        M * ell * (∑ i ∈ I, if P i then r i ^ 2 else 0) +
        Real.sqrt M * (∑ i ∈ I, if P i then d i else 0) +
        M * Real.sqrt M * (∑ i ∈ I, if P i then r i ^ 2 * d i else 0)) := by
  calc
    _ ≤ ∑ i ∈ I, if P i then 1048576 * (1 + M * r i ^ 2) * (ell + Real.sqrt M * d i) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with hp
      · exact hF i hi hp
      · exact le_rfl
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

lemma finite_radius_cross_sum {ι : Type*} (I : Finset ι) (P : ι → Prop) [DecidablePred P]
    (r d : ι → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hd : ∀ i ∈ I, P i → d i ≤ 6 * R)
    (hs : (∑ i ∈ I, if P i then r i ^ 2 else 0) ≤ 2464 * R ^ 2) :
    (∑ i ∈ I, if P i then r i ^ 2 * d i else 0) ≤ 14784 * R ^ 3 := by
  have hh : (∑ i ∈ I, if P i then r i ^ 2 * d i else 0) ≤
      6 * R * (∑ i ∈ I, if P i then r i ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    split_ifs with hp
    · nlinarith [mul_le_mul_of_nonneg_left (hd i hi hp) (sq_nonneg (r i))]
    · simp
  have hh' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6 * R by positivity)
  nlinarith

lemma aggregate_physical_cost {W M R ell P S T V G A Q : ℝ}
    (hW : 1 ≤ W) (hM : 0 ≤ M) (hR : 0 < R) (hell : 1 ≤ ell)
    (hP : P ≤ 2097152 * W * ell ^ 3) (hS : S ≤ 2464 * R ^ 2)
    (hT : T ≤ 262144 * R * ell ^ 3) (hV : V ≤ 14784 * R ^ 3)
    (hG : G ≤ 1048576 * (ell * P + M * ell * S + Real.sqrt M * T + M * Real.sqrt M * V))
    (hA : A ≤ 1024 * W * ell) (hQ : Q ≤ A + 2 * G + P + 2) :
    Q ≤ 17592186044416 * (W + (Real.sqrt M * R) ^ 3) * ell ^ 4 := by
  have hS' : S / R ^ 2 ≤ 2464 := (div_le_iff₀ (by positivity)).mpr hS
  have hT' : T / R ≤ 262144 * ell ^ 3 := (div_le_iff₀ hR).mpr (by nlinarith)
  have hV' : V / R ^ 3 ≤ 14784 := (div_le_iff₀ (by positivity)).mpr hV
  have he : (Real.sqrt M * R) ^ 2 * ell * (S / R ^ 2) +
      (Real.sqrt M * R) * (T / R) + (Real.sqrt M * R) ^ 3 * (V / R ^ 3) =
      M * ell * S + Real.sqrt M * T + M * Real.sqrt M * V := by
    have hh := Real.sq_sqrt hM
    have hc : Real.sqrt M ^ 3 = M * Real.sqrt M := by rw [pow_succ, hh]
    field_simp
    ring_nf
    rw [hh, hc]
    ring
  apply aggregate_allowance_scalar hW (by positivity) hell hP hS' hT' hV' _ hA hQ
  nlinarith [hG]

end LongTails.Proofs.PointwiseHessianComplexity
