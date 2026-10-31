import LongTails.Proofs.FeasibleGapGeometry
import LongTails.Algorithms.FeasibleGapAccelerated

namespace LongTails.Proofs.FeasibleGapTuning

lemma logarithmic_scale {U : ℝ} (hU : 1 ≤ U) :
    1 / 2 ≤ Real.log (16 * U) := by
  have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 15)
  norm_num at hh
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
    (show 16 ≤ 16 * U by linarith)
  linarith

lemma dyadic_depth {U : ℝ} (hU : 1 ≤ U) :
    let K := ⌈Real.log (16 * U) / Real.log 2⌉₊
    (K : ℝ) ≤ 4 * Real.log (16 * U) ∧
      (1 / 2 : ℝ) ^ K ≤ 1 / (16 * U) := by
  dsimp only
  let K := ⌈Real.log (16 * U) / Real.log 2⌉₊
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at hh
    linarith
  have hl := logarithmic_scale hU
  have hlog2p : 0 < Real.log 2 := by linarith
  have harg : 0 ≤ Real.log (16 * U) / Real.log 2 := by positivity
  have hceil : (K : ℝ) < Real.log (16 * U) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one harg
  have hquot : Real.log (16 * U) / Real.log 2 ≤ 2 * Real.log (16 * U) := by
    apply (div_le_iff₀ hlog2p).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ Real.log (16 * U) by linarith)]
  refine ⟨by dsimp [K] at hceil; linarith, ?_⟩
  have hceil' : Real.log (16 * U) / Real.log 2 ≤ (K : ℝ) := Nat.le_ceil _
  have he := Real.exp_le_exp.mpr ((div_le_iff₀ hlog2p).mp hceil')
  rw [Real.exp_log (show 0 < 16 * U by linarith), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hUpos : 0 < 16 * U := by linarith
  rw [one_div, inv_pow]
  simpa only [one_div] using (one_div_le_one_div_of_le hUpos he)

lemma logarithmic_gradient_bound {U M d R v : ℝ}
    (hU : 1 ≤ U) (hM : 0 < M) (hd : 0 < d) (hR : 0 ≤ R)
    (hscale : M * R ^ 2 ≤ U * d)
    (hv : ∀ K : ℕ, v ≤ 4 * (K : ℝ) * Real.sqrt (M * d) +
      4 * M * R * (1 / 2 : ℝ) ^ K) :
    v ≤ 32 * Real.log (16 * U) * Real.sqrt (M * d) := by
  let K := ⌈Real.log (16 * U) / Real.log 2⌉₊
  obtain ⟨hK, htail⟩ := dyadic_depth hU
  have hl := logarithmic_scale hU
  have hS := Real.sqrt_nonneg (M * d)
  have hSsq := Real.sq_sqrt (mul_nonneg hM.le hd.le)
  have hMR : M * R ≤ U * Real.sqrt (M * d) := by
    have hsq1 : (M * R) ^ 2 ≤ U * (M * d) := by
      nlinarith [mul_le_mul_of_nonneg_left hscale hM.le]
    have hsq2 : U * (M * d) ≤ (U * Real.sqrt (M * d)) ^ 2 := by
      have hu2 : U ≤ U ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hu2 (mul_nonneg hM.le hd.le)]
    have hpos : 0 ≤ U * Real.sqrt (M * d) := by positivity
    nlinarith
  have htail' : 4 * M * R * (1 / 2 : ℝ) ^ K ≤ Real.sqrt (M * d) / 4 := by
    have hh := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ 4 * M * R by positivity)
    have hUp : 0 < 16 * U := by linarith
    have hdiv : 4 * M * R / (16 * U) ≤ Real.sqrt (M * d) / 4 := by
      apply (div_le_iff₀ hUp).mpr
      nlinarith only [hMR]
    apply le_trans _ hdiv
    simpa only [K, div_eq_mul_inv, one_mul] using hh
  have hmain := hv K
  have hdepth := mul_le_mul_of_nonneg_right hK hS
  nlinarith

open LongTails.Setups.FeasibleHessianGapComposite
open OracleTemplate.FeasibleGapAccelerated

lemma curvature_pos (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) : 0 < curvature p Δ := by
  unfold curvature
  positivity

lemma scale_formula (p : Params) (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    scale p Δ = 1 + p.H0 * p.R ^ 2 / Δ + p.H1 * p.R ^ 2 := by
  unfold scale curvature
  field_simp
  ring

lemma scale_ge_one (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) : 1 ≤ scale p Δ := by
  rw [scale_formula p hR hΔ]
  have h₁ : 0 ≤ p.H0 * p.R ^ 2 / Δ := by positivity
  have h₂ : 0 ≤ p.H1 * p.R ^ 2 := by positivity
  linarith

lemma globalScale_ge_one (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hε : 0 < p.ε) : 1 ≤ globalScale p := by
  unfold globalScale
  have hA : 0 ≤ p.H0 * p.R ^ 2 / p.ε := by positivity
  have hB : 0 ≤ p.H1 * p.R ^ 2 := by positivity
  linarith

lemma scale_le_global (p : Params) (h0 : 0 ≤ p.H0) (hR : 0 < p.R)
    (hε : 0 < p.ε) {d : ℝ} (hd : p.ε ≤ d) : scale p d ≤ globalScale p := by
  rw [scale_formula p hR (hε.trans_le hd)]
  dsimp [globalScale]
  have hh := div_le_div_of_nonneg_left (show 0 ≤ p.H0 * p.R ^ 2 by positivity) hε hd
  linarith

lemma logarithm_lower (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hε : 0 < p.ε) : 1 / 2 ≤ logarithm p :=
  logarithmic_scale (globalScale_ge_one p h0 h1 hε)

lemma fraction_positive (p : Params) (hL : 0 < logarithm p) (d : ℝ) :
    0 < fraction p d := by unfold fraction; positivity

lemma fraction_bound (p : Params) (hL : 1 / 2 ≤ logarithm p) (d : ℝ) :
    fraction p d ≤ 1 / 2048 := by
  unfold fraction
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hn := Real.sqrt_nonneg (scale p d)
  nlinarith

lemma fraction_log_scale (p : Params) (hL : 0 < logarithm p) (d : ℝ) :
    fraction p d * logarithm p * Real.sqrt (scale p d) ≤ 1 / 4096 := by
  have hden : 0 < 4096 * logarithm p * (1 + Real.sqrt (scale p d)) := by positivity
  unfold fraction
  apply (mul_le_mul_iff_left₀ hden).mp
  field_simp
  nlinarith [Real.sqrt_nonneg (scale p d)]

lemma scale_geometry (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) {d : ℝ} (hd : 0 < d) :
    p.R * Real.sqrt (curvature p d * d) = d * Real.sqrt (scale p d) := by
  have hM := curvature_pos p h0 h1 hR hd
  have hD := scale_ge_one p h0 h1 hR hd
  have he : scale p d * d = curvature p d * p.R ^ 2 := by unfold scale; field_simp
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)]
  nlinarith only [congrArg (fun v : ℝ => v * d) he]

lemma fraction_gradient (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hL : 0 < logarithm p) {d : ℝ} (hd : 0 < d) :
    fraction p d * p.R * gradientCap p d ≤ d / 128 := by
  have hs := fraction_log_scale p hL d
  have he := scale_geometry p h0 h1 hR hd
  have hh := mul_le_mul_of_nonneg_right hs hd.le
  dsimp [gradientCap]
  nlinarith only [hh, congrArg (fun v : ℝ => 32 * fraction p d * logarithm p * v) he]

lemma fraction_quadratic (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hL : 1 / 2 ≤ logarithm p) {d : ℝ} (hd : 0 < d) :
    curvature p d * p.R ^ 2 * fraction p d ^ 2 ≤ d / 4194304 := by
  have hLp : 0 < logarithm p := by linarith
  have hs := fraction_log_scale p hLp d
  have hθ := fraction_positive p hLp d
  have hM := curvature_pos p h0 h1 hR hd
  have hD := scale_ge_one p h0 h1 hR hd
  have hs' : fraction p d * Real.sqrt (scale p d) ≤ 1 / 2048 := by
    have hh := mul_le_mul_of_nonneg_right hL
      (show 0 ≤ fraction p d * Real.sqrt (scale p d) by positivity)
    nlinarith only [hh, hs]
  have hsq := (sq_le_sq₀ (show 0 ≤ fraction p d * Real.sqrt (scale p d) by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 / 2048)).mpr hs'
  rw [mul_pow, Real.sq_sqrt (by linarith)] at hsq
  have hh := mul_le_mul_of_nonneg_right hsq hd.le
  have he : scale p d * d = curvature p d * p.R ^ 2 := by unfold scale; field_simp
  nlinarith only [hh, congrArg (fun v : ℝ => fraction p d ^ 2 * v) he]

lemma target_pos (p : Params) (hR : 0 < p.R) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < target p Δ := by
  unfold target
  positivity

lemma weight_bounds (p : Params) {Δ A : ℝ} (hA : 0 < A)
    (hAt : A < target p Δ) (hL : 1 / 2 ≤ logarithm p) :
    0 < weight p Δ A ∧ A + weight p Δ A ≤ target p Δ ∧
    weight p Δ A ≤ fraction p Δ * (A + weight p Δ A) := by
  have hθ := fraction_positive p (by linarith) Δ
  have hθle := fraction_bound p hL Δ
  have hden : 0 < 1 - fraction p Δ := by linarith
  rw [weight, ite_eq_right hA.ne']
  have hleft : 0 < target p Δ - A := by linarith
  have hright : 0 < A * fraction p Δ / (1 - fraction p Δ) := by positivity
  refine ⟨lt_min hleft hright, ?_, ?_⟩
  · linarith [min_le_left (target p Δ - A) (A * fraction p Δ / (1 - fraction p Δ))]
  · have hh := min_le_right (target p Δ - A) (A * fraction p Δ / (1 - fraction p Δ))
    have he := (le_div_iff₀ hden).mp hh
    nlinarith only [he]


lemma weight_displacement_bounds (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hL : 1 / 2 ≤ logarithm p) {d A : ℝ}
    (hd : 0 < d) (hA : 0 < A) (hAt : A < target p d) :
    weight p d A * gradientCap p d ≤ p.R / 128 ∧
    weight p d A * (d + 2 * p.R * gradientCap p d) ≤ p.R ^ 2 / 4 := by
  have hLp : 0 < logarithm p := by linarith
  obtain ⟨ha, hcap, hratio⟩ := weight_bounds p hA hAt hL
  have hθ := fraction_positive p hLp d
  have ht := hratio.trans (mul_le_mul_of_nonneg_left hcap hθ.le)
  have ht' : weight p d A * d ≤ fraction p d * p.R ^ 2 := by
    exact (le_div_iff₀ hd).mp (by simpa [target, mul_div_assoc] using ht)
  have hG : 0 ≤ gradientCap p d := by
    have hM := curvature_pos p h0 h1 hR hd
    unfold gradientCap
    positivity
  have hf := fraction_gradient p h0 h1 hR hLp hd
  have hlin : weight p d A * gradientCap p d ≤ p.R / 128 := by
    have hh := mul_le_mul_of_nonneg_right ht' hG
    have hr := mul_le_mul_of_nonneg_right hf hR.le
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith only [hh, hr]
  have hθle := mul_le_mul_of_nonneg_right (fraction_bound p hL d) (sq_nonneg p.R)
  have hj := mul_le_mul_of_nonneg_left hlin hR.le
  constructor
  · exact hlin
  · nlinarith only [ht', hθle, hj, sq_nonneg p.R]

lemma fraction_locality (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hL : 1 / 2 ≤ logarithm p) {d τ : ℝ}
    (hd : 0 < d) (hτ : 0 ≤ τ) (hτθ : τ ≤ fraction p d) :
    τ * p.R * gradientCap p d ≤ d / 128 ∧
    (2 * p.R * τ) ^ 2 / 2 * p.H0 ≤ d / 4 ∧
    (2 * p.R * τ) ^ 2 / 2 * p.H1 ≤ 1 / 8 := by
  have hM := curvature_pos p h0 h1 hR hd
  have hLp : 0 < logarithm p := by linarith
  have hG : 0 ≤ gradientCap p d := by unfold gradientCap; positivity
  have hlin := mul_le_mul_of_nonneg_right hτθ (mul_nonneg hR.le hG)
  have hf := fraction_gradient p h0 h1 hR hLp hd
  refine ⟨by nlinarith only [hlin, hf], ?_, ?_⟩
  all_goals
    have hθ := fraction_positive p hLp d
    have hs := (sq_le_sq₀ hτ hθ.le).mpr hτθ
    have hq := mul_le_mul_of_nonneg_left hs (show 0 ≤ curvature p d * p.R ^ 2 by positivity)
    have hfq := fraction_quadratic p h0 h1 hR hL hd
    have hM0 : p.H0 ≤ curvature p d := by
      unfold curvature
      have hn : 0 ≤ d / p.R ^ 2 := by positivity
      nlinarith
    have hM1 : p.H1 * d ≤ curvature p d := by
      unfold curvature
      have hn : 0 ≤ d / p.R ^ 2 := by positivity
      linarith
  · have hh := mul_le_mul_of_nonneg_right hM0
      (show 0 ≤ p.R ^ 2 * τ ^ 2 by positivity)
    nlinarith only [hh, hq, hfq, hd]
  · have hh := mul_le_mul_of_nonneg_right hM1
      (show 0 ≤ p.R ^ 2 * τ ^ 2 by positivity)
    nlinarith only [hh, hq, hfq, hd]

lemma weight_condition (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hL : 1 / 2 ≤ logarithm p) {d A : ℝ}
    (hd : 0 < d) (hA : 0 < A) (hAt : A < target p d) :
    16 * curvature p d * (weight p d A) ^ 2 ≤ A + weight p d A := by
  obtain ⟨ha, hcap, hratio⟩ := weight_bounds p hA hAt hL
  have hM := curvature_pos p h0 h1 hR hd
  have hθ := fraction_positive p (by linarith) d
  have hfq := fraction_quadratic p h0 h1 hR hL hd
  have hsq : curvature p d * fraction p d ^ 2 * target p d ≤ 1 / 4194304 := by
    rw [target, ← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hfq]
  have hat := hratio.trans (mul_le_mul_of_nonneg_left hcap hθ.le)
  have hp := mul_le_mul hratio hat ha.le
    (show 0 ≤ fraction p d * (A + weight p d A) by positivity)
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 16 * curvature p d by positivity)
  have hh := mul_le_mul_of_nonneg_right hsq (show 0 ≤ A + weight p d A by positivity)
  nlinarith only [hp', hh, show 0 < A + weight p d A by positivity]

end LongTails.Proofs.FeasibleGapTuning
