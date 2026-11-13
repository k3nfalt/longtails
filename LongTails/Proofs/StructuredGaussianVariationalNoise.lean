import LongTails.Proofs.StructuredGaussianVariationalGeometry
import LongTails.Proofs.GaussianVariationalVariance

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StructuredGaussianVariational

open LongTails.Setups.GaussianVariationalInference
open LongTails.Setups.StructuredGaussianVariationalInference
open OracleTemplate.GaussianVariational

variable {d : ℕ} {S : Fin d → Finset (Fin d)}

noncomputable def patternTail (S : Fin d → Finset (Fin d)) (τ : ℝ) (ξ : Fin d → ℝ) : ℝ :=
  64 / rexp 1 * rexp (-(τ / 8)) * ∑ i, rexp (rowSq S ξ i / 4)

lemma integral_exp_rowSq (S : Fin d → Finset (Fin d)) (i : Fin d) :
    Integrable (fun ξ : Fin d → ℝ => rexp (rowSq S ξ i / 4)) (noiseLaw d) ∧
      ∫ ξ, rexp (rowSq S ξ i / 4) ∂noiseLaw d = √2 ^ (S i).card := by
  have hprod : ∀ ξ : Fin d → ℝ, rexp (rowSq S ξ i / 4) =
      ∏ j, (if j ∈ S i then rexp (ξ j ^ 2 / 4) else 1) := by
    intro ξ
    rw [rowSq, Finset.sum_div, Real.exp_sum, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hprod]
  have hf : ∀ j : Fin d, Integrable
      ((fun (j : Fin d) (x : ℝ) => if j ∈ S i then rexp (x ^ 2 / 4) else 1) j) (gaussianReal 0 1) := by
    intro j
    by_cases hj : j ∈ S i
    · simpa [hj] using gaussian_exp_quarter.1
    · simp only [hj, ↓reduceIte]
      exact integrable_const _
  constructor
  · exact Integrable.fintype_prod (f := fun (j : Fin d) (x : ℝ) =>
      if j ∈ S i then rexp (x ^ 2 / 4) else 1) hf
  · rw [noiseLaw, integral_fintype_prod_eq_prod (f := fun (j : Fin d) (x : ℝ) =>
      if j ∈ S i then rexp (x ^ 2 / 4) else 1)]
    have he : ∀ j : Fin d, ∫ x, (if j ∈ S i then rexp (x ^ 2 / 4) else 1) ∂gaussianReal 0 1 =
        if j ∈ S i then √2 else 1 := by
      intro j
      by_cases hj : j ∈ S i
      · simp [hj, gaussian_exp_quarter.2]
      · simp [hj]
    simp_rw [he]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

lemma patternTail_integral (S : Fin d → Finset (Fin d)) (τ : ℝ) :
    Integrable (patternTail S τ) (noiseLaw d) ∧
      ∫ ξ, patternTail S τ ξ ∂noiseLaw d =
        64 / rexp 1 * rexp (-(τ / 8)) * ∑ i, √2 ^ (S i).card := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun ξ : Fin d → ℝ => rexp (rowSq S ξ i / 4)) (noiseLaw d) :=
    fun i _ => (integral_exp_rowSq S i).1
  unfold patternTail
  refine ⟨(integrable_finsetSum _ hi).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ hi]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (integral_exp_rowSq S i).2

lemma patternTail_nonneg (τ : ℝ) (ξ : Fin d → ℝ) : 0 ≤ patternTail S τ ξ := by
  unfold patternTail
  have : 0 ≤ ∑ i, rexp (rowSq S ξ i / 4) := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  positivity

lemma tail_split_pattern {τ A B : ℝ} (hτ : 0 ≤ τ) (ξ : Fin d → ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A ≤ B * (1 + rowMax S ξ)) :
    (1 + rowMax S ξ) * A ≤ (1 + τ) * A + B * patternTail S τ ξ := by
  have hT := patternTail_nonneg (S := S) τ ξ
  rcases le_or_gt (rowMax S ξ) τ with hle | hgt
  · have h1 : (1 + rowMax S ξ) * A ≤ (1 + τ) * A := mul_le_mul_of_nonneg_right (by linarith) hA
    have h2 : 0 ≤ B * patternTail S τ ξ := mul_nonneg hB hT
    linarith
  · have hM0 : 0 < rowMax S ξ := lt_of_le_of_lt hτ hgt
    obtain ⟨i, hi⟩ := rowMax_attained hM0
    have h1 := tail_split (τ := τ) (rowMax_nonneg ξ) hA hB hAB
    have hexp : rexp (rowMax S ξ / 4 - τ / 8) ≤ rexp (-(τ / 8)) * ∑ j, rexp (rowSq S ξ j / 4) := by
      have he : rexp (rowMax S ξ / 4 - τ / 8) = rexp (-(τ / 8)) * rexp (rowSq S ξ i / 4) := by
        rw [← Real.exp_add, hi]
        congr 1
        ring
      rw [he]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Finset.single_le_sum (f := fun j => rexp (rowSq S ξ j / 4))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
    have h2 : B * (64 / rexp 1 * rexp (rowMax S ξ / 4 - τ / 8)) ≤ B * patternTail S τ ξ := by
      refine mul_le_mul_of_nonneg_left ?_ hB
      unfold patternTail
      have : 0 ≤ 64 / rexp 1 := by positivity
      have := mul_le_mul_of_nonneg_left hexp this
      linarith
    linarith

lemma patternTau_nonneg (d w : ℕ) {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ patternTau d w κ := by
  unfold patternTau
  have hlog : 0 ≤ Real.log (48 * d * κ) := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · apply Real.log_nonneg
      have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  positivity

lemma pattern_tail_mass {w : ℕ} (hS : IsPattern S w) {κ : ℝ} (hκ : 1 ≤ κ) :
    Integrable (patternTail S (patternTau d w κ)) (noiseLaw d) ∧
      2 * κ * ∫ ξ, patternTail S (patternTau d w κ) ξ ∂noiseLaw d ≤ 1 := by
  have ht := patternTail_integral S (patternTau d w κ)
  refine ⟨ht.1, ?_⟩
  rw [ht.2]
  have hsum : ∑ i, √2 ^ (S i).card ≤ d * √2 ^ w := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)), √2 ^ (S i).card ≤ √2 ^ w := fun i _ =>
      pow_le_pow_right₀ (Real.one_le_sqrt.mpr (by norm_num)) (hS i).2.2
    have := Finset.sum_le_sum h1
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hκ0 : 0 < κ := by linarith
  have hpos : 0 ≤ 64 / rexp 1 * rexp (-(patternTau d w κ / 8)) := by positivity
  have hstep : 2 * κ * (64 / rexp 1 * rexp (-(patternTau d w κ / 8)) * ∑ i, √2 ^ (S i).card) ≤
      2 * κ * (64 / rexp 1 * rexp (-(patternTau d w κ / 8)) * (d * √2 ^ w)) := by
    have := mul_le_mul_of_nonneg_left hsum hpos
    nlinarith
  refine hstep.trans ?_
  rcases Nat.eq_zero_or_pos d with h0 | hd
  · subst h0
    simp
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hdκ : 1 ≤ (d : ℝ) * κ := by nlinarith
    have hb := tail_budget (d := w) hdκ
    have he : patternTau d w κ = 3 * w + 8 * Real.log (48 * ((d : ℝ) * κ)) := by
      unfold patternTau
      rw [mul_assoc]
    rw [he]
    calc 2 * κ * (64 / rexp 1 * rexp (-((3 * w + 8 * Real.log (48 * ((d : ℝ) * κ))) / 8)) *
          (d * √2 ^ w)) =
        2 * ((d : ℝ) * κ) * (64 / rexp 1 *
          rexp (-((3 * w + 8 * Real.log (48 * ((d : ℝ) * κ))) / 8)) * √2 ^ w) := by ring
      _ ≤ 1 := hb

section Smoothness

variable {L μ : ℝ} {V : Point d → ℝ}

noncomputable def maskNormSq (S : Fin d → Finset (Fin d)) (x : Location d × Scale d) : ℝ :=
  pin (maskPair S x) (maskPair S x)

lemma continuous_maskNormSq (S : Fin d → Finset (Fin d)) : Continuous (maskNormSq (d := d) S) := by
  unfold maskNormSq pin pinner maskPair maskScale
  dsimp only
  refine (continuous_finsetSum _ fun i _ => ?_).add
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_fst)
  · by_cases hj : j ∈ S i
    · simp only [hj, ↓reduceIte]
      have hc : Continuous (fun x : Location d × Scale d => x.2 i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
      exact hc.mul hc
    · simp only [hj, ↓reduceIte, mul_zero]
      exact continuous_const

lemma gradPair_sub (g g' : Point d) (ξ : Fin d → ℝ) :
    gradPair g ξ - gradPair g' ξ = gradPair (g - g') ξ :=
  Prod.ext (gradLoc_sub g g').symm (gradScale_sub g g' ξ).symm

lemma pattern_expected_smoothness (h : Potential L μ V) {w : ℕ} (hS : IsPattern S w)
    (ms : Location d) {Cs : Scale d} (m : Location d) {C : Scale d} (hC : IsLower (C - Cs))
    (hCS : IsSupported S (C - Cs)) :
    Integrable (fun ξ => maskNormSq S (sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ))
      (noiseLaw d) ∧
    ∫ ξ, maskNormSq S (sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ) ∂noiseLaw d ≤
      2 * patternSmooth L μ d w * bregmanMean V ms Cs m C := by
  set r := sqDist m ms C Cs
  set τ := patternTau d w (L / μ)
  have hL := h.L_pos
  have hr : 0 ≤ r := sqDist_nonneg _ _ _ _
  have hκ : 1 ≤ L / μ := (one_le_div h.pos).mpr h.le
  have hτ : 0 ≤ τ := patternTau_nonneg d w hκ
  have hsplit : ∀ ξ, sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ =
      gradPair (gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)) ξ := fun ξ =>
    gradPair_sub _ _ ξ
  have hΔ1 : ∀ ξ, ‖gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)‖ ^ 2 ≤
      2 * L * bregman V ms Cs m C ξ := fun ξ => h.cocoercive (sample m C ξ) (sample ms Cs ξ)
  have hΔ2 : ∀ ξ, ‖gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)‖ ^ 2 ≤
      2 * L ^ 2 * r * (1 + rowMax S ξ) := by
    intro ξ
    have h1 := h.lip (sample m C ξ) (sample ms Cs ξ)
    have h2 := norm_sample_sub_supported_le m ms hCS ξ
    have h3 : ‖gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)‖ ^ 2 ≤
        L ^ 2 * ‖sample m C ξ - sample ms Cs ξ‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg L]
  have hpt : ∀ ξ, maskNormSq S (sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ) ≤
      (1 + τ) * (2 * L * bregman V ms Cs m C ξ) + 2 * L ^ 2 * r * patternTail S τ ξ := by
    intro ξ
    rw [hsplit]
    have h1 := pin_mask_grad_self_le hS (gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)) ξ
    have h2 := tail_split_pattern (S := S) hτ ξ
      (sq_nonneg ‖gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)‖)
      (by positivity : 0 ≤ 2 * L ^ 2 * r) (hΔ2 ξ)
    have h3 : (1 + τ) * ‖gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)‖ ^ 2 ≤
        (1 + τ) * (2 * L * bregman V ms Cs m C ξ) :=
      mul_le_mul_of_nonneg_left (hΔ1 ξ) (by linarith)
    unfold maskNormSq
    linarith
  have hT := pattern_tail_mass hS hκ
  have hB := integrable_bregman h ms m hC
  have hR : Integrable (fun ξ => (1 + τ) * (2 * L * bregman V ms Cs m C ξ) +
      2 * L ^ 2 * r * patternTail S τ ξ) (noiseLaw d) :=
    ((hB.const_mul _).const_mul _).addL (hT.1.const_mul _)
  have hmeas : AEStronglyMeasurable
      (fun ξ => maskNormSq S (sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ)) (noiseLaw d) :=
    (((continuous_maskNormSq S).comp continuous_sub).measurable.comp
      ((measurable_sampleGrad h (m, C)).prodMk (measurable_sampleGrad h (ms, Cs)))).aestronglyMeasurable
  have hint : Integrable (fun ξ => maskNormSq S (sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ))
      (noiseLaw d) := by
    refine integrable_poly hmeas (2 * L ^ 2 * r) fun ξ => ?_
    have h0 : 0 ≤ maskNormSq S (sampleGrad V (m, C) ξ - sampleGrad V (ms, Cs) ξ) :=
      pin_self_nonneg _
    rw [abs_of_nonneg h0, hsplit]
    have h1 := pin_mask_grad_self_le hS (gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)) ξ
    have hM := rowMax_le_sqNorm (S := S) ξ
    have hM0 := rowMax_nonneg (S := S) ξ
    have h2 := mul_le_mul_of_nonneg_left (hΔ2 ξ) (by linarith : (0 : ℝ) ≤ 1 + rowMax S ξ)
    have h3 : 0 ≤ 2 * L ^ 2 * r := by positivity
    have h4 : (1 + rowMax S ξ) * (1 + rowMax S ξ) ≤ (1 + sqNorm ξ) ^ 2 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 h3
    unfold maskNormSq
    nlinarith
  refine ⟨hint, ?_⟩
  have hm := integral_mono hint hR hpt
  rw [integral_add ((hB.const_mul _).const_mul _) (hT.1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul] at hm
  have hlow := bregmanMean_lower h (ms := ms) (Cs := Cs) m hC
  have htail : 2 * L ^ 2 * r * ∫ ξ, patternTail S τ ξ ∂noiseLaw d ≤
      2 * L * bregmanMean V ms Cs m C := by
    have h1 := hT.2
    have hμ := h.pos
    have h2 : 2 * L ^ 2 * r * ∫ ξ, patternTail S τ ξ ∂noiseLaw d =
        L * μ * r * (2 * (L / μ) * ∫ ξ, patternTail S τ ξ ∂noiseLaw d) := by
      field_simp
    rw [h2]
    have h3 : L * μ * r * (2 * (L / μ) * ∫ ξ, patternTail S τ ξ ∂noiseLaw d) ≤ L * μ * r * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  unfold bregmanMean at htail hlow ⊢
  have hsm : patternSmooth L μ d w = L * (2 + τ) := rfl
  rw [hsm]
  nlinarith

lemma pattern_variance (h : Potential L μ V) {w : ℕ} (hS : IsPattern S w) {ms : Location d}
    {Cs : Scale d} (hopt : IsPatternOptimal V S ms Cs) :
    Integrable (fun ξ => maskNormSq S (sampleGrad V (ms, Cs) ξ)) (noiseLaw d) ∧
    ∫ ξ, maskNormSq S (sampleGrad V (ms, Cs) ξ) ∂noiseLaw d ≤
      (2 + patternTau d w (L / μ)) * L * d := by
  have hL := h.L_pos
  have hμ := h.pos
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr h.le
  set τ := patternTau d w (L / μ)
  have hτ : 0 ≤ τ := patternTau_nonneg d w hκ
  set pm : Point d := WithLp.toLp 2 ms
  set g0 : Point d := gradient V pm
  have hCs := hopt.1.1
  have hlowCs : IsLower Cs := hCs.1
  have hz : IsLower (0 : Scale d) := fun i j _ => rfl
  have hA := integral_inner_grad h ms Cs (ms - ms) hlowCs
  have hdiff : ∀ ξ, sample ms Cs ξ - pm =
      (WithLp.toLp 2 ((ms - ms) + Matrix.mulVec Cs ξ) : Point d) := by
    intro ξ
    rw [sub_self]
    exact sample_sub_center ms Cs ξ
  have hAval : ∫ ξ, ⟪gradient V (sample ms Cs ξ), sample ms Cs ξ - pm⟫ ∂noiseLaw d = d := by
    simp_rw [hdiff]
    rw [hA.2, pattern_opt_pinner h hopt (ms - ms) hlowCs hopt.1.2, sum_diag_div_self hCs]
  have hAint : Integrable (fun ξ => ⟪gradient V (sample ms Cs ξ), sample ms Cs ξ - pm⟫)
      (noiseLaw d) := by
    simp_rw [hdiff]
    exact hA.1
  have hBexp : ∀ ξ, ⟪g0, sample ms Cs ξ - pm⟫ = ∑ j, (∑ i, g0 i * Cs i j) * ξ j := by
    intro ξ
    rw [sample_sub_center, inner_eq_sum]
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hB := integral_lin (fun j => ∑ i, g0 i * Cs i j)
  have hBint : Integrable (fun ξ => ⟪g0, sample ms Cs ξ - pm⟫) (noiseLaw d) := by
    simp_rw [hBexp]
    exact hB.1
  have hBval : ∫ ξ, ⟪g0, sample ms Cs ξ - pm⟫ ∂noiseLaw d = 0 := by
    simp_rw [hBexp]
    exact hB.2
  have hnorm2 := isotropy_sub ms ms Cs 0
  have hn2 : ∀ ξ, ‖sample ms Cs ξ - sample ms 0 ξ‖ ^ 2 = ‖sample ms Cs ξ - pm‖ ^ 2 := by
    intro ξ
    rw [sample_zero_scale]
  simp_rw [hn2] at hnorm2
  have hcoc : ∀ ξ, ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 ≤
      L * (⟪gradient V (sample ms Cs ξ), sample ms Cs ξ - pm⟫ - ⟪g0, sample ms Cs ξ - pm⟫) := by
    intro ξ
    have := h.cocoercive_inner (sample ms Cs ξ) pm
    rwa [inner_sub_left] at this
  have hdiffint : Integrable (fun ξ => ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2) (noiseLaw d) := by
    refine integrable_poly ((((h.continuous_grad.comp (continuous_sample_fixed ms Cs)).sub
      continuous_const).norm.pow 2).measurable.aestronglyMeasurable) (L ^ 2 * (2 * sqDist ms ms Cs 0))
      fun ξ => ?_
    have h1 := h.lip (sample ms Cs ξ) pm
    have h2 := norm_sample_sub_sq_le ms ms Cs 0 ξ
    rw [sample_zero_scale] at h2
    have hS := sqNorm_nonneg ξ
    have hq := sqDist_nonneg ms ms Cs 0
    rw [abs_of_nonneg (sq_nonneg _)]
    have h3 : ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 ≤ L ^ 2 * ‖sample ms Cs ξ - pm‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    change ‖sample ms Cs ξ - pm‖ ^ 2 ≤ 2 * sqDist ms ms Cs 0 * (1 + sqNorm ξ) at h2
    have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
    have h5 : 1 + sqNorm ξ ≤ (1 + sqNorm ξ) ^ 2 := by nlinarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ L ^ 2 * (2 * sqDist ms ms Cs 0))
    nlinarith
  have hcocint := integral_mono hdiffint ((hAint.subL hBint).const_mul L) hcoc
  rw [integral_const_mul, integral_sub hAint hBint, hAval, hBval, sub_zero] at hcocint
  have hstr : ∀ ξ, μ * ‖sample ms Cs ξ - pm‖ ^ 2 ≤
      ⟪gradient V (sample ms Cs ξ), sample ms Cs ξ - pm⟫ - ⟪g0, sample ms Cs ξ - pm⟫ := by
    intro ξ
    have := h.strong (sample ms Cs ξ) pm
    rwa [inner_sub_left] at this
  have hstrint := integral_mono (hnorm2.1.const_mul μ) (hAint.subL hBint) hstr
  rw [integral_const_mul, hnorm2.2, integral_sub hAint hBint, hAval, hBval, sub_zero] at hstrint
  have htrace : ∑ i, ∑ j, Cs i j ^ 2 ≤ d / μ := by
    rw [le_div_iff₀ hμ]
    have he : sqDist ms ms Cs 0 = ∑ i, ∑ j, Cs i j ^ 2 := by
      simp [sqDist]
    rw [he] at hstrint
    linarith
  have hC := integral_inner_grad h ms Cs (WithLp.ofLp g0) hz
  have hcen : ∀ ξ, ⟪gradient V (sample ms Cs ξ),
      (WithLp.toLp 2 (WithLp.ofLp g0 + Matrix.mulVec (0 : Scale d) ξ) : Point d)⟫ =
      ⟪gradient V (sample ms Cs ξ), g0⟫ := by
    intro ξ
    rw [mulVec_zero_left, add_zero, WithLp.toLp_ofLp]
  simp_rw [hcen] at hC
  have hCval : ∫ ξ, ⟪gradient V (sample ms Cs ξ), g0⟫ ∂noiseLaw d = 0 := by
    rw [hC.2, pattern_opt_pinner h hopt _ hz (fun _ _ _ => rfl)]
    simp
  have hgrad_int : Integrable (fun ξ => ‖gradient V (sample ms Cs ξ)‖ ^ 2) (noiseLaw d) := by
    have he : ∀ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 =
        ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 + 2 * ⟪gradient V (sample ms Cs ξ), g0⟫ -
          ‖g0‖ ^ 2 := by
      intro ξ
      rw [norm_sub_sq_real]
      ring
    simp_rw [he]
    exact (hdiffint.addL (hC.1.const_mul 2)).subL (integrable_const _)
  have hgrad_val : ∫ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 ∂noiseLaw d =
      (∫ ξ, ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 ∂noiseLaw d) - ‖g0‖ ^ 2 := by
    have he : ∀ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 =
        ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 + 2 * ⟪gradient V (sample ms Cs ξ), g0⟫ -
          ‖g0‖ ^ 2 := by
      intro ξ
      rw [norm_sub_sq_real]
      ring
    simp_rw [he]
    rw [integral_sub (hdiffint.addL (hC.1.const_mul 2)) (integrable_const _),
      integral_add hdiffint (hC.1.const_mul 2), integral_const_mul, hCval]
    simp
  have hgrad_le : ∫ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 ∂noiseLaw d ≤ L * d := by
    rw [hgrad_val]
    nlinarith [sq_nonneg ‖g0‖]
  have hg0 : ‖g0‖ ^ 2 ≤ L * d := by
    have h0 : 0 ≤ ∫ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 ∂noiseLaw d :=
      integral_nonneg fun ξ => sq_nonneg _
    rw [hgrad_val] at h0
    linarith
  have hgrowth : ∀ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 ≤
      2 * (L / μ) * L * d * (1 + rowMax S ξ) := by
    intro ξ
    have h1 := h.lip (sample ms Cs ξ) pm
    have h2 := norm_mulVec_supported_le hopt.1.2 ξ
    rw [← sample_sub_center] at h2
    have hS0 := rowMax_nonneg (S := S) ξ
    have h3 : ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 ≤ L ^ 2 * ‖sample ms Cs ξ - pm‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h4 : ‖gradient V (sample ms Cs ξ)‖ ^ 2 ≤
        2 * ‖gradient V (sample ms Cs ξ) - g0‖ ^ 2 + 2 * ‖g0‖ ^ 2 := by
      have := norm_add_sq_real (gradient V (sample ms Cs ξ) - g0) g0
      rw [sub_add_cancel] at this
      have h5 := norm_sub_sq_real (gradient V (sample ms Cs ξ) - g0) g0
      have h6 := sq_nonneg ‖gradient V (sample ms Cs ξ) - g0 - g0‖
      linarith
    have htr : (∑ i, ∑ j, Cs i j ^ 2) * rowMax S ξ ≤ d / μ * rowMax S ξ :=
      mul_le_mul_of_nonneg_right htrace hS0
    have hLd : L * d ≤ (L / μ) * L * d := by
      have h0 : 0 ≤ L * (d : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_right hκ h0
      calc L * d = 1 * (L * d) := by ring
        _ ≤ L / μ * (L * d) := this
        _ = (L / μ) * L * d := by ring
    have hrw : L ^ 2 * (d / μ * rowMax S ξ) = (L / μ) * L * d * rowMax S ξ := by
      field_simp
    have h7 := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
    have h8 := mul_le_mul_of_nonneg_left htr (sq_nonneg L)
    have h10 : 2 * (L / μ) * L * d * (1 + rowMax S ξ) =
        2 * ((L / μ) * L * d * rowMax S ξ) + 2 * ((L / μ) * L * d) := by ring
    rw [h10]
    linarith
  have hpt : ∀ ξ, maskNormSq S (sampleGrad V (ms, Cs) ξ) ≤
      (1 + τ) * ‖gradient V (sample ms Cs ξ)‖ ^ 2 +
        2 * (L / μ) * L * d * patternTail S τ ξ := by
    intro ξ
    have h1 := pin_mask_grad_self_le hS (gradient V (sample ms Cs ξ)) ξ
    have h2 := tail_split_pattern (S := S) hτ ξ (sq_nonneg ‖gradient V (sample ms Cs ξ)‖)
      (by positivity : 0 ≤ 2 * (L / μ) * L * d) (hgrowth ξ)
    change pin (maskPair S (gradPair (gradient V (sample ms Cs ξ)) ξ))
      (maskPair S (gradPair (gradient V (sample ms Cs ξ)) ξ)) ≤ _
    linarith
  have hT := pattern_tail_mass hS hκ
  have hmeas : AEStronglyMeasurable (fun ξ => maskNormSq S (sampleGrad V (ms, Cs) ξ))
      (noiseLaw d) :=
    ((continuous_maskNormSq S).measurable.comp
      (measurable_sampleGrad h (ms, Cs))).aestronglyMeasurable
  have hint : Integrable (fun ξ => maskNormSq S (sampleGrad V (ms, Cs) ξ)) (noiseLaw d) := by
    refine integrable_poly hmeas (2 * (L / μ) * L * d) fun ξ => ?_
    have h1 := pin_mask_grad_self_le hS (gradient V (sample ms Cs ξ)) ξ
    have h0 : 0 ≤ maskNormSq S (sampleGrad V (ms, Cs) ξ) := pin_self_nonneg _
    have hM := rowMax_le_sqNorm (S := S) ξ
    have hM0 := rowMax_nonneg (S := S) ξ
    rw [abs_of_nonneg h0]
    have h2 := mul_le_mul_of_nonneg_left (hgrowth ξ) (by linarith : (0 : ℝ) ≤ 1 + rowMax S ξ)
    have h3 : 0 ≤ 2 * (L / μ) * L * d := by positivity
    have h4 : (1 + rowMax S ξ) * (1 + rowMax S ξ) ≤ (1 + sqNorm ξ) ^ 2 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 h3
    change pin (maskPair S (gradPair (gradient V (sample ms Cs ξ)) ξ))
      (maskPair S (gradPair (gradient V (sample ms Cs ξ)) ξ)) ≤ _
    nlinarith
  refine ⟨hint, ?_⟩
  have hR : Integrable (fun ξ => (1 + τ) * ‖gradient V (sample ms Cs ξ)‖ ^ 2 +
      2 * (L / μ) * L * d * patternTail S τ ξ) (noiseLaw d) :=
    (hgrad_int.const_mul _).addL (hT.1.const_mul _)
  have hm := integral_mono hint hR hpt
  rw [integral_add (hgrad_int.const_mul _) (hT.1.const_mul _), integral_const_mul,
    integral_const_mul] at hm
  have h1 : (1 + τ) * ∫ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 ∂noiseLaw d ≤ (1 + τ) * (L * d) :=
    mul_le_mul_of_nonneg_left hgrad_le (by linarith)
  have h2 : 2 * (L / μ) * L * d * ∫ ξ, patternTail S τ ξ ∂noiseLaw d ≤ L * d := by
    have := mul_le_mul_of_nonneg_left hT.2 (by positivity : (0 : ℝ) ≤ L * d)
    calc 2 * (L / μ) * L * d * ∫ ξ, patternTail S τ ξ ∂noiseLaw d =
          L * d * (2 * (L / μ) * ∫ ξ, patternTail S τ ξ ∂noiseLaw d) := by ring
      _ ≤ L * d * 1 := this
      _ = L * d := by ring
  have h3 : (2 + τ) * L * d = (1 + τ) * (L * d) + L * d := by ring
  rw [h3]
  linarith

end Smoothness

end OracleTemplate.StructuredGaussianVariational
