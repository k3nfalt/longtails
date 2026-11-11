import LongTails.Proofs.GaussianVariationalOptimality

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ} {L μ : ℝ} {V : Point d → ℝ}

lemma norm_mulVec_sq_le (U : Scale d) (ξ : Fin d → ℝ) :
    ‖(WithLp.toLp 2 ((0 : Location d) + Matrix.mulVec U ξ) : Point d)‖ ^ 2 ≤
      (∑ i, ∑ j, U i j ^ 2) * sqNorm ξ := by
  rw [norm_sq_eq_sum]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma sample_zero_scale (m : Location d) (ξ : Fin d → ℝ) :
    sample m (0 : Scale d) ξ = (WithLp.toLp 2 m : Point d) := by
  unfold sample
  rw [mulVec_zero_left, add_zero]

lemma sample_sub_center (m : Location d) (C : Scale d) (ξ : Fin d → ℝ) :
    sample m C ξ - (WithLp.toLp 2 m : Point d) =
      (WithLp.toLp 2 ((0 : Location d) + Matrix.mulVec C ξ) : Point d) := by
  rw [← sample_zero_scale m ξ, sample_sub, sub_self, sub_zero]

lemma sum_diag_div_self {Cs : Scale d} (hCs : IsCholesky Cs) :
    ∑ i, Cs i i / Cs i i = d := by
  rw [Finset.sum_congr rfl fun i _ => div_self (hCs.2 i).ne']
  simp

lemma variance_at_optimum (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) :
    Integrable (fun ξ => pinner (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ)) (noiseLaw d) ∧
    ∫ ξ, pinner (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) ∂noiseLaw d ≤ (2 + tau d (L / μ)) * L * d := by
  have hL := h.L_pos
  have hμ := h.pos
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr h.le
  set τ := tau d (L / μ)
  have hτ : 0 ≤ τ := tau_nonneg d hκ
  set pm : Point d := WithLp.toLp 2 ms
  set g0 : Point d := gradient V pm
  have hCs := hopt.1
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
    rw [hA.2, opt_pinner h hopt (ms - ms) hlowCs, sum_diag_div_self hCs]
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
    rw [hC.2, opt_pinner h hopt _ hz]
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
      2 * (L / μ) * L * d * (1 + sqNorm ξ) := by
    intro ξ
    have h1 := h.lip (sample ms Cs ξ) pm
    have h2 := norm_mulVec_sq_le Cs ξ
    rw [← sample_sub_center] at h2
    have hS := sqNorm_nonneg ξ
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
    have htr : (∑ i, ∑ j, Cs i j ^ 2) * sqNorm ξ ≤ d / μ * sqNorm ξ :=
      mul_le_mul_of_nonneg_right htrace hS
    have hLd : L * d ≤ (L / μ) * L * d := by
      have h0 : 0 ≤ L * (d : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_right hκ h0
      calc L * d = 1 * (L * d) := by ring
        _ ≤ L / μ * (L * d) := this
        _ = (L / μ) * L * d := by ring
    have hrw : L ^ 2 * (d / μ * sqNorm ξ) = (L / μ) * L * d * sqNorm ξ := by
      field_simp
    have h7 := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
    have h8 := mul_le_mul_of_nonneg_left htr (sq_nonneg L)
    have h9 : L ^ 2 * ((∑ i, ∑ j, Cs i j ^ 2) * sqNorm ξ) ≤ L ^ 2 * (d / μ * sqNorm ξ) := h8
    have h10 : 2 * (L / μ) * L * d * (1 + sqNorm ξ) =
        2 * ((L / μ) * L * d * sqNorm ξ) + 2 * ((L / μ) * L * d) := by ring
    rw [h10]
    linarith
  have hpt : ∀ ξ, pinner (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) ≤
      (1 + τ) * ‖gradient V (sample ms Cs ξ)‖ ^ 2 + 2 * (L / μ) * L * d * tailFn d τ ξ := by
    intro ξ
    have h1 := pinner_grad_self_le (gradient V (sample ms Cs ξ)) ξ
    have h2 := tail_split (τ := τ) (sqNorm_nonneg ξ) (sq_nonneg ‖gradient V (sample ms Cs ξ)‖)
      (by positivity : 0 ≤ 2 * (L / μ) * L * d) (hgrowth ξ)
    unfold tailFn
    linarith
  have hT := tail_mass h
  have hmeas : AEStronglyMeasurable (fun ξ => pinner (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ)) (noiseLaw d) := by
    have hg := measurable_grad_sample h ms Cs
    unfold pinner gradLoc gradScale
    refine Measurable.aestronglyMeasurable ?_
    refine (Finset.measurable_sum _ fun i _ => ?_).add
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    · exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg).mul
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg)
    · have hm1 : Measurable (fun ξ : Fin d → ℝ =>
          if j ≤ i then gradient V (sample ms Cs ξ) i * ξ j else 0) := by
        split_ifs
        · exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg).mul (measurable_pi_apply j)
        · exact measurable_const
      exact hm1.mul hm1
  have hint : Integrable (fun ξ => pinner (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ) (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ)) (noiseLaw d) := by
    refine integrable_poly hmeas (2 * (L / μ) * L * d) fun ξ => ?_
    have h1 := pinner_grad_self_le (gradient V (sample ms Cs ξ)) ξ
    have h0 := pinner_self_nonneg (gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample ms Cs ξ)) ξ)
    have hS := sqNorm_nonneg ξ
    rw [abs_of_nonneg h0]
    have h2 := mul_le_mul_of_nonneg_left (hgrowth ξ) (by linarith : (0 : ℝ) ≤ 1 + sqNorm ξ)
    nlinarith
  refine ⟨hint, ?_⟩
  have hR : Integrable (fun ξ => (1 + τ) * ‖gradient V (sample ms Cs ξ)‖ ^ 2 +
      2 * (L / μ) * L * d * tailFn d τ ξ) (noiseLaw d) :=
    (hgrad_int.const_mul _).addL (hT.1.const_mul _)
  have hm := integral_mono hint hR hpt
  rw [integral_add (hgrad_int.const_mul _) (hT.1.const_mul _), integral_const_mul,
    integral_const_mul] at hm
  have h1 : (1 + τ) * ∫ ξ, ‖gradient V (sample ms Cs ξ)‖ ^ 2 ∂noiseLaw d ≤ (1 + τ) * (L * d) :=
    mul_le_mul_of_nonneg_left hgrad_le (by linarith)
  have h2 : 2 * (L / μ) * L * d * ∫ ξ, tailFn d τ ξ ∂noiseLaw d ≤ L * d := by
    have := mul_le_mul_of_nonneg_left hT.2 (by positivity : (0 : ℝ) ≤ L * d)
    calc 2 * (L / μ) * L * d * ∫ ξ, tailFn d τ ξ ∂noiseLaw d =
          L * d * (2 * (L / μ) * ∫ ξ, tailFn d τ ξ ∂noiseLaw d) := by ring
      _ ≤ L * d * 1 := this
      _ = L * d := by ring
  have h3 : (2 + τ) * L * d = (1 + τ) * (L * d) + L * d := by ring
  rw [h3]
  linarith

end OracleTemplate.GaussianVariational
