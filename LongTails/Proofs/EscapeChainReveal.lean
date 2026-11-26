import LongTails.Proofs.EscapeChainSimulator

open MeasureTheory

namespace LongTails.Proofs.EscapeChainReveal

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds EscapeChainJets EscapeChainSmooth
open EscapeChainCertificate EscapeChainRegularity EscapeChainCoin EscapeChainOracle
open EscapeChainSimulator ThirdOrderJetDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

lemma sad_small (c : ℝ) : |sad c| ≤ |c| / 16 := by
  rcases le_or_gt (1 / 1024) (c ^ 2) with h | h
  · rw [sad_outer h]; simp; positivity
  · have hc : |c| ≤ 1 / 32 := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt (c ^ 2) ≤ Real.sqrt ((1 / 32) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 1 / 32 := Real.sqrt_sq (by norm_num)
    have h2 := sad_abs_le c
    have : c ^ 2 = |c| * |c| := by rw [← sq_abs]; ring
    nlinarith [abs_nonneg c]

lemma saddle_amplitude (fr : Frame K u v) {l : ℕ} (hl : l < K) (y : E) :
    |saddle u v l y| ≤ |⟪v l, y⟫| / 16 ∧ ‖gradient (saddle u v l) y‖ ≤ 2 ^ 12 * |⟪v l, y⟫| := by
  obtain ⟨g0, g1⟩ := prevGam_bounds u l y
  obtain ⟨w0, w1, -⟩ := loc_bounds (quarter u v l y)
  have hs := sad_small ⟪v l, y⟫
  have hs1 := (sad_jet_bounds ⟪v l, y⟫).2.1
  have hc0 := abs_nonneg ⟪v l, y⟫
  constructor
  · unfold saddle
    simp only [RidgeJets.value]
    rw [abs_mul, abs_mul, abs_of_nonneg g0, abs_of_nonneg (show 0 ≤ window u v l y from w0)]
    calc prevGam u l y * (|sad ⟪v l, y⟫| * window u v l y) ≤ 1 * (|⟪v l, y⟫| / 16 * 1) := by
          gcongr; exact w1
      _ = _ := by ring
  · have hWj := window_jet fr hl.le y 0 0
    have hGj := prevGam_jet fr hl y 0 0
    have hbound : ∀ e : E, |D (saddle u v l) y e| ≤ 2 ^ 12 * |⟪v l, y⟫| * ‖e‖ := by
      intro e
      rw [D_saddle]
      have hv : |⟪v l, e⟫| ≤ ‖e‖ := by
        have h := abs_real_inner_le_norm (v l) e
        rwa [show ‖v l‖ = 1 by
          have h := fr.vv l l hl hl
          rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
          nlinarith [norm_nonneg (v l), sq_nonneg (‖v l‖ - 1)], one_mul] at h
      have hDW : |D (window u v l) y e| ≤ 64 * ‖e‖ := by
        unfold D
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hWj.grad (norm_nonneg e))
      have hDG : |dGam u l y e| ≤ 2 ^ 15 * ‖e‖ := by
        rw [← D_prevGam]
        unfold D
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hGj.grad (norm_nonneg e))
      have hW1 : |window u v l y| ≤ 1 := by
        rw [abs_of_nonneg (show 0 ≤ window u v l y from w0)]; exact w1
      have he := norm_nonneg e
      calc |prevGam u l y * (sad ⟪v l, y⟫ * D (window u v l) y e +
            window u v l y * (sad1 ⟪v l, y⟫ * ⟪v l, e⟫)) +
            sad ⟪v l, y⟫ * window u v l y * dGam u l y e|
          ≤ 1 * (|⟪v l, y⟫| / 16 * (64 * ‖e‖) + 1 * (36 * |⟪v l, y⟫| * ‖e‖)) +
            |⟪v l, y⟫| / 16 * 1 * (2 ^ 15 * ‖e‖) := by
            refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [abs_mul, abs_of_nonneg g0]
              refine mul_le_mul g1 ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
                (by norm_num)
              · rw [abs_mul]; exact mul_le_mul hs hDW (abs_nonneg _) (by positivity)
              · rw [abs_mul, abs_mul]
                exact mul_le_mul hW1 (mul_le_mul hs1 hv (abs_nonneg _) (by positivity))
                  (by positivity) (by norm_num)
            · rw [abs_mul, abs_mul]
              exact mul_le_mul (mul_le_mul hs hW1 (abs_nonneg _) (by positivity)) hDG (abs_nonneg _)
                (by positivity)
        _ ≤ 2 ^ 12 * |⟪v l, y⟫| * ‖e‖ := by nlinarith
    set w := gradient (saddle u v l) y
    have h := hbound w
    unfold D at h
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
    rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
    · rw [← h0]; positivity
    · nlinarith

lemma mvec_amplitude (fr : Frame K u v) {l : ℕ} (hl : l < K) (y : E) :
    ‖mvec K u v l y‖ ≤ 2 ^ 13 * |⟪v l, y⟫| := by
  obtain ⟨c0, c1, -, -⟩ := cut_bounds K y
  obtain ⟨hs, hg⟩ := saddle_amplitude fr hl y
  have hc1 : ‖gradient (RelativeHessianCutoffSpatial.value (radius K)) y‖ ≤ 1 := by
    refine c1.trans ?_
    rw [div_le_one (by have := sqrt_succ_ge K; positivity)]
    have := sqrt_succ_ge K; nlinarith
  rw [mvec_eq]
  calc _ ≤ ‖RelativeHessianCutoffSpatial.value (radius K) y • gradient (saddle u v l) y‖ +
        ‖saddle u v l y • gradient (RelativeHessianCutoffSpatial.value (radius K)) y‖ := norm_add_le _ _
    _ ≤ 1 * (2 ^ 12 * |⟪v l, y⟫|) + |⟪v l, y⟫| / 16 * 1 :=
        add_le_add (smul_le c0 hg (by norm_num)) (smul_le hs hc1 (by positivity))
    _ ≤ _ := by nlinarith [abs_nonneg ⟪v l, y⟫]

lemma mvec_far (fr : Frame K u v) {l : ℕ} (hl : l < K) (y : E) (h : 16 < resid u v l y) :
    mvec K u v l y = 0 := by
  classical
  apply mvec_zero fr hl y
  intro ha
  exact absurd ha.2 (by linarith)

lemma prob_amplitude (fr : Frame K u v) {A : ℝ} (hA : 0 < A) {l : ℕ} (hl : l < K) (y : E) :
    prob K A u v l y ≤ 2 ^ 26 / A *
      (if resid u v l y ≤ 16 then ⟪v l, projL u v l y⟫ ^ 2 else 0) := by
  have hproj : ⟪v l, y⟫ = ⟪v l, projL u v l y⟫ := by
    rw [real_inner_comm (projL u v l y) (v l), projL_inner, real_inner_comm y (v l)]
    have h1 : ∀ m ∈ Finset.range l, (⟪u m, y⟫ * ⟪u m, v l⟫ + ⟪v m, y⟫ * ⟪v m, v l⟫) = 0 := by
      intro m hm
      have hml := Finset.mem_range.1 hm
      rw [fr.uv m l (by omega) hl, fr.vv m l (by omega) hl, ite_eq_right (by omega)]; ring
    rw [Finset.sum_eq_zero h1, sub_zero]
  unfold prob
  split_ifs with hr
  · have hm := mvec_amplitude fr hl y
    have hm2 : ‖mvec K u v l y‖ ^ 2 ≤ (2 ^ 13 * |⟪v l, y⟫|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
    rw [mul_pow, sq_abs, hproj] at hm2
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hA]
    nlinarith
  · rw [mvec_far fr hl y (lt_of_not_ge hr)]; simp

lemma answerS_outside (K j : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) (U : ℝ) (hy : 2 * radius K ≤ ‖y‖) :
    answerS K j A u v y U = y := by
  obtain ⟨c0, cg, -, -⟩ := RelativeHessianCutoffSpatial.outside_jets (radius_pos K) y hy
  have hm : ∀ l, mvec K u v l y = 0 := fun l => by rw [mvec_eq, c0, cg, zero_smul, smul_zero, add_zero]
  unfold answerS
  rw [Finset.sum_eq_zero fun l _ => by rw [hm, smul_zero], add_zero]
  have h : objJ K j u v = fun y => RelativeHessianCutoffSpatial.value (radius K) y * hidden j u v y +
      (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y := rfl
  have hq := RelativeHessianGuard.quadratic_smooth (E := E) 2
  rw [h, add_gradient ((RelativeHessianCutoffSpatial.smooth _).mul (hidden_smooth j u v))
    (contDiff_const.mul hq), ProductCompositionJets.product_gradient
    (RelativeHessianCutoffSpatial.smooth _) (hidden_smooth j u v), cmul_gradient hq]
  beta_reduce
  rw [RelativeHessianGuard.quadratic_gradient, c0, cg, zero_smul, smul_zero, zero_add, smul_smul]
  norm_num

lemma prob_outside (A : ℝ) (u v : ℕ → E) (l : ℕ) (y : E) (hy : 2 * radius K ≤ ‖y‖) :
    prob K A u v l y = 0 := by
  obtain ⟨c0, cg, -, -⟩ := RelativeHessianCutoffSpatial.outside_jets (radius_pos K) y hy
  unfold prob
  rw [mvec_eq, c0, cg, zero_smul, smul_zero, add_zero]; simp

end LongTails.Proofs.EscapeChainReveal
