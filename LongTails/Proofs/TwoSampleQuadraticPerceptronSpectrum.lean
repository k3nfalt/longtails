import LongTails.Proofs.TwoSampleQuadraticPerceptronBridge

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open LongTails.Setups.TwoSampleQuadraticPerceptron

lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

lemma norm_ones (d : ℕ) : ‖ones d‖ = Real.sqrt d := by
  rw [norm_eq_sqrt_real_inner, inner_ones_ones]

lemma level_mul_le {d : ℕ} (hd : 0 < d) (x : Features d) :
    level d x * Real.sqrt (2 * d) ≤ Real.sqrt 2 * ‖x‖ := by
  have hd' : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hdd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by positivity)
  have hi := real_inner_le_norm x (ones d)
  rw [norm_ones] at hi
  have key0 : level d x * Real.sqrt d = ⟪x, ones d⟫ / Real.sqrt d := by
    unfold level
    rw [div_mul_eq_mul_div, div_eq_div_iff (by exact_mod_cast hd.ne') hd'.ne', mul_assoc, hdd]
  have key : level d x * Real.sqrt (2 * d) = Real.sqrt 2 * (⟪x, ones d⟫ / Real.sqrt d) := by
    rw [← key0, sqrt_two_mul]; ring
  rw [key]
  gcongr
  rwa [div_le_iff₀ hd']

lemma norm_detrended_le {d : ℕ} (D : Data d) (hd : 0 < d) : ‖detrended d D‖ ≤ ‖D.negative‖ := by
  have h := norm_add_sq_real (level d D.negative • ones d) (detrended d D)
  rw [← negative_split, real_inner_smul_left, real_inner_comm, inner_detrended_ones D hd,
    mul_zero, mul_zero, add_zero] at h
  nlinarith [norm_nonneg (detrended d D), norm_nonneg D.negative,
    sq_nonneg ‖level d D.negative • ones d‖]

lemma norm_axisA {d : ℕ} (D : Data d) (h : D.positive ≠ 0) : ‖axisA d D‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_axisA_self D h, Real.sqrt_one]

theorem spectrum_bounds {m : Model} {d : ℕ} (D : Data d) (h : InClass m d D) {R : ℝ}
    (h1 : ‖D.positive‖ ≤ R) (h2 : ‖D.negative‖ ≤ R) :
    (eigenvalues m d D).first ≤ 2 * R ∧ (eigenvalues m d D).second ≤ 2 * R ∧
      (eigenvalues m d D).coupling ≤ 2 * R ∧ (eigenvalues m d D).slow ≤ 2 * R ∧
      0 ≤ (eigenvalues m d D).slow := by
  have hs2 := sqrt_two_le_two
  have hs0 : (0 : ℝ) < Real.sqrt 2 := by positivity
  cases m with
  | twoLayer =>
      have hp : D.positive ≠ 0 := by
        intro h0; have := h.1; rw [h0, inner_zero_left] at this; exact lt_irrefl _ this
      have hA := norm_axisA D hp
      have hR : 0 ≤ R := (norm_nonneg _).trans h1
      have hin : |⟪D.negative, axisA d D⟫| ≤ ‖D.negative‖ := by
        have := abs_real_inner_le_norm D.negative (axisA d D); rwa [hA, mul_one] at this
      simp only [eigenvalues]
      refine ⟨by linarith, by linarith [le_abs_self ⟪D.negative, axisA d D⟫], ?_, by linarith,
        le_rfl⟩
      unfold normalPart
      calc ‖D.negative - ⟪D.negative, axisA d D⟫ • axisA d D‖
          ≤ ‖D.negative‖ + ‖⟪D.negative, axisA d D⟫ • axisA d D‖ := norm_sub_le _ _
        _ = ‖D.negative‖ + |⟪D.negative, axisA d D⟫| := by
          rw [norm_smul, hA, mul_one, Real.norm_eq_abs]
        _ ≤ 2 * R := by linarith
  | conv =>
      obtain ⟨_, _, _, hs⟩ := h
      have hd := dimension_pos D hs
      have hdet := norm_detrended_le D hd
      have hsm : ‖smooth d D‖ ≤ 2 * ‖detrended d D‖ := by
        unfold smooth
        calc _ ≤ ‖detrended d D‖ + ‖shift (detrended d D)‖ := norm_add_le _ _
          _ = 2 * ‖detrended d D‖ := by rw [norm_shift]; ring
      have hro : ‖rough d D‖ ≤ 2 * ‖detrended d D‖ := by
        unfold rough
        calc _ ≤ ‖detrended d D‖ + ‖shift (detrended d D)‖ := norm_sub_le _ _
          _ = 2 * ‖detrended d D‖ := by rw [norm_shift]; ring
      have hhalf : ∀ x : ℝ, 0 ≤ x → x ≤ 2 * R → x / Real.sqrt 2 ≤ 2 * R := by
        intro x hx0 hx
        rw [div_le_iff₀ hs0]
        have h1s : 1 ≤ Real.sqrt 2 := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_le_sqrt (by norm_num)
        nlinarith
      have hR : 0 ≤ R := (norm_nonneg _).trans h1
      simp only [eigenvalues]
      refine ⟨?_, ?_, hhalf _ (norm_nonneg _) (by linarith), hhalf _ (norm_nonneg _) (by linarith),
        by positivity⟩
      · have := level_mul_le hd D.positive; nlinarith [norm_nonneg D.positive]
      · have := level_mul_le hd D.negative; nlinarith [norm_nonneg D.negative]

lemma model_cases {m : Model} {d : ℕ} (D : Data d) (θ : Space m d) :
    m = .conv ∨ ((coordinates m d D θ).r = 0 ∧ (coordinates m d D θ).y = 0) := by
  cases m
  · right; exact ⟨rfl, rfl⟩
  · left; rfl

end LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
