import LongTails.Proofs.HeavyTailedClipping
import LongTails.Proofs.HilbertSmallMoments

open MeasureTheory

namespace OracleTemplate.MultiplicativeRobustEstimator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clip_residual_le_norm {R : ℝ} (hR : 0 ≤ R) (v : E) :
    ‖clip R v - v‖ ≤ ‖v‖ := by
  rw [norm_sub_rev, clip_residual_norm hR]
  exact max_le (norm_nonneg _) (by linarith)

lemma clip_norm_square_power {R p : ℝ} (hR : 0 ≤ R) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (v : E) : ‖clip R v‖ ^ 2 ≤ R ^ (2-p) * ‖v‖ ^ p := by
  by_cases hv : v = 0
  · subst v
    rw [clip_eq_self (by simpa using hR), norm_zero]
    simp only [zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  by_cases hh : ‖v‖ ≤ R
  · rw [clip_eq_self hh]
    calc
      _ = ‖v‖ ^ (2-p) * ‖v‖ ^ p := by
        rw [← Real.rpow_add hvp, sub_add_cancel, Real.rpow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hvp.le hh (by linarith)) (Real.rpow_nonneg hvp.le _)
  · have hn : ‖clip R v‖ = R := by
      rw [clip, ite_eq_right hh, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hR hvp.le), div_mul_cancel₀ _ hvp.ne']
    rw [hn]
    by_cases hzero : R = 0
    · rw [hzero]
      simp only [zero_pow (by decide : 2 ≠ 0)]
      positivity
    have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    calc
      _ = R ^ (2-p) * R ^ p := by
        rw [← Real.rpow_add hRp, sub_add_cancel, Real.rpow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hR (le_of_not_ge hh) hp) (Real.rpow_nonneg hR _)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_variable_clip : Measurable (fun w : ℝ × E => clip w.1 w.2) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_snd.norm measurable_fst)
    measurable_snd ((measurable_fst.div measurable_snd.norm).smul measurable_snd)

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

lemma random_clip_second_moment {R : Ξ → ℝ} {X : Ω → E} {p : ℝ}
    (hR : Measurable R) (hX : Measurable X) (hRpos : ∀ ξ, 0 ≤ R ξ)
    (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hRi : Integrable (fun ξ => R ξ ^ (2-p)) Q)
    (hXi : Integrable (fun ω => ‖X ω‖ ^ p) P) :
    Integrable (fun w : Ξ × Ω => ‖clip (R w.1) (X w.2)‖ ^ 2) (Q.prod P) ∧
    (∫ w : Ξ × Ω, ‖clip (R w.1) (X w.2)‖ ^ 2 ∂Q.prod P) ≤
      (∫ ξ, R ξ ^ (2-p) ∂Q) * ∫ ω, ‖X ω‖ ^ p ∂P := by
  have hm : Measurable (fun w : Ξ × Ω => clip (R w.1) (X w.2)) :=
    measurable_variable_clip.comp ((hR.comp measurable_fst).prodMk (hX.comp measurable_snd))
  have hi : Integrable (fun w : Ξ × Ω => R w.1 ^ (2-p) * ‖X w.2‖ ^ p) (Q.prod P) :=
    hRi.smul_prod hXi
  have hci : Integrable (fun w : Ξ × Ω => ‖clip (R w.1) (X w.2)‖ ^ 2) (Q.prod P) := by
    apply hi.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact clip_norm_square_power (hRpos _) hp hp2 _)
  refine ⟨hci, ?_⟩
  exact (integral_mono hci hi (fun w => clip_norm_square_power (hRpos _) hp hp2 _)).trans_eq
    (integral_prod_mul (μ := Q) (ν := P) (fun ξ => R ξ ^ (2-p)) (fun ω => ‖X ω‖ ^ p))

lemma random_clip_bias {R : Ξ → ℝ} {X : Ω → E} {p C : ℝ}
    (hR : Measurable R) (hX : Measurable X) (hRpos : ∀ ξ, 0 ≤ R ξ)
    (hp : 1 ≤ p) (hC : 0 < C) (u : E) (hu : ‖u‖ ≤ C/2)
    (hXi : Integrable X P) (hmean : ∫ ω, X ω ∂P = u)
    (hpi : Integrable (fun ω => ‖X ω-u‖ ^ p) P) {B : Set Ξ}
    (hB : MeasurableSet B) (hgood : ∀ ξ ∉ B, C ≤ R ξ) :
    Integrable (fun w : Ξ × Ω => clip (R w.1) (X w.2)) (Q.prod P) ∧
    ‖(∫ w : Ξ × Ω, clip (R w.1) (X w.2) ∂Q.prod P) - u‖ ≤
      (∫ ω, ‖X ω-u‖ ^ p ∂P) / (C/2) ^ (p-1) +
        Q.real B * ∫ ω, ‖X ω‖ ∂P := by
  classical
  have hm : Measurable (fun w : Ξ × Ω => clip (R w.1) (X w.2)) :=
    measurable_variable_clip.comp ((hR.comp measurable_fst).prodMk (hX.comp measurable_snd))
  have hci : Integrable (fun w : Ξ × Ω => clip (R w.1) (X w.2)) (Q.prod P) := by
    apply (hXi.norm.comp_snd Q).mono' hm.aestronglyMeasurable
    filter_upwards [] with w
    simpa only [sub_zero] using norm_clip_sub_le (hRpos w.1)
      (show ‖(0 : E)‖ ≤ R w.1 by simpa using hRpos w.1) (X w.2)
  let F : Ξ × Ω → ℝ := fun w => ‖X w.2-u‖ ^ p / (C/2) ^ (p-1) +
    B.indicator (fun _ => (1 : ℝ)) w.1 * ‖X w.2‖
  have hBi : Integrable (fun w : Ξ × Ω => B.indicator (fun _ => (1 : ℝ)) w.1 * ‖X w.2‖) (Q.prod P) :=
    ((integrable_const (1 : ℝ)).indicator hB).smul_prod hXi.norm
  have hFi : Integrable F (Q.prod P) :=
    ((hpi.div_const _).comp_snd Q).add hBi
  have hpoint (w : Ξ × Ω) : ‖clip (R w.1) (X w.2) - X w.2‖ ≤ F w := by
    dsimp [F]
    by_cases hb : w.1 ∈ B
    · simp only [Set.indicator_of_mem hb, one_mul]
      exact (clip_residual_le_norm (hRpos _) _).trans (le_add_of_nonneg_left (by positivity))
    · simp only [Set.indicator_of_notMem hb, zero_mul, add_zero]
      rw [norm_sub_rev]
      have hr : 0 < R w.1 := hC.trans_le (hgood _ hb)
      exact (clip_residual_le_moment hr hp (hu.trans (by linarith [hgood _ hb])) _).trans
        (div_le_div_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_pos_of_pos (by positivity : 0 < C/2) _)
          (Real.rpow_le_rpow (by positivity) (by linarith [hgood _ hb]) (by linarith)))
  have hb := norm_integral_le_of_norm_le hFi (Filter.Eventually.of_forall hpoint)
  rw [integral_sub hci (hXi.comp_snd Q)] at hb
  have hx : (∫ w : Ξ × Ω, X w.2 ∂Q.prod P) = u := by
    rw [integral_fun_snd]
    simpa using hmean
  rw [hx] at hb
  refine ⟨hci, hb.trans_eq ?_⟩
  rw [show F = fun w : Ξ × Ω => ‖X w.2-u‖ ^ p / (C/2) ^ (p-1) +
    B.indicator (fun _ => (1 : ℝ)) w.1 * ‖X w.2‖ from rfl,
    integral_add ((hpi.div_const _).comp_snd Q) hBi,
    integral_fun_snd (μ := Q) (ν := P) (fun ω => ‖X ω-u‖ ^ p / (C/2) ^ (p-1)),
    integral_prod_mul (μ := Q) (ν := P) (B.indicator (fun _ => (1 : ℝ))) (fun ω => ‖X ω‖),
    integral_div, integral_indicator hB]
  simp

end OracleTemplate.MultiplicativeRobustEstimator
