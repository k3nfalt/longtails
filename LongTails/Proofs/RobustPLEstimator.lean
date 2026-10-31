import LongTails.Algorithms.HeavyTailedPLHessian
import LongTails.Proofs.RobustPLSampling

open MeasureTheory

namespace OracleTemplate.HeavyTailedPLHessian

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] in
lemma measurable_pilot : Measurable (pilot (E := E)) :=
  MultiplicativeRobustEstimator.measurable_medoid.comp
    (Measurable.of_eval fun i => MultiplicativeRobustEstimator.measurable_medoid.comp
      (measurable_pi_apply i))

lemma measurable_estimate (τ : ℝ) :
    Measurable (fun w : (Fin 8 → Fin 8 → E) × E => estimate τ w.1 w.2) :=
  RobustGradient.measurable_centeredClip_joint.comp (measurable_const.prodMk
    ((measurable_pilot.comp measurable_fst).prodMk measurable_snd))

omit [InnerProductSpace ℝ E] in
lemma pilot_fourth_moment {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω - u‖) P) {σ : ℝ}
    (hm : (∫ ω, ‖X ω - u‖ ∂P) ≤ σ) :
    Integrable (fun ξ : Fin 8 → Fin 8 → Ω => ‖pilot (fun i j => X (ξ i j)) - u‖ ^ 4)
      (Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin 8 => P) ∧
    (∫ ξ : Fin 8 → Fin 8 → Ω, ‖pilot (fun i j => X (ξ i j)) - u‖ ^ 4
      ∂Measure.pi (fun _ : Fin 8 => Measure.pi fun _ : Fin 8 => P)) ≤ 4608 ^ 4 * σ ^ 4 := by
  have hh := LongTails.Proofs.StochasticEnvelopeSampling.nested_medoid_fourth_moment
    hX u hi 7 (by norm_num)
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg fun ω => norm_nonneg _) hm 4) (by positivity)

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma first_moment_of_heavy {X : Ω → E} (hX : Measurable X) (u : E)
    {p σ : ℝ} (hp : 1 ≤ p) (hσ : 0 ≤ σ)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    Integrable (fun ω => ‖X ω - u‖) P ∧ (∫ ω, ‖X ω - u‖ ∂P) ≤ σ := by
  have hp0 : 0 < p := by linarith
  have hh := LongTails.Proofs.StochasticEnvelopeSampling.lower_power_moment
    (hX.sub_const u) hp0 (by norm_num : (0 : ℝ) ≤ 1) hp hi
  simp only [Real.rpow_one] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hb := Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hm
    (by positivity : 0 ≤ 1 / p)
  have he : (σ ^ p) ^ (1 / p) = σ := by
    rw [← Real.rpow_mul hσ, mul_one_div_cancel hp0.ne', Real.rpow_one]
  rwa [he] at hb

lemma fourth_tail_power {σ τ p r : ℝ} (hσ : 0 ≤ σ) (hτ : 0 < τ)
    (hστ : σ ≤ τ) (hp : 0 < p) (hp4 : p ≤ 4) :
    σ ^ 4 / τ ^ (4 - r) ≤ σ ^ p * τ ^ (r - p) := by
  have hb : σ ^ 4 ≤ σ ^ p * τ ^ (4 - p) := by
    by_cases hz : σ = 0
    · simp [hz, Real.zero_rpow hp.ne']
    · have hs : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
      calc
        σ ^ 4 = σ ^ p * σ ^ (4 - p) := by
          rw [← Real.rpow_add hs, add_sub_cancel, Real.rpow_ofNat]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hσ hστ (sub_nonneg.mpr hp4)) (by positivity)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hτ _)).mpr
  have he : σ ^ p * τ ^ (r - p) * τ ^ (4 - r) = σ ^ p * τ ^ (4 - p) := by
    rw [mul_assoc, ← Real.rpow_add hτ]
    congr 2
    ring
  rwa [he]

lemma clipping_coefficients {τ p : ℝ} (hτ : 0 < τ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    (3 * τ / 2) ^ (2 - p) ≤ 2 * τ ^ (2 - p) ∧
    (3 * τ / 2) ^ 2 * (3 * τ / 2) ^ (2 - p) ≤ 8 * τ ^ (4 - p) ∧
    1 / (τ / 2) ^ (p - 1) ≤ 2 * τ ^ (1 - p) := by
  have hc : (3 / 2 : ℝ) ^ (2 - p) ≤ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3 / 2)
      (by linarith : 2 - p ≤ 1)
    norm_num only [Real.rpow_one] at hh
    linarith
  have h2 : (3 * τ / 2) ^ (2 - p) ≤ 2 * τ ^ (2 - p) := by
    rw [show 3 * τ / 2 = (3 / 2) * τ by ring, Real.mul_rpow (by norm_num) hτ.le]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  refine ⟨h2, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left h2 (sq_nonneg (3 * τ / 2))
    have he : (3 * τ / 2) ^ 2 * (2 * τ ^ (2 - p)) = (9 / 2) * τ ^ (4 - p) := by
      have ht : τ ^ 2 * τ ^ (2 - p) = τ ^ (4 - p) := by
        rw [← Real.rpow_two, ← Real.rpow_add hτ]
        congr 1
        ring
      calc
        _ = (9 / 2) * (τ ^ 2 * τ ^ (2 - p)) := by ring
        _ = _ := by rw [ht]
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · have hc2 : (2 : ℝ) ^ (p - 1) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) (by linarith : p - 1 ≤ 1)
    have he : 1 / (τ / 2) ^ (p - 1) = 2 ^ (p - 1) * τ ^ (1 - p) := by
      rw [Real.div_rpow hτ.le (by norm_num), show 1 - p = -(p - 1) by ring,
        Real.rpow_neg hτ.le]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
    rw [he]
    exact mul_le_mul_of_nonneg_right hc2 (by positivity)

lemma estimator_bounds {σ τ p : ℝ} (hσ : 0 ≤ σ) (hτ : 0 < τ)
    (hστ : σ ≤ τ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    σ ^ p / (τ / 2) ^ (p - 1) + 24 / τ ^ 3 * (4608 ^ 4 * σ ^ 4) ≤
      2 ^ 64 * σ ^ p * τ ^ (1 - p) ∧
    (3 * τ / 2) ^ (2 - p) * σ ^ p + 36 / τ ^ 2 * (4608 ^ 4 * σ ^ 4) ≤
      2 ^ 64 * σ ^ p * τ ^ (2 - p) ∧
    (3 * τ / 2) ^ 2 * ((3 * τ / 2) ^ (2 - p) * σ ^ p) + 81 * (4608 ^ 4 * σ ^ 4) ≤
      2 ^ 64 * σ ^ p * τ ^ (4 - p) := by
  have hp0 : 0 < p := by linarith
  have hp4 : p ≤ 4 := by linarith
  have h1 : σ ^ 4 / τ ^ 3 ≤ σ ^ p * τ ^ (1 - p) := by
    convert fourth_tail_power (r := 1) hσ hτ hστ hp0 hp4 using 1
    norm_num
  have h2 : σ ^ 4 / τ ^ 2 ≤ σ ^ p * τ ^ (2 - p) := by
    convert fourth_tail_power (r := 2) hσ hτ hστ hp0 hp4 using 1
    norm_num
  have h4 : σ ^ 4 ≤ σ ^ p * τ ^ (4 - p) := by
    simpa using fourth_tail_power (r := 4) hσ hτ hστ hp0 hp4
  have hc := clipping_coefficients hτ hp hp2
  have hs : 0 ≤ σ ^ p := Real.rpow_nonneg hσ _
  refine ⟨?_, ?_, ?_⟩
  · have ha := mul_le_mul_of_nonneg_left hc.2.2 hs
    have hb := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 24 * 4608 ^ 4)
    have hn : 0 ≤ σ ^ p * τ ^ (1 - p) := by positivity
    have he : σ ^ p * (1 / (τ / 2) ^ (p - 1)) = σ ^ p / (τ / 2) ^ (p - 1) := by ring
    rw [he] at ha
    simp only [div_eq_mul_inv] at ha hb ⊢
    nlinarith only [ha, hb, hn]
  · have ha := mul_le_mul_of_nonneg_right hc.1 hs
    have hb := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 36 * 4608 ^ 4)
    have hn : 0 ≤ σ ^ p * τ ^ (2 - p) := by positivity
    simp only [div_eq_mul_inv] at ha hb ⊢
    nlinarith only [ha, hb, hn]
  · have ha := mul_le_mul_of_nonneg_right hc.2.1 hs
    have hb := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 81 * 4608 ^ 4)
    have hn : 0 ≤ σ ^ p * τ ^ (4 - p) := by positivity
    simp only [div_eq_mul_inv] at ha hb ⊢
    nlinarith only [ha, hb, hn]

lemma estimate_moments [CompleteSpace E] {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (u : E) (hmean : ∫ ω, X ω ∂P = u)
    {p σ τ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hτ : 0 < τ) (hστ : σ ≤ τ)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpm : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    let Q := (Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin 8 => P).prod P
    let Z := fun w : (Fin 8 → Fin 8 → Ω) × Ω => estimate τ (fun i j => X (w.1 i j)) (X w.2) - u
    Integrable Z Q ∧ Integrable (fun w => ‖Z w‖ ^ 2) Q ∧ Integrable (fun w => ‖Z w‖ ^ 4) Q ∧
    ‖∫ w, Z w ∂Q‖ ≤ 2 ^ 64 * σ ^ p * τ ^ (1 - p) ∧
    (∫ w, ‖Z w‖ ^ 2 ∂Q) ≤ 2 ^ 64 * σ ^ p * τ ^ (2 - p) ∧
    (∫ w, ‖Z w‖ ^ 4 ∂Q) ≤ 2 ^ 64 * σ ^ p * τ ^ (4 - p) := by
  let R := Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin 8 => P
  let C := fun ξ : Fin 8 → Fin 8 → Ω => pilot (fun i j => X (ξ i j))
  have hCm : Measurable C := measurable_pilot.comp (Measurable.of_eval fun i =>
    Measurable.of_eval fun j => hX.comp ((measurable_pi_apply j).comp (measurable_pi_apply i)))
  have hfirst := first_moment_of_heavy hX u hp hσ hpi hpm
  have hfourth := pilot_fourth_moment hX u hfirst.1 hfirst.2
  have hB := RobustGradient.random_center_heavy_bias (P := R) hCm hX hXi u hmean hτ hp hp2 hfourth.1 hpi
  have hV := RobustGradient.random_center_heavy_second (P := R) hCm hX u hτ
    (by linarith : 0 ≤ p) hp2 hfourth.1 hpi
  have hQ := RobustGradient.random_center_heavy_fourth (P := R) hCm hX u hτ
    (by linarith : 0 ≤ p) hp2 hfourth.1 hpi
  have hb := estimator_bounds hσ hτ hστ hp hp2
  refine ⟨hB.1, hV.1, hQ.1, hB.2.trans ?_, hV.2.trans ?_, hQ.2.trans ?_⟩
  · apply le_trans ?_ hb.1
    gcongr
    exact hfourth.2
  · apply le_trans ?_ hb.2.1
    gcongr
    exact hfourth.2
  · apply le_trans ?_ hb.2.2
    gcongr
    exact hfourth.2

end OracleTemplate.HeavyTailedPLHessian
