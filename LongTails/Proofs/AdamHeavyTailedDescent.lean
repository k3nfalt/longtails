import LongTails.Proofs.AdamHeavyTailedTrajectory
import LongTails.Proofs.GdConvex
import LongTails.Proofs.MixedNoiseSelectors

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.Adam

lemma trajectory_step {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    (trajectory g q ρ η τ x0 ξ (t + 1)).1 =
      (trajectory g q ρ η τ x0 ξ t).1 - η • velocity g q ρ η τ x0 ξ (t + 1) := rfl

lemma trajectory_descent_step {d : ℕ} {Ω : Type*} {f : Point d → ℝ}
    {grad : Point d → Point d} {L : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    f (trajectory g q ρ η τ x0 ξ (t + 1)).1 ≤
      f (trajectory g q ρ η τ x0 ξ t).1 -
        η * ⟪grad (trajectory g q ρ η τ x0 ξ t).1, velocity g q ρ η τ x0 ξ (t + 1)⟫ +
        L * η ^ 2 / 2 * ‖velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 := by
  have h := Gradient.smooth_upper_bound hf hlip
    (trajectory g q ρ η τ x0 ξ t).1 (trajectory g q ρ η τ x0 ξ (t + 1)).1
  have he : (trajectory g q ρ η τ x0 ξ (t + 1)).1 -
      (trajectory g q ρ η τ x0 ξ t).1 = -η • velocity g q ρ η τ x0 ξ (t + 1) := by
    rw [trajectory_step]
    module
  rw [he] at h
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs] at h
  nlinarith

lemma trajectory_descent_sum {d : ℕ} {Ω : Type*} {f : Point d → ℝ}
    {grad : Point d → Point d} {L Δ : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q ρ η τ : ℝ) (x0 : Point d)
    (hgap : ∀ x, f x0 - f x ≤ Δ) (ξ : ℕ → Ω) (T : ℕ) :
    η * (∑ t ∈ Finset.range T,
      ⟪grad (trajectory g q ρ η τ x0 ξ t).1, velocity g q ρ η τ x0 ξ (t + 1)⟫) ≤
      Δ + L * η ^ 2 / 2 * ∑ t ∈ Finset.range T, ‖velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 := by
  have ht : f (trajectory g q ρ η τ x0 ξ T).1 ≤ f x0 -
      η * (∑ t ∈ Finset.range T,
        ⟪grad (trajectory g q ρ η τ x0 ξ t).1, velocity g q ρ η τ x0 ξ (t + 1)⟫) +
      L * η ^ 2 / 2 * ∑ t ∈ Finset.range T, ‖velocity g q ρ η τ x0 ξ (t + 1)‖ ^ 2 := by
    induction T with
    | zero => simp [trajectory]
    | succ T ih =>
      have hh := trajectory_descent_step hf hlip g q ρ η τ x0 ξ T
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  linarith [hgap (trajectory g q ρ η τ x0 ξ T).1]

lemma trajectory_displacement {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) :
    ‖(trajectory g q ρ η τ x0 ξ (s + j)).1 - (trajectory g q ρ η τ x0 ξ s).1‖ ≤
      |η| * ∑ k ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, trajectory_step, Finset.sum_range_succ]
    have he : (trajectory g q ρ η τ x0 ξ (s + j)).1 - η • velocity g q ρ η τ x0 ξ (s + j + 1) -
        (trajectory g q ρ η τ x0 ξ s).1 =
        ((trajectory g q ρ η τ x0 ξ (s + j)).1 - (trajectory g q ρ η τ x0 ξ s).1) -
          η • velocity g q ρ η τ x0 ξ (s + j + 1) := by abel
    rw [he]
    have ht := norm_sub_le
      ((trajectory g q ρ η τ x0 ξ (s + j)).1 - (trajectory g q ρ η τ x0 ξ s).1)
      (η • velocity g q ρ η τ x0 ξ (s + j + 1))
    rw [norm_smul, Real.norm_eq_abs] at ht
    nlinarith

lemma gradient_window_variation {d : ℕ} {Ω : Type*} {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) :
    ‖grad (trajectory g q ρ η τ x0 ξ (s + j)).1 - grad (trajectory g q ρ η τ x0 ξ s).1‖ ≤
      L * |η| * ∑ k ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖ := by
  exact (hlip _ _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (trajectory_displacement g q ρ η τ x0 ξ s j) hL)

noncomputable def signalEnergy {d : ℕ} (ρ τ : ℝ) (v μ : Point d) : ℝ :=
  ∑ i, (μ i) ^ 2 / (Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ)

lemma signalEnergy_nonneg {d : ℕ} {ρ τ : ℝ} (hτ : 0 < τ) (v μ : Point d) :
    0 ≤ signalEnergy ρ τ v μ := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (by positivity)

lemma current_direction_energy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → Point d}
    (hg : Measurable g) (hgi : Integrable g P) (v μ : Point d)
    {ρ τ p M : ℝ} (hv : ∀ i, 0 ≤ v i) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ)
    (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hm : Integrable (fun ω => ∑ i, |(g ω - μ) i| ^ p) P)
    (hmass : (∫ ω, ∑ i, |(g ω - μ) i| ^ p ∂P) ≤ M) :
    (∫ ω, ‖direction τ (g ω) (secondMomentStep ρ v (g ω))‖ ^ 2 ∂P) ≤
      (2 / τ) * signalEnergy ρ τ v μ + ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M := by
  have hh := LongTails.Proofs.AdamHeavyTailedWindow.joint_response_energy
    (fun i => (1 - ρ) * v i) (fun i => μ i)
    (fun i => mul_nonneg (sub_nonneg.mpr hρ1) (hv i)) hρ hτ hp hp2
    (fun i ω => (g ω - μ) i)
    (fun i => integrable_error_coordinate hgi μ i)
    (fun i => integrable_error_power hg μ p hm i)
    ((sum_integral_error_power hg μ p hm).trans_le hmass)
  have he (ω : Ω) (i : Fin d) : μ i + (g ω - μ) i = g ω i := by
    change μ i + (g ω i - μ i) = g ω i
    ring
  simp_rw [he] at hh
  simpa only [signalEnergy, PiLp.norm_sq_eq_of_L2, direction, secondMomentStep,
    Real.norm_eq_abs, sq_abs] using hh

lemma measurable_gradient_of_lipschitz {d : ℕ} {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖) : Measurable grad := by
  have hh : LipschitzWith ⟨L, hL⟩ grad := lipschitzWith_iff_norm_sub_le.mpr hlip
  exact hh.continuous.measurable

lemma trajectory_gradient_bound {d : ℕ} {Ω : Type*} {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) {q ρ η τ : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) :
    ‖grad (trajectory g q ρ η τ x0 ξ t).1‖ ≤ ‖grad x0‖ + L *
      ((t : ℝ) * (|η| * (((d : ℝ) + 1) * ((1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ)))))) := by
  have hh := norm_le_norm_sub_add (grad (trajectory g q ρ η τ x0 ξ t).1) (grad x0)
  have hd := mul_le_mul_of_nonneg_left (trajectory_distance_bound (η := η) g hq hq1 hρ hρ1 hτ hstable x0 ξ t) hL
  linarith [hlip (trajectory g q ρ η τ x0 ξ t).1 x0]

lemma integrable_trajectory_gradient_norm {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (t : ℕ) :
    Integrable (fun ξ => ‖grad (trajectory g q ρ η τ x0 ξ t).1‖) P := by
  apply Integrable.of_bound (((measurable_gradient_of_lipschitz hL hlip).comp
    (measurable_trajectory hg q ρ η τ x0 t).fst).norm.aestronglyMeasurable)
    (‖grad x0‖ + L * ((t : ℝ) * (|η| * (((d : ℝ) + 1) *
      ((1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ)))))))
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_norm]
    exact trajectory_gradient_bound hL hlip g hq hq1 hρ hρ1 hτ hstable x0 ξ t

lemma signalEnergy_le_norm_sq {d : ℕ} {ρ τ : ℝ} (hτ : 0 < τ) (v μ : Point d) :
    signalEnergy ρ τ v μ ≤ ‖μ‖ ^ 2 / τ := by
  rw [signalEnergy, PiLp.norm_sq_eq_of_L2, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hτ (le_add_of_nonneg_left (Real.sqrt_nonneg _))

lemma measurable_selected_trajectory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (q ρ η τ : ℝ) (x0 : Point d) (n : ℕ) :
    Measurable (fun z : Fin (n + 1) × (ℕ → Ω) => (trajectory g q ρ η τ x0 z.2 z.1.val).1) :=
  measurable_from_prod_countable_right fun i => (measurable_trajectory hg q ρ η τ x0 i.val).fst

lemma integrable_selected_gradient {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (n : ℕ)
    (hi : ∀ t, Integrable (fun ξ => ‖grad (trajectory g q ρ η τ x0 ξ t).1‖) P) :
    Integrable (fun z : Fin (n + 1) × (ℕ → Ω) => ‖grad (trajectory g q ρ η τ x0 z.2 z.1.val).1‖)
      ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.prod P) := by
  apply (integrable_prod_iff ((hgrad.comp (measurable_selected_trajectory hg q ρ η τ x0 n)).norm.aestronglyMeasurable)).2
  exact ⟨Filter.Eventually.of_forall fun i => hi i.val, Integrable.of_finite⟩

lemma integral_selected_gradient {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (n : ℕ)
    (hi : ∀ t, Integrable (fun ξ => ‖grad (trajectory g q ρ η τ x0 ξ t).1‖) P) :
    (∫ z : Fin (n + 1) × (ℕ → Ω), ‖grad (trajectory g q ρ η τ x0 z.2 z.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.prod P)) =
        ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ t ∈ Finset.range (n + 1), ∫ ξ, ‖grad (trajectory g q ρ η τ x0 ξ t).1‖ ∂P := by
  rw [integral_prod _ (integrable_selected_gradient P hg hgrad q ρ η τ x0 n hi),
    OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, ‖grad (trajectory g q ρ η τ x0 ξ t).1‖ ∂P)]

lemma signal_coordinate_control {d : ℕ} {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hτ : 0 < τ) (v μ : Point d) (hv : ∀ i, 0 ≤ v i) (i : Fin d) :
    (μ i) ^ 2 ≤ signalEnergy ρ τ v μ *
      ((Real.sqrt ((1 - ρ) * v i) + τ) + Real.sqrt ρ * |μ i|) := by
  have hd : 0 < Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ := by positivity
  have ht : (μ i) ^ 2 / (Real.sqrt ((1 - ρ) * v i + ρ * (μ i) ^ 2) + τ) ≤ signalEnergy ρ τ v μ := by
    apply Finset.single_le_sum _ (Finset.mem_univ i)
    intro j _
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hs := (div_le_iff₀ hd).mp ht
  exact hs.trans (mul_le_mul_of_nonneg_left
    (LongTails.Proofs.AdamHeavyTailedNormalizer.signal_denominator_upper (mul_nonneg (sub_nonneg.mpr hρ1) (hv i)) hρ)
    (signalEnergy_nonneg hτ v μ))

lemma coordinate_bias_absorbed {d : ℕ} {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hτ : 0 < τ) (v μ : Point d) (hv : ∀ i, 0 ≤ v i) (i : Fin d) :
    100 * τ * Real.sqrt ρ * |μ i| / (Real.sqrt ((1 - ρ) * v i) + τ) ≤
      (1 / 40 + 200 * ρ) * signalEnergy ρ τ v μ + 200000 * τ * ρ := by
  have hh := LongTails.Proofs.AdamHeavyTailedAlgebra.bias_absorption hτ
    (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (Real.sqrt_nonneg ρ) (abs_nonneg (μ i))
    (signalEnergy_nonneg hτ v μ) (by simpa only [sq_abs] using signal_coordinate_control hρ hρ1 hτ v μ hv i)
  simpa only [Real.sq_sqrt hρ] using hh

lemma geometric_window_coefficient {d : ℕ} {ρ τ p M : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hM : 0 ≤ M) (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (v μ : Point d) (hv : ∀ i, 0 ≤ v i) (j k : ℕ) (i : Fin d) :
    |μ i| * ((4 * (Real.sqrt (ρ * (1 - ρ) ^ (j - k)) /
      (Real.sqrt ((1 - ρ) ^ (j + 1) * v i) + τ)) ^ p) / Real.sqrt (ρ * (1 - ρ) ^ j)) * M ≤
      ((1 / 40 + 200 * ρ) * signalEnergy ρ τ v μ + 200000 * τ * ρ) /
        (25 * ((1 - ρ) ^ 2) ^ j) := by
  let b := 1 - ρ
  let c := Real.sqrt (b ^ j)
  have hb : 0 < b := sub_pos.mpr hρ1
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hc : 0 < c := Real.sqrt_pos.mpr (pow_pos hb _)
  have hc1 : c ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by simpa using (pow_le_one₀ hb.le hb1 : b ^ j ≤ 1)⟩
  have hu : Real.sqrt (ρ * b ^ (j - k)) ≤ Real.sqrt ρ := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_one₀ hb.le hb1 : b ^ (j - k) ≤ 1) hρ.le]
  have hD : Real.sqrt (b ^ (j + 1) * v i) = c * Real.sqrt (b * v i) := by
    rw [show b ^ (j + 1) * v i = b ^ j * (b * v i) by rw [pow_succ]; ring]
    exact Real.sqrt_mul (pow_nonneg hb.le _) _
  have hB : c * (Real.sqrt (b * v i) + τ) ≤ Real.sqrt (b ^ (j + 1) * v i) + τ := by
    rw [hD]
    nlinarith [mul_le_mul_of_nonneg_right hc1 hτ.le]
  have hai : Real.sqrt (ρ * b ^ j) = Real.sqrt ρ * c := Real.sqrt_mul hρ.le _
  have hc4 : c ^ 4 = (b ^ 2) ^ j := by
    calc
      c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = (b ^ j) ^ 2 := by rw [Real.sq_sqrt (pow_nonneg hb.le _)]
      _ = (b ^ 2) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm j 2]
  have hno : M * (Real.sqrt ρ / τ) ^ p ≤ (Real.sqrt ρ) ^ 2 := by simpa only [Real.sq_sqrt hρ.le] using hnoise
  have hh := LongTails.Proofs.AdamHeavyTailedAlgebra.window_coefficient_absorption
    (abs_nonneg (μ i)) (Real.sqrt_nonneg _) hu (Real.sqrt_pos.mpr hρ) hc hc1 hτ
    (le_add_of_nonneg_left (Real.sqrt_nonneg _)) hB hM hp hp2 hno
    (coordinate_bias_absorbed hρ.le hρ1.le hτ v μ hv i)
  rw [hc4] at hh
  change |μ i| * ((4 * (Real.sqrt (ρ * b ^ (j - k)) /
    (Real.sqrt (b ^ (j + 1) * v i) + τ)) ^ p) / Real.sqrt (ρ * b ^ j)) * M ≤ _
  rw [hai]
  exact hh

lemma geometric_oracle_window_bias {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {grad : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (hint : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    {p M : ℝ} (hm : ∀ x, Integrable (fun ω => ∑ k, |(g x ω - grad x) k| ^ p) P)
    (hmass : ∀ x, ∫ ω, ∑ k, |(g x ω - grad x) k| ^ p ∂P ≤ M)
    (q η : ℝ) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (s : Point d × Point d × Point d) (hv : ∀ i, 0 ≤ s.2.2 i) (j : ℕ) :
    let w := fun k => (1 - ρ) ^ (j + 1) * s.2.2 k
    let a := fun l : Fin (j + 1) => ρ * (1 - ρ) ^ (j - l.val)
    (∫ ξ, (∑ k, grad s.1 k * LongTails.Proofs.AdamHeavyTailedWindow.response (w k) a τ 0 (fun _ => grad s.1 k)) -
      (∑ k, grad s.1 k * LongTails.Proofs.AdamHeavyTailedWindow.response (w k) a τ 0
        (fun l => grad s.1 k + stateError g grad
          (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ l.val) (ξ l.val) k))
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ((j : ℝ) + 1) *
        (((1 / 40 + 200 * ρ) * signalEnergy ρ τ s.2.2 (grad s.1) + 200000 * τ * ρ) /
          (25 * ((1 - ρ) ^ 2) ^ j)) := by
  dsimp only
  have hb : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hH : 0 ≤ (1 / 40 + 200 * ρ) * signalEnergy ρ τ s.2.2 (grad s.1) + 200000 * τ * ρ := by
    have hs := signalEnergy_nonneg (ρ := ρ) hτ s.2.2 (grad s.1)
    positivity
  have hh := oracle_window_bias (B := ((1 / 40 + 200 * ρ) * signalEnergy ρ τ s.2.2 (grad s.1) + 200000 * τ * ρ) / (25 * ((1 - ρ) ^ 2) ^ j)) P hg hgrad hint hmean hm hmass q ρ η
    (fun k => (1 - ρ) ^ (j + 1) * s.2.2 k)
    (fun l : Fin (j + 1) => ρ * (1 - ρ) ^ (j - l.val)) 0
    (fun k => mul_nonneg (pow_nonneg hb.le _) (hv k))
    (fun l => mul_nonneg hρ.le (pow_nonneg hb.le _)) hτ
    (by simpa using mul_pos hρ (pow_pos hb j)) hp hp2
    (div_nonneg hH (by positivity)) hM s
    (fun l k => by simpa using (geometric_window_coefficient hρ hρ1 hτ hp hp2 hM hnoise
      s.2.2 (grad s.1) hv j l.val k))
  simpa only [Nat.cast_add, Nat.cast_one] using hh


lemma geometric_cancellation_parameters {ρ τ p M v μ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ) (hv : 0 ≤ v)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ) (j : ℕ) :
    let A := Real.sqrt ((1 - ρ) ^ (j + 1) * v) + τ
    let r := Real.sqrt (ρ * (1 - ρ) ^ j)
    M * (Real.sqrt ρ / τ) ^ p ≤ A ^ 2 * (Real.sqrt ρ / τ) ^ 2 ∧
    r ≤ A * (Real.sqrt ρ / τ) ∧
    Real.sqrt ((1 - ρ) ^ j) * (Real.sqrt ((1 - ρ) * v + ρ * μ ^ 2) + τ) ≤ A + r * |μ| := by
  dsimp only
  let b := 1 - ρ
  let c := Real.sqrt (b ^ j)
  let A := Real.sqrt (b ^ (j + 1) * v) + τ
  have hb : 0 < b := sub_pos.mpr hρ1
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using pow_le_one₀ hb.le hb1 (n := j)⟩
  have hA : τ ≤ A := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have he : τ ^ 2 * (Real.sqrt ρ / τ) ^ 2 = ρ := by
    rw [div_pow, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt (sq_pos_of_pos hτ)), Real.sq_sqrt hρ.le]
  have hs : M * (Real.sqrt ρ / τ) ^ p ≤ A ^ 2 * (Real.sqrt ρ / τ) ^ 2 := by
    calc
      _ ≤ ρ := hnoise
      _ = τ ^ 2 * (Real.sqrt ρ / τ) ^ 2 := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ.le hA 2) (sq_nonneg _)
  have hr : Real.sqrt (ρ * b ^ j) ≤ A * (Real.sqrt ρ / τ) := by
    calc
      _ ≤ Real.sqrt ρ := Real.sqrt_le_sqrt (mul_le_of_le_one_right hρ.le (pow_le_one₀ hb.le hb1))
      _ = τ * (Real.sqrt ρ / τ) := by field_simp
      _ ≤ A * (Real.sqrt ρ / τ) := mul_le_mul_of_nonneg_right hA (by positivity)
  have hD : Real.sqrt (b ^ (j + 1) * v) = c * Real.sqrt (b * v) := by
    rw [show b ^ (j + 1) * v = b ^ j * (b * v) by rw [pow_succ]; ring]
    exact Real.sqrt_mul (pow_nonneg hb.le _) _
  have hri : Real.sqrt (ρ * b ^ j) = c * Real.sqrt ρ := by
    rw [Real.sqrt_mul hρ.le]
    ring
  refine ⟨hs, hr, ?_⟩
  change c * (Real.sqrt (b * v + ρ * μ ^ 2) + τ) ≤ A + Real.sqrt (ρ * b ^ j) * |μ|
  have hu := LongTails.Proofs.AdamHeavyTailedNormalizer.signal_denominator_upper
    (mul_nonneg hb.le hv) hρ.le (τ := τ) (μ := μ)
  have hh := mul_le_mul_of_nonneg_left hu hc
  dsimp [A]
  rw [hD, hri]
  nlinarith [mul_le_mul_of_nonneg_right hc1 hτ.le]


noncomputable def frozenDenominator {d : ℕ} {Ω : Type*}
    (g : Point d → Ω → Point d) (grad : Point d → Point d) (q ρ η τ : ℝ)
    (s : Point d × Point d × Point d) (j : ℕ) (ξ : ℕ → Ω) (i : Fin d) : ℝ :=
  Real.sqrt ((1 - ρ) ^ (j + 1) * s.2.2 i + ∑ l : Fin (j + 1),
    ρ * (1 - ρ) ^ (j - l.val) * (grad s.1 i + stateError g grad
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ l.val) (ξ l.val) i) ^ 2) + τ

lemma measurable_frozenDenominator {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad) (q ρ η τ : ℝ)
    (s : Point d × Point d × Point d) (j : ℕ) (i : Fin d) :
    Measurable (fun ξ => frozenDenominator g grad q ρ η τ s j ξ i) := by
  have he (l : Fin (j + 1)) : Measurable (fun ξ => stateError g grad
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ l.val) (ξ l.val) i) :=
    (measurable_pi_apply i).comp ((measurable_stateError hg hgrad).comp
      ((LongTails.Proofs.AdamHeavyTailedProcess.measurable_stateAt
        (measurable_stateTransition hg q ρ η τ) s l.val).prodMk (measurable_pi_apply l.val)))
  unfold frozenDenominator
  fun_prop

lemma frozenDenominator_first_two {d : ℕ} {Ω : Type*}
    (g : Point d → Ω → Point d) (grad : Point d → Point d) (q η : ℝ)
    {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (s : Point d × Point d × Point d) (j : ℕ) (ξ : ℕ → Ω) (i : Fin d) :
    Real.sqrt ((1 - ρ) ^ (j + 2) * s.2.2 i +
      (ρ * (1 - ρ) ^ (j + 1)) * (grad s.1 i + stateError g grad s (ξ 0) i) ^ 2 +
      (ρ * (1 - ρ) ^ j) * (grad s.1 i + stateError g grad
        (stateTransition g q ρ η τ s (ξ 0)) (ξ 1) i) ^ 2) + τ ≤
      frozenDenominator g grad q ρ η τ s (j + 1) ξ i := by
  let a := fun l : Fin (j + 1 + 1) => ρ * (1 - ρ) ^ (j + 1 - l.val)
  let z := fun l : Fin (j + 1 + 1) => grad s.1 i + stateError g grad
    (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ l.val) (ξ l.val) i
  have hh := LongTails.Proofs.AdamHeavyTailedWindow.denominator_two_lower
    ((1 - ρ) ^ (j + 2) * s.2.2 i) τ a z
    (fun l => mul_nonneg hρ (pow_nonneg (sub_nonneg.mpr hρ1) _)) (0 : Fin (j + 1 + 1))
    (⟨1, by omega⟩ : Fin (j + 1 + 1)) (by simp)
  simpa [a, z, frozenDenominator, LongTails.Proofs.AdamHeavyTailedProcess.stateAt_succ,
    LongTails.Proofs.AdamHeavyTailedProcess.stateAt_zero, Nat.add_assoc] using hh


lemma frozenDenominator_ratio_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {grad : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    {p M : ℝ} (hm : ∀ x, Integrable (fun ω => ∑ k, |(g x ω - grad x) k| ^ p) P)
    (hmass : ∀ x, ∫ ω, ∑ k, |(g x ω - grad x) k| ^ p ∂P ≤ M)
    (q η : ℝ) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (s : Point d × Point d × Point d) (hv : ∀ i, 0 ≤ s.2.2 i) (j : ℕ) (i : Fin d) :
    (∫ ξ, (grad s.1 i) ^ 2 / (frozenDenominator g grad q ρ η τ s (j + 1) ξ i) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      (3 / (τ * Real.sqrt ((1 - ρ) ^ (j + 1)))) *
        ((grad s.1 i) ^ 2 / (Real.sqrt ((1 - ρ) * s.2.2 i + ρ * (grad s.1 i) ^ 2) + τ)) +
      16 * (∫ ω, |stateError g grad s ω i| ^ p ∂P) * (Real.sqrt ρ / τ) ^ p := by
  let X := fun ω => stateError g grad s ω i
  let Y := fun ω z => stateError g grad (stateTransition g q ρ η τ s ω) z i
  have hX : Measurable X := (measurable_pi_apply i).comp
    ((measurable_stateError hg hgrad).comp (measurable_const.prodMk measurable_id))
  have hY : Measurable (Function.uncurry Y) := (measurable_pi_apply i).comp
    ((measurable_stateError hg hgrad).comp
      (((measurable_stateTransition hg q ρ η τ).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd))
  have hi (s' : Point d × Point d × Point d) : Integrable (fun ω => |stateError g grad s' ω i| ^ p) P :=
    integrable_error_power (hg.comp measurable_prodMk_left) (grad s'.1) p (hm s'.1) i
  have hb (s' : Point d × Point d × Point d) : (∫ ω, |stateError g grad s' ω i| ^ p ∂P) ≤ M := by
    apply (integral_mono (hi s') (hm s'.1) (fun ω => ?_)).trans (hmass s'.1)
    exact Finset.single_le_sum (fun k _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
  have hb0 : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hb1 : 1 - ρ ≤ 1 := by linarith
  have hweights : ρ * (1 - ρ) ^ (j + 1) ≤ ρ * (1 - ρ) ^ j := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hb1 (mul_nonneg hρ.le (pow_nonneg hb0.le j))]
  obtain ⟨hscale, hrr, hsignal⟩ := geometric_cancellation_parameters (μ := grad s.1 i)
    hρ hρ1 hτ (hv i) hnoise (j + 1)
  have hh := LongTails.Proofs.AdamHeavyTailedProcess.two_observation_stream_integral P
    hX hY (measurable_frozenDenominator hg hgrad q ρ η τ s (j + 1) i)
    (mul_nonneg (pow_nonneg hb0.le _) (hv i))
    (mul_nonneg hρ.le (pow_nonneg hb0.le _)) hweights hτ (by positivity)
    hp hp2 hM hscale hrr
    (fun ξ => frozenDenominator_first_two g grad q η hρ.le hρ1.le s j ξ i)
    (hi s) (fun ω => hi (stateTransition g q ρ η τ s ω))
    (fun ω => hb (stateTransition g q ρ η τ s ω))
  apply hh.trans
  apply add_le_add _ le_rfl
  have hc : 0 < Real.sqrt ((1 - ρ) ^ (j + 1)) := Real.sqrt_pos.mpr (pow_pos hb0 _)
  have hD : 0 < Real.sqrt ((1 - ρ) * s.2.2 i + ρ * (grad s.1 i) ^ 2) + τ := by positivity
  calc
    _ ≤ (3 * (grad s.1 i) ^ 2) /
        (τ * (Real.sqrt ((1 - ρ) ^ (j + 1)) * (Real.sqrt ((1 - ρ) * s.2.2 i + ρ * (grad s.1 i) ^ 2) + τ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hsignal hτ.le)
    _ = _ := by field_simp


lemma frozenDenominator_energy_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {grad : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    {p M : ℝ} (hm : ∀ x, Integrable (fun ω => ∑ k, |(g x ω - grad x) k| ^ p) P)
    (hmass : ∀ x, ∫ ω, ∑ k, |(g x ω - grad x) k| ^ p ∂P ≤ M)
    (q η : ℝ) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (s : Point d × Point d × Point d) (hv : ∀ i, 0 ≤ s.2.2 i) (j : ℕ) :
    (∫ ξ, ∑ i, (grad s.1 i) ^ 2 / (frozenDenominator g grad q ρ η τ s (j + 1) ξ i) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      (3 / (τ * Real.sqrt ((1 - ρ) ^ (j + 1)))) * signalEnergy ρ τ s.2.2 (grad s.1) + 16 * ρ := by
  have hi (i : Fin d) := LongTails.Proofs.AdamHeavyTailedCancellation.integrable_ratio_square
    (P := Measure.infinitePi (fun _ : ℕ => P)) (μ := grad s.1 i)
    (measurable_frozenDenominator hg hgrad q ρ η τ s (j + 1) i) hτ
    (fun ξ => le_add_of_nonneg_left (Real.sqrt_nonneg _))
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    frozenDenominator_ratio_integral P hg hgrad hm hmass q η hρ hρ1 hτ hp hp2 hM hnoise s hv j i)
  apply hh.trans
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change _ * signalEnergy ρ τ s.2.2 (grad s.1) + _ ≤ _
  apply add_le_add le_rfl
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hs : (∑ i, ∫ ω, |stateError g grad s ω i| ^ p ∂P) ≤ M :=
    (sum_integral_error_power (hg.comp measurable_prodMk_left) (grad s.1) p (hm s.1)).trans_le (hmass s.1)
  calc
    _ ≤ 16 * M * (Real.sqrt ρ / τ) ^ p := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by norm_num)) (Real.rpow_nonneg (by positivity) _)
    _ ≤ 16 * ρ := by nlinarith


lemma weighted_gradient_window_variation {d : ℕ} {Ω : Type*} {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q η τ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) :
    (∑ l : Fin (j + 1), ρ * (1 - ρ) ^ (j - l.val) *
      ‖grad (trajectory g q ρ η τ x0 ξ (s + l.val)).1 - grad (trajectory g q ρ η τ x0 ξ s).1‖ ^ 2) ≤
      ρ * (j : ℝ) * (L * |η| * ∑ k ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖) ^ 2 := by
  have hvar (l : Fin (j + 1)) :
      ‖grad (trajectory g q ρ η τ x0 ξ (s + l.val)).1 - grad (trajectory g q ρ η τ x0 ξ s).1‖ ≤
        L * |η| * ∑ k ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖ := by
    apply (gradient_window_variation hL hlip g q ρ η τ x0 ξ s l.val).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL (abs_nonneg η))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => norm_nonneg _)
  have hb : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1
  have hb1 : 1 - ρ ≤ 1 := by linarith
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.add_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]
  calc
    _ ≤ ∑ _ : Fin j, ρ * (L * |η| * ∑ k ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul
      · exact mul_le_of_le_one_right hρ (pow_le_one₀ hb hb1)
      · exact pow_le_pow_left₀ (norm_nonneg _) (hvar l.succ) 2
      · positivity
      · exact hρ
    _ = _ := by simp; ring


lemma trajectory_denominator_transport {d : ℕ} {Ω : Type*} {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q η τ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) :
    (∑ i, (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ -
      frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2) ≤
      ρ * (j : ℝ) * (L * |η| * ∑ k ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖) ^ 2 := by
  let w := fun i => (1 - ρ) ^ (j + 1) * (trajectory g q ρ η τ x0 ξ s).2.2 i
  let a := fun l : Fin (j + 1) => ρ * (1 - ρ) ^ (j - l.val)
  let G := fun l : Fin (j + 1) => g (trajectory g q ρ η τ x0 ξ (s + l.val)).1 (ξ (s + l.val))
  let H := fun l : Fin (j + 1) => grad (trajectory g q ρ η τ x0 ξ s).1 +
    (G l - grad (trajectory g q ρ η τ x0 ξ (s + l.val)).1)
  have hw : ∀ i, 0 ≤ w i := fun i => mul_nonneg (pow_nonneg (sub_nonneg.mpr hρ1) _)
    (trajectory_secondMoment_nonneg g q η τ hρ hρ1 x0 ξ s i)
  have ha : ∀ l, 0 ≤ a l := fun l => mul_nonneg hρ (pow_nonneg (sub_nonneg.mpr hρ1) _)
  have he (i : Fin d) : (trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i = w i + ∑ l, a l * (G l i) ^ 2 := by
    rw [Nat.add_assoc, secondMoment_window]
    dsimp [w, a, G]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun k => (1 - ρ) ^ (j - k) *
      (g (trajectory g q ρ η τ x0 ξ (s + k)).1 (ξ (s + k)) i) ^ 2), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hf (i : Fin d) : frozenDenominator g grad q ρ η τ
      (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i =
      Real.sqrt (w i + ∑ l, a l * (H l i) ^ 2) + τ := by
    unfold frozenDenominator
    simp only [stateAt_after]
    rfl
  have hh := LongTails.Proofs.AdamHeavyTailedWindow.denominator_vector_difference_sq w hw a ha G H
  have hd (l : Fin (j + 1)) : G l - H l =
      grad (trajectory g q ρ η τ x0 ξ (s + l.val)).1 - grad (trajectory g q ρ η τ x0 ξ s).1 := by
    dsimp [H]
    module
  simp_rw [hd] at hh
  have heq : (∑ i, (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ -
      frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2) =
      ∑ i, (Real.sqrt (w i + ∑ l, a l * (G l i) ^ 2) - Real.sqrt (w i + ∑ l, a l * (H l i) ^ 2)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [he, hf]
    ring
  rw [heq]
  exact hh.trans (weighted_gradient_window_variation hL hlip g q η τ hρ hρ1 x0 ξ s j)


lemma mean_window_nonneg {d N : ℕ} (w : Fin d → ℝ) (a : Fin N → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (μ : Point d) (i : Fin N) :
    0 ≤ ∑ k, μ k * LongTails.Proofs.AdamHeavyTailedWindow.response (w k) a τ i (fun _ => μ k) := by
  apply Finset.sum_nonneg
  intro k _
  unfold LongTails.Proofs.AdamHeavyTailedWindow.response
  rw [← mul_div_assoc]
  exact div_nonneg (mul_self_nonneg _) (by positivity)

lemma mean_zero_window_signal {d : ℕ} (ρ τ : ℝ) (v μ : Point d) :
    (∑ k, μ k * LongTails.Proofs.AdamHeavyTailedWindow.response ((1 - ρ) * v k)
      (fun _ : Fin 1 => ρ) τ 0 (fun _ => μ k)) = signalEnergy ρ τ v μ := by
  unfold signalEnergy
  apply Finset.sum_congr rfl
  intro k _
  simp only [LongTails.Proofs.AdamHeavyTailedWindow.response, Fin.sum_univ_one]
  ring


lemma integrable_trajectory_gradient_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (t : ℕ) :
    Integrable (fun ξ => ‖grad (trajectory g q ρ η τ x0 ξ t).1‖ ^ 2) P := by
  apply Integrable.of_bound ((((measurable_gradient_of_lipschitz hL hlip).comp
    (measurable_trajectory hg q ρ η τ x0 t).fst).norm.pow_const 2).aestronglyMeasurable)
    ((‖grad x0‖ + L * ((t : ℝ) * (|η| * (((d : ℝ) + 1) *
      ((1 - q) * (1 / Real.sqrt ρ) / (1 - q / Real.sqrt (1 - ρ))))))) ^ 2)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (trajectory_gradient_bound hL hlip g hq hq1 hρ hρ1 hτ hstable x0 ξ t) 2

lemma measurable_trajectory_signalEnergy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (t : ℕ) :
    Measurable (fun ξ => signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ t).2.2
      (grad (trajectory g q ρ η τ x0 ξ t).1)) := by
  apply Finset.measurable_sum
  intro i _
  have hμ := (measurable_coordinate i).comp (hgrad.comp (measurable_trajectory hg q ρ η τ x0 t).fst)
  have hv := (measurable_coordinate i).comp (measurable_trajectory hg q ρ η τ x0 t).snd.snd
  exact (hμ.pow_const 2).div ((Real.continuous_sqrt.measurable.comp
    ((measurable_const.mul hv).add (measurable_const.mul (hμ.pow_const 2)))).add measurable_const)

lemma integrable_trajectory_signalEnergy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (t : ℕ) :
    Integrable (fun ξ => signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ t).2.2
      (grad (trajectory g q ρ η τ x0 ξ t).1)) P := by
  apply ((integrable_trajectory_gradient_square (P := P) (η := η) hg hL hlip
    hq hq1 hρ hρ1 hτ hstable x0 t).div_const τ).mono'
    (measurable_trajectory_signalEnergy hg (measurable_gradient_of_lipschitz hL hlip) q ρ η τ x0 t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (signalEnergy_nonneg (ρ := ρ) hτ _ _)]
    exact signalEnergy_le_norm_sq hτ _ _

lemma integrable_instantDirection_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (q η : ℝ) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ) (x0 : Point d) (t : ℕ) :
    Integrable (fun ξ => ‖instantDirection g q ρ η τ x0 ξ t‖ ^ 2) P := by
  have hx := (measurable_trajectory hg q ρ η τ x0 t).fst
  have hv := (measurable_trajectory hg q ρ η τ x0 (t + 1)).snd.snd
  have hm : Measurable (fun ξ => instantDirection g q ρ η τ x0 ξ t) :=
    (measurable_direction τ).comp ((hg.comp (hx.prodMk (measurable_pi_apply t))).prodMk hv)
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable
    ((d : ℝ) * (1 / Real.sqrt ρ) ^ 2)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (sq_nonneg _), PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ : Fin d, (1 / Real.sqrt ρ) ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (instantDirection_coordinate_bound g hρ hρ1 hτ x0 ξ t i) 2
      _ = _ := by simp

lemma integrable_current_direction_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {g : Ω → Point d} (hg : Measurable g)
    (v : Point d) {ρ τ : ℝ} (hv : ∀ i, 0 ≤ v i) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ) :
    Integrable (fun ω => ‖direction τ (g ω) (secondMomentStep ρ v (g ω))‖ ^ 2) P := by
  have hm : Measurable (fun ω => direction τ (g ω) (secondMomentStep ρ v (g ω))) :=
    (measurable_direction τ).comp
      (hg.prodMk ((measurable_secondMomentStep ρ).comp (measurable_const.prodMk hg)))
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable
    ((d : ℝ) * (1 / Real.sqrt ρ) ^ 2)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _), PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ : Fin d, (1 / Real.sqrt ρ) ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa only [Real.norm_eq_abs, direction, secondMomentStep] using pow_le_pow_left₀ (abs_nonneg _)
          (LongTails.Proofs.AdamHeavyTailedNormalizer.normalized_current_bound
            (hv i) hρ hρ1 hτ (g ω i)) 2
      _ = _ := by simp

lemma trajectory_instant_energy_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) P)
    {grad : Point d → Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (x0 : Point d) (ω0 : Ω) (t : ℕ) :
    (∫ ξ, ‖instantDirection g q ρ η τ x0 ξ t‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      (2 / τ) * (∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ t).2.2
        (grad (trajectory g q ρ η τ x0 ξ t).1) ∂Measure.infinitePi (fun _ : ℕ => P)) +
          ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M := by
  let F := fun s : Point d × Point d × Point d => fun ω =>
    ‖direction τ (g s.1 ω) (secondMomentStep ρ s.2.2 (g s.1 ω))‖ ^ 2
  let B := fun s : Point d × Point d × Point d =>
    (2 / τ) * signalEnergy ρ τ s.2.2 (grad s.1) + ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M
  have hiS := integrable_trajectory_signalEnergy
    (P := Measure.infinitePi (fun _ : ℕ => P)) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 t
  have hiF : Integrable (fun ξ => F
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ t) (ξ t))
      (Measure.infinitePi fun _ : ℕ => P) := by
    simpa only [stateAt_initial, F, instantDirection, trajectory] using
      integrable_instantDirection_square (P := Measure.infinitePi (fun _ : ℕ => P)) hg q η hρ hρ1.le hτ x0 t
  have hiB : Integrable (fun ξ => B
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ t))
      (Measure.infinitePi fun _ : ℕ => P) := by
    simpa only [stateAt_initial, B, Pi.add_def] using (hiS.const_mul (2 / τ)).add (integrable_const (((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M))
  have hv (b : Fin t → Ω) (i : Fin d) : 0 ≤
      (LongTails.Proofs.AdamHeavyTailedProcess.prefixState (stateTransition g q ρ η τ) (x0, 0, 0) ω0 t b).2.2 i := by
    unfold LongTails.Proofs.AdamHeavyTailedProcess.prefixState
    rw [stateAt_initial]
    exact trajectory_secondMoment_nonneg g q η τ hρ.le hρ1.le x0 _ t i
  have hslice (x : Point d) : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
  have hh := LongTails.Proofs.AdamHeavyTailedProcess.stateAt_sample_integral_le P
    (stateTransition g q ρ η τ) (x0, 0, 0) ω0 t F B hiF hiB
    (fun b => integrable_current_direction_square (hslice _) _ (hv b) hρ hρ1.le hτ)
    (fun b => current_direction_energy (hslice _) (hgi _) _ _ (hv b) hρ hρ1.le hτ hp hp2 (hm _) (hmass _))
  simp only [stateAt_initial, F, B] at hh
  rw [integral_add (hiS.const_mul _) (integrable_const _), integral_const_mul] at hh
  simpa [instantDirection, trajectory] using hh

lemma trajectory_numerator_transport {d : ℕ} {Ω : Type*}
    {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q η : ℝ) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) :
    |(∑ i, grad (trajectory g q ρ η τ x0 ξ (s + j)).1 i *
        g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
          (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ)) -
      ∑ i, grad (trajectory g q ρ η τ x0 ξ s).1 i *
        g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
          (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ)| ≤
    (1 / Real.sqrt ((1 - ρ) ^ j)) * (L * |η| * ∑ r ∈ Finset.range j, ‖velocity g q ρ η τ x0 ξ (s + r + 1)‖) *
      ‖instantDirection g q ρ η τ x0 ξ s‖ := by
  let u := grad (trajectory g q ρ η τ x0 ξ (s + j)).1 - grad (trajectory g q ρ η τ x0 ξ s).1
  let z := g (trajectory g q ρ η τ x0 ξ s).1 (ξ s)
  let E := fun i => Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ
  have hh := LongTails.Proofs.AdamHeavyTailedAlgebra.coordinate_inner_bound
    (fun i => u i) (fun i => z i) E (fun i => instantDirection g q ρ η τ x0 ξ s i)
    (by positivity : 0 ≤ 1 / Real.sqrt ((1 - ρ) ^ j))
    (fun i => by dsimp [E]; positivity)
    (fun i => trajectory_past_response_bound g q η hρ hρ1 hτ x0 ξ s j i)
  have hnorm (v : Point d) : Real.sqrt (∑ i, (v i) ^ 2) = ‖v‖ := by
    have he : (∑ i, (v i) ^ 2) = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm u, hnorm (instantDirection g q ρ η τ x0 ξ s)] at hh
  have he : (∑ i, grad (trajectory g q ρ η τ x0 ξ (s + j)).1 i * z i / E i) -
      ∑ i, grad (trajectory g q ρ η τ x0 ξ s).1 i * z i / E i = ∑ i, u i * z i / E i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [u, PiLp.sub_apply]
    ring
  change |(∑ i, grad (trajectory g q ρ η τ x0 ξ (s + j)).1 i * z i / E i) -
      ∑ i, grad (trajectory g q ρ η τ x0 ξ s).1 i * z i / E i| ≤ _
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (gradient_window_variation hL hlip g q ρ η τ x0 ξ s j) (by positivity))
    (norm_nonneg _))

lemma measurable_trajectory_frozenDenominator {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (s j : ℕ) (i : Fin d) :
    Measurable (fun ξ => frozenDenominator g grad q ρ η τ
      (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) := by
  have hv := (measurable_coordinate i).comp (measurable_trajectory hg q ρ η τ x0 s).snd.snd
  have hμ := (measurable_coordinate i).comp (hgrad.comp (measurable_trajectory hg q ρ η τ x0 s).fst)
  have he (l : Fin (j + 1)) : Measurable (fun ξ => stateError g grad
      (trajectory g q ρ η τ x0 ξ (s + l.val)) (ξ (s + l.val)) i) :=
    (measurable_pi_apply i).comp ((measurable_stateError hg hgrad).comp
      ((measurable_trajectory hg q ρ η τ x0 (s + l.val)).prodMk (measurable_pi_apply (s + l.val))))
  unfold frozenDenominator
  simp_rw [stateAt_after]
  exact (Real.continuous_sqrt.measurable.comp ((measurable_const.mul hv).add
    (Finset.measurable_sum _ (fun l _ => measurable_const.mul ((hμ.add (he l)).pow_const 2))))).add measurable_const

lemma integrable_trajectory_frozenEnergy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (s j : ℕ) :
    Integrable (fun ξ => ∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
      (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2) P := by
  have hgrad := measurable_gradient_of_lipschitz hL hlip
  have hmeas : Measurable (fun ξ => ∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
      (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2) := by
    apply Finset.measurable_sum
    intro i _
    exact (((measurable_coordinate i).comp (hgrad.comp (measurable_trajectory hg q ρ η τ x0 s).fst)).pow_const 2).div
      ((measurable_trajectory_frozenDenominator hg hgrad q ρ η τ x0 s j i).pow_const 2)
  apply ((integrable_trajectory_gradient_square (P := P) (η := η) hg hL hlip
    hq hq1 hρ hρ1 hτ hstable x0 s).div_const (τ ^ 2)).mono' hmeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)),
      PiLp.norm_sq_eq_of_L2, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs, sq_abs]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hτ)
    apply pow_le_pow_left₀ hτ.le
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)

lemma trajectory_frozenEnergy_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : Point d) (ω0 : Ω) (s j : ℕ) :
    (∫ ξ, ∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
      (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) (j + 1) (fun k => ξ (s + k)) i) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
    (3 / (τ * Real.sqrt ((1 - ρ) ^ (j + 1)))) *
      (∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
        (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Measure.infinitePi (fun _ : ℕ => P)) + 16 * ρ := by
  let F := fun z : Point d × Point d × Point d => fun ξ =>
    ∑ i, (grad z.1 i) ^ 2 / (frozenDenominator g grad q ρ η τ z (j + 1) ξ i) ^ 2
  let C := 3 / (τ * Real.sqrt ((1 - ρ) ^ (j + 1)))
  let B := fun z : Point d × Point d × Point d => C * signalEnergy ρ τ z.2.2 (grad z.1) + 16 * ρ
  have hiS := integrable_trajectory_signalEnergy (P := Measure.infinitePi (fun _ : ℕ => P))
    (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s
  have hiF : Integrable (fun ξ => F
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ s)
      (fun k => ξ (s + k))) (Measure.infinitePi (fun _ : ℕ => P)) := by
    simpa only [stateAt_initial, F] using integrable_trajectory_frozenEnergy
      (P := Measure.infinitePi (fun _ : ℕ => P)) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s (j + 1)
  have hiB : Integrable (fun ξ => B
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ s))
      (Measure.infinitePi (fun _ : ℕ => P)) := by
    simpa only [stateAt_initial, B, Pi.add_def] using (hiS.const_mul C).add (integrable_const (16 * ρ))
  have hv (b : Fin s → Ω) (i : Fin d) : 0 ≤
      (LongTails.Proofs.AdamHeavyTailedProcess.prefixState (stateTransition g q ρ η τ) (x0, 0, 0) ω0 s b).2.2 i := by
    unfold LongTails.Proofs.AdamHeavyTailedProcess.prefixState
    rw [stateAt_initial]
    exact trajectory_secondMoment_nonneg g q η τ hρ.le hρ1.le x0 _ s i
  have hh := LongTails.Proofs.AdamHeavyTailedProcess.stateAt_tail_integral_le P
    (stateTransition g q ρ η τ) (x0, 0, 0) ω0 s F B hiF hiB
    (fun b => frozenDenominator_energy_integral P hg (measurable_gradient_of_lipschitz hL hlip)
      hm hmass q η hρ hρ1 hτ hp hp2 hM hnoise _ (hv b) j)
  simp only [stateAt_initial, F, B] at hh
  rw [integral_add (hiS.const_mul _) (integrable_const _), integral_const_mul] at hh
  simpa only [C, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma velocity_pairing_expansion {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (t : ℕ) (μ : Point d) :
    ⟪μ, velocity g q ρ η τ x0 ξ (t + 1)⟫ =
      (1 - q) * ∑ s ∈ Finset.range (t + 1), q ^ (t - s) *
        ∑ i, μ i * g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
          (Real.sqrt ((trajectory g q ρ η τ x0 ξ (t + 1)).2.2 i) + τ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, velocity, direction]
  simp_rw [momentum_expansion, Nat.add_sub_cancel]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma trajectory_momentum_pairing_sum {d : ℕ} {Ω : Type*}
    (g : Point d → Ω → Point d) (grad : Point d → Point d)
    (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) :
    (∑ t ∈ Finset.range T, ⟪grad (trajectory g q ρ η τ x0 ξ t).1,
      velocity g q ρ η τ x0 ξ (t + 1)⟫) =
      (1 - q) * ∑ j ∈ Finset.range T, q ^ j * ∑ s ∈ Finset.range (T - j),
        ∑ i, grad (trajectory g q ρ η τ x0 ξ (s + j)).1 i *
          g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
            (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ) := by
  simp_rw [velocity_pairing_expansion]
  rw [← Finset.mul_sum]
  congr 1
  exact LongTails.Proofs.AdamHeavyTailedAlgebra.triangle_convolution_exchange q
    (fun s t => ∑ i, grad (trajectory g q ρ η τ x0 ξ t).1 i *
      g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
        (Real.sqrt ((trajectory g q ρ η τ x0 ξ (t + 1)).2.2 i) + τ)) T

noncomputable def meanPairing {d : ℕ} (ρ τ : ℝ) (s : Point d × Point d × Point d)
    (grad : Point d → Point d) (j : ℕ) : ℝ :=
  ∑ i, grad s.1 i * LongTails.Proofs.AdamHeavyTailedWindow.response ((1 - ρ) ^ (j + 1) * s.2.2 i)
    (fun l : Fin (j + 1) => ρ * (1 - ρ) ^ (j - l.val)) τ 0 (fun _ => grad s.1 i)

noncomputable def frozenPairing {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (grad : Point d → Point d) (q ρ η τ : ℝ) (s : Point d × Point d × Point d)
    (j : ℕ) (ξ : ℕ → Ω) : ℝ :=
  ∑ i, grad s.1 i * g s.1 (ξ 0) i / frozenDenominator g grad q ρ η τ s j ξ i

lemma frozenPairing_window {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (grad : Point d → Point d) (q ρ η τ : ℝ) (s : Point d × Point d × Point d)
    (j : ℕ) (ξ : ℕ → Ω) :
    frozenPairing g grad q ρ η τ s j ξ =
      ∑ i, grad s.1 i * LongTails.Proofs.AdamHeavyTailedWindow.response ((1 - ρ) ^ (j + 1) * s.2.2 i)
        (fun l : Fin (j + 1) => ρ * (1 - ρ) ^ (j - l.val)) τ 0
        (fun l => grad s.1 i + stateError g grad
          (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ l.val) (ξ l.val) i) := by
  unfold frozenPairing
  apply Finset.sum_congr rfl
  intro i _
  simp only [LongTails.Proofs.AdamHeavyTailedWindow.response, Fin.val_zero,
    LongTails.Proofs.AdamHeavyTailedProcess.stateAt_zero]
  have he : grad s.1 i + stateError g grad s (ξ 0) i = g s.1 (ξ 0) i := by
    simp [stateError]
  rw [he]
  unfold frozenDenominator
  ring

lemma meanPairing_nonneg {d : ℕ} {ρ τ : ℝ} (hτ : 0 < τ)
    (s : Point d × Point d × Point d) (grad : Point d → Point d) (j : ℕ) :
    0 ≤ meanPairing ρ τ s grad j :=
  mean_window_nonneg _ _ hτ _ _

lemma meanPairing_zero {d : ℕ} (ρ τ : ℝ) (s : Point d × Point d × Point d)
    (grad : Point d → Point d) : meanPairing ρ τ s grad 0 = signalEnergy ρ τ s.2.2 (grad s.1) := by
  simpa only [meanPairing, zero_add, pow_one, Fin.val_zero, Nat.sub_zero, Nat.zero_sub, pow_zero, mul_one]
    using mean_zero_window_signal ρ τ s.2.2 (grad s.1)

lemma meanPairing_le {d : ℕ} {ρ τ : ℝ} (hτ : 0 < τ)
    (s : Point d × Point d × Point d) (grad : Point d → Point d) (j : ℕ) :
    meanPairing ρ τ s grad j ≤ ‖grad s.1‖ ^ 2 / τ := by
  rw [meanPairing, PiLp.norm_sq_eq_of_L2, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  simp only [LongTails.Proofs.AdamHeavyTailedWindow.response, Real.norm_eq_abs, sq_abs]
  rw [← mul_div_assoc, ← pow_two]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hτ
    (le_add_of_nonneg_left (Real.sqrt_nonneg _))

lemma frozenPairing_abs_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (grad : Point d → Point d) (q η : ℝ) {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (s : Point d × Point d × Point d) (hv : ∀ i, 0 ≤ s.2.2 i) (j : ℕ) (ξ : ℕ → Ω) :
    |frozenPairing g grad q ρ η τ s j ξ| ≤
      (d : ℝ) * ‖grad s.1‖ * (1 / Real.sqrt (ρ * (1 - ρ) ^ j)) := by
  rw [frozenPairing_window]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ : Fin d, ‖grad s.1‖ * (1 / Real.sqrt (ρ * (1 - ρ) ^ j)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hr := LongTails.Proofs.AdamHeavyTailedWindow.response_bound
        (mul_nonneg (pow_nonneg (sub_pos.mpr hρ1).le (j + 1)) (hv i)) hτ
        (fun l : Fin (j + 1) => ρ * (1 - ρ) ^ (j - l.val))
        (fun l => grad s.1 i + stateError g grad
          (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) s ξ l.val) (ξ l.val) i)
        (fun l => mul_nonneg hρ.le (pow_nonneg (sub_pos.mpr hρ1).le _)) 0
        (by simpa using mul_pos hρ (pow_pos (sub_pos.mpr hρ1) j))
      simp only [Fin.val_zero, Nat.sub_zero] at hr
      have hμ : |grad s.1 i| ≤ ‖grad s.1‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (grad s.1) i
      exact mul_le_mul hμ hr (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma measurable_trajectory_meanPairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (s j : ℕ) :
    Measurable (fun ξ => meanPairing ρ τ (trajectory g q ρ η τ x0 ξ s) grad j) := by
  unfold meanPairing LongTails.Proofs.AdamHeavyTailedWindow.response
  apply Finset.measurable_sum
  intro i _
  have hv := (measurable_coordinate i).comp (measurable_trajectory hg q ρ η τ x0 s).snd.snd
  have hμ := (measurable_coordinate i).comp (hgrad.comp (measurable_trajectory hg q ρ η τ x0 s).fst)
  exact hμ.mul (hμ.div ((Real.continuous_sqrt.measurable.comp ((measurable_const.mul hv).add
    (Finset.measurable_sum _ (fun _ _ => measurable_const.mul (hμ.pow_const 2))))).add measurable_const))

lemma measurable_trajectory_frozenPairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (s j : ℕ) :
    Measurable (fun ξ => frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))) := by
  unfold frozenPairing
  simp only [Nat.add_zero]
  apply Finset.measurable_sum
  intro i _
  have hx := (measurable_trajectory hg q ρ η τ x0 s).fst
  exact (((measurable_coordinate i).comp (hgrad.comp hx)).mul
    ((measurable_coordinate i).comp (hg.comp (hx.prodMk (measurable_pi_apply s))))).div
      (measurable_trajectory_frozenDenominator hg hgrad q ρ η τ x0 s j i)

lemma integrable_trajectory_meanPairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (s j : ℕ) :
    Integrable (fun ξ => meanPairing ρ τ (trajectory g q ρ η τ x0 ξ s) grad j) P := by
  apply ((integrable_trajectory_gradient_square (P := P) (η := η) hg hL hlip
    hq hq1 hρ hρ1 hτ hstable x0 s).div_const τ).mono'
    (measurable_trajectory_meanPairing hg (measurable_gradient_of_lipschitz hL hlip) q ρ η τ x0 s j).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_of_nonneg (meanPairing_nonneg hτ _ _ _)]
    exact meanPairing_le hτ _ _ _

lemma integrable_trajectory_frozenPairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (s j : ℕ) :
    Integrable (fun ξ => frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))) P := by
  apply (((integrable_trajectory_gradient_norm (P := P) (η := η) hg hL hlip
    hq hq1 hρ hρ1 hτ hstable x0 s).const_mul (d : ℝ)).mul_const
    (1 / Real.sqrt (ρ * (1 - ρ) ^ j))).mono'
    (measurable_trajectory_frozenPairing hg (measurable_gradient_of_lipschitz hL hlip) q ρ η τ x0 s j).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs]
    exact frozenPairing_abs_bound g grad q η hρ hρ1 hτ _
      (fun i => trajectory_secondMoment_nonneg g q η τ hρ.le hρ1.le x0 ξ s i) j _

lemma trajectory_pairing_bias_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L p M : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hm : ∀ x, Integrable (fun ω => ∑ i, |(g x ω - grad x) i| ^ p) P)
    (hmass : ∀ x, (∫ ω, ∑ i, |(g x ω - grad x) i| ^ p ∂P) ≤ M)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hnoise : M * (Real.sqrt ρ / τ) ^ p ≤ ρ)
    (x0 : Point d) (ω0 : Ω) (s j : ℕ) :
    (∫ ξ, meanPairing ρ τ (trajectory g q ρ η τ x0 ξ s) grad j ∂Measure.infinitePi (fun _ : ℕ => P)) -
      (∫ ξ, frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
    (((j : ℝ) + 1) / (25 * ((1 - ρ) ^ 2) ^ j)) *
      ((1 / 40 + 200 * ρ) * (∫ ξ, signalEnergy ρ τ (trajectory g q ρ η τ x0 ξ s).2.2
        (grad (trajectory g q ρ η τ x0 ξ s).1) ∂Measure.infinitePi (fun _ : ℕ => P)) + 200000 * τ * ρ) := by
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let C := ((j : ℝ) + 1) / (25 * ((1 - ρ) ^ 2) ^ j)
  let F := fun z : Point d × Point d × Point d => fun ξ => meanPairing ρ τ z grad j - frozenPairing g grad q ρ η τ z j ξ
  let B := fun z : Point d × Point d × Point d => C * ((1 / 40 + 200 * ρ) * signalEnergy ρ τ z.2.2 (grad z.1) + 200000 * τ * ρ)
  have hiS := integrable_trajectory_signalEnergy (P := Q) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s
  have hiM := integrable_trajectory_meanPairing (P := Q) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j
  have hiR := integrable_trajectory_frozenPairing (P := Q) (η := η) hg hL hlip hq hq1 hρ hρ1 hτ hstable x0 s j
  have hiF : Integrable (fun ξ => F
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ s)
      (fun k => ξ (s + k))) Q := by
    simpa only [stateAt_initial, F, Pi.sub_def] using hiM.sub hiR
  have hiH : Integrable (fun ξ => (1 / 40 + 200 * ρ) * signalEnergy ρ τ
      (trajectory g q ρ η τ x0 ξ s).2.2 (grad (trajectory g q ρ η τ x0 ξ s).1) + 200000 * τ * ρ) Q := by
    simpa only [Pi.add_def] using (hiS.const_mul (1 / 40 + 200 * ρ)).add (integrable_const (200000 * τ * ρ))
  have hiB : Integrable (fun ξ => B
      (LongTails.Proofs.AdamHeavyTailedProcess.stateAt (stateTransition g q ρ η τ) (x0, 0, 0) ξ s)) Q := by
    simpa only [stateAt_initial, B] using hiH.const_mul C
  have hv (b : Fin s → Ω) (i : Fin d) : 0 ≤
      (LongTails.Proofs.AdamHeavyTailedProcess.prefixState (stateTransition g q ρ η τ) (x0, 0, 0) ω0 s b).2.2 i := by
    unfold LongTails.Proofs.AdamHeavyTailedProcess.prefixState
    rw [stateAt_initial]
    exact trajectory_secondMoment_nonneg g q η τ hρ.le hρ1.le x0 _ s i
  have hh := LongTails.Proofs.AdamHeavyTailedProcess.stateAt_tail_integral_le P
    (stateTransition g q ρ η τ) (x0, 0, 0) ω0 s F B hiF hiB (fun b => by
      have hb := geometric_oracle_window_bias P hg (measurable_gradient_of_lipschitz hL hlip)
        hgi hmean hm hmass q η hρ hρ1 hτ hp hp2 hM hnoise _ (hv b) j
      change (∫ ξ, meanPairing ρ τ _ grad j - frozenPairing g grad q ρ η τ _ j ξ ∂Q) ≤ _
      simp_rw [frozenPairing_window]
      change _ ≤ C * _
      dsimp only at hb
      convert hb using 1 <;> dsimp [meanPairing, C, Q]
      ring)
  simp only [stateAt_initial, F, B] at hh
  rw [integral_sub hiM hiR, integral_const_mul,
    integral_add (hiS.const_mul _) (integrable_const _), integral_const_mul] at hh
  simpa only [C, Q, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma trajectory_denominator_pairing_transport {d : ℕ} {Ω : Type*}
    {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (g : Point d → Ω → Point d) (q η : ℝ) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (x0 : Point d) (ξ : ℕ → Ω) (s j : ℕ) :
    |(∑ i, grad (trajectory g q ρ η τ x0 ξ s).1 i *
        g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
          (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ)) -
      frozenPairing g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k))| ≤
    (1 / (Real.sqrt ρ * Real.sqrt ((1 - ρ) ^ j))) *
      Real.sqrt (∑ i, (grad (trajectory g q ρ η τ x0 ξ s).1 i) ^ 2 /
        (frozenDenominator g grad q ρ η τ (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i) ^ 2) *
      Real.sqrt (ρ * (j : ℝ) * (L * |η| * ∑ k ∈ Finset.range j,
        ‖velocity g q ρ η τ x0 ξ (s + k + 1)‖) ^ 2) := by
  let D := fun i => Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ
  let E := fun i => frozenDenominator g grad q ρ η τ
    (trajectory g q ρ η τ x0 ξ s) j (fun k => ξ (s + k)) i
  have hr : 0 < Real.sqrt ρ * Real.sqrt ((1 - ρ) ^ j) := by
    exact mul_pos (Real.sqrt_pos.mpr hρ) (Real.sqrt_pos.mpr (pow_pos (sub_pos.mpr hρ1) j))
  have hb (i : Fin d) : |g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i| / D i ≤
      1 / (Real.sqrt ρ * Real.sqrt ((1 - ρ) ^ j)) := by
    have hh := (trajectory_past_response_bound g q η hρ hρ1 hτ x0 ξ s j i).trans
      (mul_le_mul_of_nonneg_left (instantDirection_coordinate_bound g hρ hρ1.le hτ x0 ξ s i)
        (by positivity : 0 ≤ 1 / Real.sqrt ((1 - ρ) ^ j)))
    convert hh using 1
    dsimp [D]
    ring
  have hh := LongTails.Proofs.AdamHeavyTailedAlgebra.reciprocal_transport_cauchy
    (fun i => grad (trajectory g q ρ η τ x0 ξ s).1 i)
    (fun i => g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i) D E
    (fun i => by dsimp [D]; positivity)
    (fun i => by dsimp [E, frozenDenominator]; positivity) hr hb
  have hd := Real.sqrt_le_sqrt (trajectory_denominator_transport hL hlip g q η τ hρ.le hρ1.le x0 ξ s j)
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  simpa only [D, E, frozenPairing, Nat.add_zero] using hh'

noncomputable def lagPairing {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (grad : Point d → Point d) (q ρ η τ : ℝ) (x0 : Point d) (ξ : ℕ → Ω)
    (s j r : ℕ) : ℝ :=
  ∑ i, grad (trajectory g q ρ η τ x0 ξ (s + r)).1 i *
    g (trajectory g q ρ η τ x0 ξ s).1 (ξ s) i /
      (Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ)

lemma measurable_lagPairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} {grad : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hgrad : Measurable grad)
    (q ρ η τ : ℝ) (x0 : Point d) (s j r : ℕ) :
    Measurable (fun ξ => lagPairing g grad q ρ η τ x0 ξ s j r) := by
  unfold lagPairing
  apply Finset.measurable_sum
  intro i _
  have hx := (measurable_trajectory hg q ρ η τ x0 s).fst
  have hμ := (measurable_coordinate i).comp
    (hgrad.comp (measurable_trajectory hg q ρ η τ x0 (s + r)).fst)
  have hv := (measurable_coordinate i).comp
    (measurable_trajectory hg q ρ η τ x0 (s + j + 1)).snd.snd
  exact (hμ.mul ((measurable_coordinate i).comp (hg.comp (hx.prodMk (measurable_pi_apply s))))).div
    ((Real.continuous_sqrt.measurable.comp hv).add measurable_const)

lemma lagPairing_abs_bound {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (grad : Point d → Point d) (q η : ℝ) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (x0 : Point d) (ξ : ℕ → Ω) (s j r : ℕ) :
    |lagPairing g grad q ρ η τ x0 ξ s j r| ≤
      (d : ℝ) * ‖grad (trajectory g q ρ η τ x0 ξ (s + r)).1‖ *
        ((1 / Real.sqrt ((1 - ρ) ^ j)) * (1 / Real.sqrt ρ)) := by
  unfold lagPairing
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ : Fin d, ‖grad (trajectory g q ρ η τ x0 ξ (s + r)).1‖ *
        ((1 / Real.sqrt ((1 - ρ) ^ j)) * (1 / Real.sqrt ρ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hd : 0 < Real.sqrt ((trajectory g q ρ η τ x0 ξ (s + j + 1)).2.2 i) + τ := by positivity
      rw [abs_div, abs_mul, abs_of_pos hd, mul_div_assoc]
      have hμ : |grad (trajectory g q ρ η τ x0 ξ (s + r)).1 i| ≤
          ‖grad (trajectory g q ρ η τ x0 ξ (s + r)).1‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (grad (trajectory g q ρ η τ x0 ξ (s + r)).1) i
      have hh := (trajectory_past_response_bound g q η hρ hρ1 hτ x0 ξ s j i).trans
        (mul_le_mul_of_nonneg_left (instantDirection_coordinate_bound g hρ hρ1.le hτ x0 ξ s i)
          (by positivity : 0 ≤ 1 / Real.sqrt ((1 - ρ) ^ j)))
      exact mul_le_mul hμ hh (by positivity) (norm_nonneg _)
    _ = _ := by simp; ring

lemma integrable_lagPairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure (ℕ → Ω)} [IsFiniteMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) {grad : Point d → Point d} {L : ℝ}
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {q ρ η τ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hstable : q / Real.sqrt (1 - ρ) < 1) (x0 : Point d) (s j r : ℕ) :
    Integrable (fun ξ => lagPairing g grad q ρ η τ x0 ξ s j r) P := by
  apply (((integrable_trajectory_gradient_norm (P := P) (η := η) hg hL hlip
    hq hq1 hρ hρ1 hτ hstable x0 (s + r)).const_mul (d : ℝ)).mul_const
    ((1 / Real.sqrt ((1 - ρ) ^ j)) * (1 / Real.sqrt ρ))).mono'
    (measurable_lagPairing hg (measurable_gradient_of_lipschitz hL hlip) q ρ η τ x0 s j r).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs]
    exact lagPairing_abs_bound g grad q η hρ hρ1 hτ x0 ξ s j r

end OracleTemplate.Adam
