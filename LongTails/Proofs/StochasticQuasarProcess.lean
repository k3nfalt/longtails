import LongTails.Proofs.StochasticQuasarSchedule
import LongTails.Proofs.StochasticQuasarBarrier
import LongTails.Proofs.StochasticQuasarHolding

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

open GradientOnlyQuasar

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def shiftedEnergyBarrier (f : E → ℝ) (u : E) (A B : ℝ) (p : ℕ) (x z : E) : ℝ :=
  barrier (((weightedEnergy f u A x z + B) / (2 * B)) ^ p)

noncomputable def shiftedEnergyBarrierDrift (f : E → ℝ) (G : E → E) (u : E)
    (A B γ c : ℝ) (p : ℕ) (x z : E) : ℝ :=
  barrierSlope (((weightedEnergy f u A x z + B) / (2 * B)) ^ p) *
    ((p : ℝ) * ((weightedEnergy f u A x z + B) / (2 * B)) ^ (p - 1) *
      ((γ * c * (f x - f u) + c * ⟪G x, z - x⟫) / (2 * B)))

omit [InnerProductSpace ℝ E] in
lemma shifted_barrier_nonneg {f : E → ℝ} {u x z : E} {A B : ℝ} {p : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : ∀ y, f u ≤ f y) :
    0 ≤ shiftedEnergyBarrier f u A B p x z := by
  have he := weightedEnergy_nonneg (f := f) (u := u) (y := x) (z := z) hA
    (show IsMinOn f univ u from fun y _ => hm y)
  apply barrier_nonneg
  exact pow_nonneg (div_nonneg (by linarith) (by positivity)) p

omit [InnerProductSpace ℝ E] in
lemma shifted_barrier_le_one (f : E → ℝ) (u : E) (A B : ℝ) (p : ℕ) (x z : E) :
    shiftedEnergyBarrier f u A B p x z ≤ 1 := barrier_le_one _

omit [InnerProductSpace ℝ E] in
lemma continuous_shifted_barrier {f : E → ℝ} (hf : Continuous f) (u : E) (B : ℝ) (p : ℕ) :
    Continuous (fun w : ℝ × E × E => shiftedEnergyBarrier f u w.1 B p w.2.1 w.2.2) := by
  unfold shiftedEnergyBarrier weightedEnergy
  apply continuous_barrier.comp
  fun_prop

noncomputable def compensatedEnergyBarrier (f : E → ℝ) (u : E) (A : ℝ → ℝ)
    (B ρ : ℝ) (p : ℕ) (state : ℝ × E × E) : ℝ :=
  Real.exp (-(ρ * state.1)) * shiftedEnergyBarrier f u (A state.1) B p state.2.1 state.2.2

omit [InnerProductSpace ℝ E] in
lemma continuous_compensated_barrier {f : E → ℝ} {A : ℝ → ℝ}
    (hf : Continuous f) (hA : Continuous A) (u : E) (B ρ : ℝ) (p : ℕ) :
    Continuous (compensatedEnergyBarrier f u A B ρ p) := by
  have hb := continuous_barrier
  unfold compensatedEnergyBarrier shiftedEnergyBarrier weightedEnergy
  fun_prop

omit [InnerProductSpace ℝ E] in
lemma compensated_barrier_nonneg {f : E → ℝ} {A : ℝ → ℝ} {u : E} {B ρ : ℝ} {p : ℕ}
    (hA : ∀ t, 0 ≤ A t) (hB : 0 ≤ B) (hm : ∀ y, f u ≤ f y) (state : ℝ × E × E) :
    0 ≤ compensatedEnergyBarrier f u A B ρ p state :=
  mul_nonneg (Real.exp_pos _).le (shifted_barrier_nonneg (hA state.1) hB hm)

omit [InnerProductSpace ℝ E] in
lemma compensated_barrier_le_one {f : E → ℝ} {A : ℝ → ℝ} {u : E} {B ρ : ℝ} {p : ℕ}
    (hA : ∀ t, 0 ≤ A t) (hB : 0 ≤ B) (hm : ∀ y, f u ≤ f y) (hρ : 0 ≤ ρ)
    (state : ℝ × E × E) (ht : 0 ≤ state.1) :
    compensatedEnergyBarrier f u A B ρ p state ≤ 1 := by
  have he : Real.exp (-(ρ * state.1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hρ ht))
  exact (mul_le_mul_of_nonneg_right he (shifted_barrier_nonneg (hA state.1) hB hm)).trans
    (by simpa using shifted_barrier_le_one f u (A state.1) B p state.2.1 state.2.2)

lemma continuous_shifted_barrier_drift {f : E → ℝ} {G : E → E}
    (hf : Continuous f) (hG : Continuous G) (u : E) (B γ : ℝ) (p : ℕ) :
    Continuous (fun w : (ℝ × ℝ) × E × E =>
      shiftedEnergyBarrierDrift f G u w.1.1 B γ w.1.2 p w.2.1 w.2.2) := by
  have hs := continuous_barrierSlope
  unfold shiftedEnergyBarrierDrift weightedEnergy
  fun_prop

lemma shifted_barrier_flow_deriv [CompleteSpace E] {A c : ℝ → ℝ} {γ s t B : ℝ}
    {p : ℕ} (hγ : γ ≠ 0) (hAs : 0 < A s) (hAt : 0 < A t)
    (hAder : HasDerivAt A (γ * c t) t)
    {f : E → ℝ} {G : E → E} (hf : ∀ y, HasGradientAt f (G y) y) (x z u : E) :
    HasDerivAt (fun v => shiftedEnergyBarrier f u (A v) B p (accelerationFlow A γ s v x z) z)
      (shiftedEnergyBarrierDrift f G u (A t) B γ (c t) p (accelerationFlow A γ s t x z) z) t := by
  have he := (((acceleration_flow_energy_deriv hγ hAs hAt hAder hf x z u).add_const B).div_const
    (2 * B)).pow p
  exact (hasDerivAt_barrier _).comp t he

lemma shifted_barrier_drift_formula (f : E → ℝ) (G : E → E) (u x z : E)
    (A γ c : ℝ) {B : ℝ} (hB : B ≠ 0) {p : ℕ} (hp : 0 < p) :
    shiftedEnergyBarrierDrift f G u A B γ c p x z =
      barrierSlope (((weightedEnergy f u A x z + B) / (2 * B)) ^ p) *
        ((p : ℝ) * (weightedEnergy f u A x z + B) ^ (p - 1) *
          (γ * c * (f x - f u) + c * ⟪G x, z - x⟫) / (2 * B) ^ p) := by
  unfold shiftedEnergyBarrierDrift
  congr 1
  have hp' : p = (p - 1) + 1 := by omega
  have hpow : (2 * B) ^ p = (2 * B) ^ (p - 1) * (2 * B) := by
    conv_lhs => rw [hp', pow_succ]
  rw [div_pow, hpow]
  field_simp

lemma shifted_barrier_holding_step [CompleteSpace E] {A c : ℝ → ℝ} {γ B ρ s T : ℝ}
    {p : ℕ} (hγ : 0 < γ) (hB : 0 < B) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hA : Continuous A) (hc : Continuous c) (hAp : ∀ t, 0 < A t)
    (hAder : ∀ t, HasDerivAt A (γ * c t) t) (hcend : ∀ t, T ≤ t → c t = 0)
    {f : E → ℝ} {G : E → E} (hf : ∀ y, HasGradientAt f (G y) y) (hG : Continuous G)
    (x z u : E) (hmin : ∀ y, f u ≤ f y) {J : ℝ → ℝ} (hJ : Measurable J)
    (hJbound : ∀ t, 0 ≤ t → 0 ≤ J t ∧ J t ≤ 1)
    (hgen : ∀ t, 0 ≤ t →
      shiftedEnergyBarrierDrift f G u (A (s + t)) B γ (c (s + t)) p
          (accelerationFlow A γ s (s + t) x z) z + J t -
        shiftedEnergyBarrier f u (A (s + t)) B p (accelerationFlow A γ s (s + t) x z) z ≤
          ρ * shiftedEnergyBarrier f u (A (s + t)) B p (accelerationFlow A γ s (s + t) x z) z) :
    (∫ t, Real.exp (-(ρ * (s + t))) * J t ∂expMeasure 1) ≤
      Real.exp (-(ρ * s)) * shiftedEnergyBarrier f u (A s) B p x z := by
  let Y := fun t => accelerationFlow A γ s (s + t) x z
  let V := fun t => shiftedEnergyBarrier f u (A (s + t)) B p (Y t) z
  let D := fun t => shiftedEnergyBarrierDrift f G u (A (s + t)) B γ (c (s + t)) p (Y t) z
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).hasFDerivAt.continuousAt
  have ht : Continuous (fun t : ℝ => s + t) := continuous_const.add continuous_id
  have hY : Continuous Y := (continuous_acceleration_flow hA hAp hγ.le).comp
    (show Continuous (fun t : ℝ => ((s, s + t), x, z)) by fun_prop)
  have hV : Continuous V := by
    dsimp only [V, shiftedEnergyBarrier, weightedEnergy]
    apply continuous_barrier.comp
    fun_prop
  have hD : Continuous D := by
    have hb := continuous_barrierSlope
    dsimp only [D, shiftedEnergyBarrierDrift, weightedEnergy]
    fun_prop
  have hd (t : ℝ) : HasDerivAt V (D t) t := by
    have he := (shifted_barrier_flow_deriv (B := B) (p := p) (ne_of_gt hγ) (hAp s) (hAp (s + t))
      (hAder (s + t)) hf x z u).comp t ((hasDerivAt_id t).const_add s)
    convert! he using 1
    simp [D, Y]
  have hb (t : ℝ) : ‖V t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (shifted_barrier_nonneg (hAp (s + t)).le hB.le hmin)]
    exact shifted_barrier_le_one _ _ _ _ _ _ _
  have hdz (t : ℝ) (ht' : T - s ≤ t) : D t = 0 := by
    dsimp only [D, shiftedEnergyBarrierDrift]
    rw [hcend (s + t) (by linarith)]
    ring
  obtain ⟨CD, hCD⟩ := bounded_of_continuous_eventually_zero hD hdz
  have hR : Continuous (fun t : ℝ => ρ * (s + t)) := continuous_const.mul ht
  have hr : Continuous (fun _ : ℝ => ρ) := continuous_const
  have hRd (t : ℝ) : HasDerivAt (fun t : ℝ => ρ * (s + t)) ρ t := by
    convert ((hasDerivAt_id t).const_add s).const_mul ρ using 1 <;> simp
  have hh := compensated_holding_nonincrease hV hD hJ hR hr hd hRd
    (fun t ht' => mul_nonneg hρ (add_nonneg hs ht')) (fun t _ => hb t) hCD
    (fun t ht' => by rw [Real.norm_eq_abs, abs_of_nonneg (hJbound t ht').1]; exact (hJbound t ht').2)
    (Cr := ‖ρ‖) (fun _ _ => le_rfl) hgen
  simpa only [V, Y, add_zero, acceleration_flow_initial (ne_of_gt (hAp s))] using hh

lemma shifted_barrier_random_holding [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A c : ℝ → ℝ} {γ B ρ s T : ℝ}
    {p : ℕ} (hγ : 0 < γ) (hB : 0 < B) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hA : Continuous A) (hc : Continuous c) (hAp : ∀ t, 0 < A t)
    (hAder : ∀ t, HasDerivAt A (γ * c t) t) (hcend : ∀ t, T ≤ t → c t = 0)
    {f : E → ℝ} {G : E → E} (hf : ∀ y, HasGradientAt f (G y) y) (hG : Continuous G)
    (x z u : E) (hmin : ∀ y, f u ≤ f y) {F : ℝ × Ω → ℝ} (hF : Measurable F)
    (hFb : ∀ w, 0 ≤ F w ∧ F w ≤ 1)
    (hgen : ∀ t, 0 ≤ t →
      shiftedEnergyBarrierDrift f G u (A (s + t)) B γ (c (s + t)) p
          (accelerationFlow A γ s (s + t) x z) z + (∫ ω, F (t, ω) ∂μ) -
        shiftedEnergyBarrier f u (A (s + t)) B p (accelerationFlow A γ s (s + t) x z) z ≤
          ρ * shiftedEnergyBarrier f u (A (s + t)) B p (accelerationFlow A γ s (s + t) x z) z) :
    (∫ w : ℝ × Ω, Real.exp (-(ρ * (s + max 0 w.1))) * F (max 0 w.1, w.2)
      ∂(RelativeQuasar.holdingLaw : Measure ℝ).prod μ) ≤
      Real.exp (-(ρ * s)) * shiftedEnergyBarrier f u (A s) B p x z := by
  let J := fun t => ∫ ω, F (t, ω) ∂μ
  have hJ : Measurable J := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hFi (t : ℝ) : Integrable (fun ω => F (t, ω)) μ := by
    apply Integrable.of_bound (hF.comp measurable_prodMk_left).aestronglyMeasurable 1
    filter_upwards with ω
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (hFb (t, ω)).1]
    exact (hFb (t, ω)).2
  have hJb (t : ℝ) : 0 ≤ J t ∧ J t ≤ 1 := by
    refine ⟨integral_nonneg (fun ω => (hFb (t, ω)).1), ?_⟩
    have hh := integral_mono (hFi t) (integrable_const (1 : ℝ)) (fun ω => (hFb (t, ω)).2)
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hh := shifted_barrier_holding_step hγ hB hρ hs hA hc hAp hAder hcend hf hG
    x z u hmin hJ (fun t _ => hJb t) hgen
  let W := fun w : ℝ × Ω => Real.exp (-(ρ * (s + max 0 w.1))) * F (max 0 w.1, w.2)
  have hWm : Measurable W := by
    apply Measurable.mul
    · fun_prop
    · exact hF.comp ((measurable_const.max measurable_fst).prodMk measurable_snd)
  have hWi : Integrable W ((RelativeQuasar.holdingLaw : Measure ℝ).prod μ) := by
    apply Integrable.of_bound hWm.aestronglyMeasurable 1
    filter_upwards with w
    have he : Real.exp (-(ρ * (s + max 0 w.1))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hρ (add_nonneg hs (le_max_left _ _))))
    have hw0 : 0 ≤ W w := mul_nonneg (Real.exp_pos _).le (hFb _).1
    rw [Real.norm_eq_abs, abs_of_nonneg hw0]
    exact (mul_le_mul_of_nonneg_right he (hFb _).1).trans (by simpa using (hFb (max 0 w.1, w.2)).2)
  change (∫ w, W w ∂(RelativeQuasar.holdingLaw : Measure ℝ).prod μ) ≤ _
  rw [integral_prod W hWi]
  dsimp only [W]
  simp only [integral_const_mul]
  convert hh using 1
  change (∫ t, Real.exp (-(ρ * (s + max 0 t))) * J (max 0 t) ∂expMeasure 1) = _
  rw [ContinuizedSimilarQuasar.integral_expMeasure_one,
    ContinuizedSimilarQuasar.integral_expMeasure_one]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [max_eq_right (mem_Ioi.mp ht).le]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type*} [MeasurableSpace Ω]

lemma shifted_barrier_jump_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P)
    {f : E → ℝ} {G : E → E} {u x z : E} {Z : Ω → E}
    {A η c L q B H γ β V : ℝ} {p : ℕ} (hu : u ∈ Q) (hz : z ∈ Q)
    (hA : 0 < A) (hη : 0 < η) (hc0 : 0 ≤ c) (hL : 0 < L)
    (hq : 0 ≤ q) (hB : 0 < B) (hH : 0 < H) (hp : 2 ≤ p)
    (hLη : L * η = q) (hc : c ^ 2 ≤ A * η * q)
    (hsmall : 144 * (p : ℝ) * q ≤ 1) (hqcap : q ≤ 1 / 16)
    (hbalance : (p : ℝ) * (A * η) * H ^ 2 = B)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (hquasar : γ * (f x - f u) ≤ ⟪G x, x - u⟫)
    (hm : Measurable Z) (hi : Integrable Z μ)
    (h2i : Integrable (fun ω => ‖Z ω - G x‖ ^ 2) μ)
    (hb : ‖(∫ ω, Z ω ∂μ) - G x‖ ≤ β) (h2 : (∫ ω, ‖Z ω - G x‖ ^ 2 ∂μ) ≤ V) :
    Integrable (fun ω => shiftedEnergyBarrier f u A B p (x - η • clip H (Z ω))
      (P (z - c • clip H (Z ω)))) μ ∧
    shiftedEnergyBarrierDrift f G u A B γ c p x z +
      (∫ ω, shiftedEnergyBarrier f u A B p (x - η • clip H (Z ω))
        (P (z - c • clip H (Z ω))) ∂μ) - shiftedEnergyBarrier f u A B p x z ≤
      (2 * (p : ℝ) * (A * η * V + 3 * Real.sqrt (q * (A * η) * B) * β) / B) *
        shiftedEnergyBarrier f u A B p x z := by
  have hh := clipped_energy_barrier_drift hP hu hz hA hη hc0 hL hq hB hH hp hLη hc
    hsmall hqcap hbalance hG hlip hmin hquasar hm hi h2i hb h2
  dsimp only at hh
  have he (ω : Ω) : weightedEnergy f u A x z + B +
      (weightedEnergy f u A (x - η • clip H (Z ω)) (P (z - c • clip H (Z ω))) -
        weightedEnergy f u A x z) =
      weightedEnergy f u A (x - η • clip H (Z ω)) (P (z - c • clip H (Z ω))) + B := by ring
  simp only [he] at hh
  rw [shifted_barrier_drift_formula f G u x z A γ c (ne_of_gt hB) (by omega : 0 < p)]
  exact hh

end OracleTemplate.StochasticQuasar
