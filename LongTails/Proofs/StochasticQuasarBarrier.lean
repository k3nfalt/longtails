import LongTails.Proofs.StochasticQuasarEnergyMoments
import LongTails.Proofs.StochasticQuasarPowerDrift

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrated_power_remainder {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : Ω → ℝ} {u : ℝ} {p : ℕ} (hu : 0 < u) (hp : 2 ≤ p)
    (hJm : Measurable J) (hJi : Integrable J μ) (hJ2i : Integrable (fun ω => J ω ^ 2) μ)
    (hcap : ∀ ω, |J ω| ≤ u / p) :
    Integrable (fun ω => (u + J ω) ^ p) μ ∧
      (∫ ω, (u + J ω) ^ p ∂μ) ≤ u ^ p +
        (p : ℝ) * u ^ (p - 1) * (∫ ω, J ω ∂μ) +
        (p : ℝ) ^ 2 * u ^ (p - 2) * (∫ ω, J ω ^ 2 ∂μ) := by
  have hbound (ω : Ω) : |u + J ω| ≤ u + u / p := by
    have hh := abs_add_le u (J ω)
    rw [abs_of_pos hu] at hh
    linarith [hcap ω]
  have hpowi : Integrable (fun ω => (u + J ω) ^ p) μ := Integrable.of_bound
    (((measurable_const (a := u)).add hJm).pow_const p).aestronglyMeasurable ((u + u / p) ^ p)
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound ω) p))
  have hi1 : Integrable (fun ω => u ^ p + (p : ℝ) * u ^ (p - 1) * J ω) μ :=
    (integrable_const _).add (hJi.const_mul _)
  have hi2 : Integrable (fun ω => (p : ℝ) ^ 2 * u ^ (p - 2) * J ω ^ 2) μ := hJ2i.const_mul _
  have hint := integral_mono hpowi (hi1.add hi2) (fun ω => energy_power_remainder hu hp (hcap ω))
  simp only [Pi.add_apply] at hint
  rw [integral_add hi1 hi2, integral_add (integrable_const _) (hJi.const_mul _)] at hint
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at hint
  exact ⟨hpowi, hint⟩

lemma integrated_power_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : Ω → ℝ} {u B q F D N R : ℝ} {p : ℕ} (hp : 2 ≤ p)
    (hB : 0 < B) (hu : B ≤ u) (hq : 0 ≤ q) (hD : 0 ≤ D) (hR : 0 ≤ R) (hRN : R ≤ N)
    (hgrad : 18 * (p : ℝ) * q ≤ 1 - q) (hnoise : 66 * (p : ℝ) * q ≤ 1)
    (hJm : Measurable J) (hJi : Integrable J μ) (hJ2i : Integrable (fun ω => J ω ^ 2) μ)
    (hcap : ∀ ω, |J ω| ≤ B / p)
    (hmean : F + (∫ ω, J ω ∂μ) ≤ -(1 - q) * D + N)
    (hsecond : (∫ ω, J ω ^ 2 ∂μ) ≤ 18 * q * B * D + 66 * q * B * R) :
    Integrable (fun ω => (u + J ω) ^ p) μ ∧
      (p : ℝ) * u ^ (p - 1) * F + (∫ ω, (u + J ω) ^ p ∂μ) - u ^ p ≤
        2 * (p : ℝ) * u ^ (p - 1) * N := by
  have hu0 := hB.trans_le hu
  have hcapu (ω : Ω) : |J ω| ≤ u / p :=
    (hcap ω).trans (div_le_div_of_nonneg_right hu (Nat.cast_nonneg p))
  have hpow := integrated_power_remainder hu0 hp hJm hJi hJ2i hcapu
  have habs := power_drift_absorption hB.le hu hq (Nat.cast_nonneg p) hD hR hRN hgrad hnoise hmean hsecond
  have hh := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ (p : ℝ) * u ^ (p - 2))
  have he : u ^ (p - 1) = u ^ (p - 2) * u := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨hpow.1, ?_⟩
  have hr := hpow.2
  rw [he] at hr ⊢
  nlinarith

lemma barrier_slope_product_le (s : ℝ) :
    GradientOnlyQuasar.barrierSlope s * s ≤ GradientOnlyQuasar.barrier s := by
  by_cases h1 : s ≤ 1
  · simp only [GradientOnlyQuasar.barrierSlope, GradientOnlyQuasar.barrier,
      max_eq_right (by linarith : 0 ≤ 1 - s)]
    nlinarith [sq_nonneg s]
  · have hh : 1 ≤ s := (lt_of_not_ge h1).le
    rw [GradientOnlyQuasar.barrier_eq_one hh]
    simp only [GradientOnlyQuasar.barrierSlope, max_eq_left (by linarith : 1 - s ≤ 0)]
    norm_num

lemma integrated_barrier_transfer {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {s d r : ℝ} (hYm : Measurable Y) (hYi : Integrable Y μ)
    (hY : ∀ ω, 0 ≤ Y ω) (hr : 0 ≤ r) (hd : d + (∫ ω, Y ω ∂μ) - s ≤ r * s) :
    Integrable (fun ω => GradientOnlyQuasar.barrier (Y ω)) μ ∧
      GradientOnlyQuasar.barrierSlope s * d +
        (∫ ω, GradientOnlyQuasar.barrier (Y ω) ∂μ) - GradientOnlyQuasar.barrier s ≤
        r * GradientOnlyQuasar.barrier s := by
  have hBm : Measurable (fun ω => GradientOnlyQuasar.barrier (Y ω)) :=
    GradientOnlyQuasar.continuous_barrier.measurable.comp hYm
  have hBi : Integrable (fun ω => GradientOnlyQuasar.barrier (Y ω)) μ :=
    Integrable.of_bound hBm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (GradientOnlyQuasar.barrier_nonneg (hY ω))]
      exact GradientOnlyQuasar.barrier_le_one (Y ω)))
  have hsub : Integrable (fun ω => Y ω - s) μ := hYi.sub (integrable_const s)
  have hupper : Integrable (fun ω => GradientOnlyQuasar.barrier s +
      GradientOnlyQuasar.barrierSlope s * (Y ω - s)) μ :=
    (integrable_const _).add (hsub.const_mul _)
  have hint := integral_mono hBi hupper (fun ω => GradientOnlyQuasar.barrier_tangent s (Y ω))
  rw [integral_add (integrable_const _) (hsub.const_mul _), integral_const_mul,
    integral_sub hYi (integrable_const s)] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  have hh := mul_le_mul_of_nonneg_left hd (GradientOnlyQuasar.barrierSlope_nonneg s)
  have hs := mul_le_mul_of_nonneg_left (barrier_slope_product_le s) hr
  exact ⟨hBi, by nlinarith⟩

lemma normalized_energy_barrier_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : Ω → ℝ} {u B q F D N R : ℝ} {p : ℕ} (hp : 2 ≤ p)
    (hB : 0 < B) (hu : B ≤ u) (hq : 0 ≤ q) (hD : 0 ≤ D) (hR : 0 ≤ R) (hRN : R ≤ N)
    (hgrad : 18 * (p : ℝ) * q ≤ 1 - q) (hnoise : 66 * (p : ℝ) * q ≤ 1)
    (hJm : Measurable J) (hJi : Integrable J μ) (hJ2i : Integrable (fun ω => J ω ^ 2) μ)
    (hcap : ∀ ω, |J ω| ≤ B / p)
    (hmean : F + (∫ ω, J ω ∂μ) ≤ -(1 - q) * D + N)
    (hsecond : (∫ ω, J ω ^ 2 ∂μ) ≤ 18 * q * B * D + 66 * q * B * R) :
    Integrable (fun ω => GradientOnlyQuasar.barrier (((u + J ω) / (2 * B)) ^ p)) μ ∧
      GradientOnlyQuasar.barrierSlope ((u / (2 * B)) ^ p) *
          ((p : ℝ) * u ^ (p - 1) * F / (2 * B) ^ p) +
        (∫ ω, GradientOnlyQuasar.barrier (((u + J ω) / (2 * B)) ^ p) ∂μ) -
        GradientOnlyQuasar.barrier ((u / (2 * B)) ^ p) ≤
        (2 * (p : ℝ) * N / B) * GradientOnlyQuasar.barrier ((u / (2 * B)) ^ p) := by
  have hpow := integrated_power_drift hp hB hu hq hD hR hRN hgrad hnoise hJm hJi hJ2i hcap hmean hsecond
  have hu0 := hB.trans_le hu
  have hN : 0 ≤ N := hR.trans hRN
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hpost (ω : Ω) : 0 ≤ u + J ω := by
    have hh := (hcap ω).trans (div_le_self hB.le hp1)
    have hj := neg_abs_le (J ω)
    linarith
  have hYm : Measurable (fun ω => ((u + J ω) / (2 * B)) ^ p) :=
    (((measurable_const (a := u)).add hJm).div_const _).pow_const p
  have hYi : Integrable (fun ω => ((u + J ω) / (2 * B)) ^ p) μ := by
    simpa only [div_pow] using hpow.1.div_const ((2 * B) ^ p)
  have hY (ω : Ω) : 0 ≤ ((u + J ω) / (2 * B)) ^ p :=
    pow_nonneg (div_nonneg (hpost ω) (by positivity)) p
  have hr : 0 ≤ 2 * (p : ℝ) * N / B := by positivity
  apply integrated_barrier_transfer hYm hYi hY hr
  have he : u ^ p = u ^ (p - 1) * u := by
    rw [← pow_succ]
    congr 1
    omega
  have hscale : 2 * (p : ℝ) * u ^ (p - 1) * N ≤ (2 * (p : ℝ) * N / B) * u ^ p := by
    have hh := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * (p : ℝ) * u ^ (p - 1) * N)
    have ht : 2 * (p : ℝ) * u ^ (p - 1) * N ≤ (2 * (p : ℝ) * N * u ^ p) / B := by
      apply (le_div_iff₀ hB).mpr
      rw [he]
      nlinarith
    convert ht using 1; ring
  have htotal := div_le_div_of_nonneg_right (hpow.2.trans hscale)
    (by positivity : 0 ≤ (2 * B) ^ p)
  simp_rw [div_pow]
  rw [integral_div]
  convert htotal using 1 <;> ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma clipped_energy_barrier_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
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
    let Φ := GradientOnlyQuasar.weightedEnergy f u A x z
    let J := fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • clip H (Z ω))
      (P (z - c • clip H (Z ω))) - Φ
    Integrable (fun ω => GradientOnlyQuasar.barrier (((Φ + B + J ω) / (2 * B)) ^ p)) μ ∧
      GradientOnlyQuasar.barrierSlope (((Φ + B) / (2 * B)) ^ p) *
          ((p : ℝ) * (Φ + B) ^ (p - 1) * (γ * c * (f x - f u) + c * ⟪G x, z - x⟫) / (2 * B) ^ p) +
        (∫ ω, GradientOnlyQuasar.barrier (((Φ + B + J ω) / (2 * B)) ^ p) ∂μ) -
        GradientOnlyQuasar.barrier (((Φ + B) / (2 * B)) ^ p) ≤
        (2 * (p : ℝ) * (A * η * V + 3 * Real.sqrt (q * (A * η) * B) * β) / B) *
          GradientOnlyQuasar.barrier (((Φ + B) / (2 * B)) ^ p) := by
  let Φ := GradientOnlyQuasar.weightedEnergy f u A x z
  let J := fun ω => GradientOnlyQuasar.weightedEnergy f u A (x - η • clip H (Z ω))
    (P (z - c • clip H (Z ω))) - Φ
  let F := γ * c * (f x - f u) + c * ⟪G x, z - x⟫
  let N := A * η * V + 3 * Real.sqrt (q * (A * η) * B) * β
  have hV0 : 0 ≤ V := (integral_nonneg (μ := μ) (fun ω => sq_nonneg ‖Z ω - G x‖)).trans h2
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hb
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hmin' : IsMinOn f Set.univ u := fun y _ => hmin y
  have hΦ0 : 0 ≤ Φ := GradientOnlyQuasar.weightedEnergy_nonneg hA.le hmin'
  by_cases hΦ : Φ ≤ B
  · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hs := clipped_energy_moments hP hu hz hA hη hc0 hL hq hB.le hH hp' hLη hc hsmall hqcap hbalance
      hG hlip hmin hΦ hquasar hm hi h2i hb h2
    have hgrad : 18 * (p : ℝ) * q ≤ 1 - q := by nlinarith
    have hnoise : 66 * (p : ℝ) * q ≤ 1 := by nlinarith [mul_nonneg (Nat.cast_nonneg p) hq]
    have hRN : A * η * V ≤ N := by
      have hh : 0 ≤ 3 * Real.sqrt (q * (A * η) * B) * β := by positivity
      dsimp [N]
      linarith
    have hmean : F + (∫ ω, J ω ∂μ) ≤ -(1 - q) * (A * η * ‖G x‖ ^ 2) + N := by
      have hh := hs.2.2.2.2.2
      dsimp only [F, J, Φ, N]
      linarith
    have hsecond : (∫ ω, J ω ^ 2 ∂μ) ≤
        18 * q * B * (A * η * ‖G x‖ ^ 2) + 66 * q * B * (A * η * V) := by
      have hh := hs.2.2.2.2.1
      dsimp only [J, Φ]
      nlinarith
    exact normalized_energy_barrier_drift hp hB (by linarith : B ≤ Φ + B) hq
      (by positivity : 0 ≤ A * η * ‖G x‖ ^ 2) (by positivity : 0 ≤ A * η * V) hRN hgrad hnoise
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hmean hsecond
  · have hs : 1 ≤ ((Φ + B) / (2 * B)) ^ p := by
      apply one_le_pow₀
      apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
      linarith
    have hbbase := GradientOnlyQuasar.barrier_eq_one hs
    have hslope : GradientOnlyQuasar.barrierSlope (((Φ + B) / (2 * B)) ^ p) = 0 := by
      simp only [GradientOnlyQuasar.barrierSlope, max_eq_left (by linarith : 1 - ((Φ + B) / (2 * B)) ^ p ≤ 0)]
      ring
    have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hG y).differentiableAt.continuousAt
    have hJm : Measurable J := measurable_energy_jump hP hfc ((measurable_clip H).comp hm) u x z A η c
    have hYm : Measurable (fun ω => ((Φ + B + J ω) / (2 * B)) ^ p) :=
      (((measurable_const (a := Φ + B)).add hJm).div_const _).pow_const p
    have hY0 (ω : Ω) : 0 ≤ ((Φ + B + J ω) / (2 * B)) ^ p := by
      have he := GradientOnlyQuasar.weightedEnergy_nonneg (y := x - η • clip H (Z ω))
        (z := P (z - c • clip H (Z ω))) hA.le hmin'
      have hh : 0 ≤ Φ + B + J ω := by dsimp [J]; linarith
      exact pow_nonneg (div_nonneg hh (by positivity)) p
    have hBi : Integrable (fun ω => GradientOnlyQuasar.barrier (((Φ + B + J ω) / (2 * B)) ^ p)) μ :=
      Integrable.of_bound (GradientOnlyQuasar.continuous_barrier.measurable.comp hYm).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (GradientOnlyQuasar.barrier_nonneg (hY0 ω))]
          exact GradientOnlyQuasar.barrier_le_one _))
    have hint := integral_mono hBi (integrable_const (1 : ℝ))
      (fun ω => GradientOnlyQuasar.barrier_le_one (((Φ + B + J ω) / (2 * B)) ^ p))
    simp only [integral_const, probReal_univ, one_smul] at hint
    refine ⟨hBi, ?_⟩
    change GradientOnlyQuasar.barrierSlope (((Φ + B) / (2 * B)) ^ p) *
      ((p : ℝ) * (Φ + B) ^ (p - 1) * F / (2 * B) ^ p) +
      (∫ ω, GradientOnlyQuasar.barrier (((Φ + B + J ω) / (2 * B)) ^ p) ∂μ) -
      GradientOnlyQuasar.barrier (((Φ + B) / (2 * B)) ^ p) ≤
      (2 * (p : ℝ) * N / B) * GradientOnlyQuasar.barrier (((Φ + B) / (2 * B)) ^ p)
    rw [hslope, hbbase, zero_mul, zero_add, mul_one]
    have hr : 0 ≤ 2 * (p : ℝ) * N / B := by positivity
    linarith

end OracleTemplate.StochasticQuasar
