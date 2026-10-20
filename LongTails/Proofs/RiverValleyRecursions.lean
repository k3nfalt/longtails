import LongTails.Proofs.RiverValleyDescent

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}


set_option maxHeartbeats 1000000 in
lemma w_real {η μ Lv Γ Luv LJ G σu σv na nw nY nr0 nd0 Ysq : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv)
    (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (hΓ0 : 0 ≤ Γ) (hΓ : 16 * Γ ≤ 1) (hLuv : Luv = Γ * μ)
    (hLJ : 0 ≤ LJ) (hna : 0 ≤ na) (hnaG : na ≤ G) (hnw : 0 ≤ nw)
    (hY : Ysq ≤ (1 - η * μ) * nw ^ 2 + 3 * η * Γ ^ 2 * na ^ 2 / μ)
    (hnY' : nY ≤ 2 * nw + η * Γ * na) (hnr0 : 0 ≤ nr0)
    (hnr0b : nr0 ≤ 4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw) (hnd0 : 0 ≤ nd0)
    (hnd0' : nd0 ≤ η * (na + Luv * nw)) :
    Ysq + 2 * nY * (nr0 + LJ * η ^ 2 * σu ^ 2) + 4 * η ^ 2 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) +
        16 * Γ ^ 2 * nd0 ^ 2 + 16 * Γ ^ 2 * η ^ 2 * σu ^ 2 ≤
      (1 - η * μ / 2) * nw ^ 2 +
        η * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) * na ^ 2 / μ +
        η ^ 2 * (4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)) := by
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have hG : 0 ≤ G := hna.trans hnaG
  have hLJG0 : 0 ≤ LJ * G := mul_nonneg hLJ hG
  have hΓ16 : Γ ≤ 1 / 16 := by linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by
    calc Γ ^ 2 = Γ * Γ := sq Γ
      _ ≤ 1 / 16 * (1 / 16) := mul_le_mul hΓ16 hΓ16 hΓ0 (by norm_num)
      _ = 1 / 256 := by norm_num
  have hημ : η * μ ≤ 1 / 8 := by have := mul_le_mul_of_nonneg_left hμLv hη0; linarith
  have hη2μ2 : η ^ 2 * μ ^ 2 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ (mul_nonneg hη0 hμ.le) hημ 2
    have e : (η * μ) ^ 2 = η ^ 2 * μ ^ 2 := by ring
    linarith
  have hη3 : η ^ 3 ≤ η ^ 2 / (8 * Lv) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hη (sq_nonneg η); linarith
  have hY2 : nY ≤ 2 * nw + η * Γ * G :=
    hnY'.trans (by have := mul_le_mul_of_nonneg_left hnaG (mul_nonneg hη0 hΓ0); linarith)
  have hnY0 : 0 ≤ 2 * nw + η * Γ * na := by positivity
  -- P1
  have p1 : 2 * nY * nr0 ≤ 2 * ((2 * nw + η * Γ * na) *
      (4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw)) := by
    rcases le_total 0 nY with hy | hy
    · have := mul_le_mul hnY' hnr0b hnr0 hnY0; linarith
    · have : 0 ≤ (2 * nw + η * Γ * na) * (4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw) :=
        mul_nonneg hnY0 (le_trans hnr0 hnr0b)
      nlinarith
  have pa : 2 * (2 * nw * (4 * LJ * η ^ 2 * na ^ 2)) ≤
      η * μ * nw ^ 2 / 16 + η * (16 * (LJ * G) ^ 2 / μ ^ 2) * na ^ 2 / μ := by
    have b1 : 2 * (2 * nw * (4 * LJ * η ^ 2 * na ^ 2)) ≤ 16 * (LJ * G) * η ^ 2 * na * nw := by
      have := mul_le_mul_of_nonneg_left hnaG (by positivity : (0:ℝ) ≤ 16 * LJ * η ^ 2 * na * nw)
      linear_combination this
    have b2 : 16 * (LJ * G) * η ^ 2 * na * nw ≤
        η * μ * nw ^ 2 / 16 + 1024 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ := by
      have h0 : 0 ≤ η / (16 * μ) * (μ * nw - 128 * (LJ * G) * η * na) ^ 2 := by positivity
      have e : η / (16 * μ) * (μ * nw - 128 * (LJ * G) * η * na) ^ 2 =
          η * μ * nw ^ 2 / 16 + 1024 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ -
            16 * (LJ * G) * η ^ 2 * na * nw := by field_simp; ring
      linarith
    have b3 : 1024 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ ≤
        η * (16 * (LJ * G) ^ 2 / μ ^ 2) * na ^ 2 / μ := by
      have e1 : 1024 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ =
          (1024 * (LJ * G) ^ 2 * η * na ^ 2 / μ ^ 3) * (η ^ 2 * μ ^ 2) := by field_simp
      have e2 : η * (16 * (LJ * G) ^ 2 / μ ^ 2) * na ^ 2 / μ =
          (1024 * (LJ * G) ^ 2 * η * na ^ 2 / μ ^ 3) * (1 / 64) := by field_simp; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hη2μ2 (by positivity)
    linarith
  have pb : 2 * (2 * nw * (4 * Γ * η * Luv * nw)) ≤ η * μ * nw ^ 2 / 16 := by
    rw [hLuv]
    have := mul_le_mul_of_nonneg_left hΓ2 (by positivity : (0:ℝ) ≤ 16 * η * μ * nw ^ 2)
    linarith
  have pc : 2 * (η * Γ * na * (4 * LJ * η ^ 2 * na ^ 2)) ≤ η * (Γ * (LJ * G) / μ) * na ^ 2 / μ := by
    have b1 : 2 * (η * Γ * na * (4 * LJ * η ^ 2 * na ^ 2)) ≤ 8 * Γ * (LJ * G) * η ^ 3 * na ^ 2 := by
      have := mul_le_mul_of_nonneg_left hnaG (by positivity : (0:ℝ) ≤ 8 * Γ * LJ * η ^ 3 * na ^ 2)
      linear_combination this
    have e1 : 8 * Γ * (LJ * G) * η ^ 3 * na ^ 2 =
        (8 * Γ * (LJ * G) * η * na ^ 2 / μ ^ 2) * (η ^ 2 * μ ^ 2) := by field_simp
    have e2 : η * (Γ * (LJ * G) / μ) * na ^ 2 / μ =
        (8 * Γ * (LJ * G) * η * na ^ 2 / μ ^ 2) * (1 / 8) := by field_simp
    have := mul_le_mul_of_nonneg_left (hη2μ2.trans (by norm_num : (1:ℝ) / 64 ≤ 1 / 8))
      (by positivity : (0:ℝ) ≤ 8 * Γ * (LJ * G) * η * na ^ 2 / μ ^ 2)
    linarith
  have pd : 2 * (η * Γ * na * (4 * Γ * η * Luv * nw)) ≤
      η * μ * nw ^ 2 / 64 + η * Γ ^ 2 * na ^ 2 / μ := by
    rw [hLuv]
    have b1 : 2 * (η * Γ * na * (4 * Γ * η * (Γ * μ) * nw)) ≤ Γ ^ 3 * η * na * nw := by
      have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 8 * Γ ^ 3 * η * na * nw)
      linarith
    have b2 : Γ ^ 3 * η * na * nw ≤ η * μ * nw ^ 2 / 64 + 16 * Γ ^ 6 * η * na ^ 2 / μ := by
      have h0 : 0 ≤ η / (64 * μ) * (μ * nw - 32 * Γ ^ 3 * na) ^ 2 := by positivity
      have e : η / (64 * μ) * (μ * nw - 32 * Γ ^ 3 * na) ^ 2 =
          η * μ * nw ^ 2 / 64 + 16 * Γ ^ 6 * η * na ^ 2 / μ - Γ ^ 3 * η * na * nw := by
        field_simp; ring
      linarith
    have b3 : 16 * Γ ^ 6 * η * na ^ 2 / μ ≤ η * Γ ^ 2 * na ^ 2 / μ := by
      apply div_le_div_of_nonneg_right _ hμ.le
      have g4 : Γ ^ 4 ≤ 1 / 16 := by
        have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; linarith
      have := mul_le_mul_of_nonneg_left g4 (by positivity : (0:ℝ) ≤ 16 * Γ ^ 2 * η * na ^ 2)
      linear_combination this
    linarith
  have hsplit : 2 * ((2 * nw + η * Γ * na) * (4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw)) =
      2 * (2 * nw * (4 * LJ * η ^ 2 * na ^ 2)) + 2 * (2 * nw * (4 * Γ * η * Luv * nw)) +
      2 * (η * Γ * na * (4 * LJ * η ^ 2 * na ^ 2)) + 2 * (η * Γ * na * (4 * Γ * η * Luv * nw)) := by
    ring
  -- P2
  have q1 : 2 * nY * (LJ * η ^ 2 * σu ^ 2) ≤ 2 * (2 * nw + η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have q2 : 4 * LJ * η ^ 2 * σu ^ 2 * nw ≤ η * μ * nw ^ 2 / 16 + 64 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ := by
    have h0 : 0 ≤ η / (16 * μ) * (μ * nw - 32 * LJ * η * σu ^ 2) ^ 2 := by positivity
    have e : η / (16 * μ) * (μ * nw - 32 * LJ * η * σu ^ 2) ^ 2 =
        η * μ * nw ^ 2 / 16 + 64 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ - 4 * LJ * η ^ 2 * σu ^ 2 * nw := by
      field_simp; ring
    linarith
  have q3 : 64 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ ≤ η ^ 2 * (8 * LJ ^ 2 * σu ^ 4 / (μ * Lv)) := by
    have := mul_le_mul_of_nonneg_left hη3 (by positivity : (0:ℝ) ≤ 64 * LJ ^ 2 * σu ^ 4 / μ)
    have e1 : 64 * LJ ^ 2 * σu ^ 4 / μ * η ^ 3 = 64 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ := by ring
    have e2 : 64 * LJ ^ 2 * σu ^ 4 / μ * (η ^ 2 / (8 * Lv)) =
        η ^ 2 * (8 * LJ ^ 2 * σu ^ 4 / (μ * Lv)) := by field_simp; ring
    linarith
  have q4 : 2 * (η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) ≤ η ^ 2 * (Γ * G * LJ * σu ^ 2 / (4 * Lv)) := by
    have := mul_le_mul_of_nonneg_left hη3 (by positivity : (0:ℝ) ≤ 2 * Γ * G * LJ * σu ^ 2)
    have e2 : 2 * Γ * G * LJ * σu ^ 2 * (η ^ 2 / (8 * Lv)) =
        η ^ 2 * (Γ * G * LJ * σu ^ 2 / (4 * Lv)) := by field_simp; ring
    nlinarith
  -- P3
  have r1 : 16 * Γ ^ 2 * nd0 ^ 2 ≤ η * (4 * Γ ^ 2) * na ^ 2 / μ + η * μ * nw ^ 2 / 64 := by
    have hd2 : nd0 ^ 2 ≤ 2 * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2) := by
      have h1 := pow_le_pow_left₀ hnd0 hnd0' 2
      have hs : (na + Luv * nw) ^ 2 ≤ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2) := by
        nlinarith [sq_nonneg (na - Luv * nw)]
      have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg η)
      have e : (η * (na + Luv * nw)) ^ 2 = η ^ 2 * (na + Luv * nw) ^ 2 := by ring
      linarith
    have h1 := mul_le_mul_of_nonneg_left hd2 (by positivity : (0:ℝ) ≤ 16 * Γ ^ 2)
    have h2 : 32 * Γ ^ 2 * η ^ 2 * na ^ 2 ≤ η * (4 * Γ ^ 2) * na ^ 2 / μ := by
      rw [le_div_iff₀ hμ]
      have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 32 * Γ ^ 2 * η * na ^ 2)
      linarith
    have h3 : 32 * Γ ^ 2 * η ^ 2 * Luv ^ 2 * nw ^ 2 ≤ η * μ * nw ^ 2 / 64 := by
      rw [hLuv]
      have g4 : Γ ^ 4 ≤ 1 / 65536 := by
        have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; linarith
      have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 32 * Γ ^ 4 * η * μ * nw ^ 2)
      have := mul_le_mul_of_nonneg_left g4 (by positivity : (0:ℝ) ≤ 4 * η * μ * nw ^ 2)
      nlinarith
    linarith
  have hq : 2 * nY * (nr0 + LJ * η ^ 2 * σu ^ 2) = 2 * nY * nr0 + 2 * nY * (LJ * η ^ 2 * σu ^ 2) := by
    ring
  have e3 : 3 * η * Γ ^ 2 * na ^ 2 / μ + η * (4 * Γ ^ 2) * na ^ 2 / μ + η * Γ ^ 2 * na ^ 2 / μ +
      η * (16 * (LJ * G) ^ 2 / μ ^ 2) * na ^ 2 / μ + η * (Γ * (LJ * G) / μ) * na ^ 2 / μ =
      η * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) * na ^ 2 / μ := by ring
  have e4 : 2 * (2 * nw + η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) =
      4 * LJ * η ^ 2 * σu ^ 2 * nw + 2 * (η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) := by ring
  have : 0 ≤ η * μ * nw ^ 2 := by positivity
  linarith

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma Q_next (x z : E) (η : ℝ) :
    Kᗮ.starProjection (x - η • (gradF K gh φ Jφ A x + z)) =
      Kᗮ.starProjection x + (d0v K gh φ Jφ A η x + -η • Kᗮ.starProjection z) := by
  rw [H.Q_step x η z]
  simp only [d0v, smul_add, smul_sub, neg_smul, neg_sub]
  abel

omit [MeasurableSpace E] [BorelSpace E] in
lemma w_next (x z : E) (η : ℝ) :
    wv K φ (x - η • (gradF K gh φ Jφ A x + z)) =
      Yv K gh φ Jφ A η x -
        η • (K.starProjection z - Jr K Jφ (Kᗮ.starProjection x) (Kᗮ.starProjection z)) -
        (φ (Kᗮ.starProjection x + (d0v K gh φ Jφ A η x + -η • Kᗮ.starProjection z)) -
          φ (Kᗮ.starProjection x) -
          Jφ (Kᗮ.starProjection x) (d0v K gh φ Jφ A η x + -η • Kᗮ.starProjection z)) := by
  have hq := H.Q_next x z η
  rw [H.w_path x η z _ (d0v K gh φ Jφ A η x + -η • Kᗮ.starProjection z) rfl
    (by rw [hq]; abel)]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma d0_norm (x : E) {η : ℝ} (hη0 : 0 ≤ η) :
    ‖d0v K gh φ Jφ A η x‖ ≤ η * (‖ar K gh (Kᗮ.starProjection x)‖ + Luv * ‖wv K φ x‖) := by
  show ‖-(η • (ar K gh (Kᗮ.starProjection x) - ContinuousLinearMap.adjoint
    (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x))))‖ ≤ _
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
  gcongr
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (H.adjJA_norm x))

lemma exp_a {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (y d0 : E) (η : ℝ) :
    Integrable (fun ω => ar K gh (y + (d0 + -η • Kᗮ.starProjection (ζ ω)))) p ∧
      ‖∫ ω, ar K gh (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) ∂p - ar K gh (y + d0)‖ ≤
        ρh * η ^ 2 * σu ^ 2 := by
  set e : Ω → E := fun ω => -η • Kᗮ.starProjection (ζ ω)
  set L : E →L[ℝ] E := (Kᗮ.starProjection.comp (Hh (y + d0))).comp ((-η) • Kᗮ.starProjection)
  set q : Ω → E := fun ω => ar K gh (y + d0 + e ω) - ar K gh (y + d0) -
    Kᗮ.starProjection (Hh (y + d0) (e ω))
  have hdec : ∀ ω, ar K gh (y + (d0 + e ω)) = ar K gh (y + d0) + L (ζ ω) + q ω := by
    intro ω
    simp only [L, q, e, ContinuousLinearMap.comp_apply, smul_apply, add_assoc]
    abel
  have hem : Measurable e := (Kᗮ.starProjection.continuous.measurable.comp N.meas).const_smul _
  have hac : Continuous (ar K gh) :=
    Kᗮ.starProjection.continuous.comp
      (continuous_iff_continuousAt.mpr fun z => (H.hHh z).continuousAt)
  have hqm : Measurable q :=
    ((hac.measurable.comp (measurable_const.add hem)).sub measurable_const).sub
      ((Kᗮ.starProjection.comp (Hh (y + d0))).continuous.measurable.comp hem)
  have hqb : ∀ ω, ‖q ω‖ ≤ ρh * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by
    intro ω
    have := H.ar_taylor (y + d0) (e ω)
    simp only [e, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs] at this
    simp only [q]; linarith
  have hqi : Integrable q p :=
    Integrable.mono' (N.intQ.const_mul (ρh * η ^ 2)) hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall hqb)
  have hLi : Integrable (fun ω => L (ζ ω)) p := L.integrable_comp N.int
  have hint : Integrable (fun ω => ar K gh (y + (d0 + e ω))) p := by
    simp_rw [hdec]; exact ((integrable_const _).add hLi).add hqi
  refine ⟨hint, ?_⟩
  change ‖∫ ω, ar K gh (y + (d0 + e ω)) ∂p - ar K gh (y + d0)‖ ≤ _
  simp_rw [hdec]
  have hc : Integrable (fun ω => ar K gh (y + d0) + L (ζ ω)) p := (integrable_const _).add hLi
  rw [integral_add hc hqi, integral_add (integrable_const _) hLi, N.clm_mean L, integral_const]
  simp only [probReal_univ, one_smul, add_zero, add_sub_cancel_left]
  calc ‖∫ ω, q ω ∂p‖ ≤ ∫ ω, ‖q ω‖ ∂p := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ρh * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p :=
        integral_mono hqi.norm (N.intQ.const_mul _) hqb
    _ = ρh * η ^ 2 * ∫ ω, ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p := integral_const_mul _ _
    _ ≤ ρh * η ^ 2 * σu ^ 2 := mul_le_mul_of_nonneg_left N.varQ (by have := H.ρh_nn; positivity)

lemma a_step {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (x : E) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : 8 * Lh * η ≤ 1) :
    Integrable (fun ω => ‖ar K gh (Kᗮ.starProjection (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2)
      p ∧
    ∫ ω, ‖ar K gh (Kᗮ.starProjection (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2 ∂p ≤
      (1 + 4 * Lh * η) * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 +
        2 * Lh * η * Luv ^ 2 * ‖wv K φ x‖ ^ 2 + η ^ 2 * ((2 * G * ρh + Lh ^ 2) * σu ^ 2) := by
  set y := Kᗮ.starProjection x
  set d0 := d0v K gh φ Jφ A η x
  set z0 := ar K gh (y + d0)
  set F : Ω → E := fun ω => ar K gh (y + (d0 + -η • Kᗮ.starProjection (ζ ω)))
  have hF : ∀ ω, ar K gh (Kᗮ.starProjection (x - η • (gradF K gh φ Jφ A x + ζ ω))) = F ω :=
    fun ω => by rw [H.Q_next x (ζ ω) η]
  simp_rw [hF]
  obtain ⟨hFi, hFE⟩ := H.exp_a N y d0 η
  have hdiff : ∀ ω, ‖F ω - z0‖ ≤ Lh * η * ‖Kᗮ.starProjection (ζ ω)‖ := by
    intro ω
    have := H.ar_sub (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) (y + d0)
    have e : y + (d0 + -η • Kᗮ.starProjection (ζ ω)) - (y + d0) = -η • Kᗮ.starProjection (ζ ω) :=
      by abel
    rw [e, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hη0] at this
    simpa [F, z0, mul_assoc] using this
  have hpath : ∀ ω, ‖F ω‖ ^ 2 ≤ ‖z0‖ ^ 2 + 2 * ⟪z0, F ω - z0⟫ +
      Lh ^ 2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by
    intro ω
    have e : F ω = z0 + (F ω - z0) := by abel
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hdiff ω) 2
    rw [e, norm_add_sq_real]
    simp only [add_sub_cancel_left]
    have e2 : (Lh * η * ‖Kᗮ.starProjection (ζ ω)‖) ^ 2 =
        Lh ^ 2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by ring
    linarith
  have hac : Continuous (ar K gh) :=
    Kᗮ.starProjection.continuous.comp
      (continuous_iff_continuousAt.mpr fun z => (H.hHh z).continuousAt)
  have hFm : Measurable F :=
    hac.measurable.comp (measurable_const.add (measurable_const.add
      ((Kᗮ.starProjection.continuous.measurable.comp N.meas).const_smul _)))
  have hgi : Integrable (fun ω => ‖z0‖ ^ 2 + 2 * ⟪z0, F ω - z0⟫ +
      Lh ^ 2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2) p := by
    have i1 : Integrable (fun ω => 2 * ⟪z0, F ω - z0⟫) p :=
      ((innerSL ℝ z0).integrable_comp (hFi.sub (integrable_const z0))).const_mul 2
    exact ((integrable_const _).add i1).add (N.intQ.const_mul _)
  have hsqi : Integrable (fun ω => ‖F ω‖ ^ 2) p := by
    refine Integrable.mono' (hgi.add (integrable_const (2 * ‖z0‖ ^ 2 + 2 * ‖z0‖ ^ 2)))
      (hFm.norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hpath ω
    have h3 : -2 * ⟪z0, F ω - z0⟫ ≤ ‖z0‖ ^ 2 + ‖F ω - z0‖ ^ 2 := by
      have := abs_real_inner_le_norm z0 (F ω - z0)
      nlinarith [neg_abs_le ⟪z0, F ω - z0⟫, sq_nonneg (‖z0‖ - ‖F ω - z0‖)]
    have h4 : ‖F ω - z0‖ ^ 2 ≤ 2 * ‖F ω‖ ^ 2 + 2 * ‖z0‖ ^ 2 := by
      have := norm_sub_le (F ω) z0
      nlinarith [sq_nonneg (‖F ω‖ - ‖z0‖), norm_nonneg (F ω - z0)]
    have : 0 ≤ Lh ^ 2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by positivity
    show ‖F ω‖ ^ 2 ≤ ‖z0‖ ^ 2 + 2 * ⟪z0, F ω - z0⟫ +
      Lh ^ 2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 + (2 * ‖z0‖ ^ 2 + 2 * ‖z0‖ ^ 2)
    nlinarith
  refine ⟨hsqi, ?_⟩
  have hE : ∫ ω, ‖F ω‖ ^ 2 ∂p ≤ ‖z0‖ ^ 2 + 2 * ‖z0‖ * (ρh * η ^ 2 * σu ^ 2) +
      Lh ^ 2 * η ^ 2 * σu ^ 2 := by
    refine (integral_mono hsqi hgi hpath).trans ?_
    have i1 : Integrable (fun ω => 2 * ⟪z0, F ω - z0⟫) p :=
      ((innerSL ℝ z0).integrable_comp (hFi.sub (integrable_const z0))).const_mul 2
    have i0 : Integrable (fun ω => ‖z0‖ ^ 2 + 2 * ⟪z0, F ω - z0⟫) p := (integrable_const _).add i1
    have hFs : Integrable (fun ω => F ω - z0) p := hFi.sub (integrable_const z0)
    rw [integral_add i0 (N.intQ.const_mul _), integral_add (integrable_const _) i1,
      integral_const, integral_const_mul, integral_const_mul,
      integral_inner hFs z0, integral_sub hFi (integrable_const z0), integral_const]
    simp only [probReal_univ, one_smul]
    have h1 : 2 * ⟪z0, ∫ ω, F ω ∂p - z0⟫ ≤ 2 * ‖z0‖ * (ρh * η ^ 2 * σu ^ 2) := by
      have := real_inner_le_norm z0 (∫ ω, F ω ∂p - z0)
      have h2 := mul_le_mul_of_nonneg_left hFE (norm_nonneg z0)
      linarith
    have h3 := mul_le_mul_of_nonneg_left N.varQ (by positivity : (0:ℝ) ≤ Lh ^ 2 * η ^ 2)
    linarith
  -- deterministic part
  have hz0G : ‖z0‖ ≤ G := H.ar_norm _
  have hd0 := H.d0_norm x hη0
  set a := ar K gh y
  set w := wv K φ x
  have hLh := H.Lh_nn
  have hLuv := H.Luv_nn
  have hz1 : ‖z0‖ ≤ ‖a‖ + Lh * ‖d0‖ := by
    have := H.ar_sub (y + d0) y
    rw [add_sub_cancel_left] at this
    have := norm_sub_norm_le z0 a
    linarith
  set t := Lh * η
  have ht0 : 0 ≤ t := mul_nonneg hLh hη0
  have ht : t ≤ 1 / 8 := by simp only [t]; linarith
  have hz2 : ‖z0‖ ≤ (1 + t) * ‖a‖ + t * (Luv * ‖w‖) := by
    have := mul_le_mul_of_nonneg_left hd0 hLh
    have e : Lh * (η * (‖a‖ + Luv * ‖w‖)) = t * ‖a‖ + t * (Luv * ‖w‖) := by simp only [t]; ring
    linarith
  have hsq : ‖z0‖ ^ 2 ≤ (1 + 4 * t) * ‖a‖ ^ 2 + 2 * t * Luv ^ 2 * ‖w‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hz2 2
    have hX : 0 ≤ ‖a‖ := norm_nonneg _
    have hW : 0 ≤ Luv * ‖w‖ := by positivity
    have h2 : 2 * ((1 + t) * ‖a‖) * (t * (Luv * ‖w‖)) ≤
        t * (1 + t) * (‖a‖ ^ 2 + (Luv * ‖w‖) ^ 2) := by
      have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq ‖a‖ (Luv * ‖w‖))
        (mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 1 + t))
      nlinarith
    have h3 : (1 + t) ^ 2 + t * (1 + t) ≤ 1 + 4 * t := by nlinarith
    have h4 : t * (1 + t) + t ^ 2 ≤ 2 * t := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖a‖)
    have h6 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (Luv * ‖w‖))
    have e : (Luv * ‖w‖) ^ 2 = Luv ^ 2 * ‖w‖ ^ 2 := by ring
    nlinarith
  have hρ : 2 * ‖z0‖ * (ρh * η ^ 2 * σu ^ 2) ≤ 2 * G * ρh * η ^ 2 * σu ^ 2 := by
    have := mul_le_mul_of_nonneg_right hz0G
      (by have := H.ρh_nn; positivity : (0:ℝ) ≤ 2 * (ρh * η ^ 2 * σu ^ 2))
    linarith
  have e2 : t = Lh * η := rfl
  rw [e2] at hsq
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma wv_cont : Continuous (wv K φ) :=
  K.starProjection.continuous.sub (H.φ_cont.comp Kᗮ.starProjection.continuous)

lemma w_exp {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (x : E) (η : ℝ) :
    Integrable (fun ω => ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2) p ∧
    ∫ ω, ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2 ∂p ≤
      ‖Yv K gh φ Jφ A η x‖ ^ 2 + 2 * ‖Yv K gh φ Jφ A η x‖ *
        (‖φ (Kᗮ.starProjection x + d0v K gh φ Jφ A η x) - φ (Kᗮ.starProjection x) -
          Jφ (Kᗮ.starProjection x) (d0v K gh φ Jφ A η x)‖ + LJ * η ^ 2 * σu ^ 2) +
        4 * η ^ 2 * (σv ^ 2 + (Luv / μ) ^ 2 * σu ^ 2) +
        16 * (Luv / μ) ^ 2 * ‖d0v K gh φ Jφ A η x‖ ^ 2 + 16 * (Luv / μ) ^ 2 * η ^ 2 * σu ^ 2 := by
  set y := Kᗮ.starProjection x
  set d0 := d0v K gh φ Jφ A η x
  set Y := Yv K gh φ Jφ A η x
  set Γ := Luv / μ
  set J := Jr K Jφ y
  set Qz : Ω → E := fun ω => Kᗮ.starProjection (ζ ω)
  set Pz : Ω → E := fun ω => K.starProjection (ζ ω)
  set dd : Ω → E := fun ω => d0 + -η • Qz ω
  set r : Ω → E := fun ω => φ (y + dd ω) - φ y - Jφ y (dd ω)
  set ξ : Ω → E := fun ω => Pz ω - J (Qz ω)
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn H.μpos.le
  have hJ : ‖J‖ ≤ Γ := H.Jr_norm y
  have hw' : ∀ ω, wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)) = Y - η • ξ ω - r ω :=
    fun ω => H.w_next x (ζ ω) η
  have hddmem : ∀ ω, dd ω ∈ Kᗮ := by
    intro ω
    refine Kᗮ.add_mem ?_ (Kᗮ.smul_mem _ (Q_mem _))
    show -(η • (ar K gh y - ContinuousLinearMap.adjoint J (A (wv K φ x)))) ∈ Kᗮ
    exact Kᗮ.neg_mem (Kᗮ.smul_mem _ (Kᗮ.sub_mem (Q_mem _) (adjJ_mem Jφ _ _)))
  have hr2 : ∀ ω, ‖r ω‖ ^ 2 ≤ 4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2) := by
    intro ω
    have h1 := H.φ_river y (dd ω) (hddmem ω)
    have h2 : ‖dd ω‖ ^ 2 ≤ 2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2 := by
      have := norm_add_le d0 (-η • Qz ω)
      rw [norm_smul, norm_neg, Real.norm_eq_abs] at this
      have h3 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (‖d0‖ - |η| * ‖Qz ω‖), sq_abs η]
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e : (2 * Γ * ‖dd ω‖) ^ 2 = 4 * Γ ^ 2 * ‖dd ω‖ ^ 2 := by ring
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 4 * Γ ^ 2)
    show ‖φ (y + dd ω) - φ y - Jφ y (dd ω)‖ ^ 2 ≤ _
    linarith
  have hξ2 : ∀ ω, ‖ξ ω‖ ^ 2 ≤ 2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2 := by
    intro ω
    have h1 : ‖J (Qz ω)‖ ≤ Γ * ‖Qz ω‖ :=
      (J.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    have : ‖ξ ω‖ ≤ ‖Pz ω‖ + Γ * ‖Qz ω‖ := (norm_sub_le _ _).trans (add_le_add le_rfl h1)
    have hsq : (‖Pz ω‖ + Γ * ‖Qz ω‖) ^ 2 ≤ 2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Pz ω‖ - Γ * ‖Qz ω‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) this 2).trans hsq
  set U : Ω → ℝ := fun ω => ‖Y‖ ^ 2 - 2 * η * ⟪Y, ξ ω⟫ - 2 * ⟪Y, r ω⟫ +
    (2 * η ^ 2 * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
      2 * (4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)))
  have hpath : ∀ ω, ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2 ≤ U ω := by
    intro ω
    rw [hw' ω]
    have e1 : Y - η • ξ ω - r ω = Y - (η • ξ ω + r ω) := by abel
    rw [e1, norm_sub_sq_real, inner_add_right, inner_smul_right]
    have h2 : ‖η • ξ ω + r ω‖ ^ 2 ≤ 2 * η ^ 2 * ‖ξ ω‖ ^ 2 + 2 * ‖r ω‖ ^ 2 := by
      have := norm_add_le (η • ξ ω) (r ω)
      rw [norm_smul, Real.norm_eq_abs] at this
      have h3 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (|η| * ‖ξ ω‖ - ‖r ω‖), sq_abs η]
    have h4 := mul_le_mul_of_nonneg_left (hξ2 ω) (by positivity : (0:ℝ) ≤ 2 * η ^ 2)
    have h5 := mul_le_mul_of_nonneg_left (hr2 ω) (by norm_num : (0:ℝ) ≤ 2)
    simp only [U]
    linarith
  obtain ⟨hri, hrE⟩ := H.exp_r N y d0 η
  have hQzi : Integrable Qz p := Kᗮ.starProjection.integrable_comp N.int
  set Lξ : E →L[ℝ] E := K.starProjection - J.comp Kᗮ.starProjection
  have hξe : ∀ ω, ξ ω = Lξ (ζ ω) := fun ω => by simp [ξ, Lξ, Pz, Qz]
  have hξi : Integrable ξ p :=
    (Lξ.integrable_comp N.int).congr (Filter.Eventually.of_forall fun ω => (hξe ω).symm)
  have hrI : Integrable r p := hri
  have i1 : Integrable (fun ω => 2 * η * ⟪Y, ξ ω⟫) p :=
    ((innerSL ℝ Y).integrable_comp hξi).const_mul _
  have i2 : Integrable (fun ω => 2 * ⟪Y, r ω⟫) p := ((innerSL ℝ Y).integrable_comp hrI).const_mul _
  have j1 : Integrable (fun ω => 2 * η ^ 2 * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2)) p :=
    ((N.intP.const_mul _).add (N.intQ.const_mul _)).const_mul _
  have j2 : Integrable (fun ω => 2 * (4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2))) p :=
    (((integrable_const _).add (N.intQ.const_mul _)).const_mul _).const_mul _
  have i0 : Integrable (fun ω => ‖Y‖ ^ 2 - 2 * η * ⟪Y, ξ ω⟫) p := (integrable_const _).sub i1
  have i3 : Integrable (fun ω => ‖Y‖ ^ 2 - 2 * η * ⟪Y, ξ ω⟫ - 2 * ⟪Y, r ω⟫) p := i0.sub i2
  have hUi : Integrable U p := i3.add (j1.add j2)
  have hwm : Measurable (fun ω => ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2) :=
    ((H.wv_cont.measurable.comp (measurable_const.sub
      ((measurable_const.add N.meas).const_smul η))).norm).pow_const 2
  have hFi : Integrable (fun ω => ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2) p :=
    Integrable.mono' hUi hwm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpath ω)
  refine ⟨hFi, (integral_mono hFi hUi hpath).trans ?_⟩
  have e1 : ∫ ω, 2 * η * ⟪Y, ξ ω⟫ ∂p = 0 := by
    rw [integral_const_mul]; simp_rw [hξe]; rw [N.inner_mean Lξ Y, mul_zero]
  have e2 : ∫ ω, 2 * ⟪Y, r ω⟫ ∂p = 2 * ⟪Y, ∫ ω, r ω ∂p⟫ := by
    rw [integral_const_mul, integral_inner hrI Y]
  have e3 : ∫ ω, 2 * η ^ 2 * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) ∂p ≤
      4 * η ^ 2 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) := by
    rw [integral_const_mul, integral_add (N.intP.const_mul _) (N.intQ.const_mul _),
      integral_const_mul, integral_const_mul]
    have := N.varP; have := N.varQ
    have k1 := mul_le_mul_of_nonneg_left N.varP (by positivity : (0:ℝ) ≤ 4 * η ^ 2)
    have k2 := mul_le_mul_of_nonneg_left N.varQ (by positivity : (0:ℝ) ≤ 4 * η ^ 2 * Γ ^ 2)
    linarith
  have e4 : ∫ ω, 2 * (4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)) ∂p ≤
      16 * Γ ^ 2 * ‖d0‖ ^ 2 + 16 * Γ ^ 2 * η ^ 2 * σu ^ 2 := by
    rw [integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) (N.intQ.const_mul _), integral_const, integral_const_mul]
    simp only [probReal_univ, one_smul]
    have k := mul_le_mul_of_nonneg_left N.varQ (by positivity : (0:ℝ) ≤ 16 * Γ ^ 2 * η ^ 2)
    linarith
  have e5 : -(2 * ⟪Y, ∫ ω, r ω ∂p⟫) ≤
      2 * ‖Y‖ * (‖φ (y + d0) - φ y - Jφ y d0‖ + LJ * η ^ 2 * σu ^ 2) := by
    have := real_inner_le_norm (-Y) (∫ ω, r ω ∂p)
    rw [inner_neg_left, norm_neg] at this
    have h2 := mul_le_mul_of_nonneg_left hrE (norm_nonneg Y)
    linarith
  have hU : ∫ ω, U ω ∂p = ‖Y‖ ^ 2 - ∫ ω, 2 * η * ⟪Y, ξ ω⟫ ∂p - ∫ ω, 2 * ⟪Y, r ω⟫ ∂p +
      (∫ ω, 2 * η ^ 2 * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) ∂p +
        ∫ ω, 2 * (4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)) ∂p) := by
    show ∫ ω, (‖Y‖ ^ 2 - 2 * η * ⟪Y, ξ ω⟫ - 2 * ⟪Y, r ω⟫ +
      (2 * η ^ 2 * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
        2 * (4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)))) ∂p = _
    have j12 : Integrable (fun ω => 2 * η ^ 2 * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
        2 * (4 * Γ ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2))) p := j1.add j2
    rw [integral_add i3 j12, integral_add j1 j2, integral_sub i0 i2,
      integral_sub (integrable_const _) i1, integral_const]
    simp
  rw [hU, e1, e2]
  linarith

lemma w_step {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (x : E) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : 8 * η * Lv ≤ 1) (hΓ : 16 * Luv ≤ μ) :
    Integrable (fun ω => ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2) p ∧
    ∫ ω, ‖wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))‖ ^ 2 ∂p ≤
      (1 - η * μ / 2) * ‖wv K φ x‖ ^ 2 +
        η * (8 * (Luv / μ) ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Luv / μ * (LJ * G) / μ) *
          ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 / μ +
        η ^ 2 * (4 * (σv ^ 2 + (Luv / μ) ^ 2 * σu ^ 2) + 16 * (Luv / μ) ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Luv / μ * G * LJ * σu ^ 2 / (4 * Lv)) := by
  obtain ⟨hi, hE⟩ := H.w_exp N x η
  refine ⟨hi, hE.trans ?_⟩
  have hμ := H.μpos
  have hΓ0 : 0 ≤ Luv / μ := div_nonneg H.Luv_nn hμ.le
  have hΓ16 : 16 * (Luv / μ) ≤ 1 := by rw [← mul_div_assoc, div_le_one hμ]; exact hΓ
  have hLuv : Luv = Luv / μ * μ := by field_simp
  obtain ⟨hY2, hY1, hd0⟩ := H.hill_bounds x hη0 hη hΓ
  obtain ⟨-, hr2⟩ := H.r0_bounds x hη0
  exact w_real hμ H.μ_le hη0 hη hΓ0 hΓ16 hLuv H.LJ_nn (norm_nonneg _) (H.ar_norm _)
    (norm_nonneg _) hY2 hY1 (norm_nonneg _) hr2 (norm_nonneg _) hd0

end Model

end OracleTemplate.RiverValley
