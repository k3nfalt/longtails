import LongTails.Proofs.RiverValleyRecursions

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
lemma Aw_real {η μ Lv Γ Luv LJ G σu σv na nw nY nr0 nd0 Ysq : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv)
    (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (hΓ0 : 0 ≤ Γ) (hΓ : 16 * Γ ≤ 1) (hLuv : Luv = Γ * μ)
    (hLJ : 0 ≤ LJ) (hna : 0 ≤ na) (hnaG : na ≤ G) (hnw : 0 ≤ nw)
    (hY : Ysq ≤ (1 - η * μ) * nw ^ 2 + 3 * η * Γ ^ 2 * μ * na ^ 2)
    (hnY' : nY ≤ 2 * nw + η * Γ * μ * na) (hnr0 : 0 ≤ nr0)
    (hnr0b : nr0 ≤ 4 * Lv * LJ * η ^ 2 * na ^ 2 + 4 * Γ * Luv * η * nw) (hnd0 : 0 ≤ nd0)
    (hnd0' : nd0 ≤ η * (na + Γ * nw)) :
    Ysq + 2 * nY * (nr0 + Lv * LJ * η ^ 2 * σu ^ 2) + 4 * η ^ 2 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) +
        16 * Luv ^ 2 * nd0 ^ 2 + 16 * Luv ^ 2 * η ^ 2 * σu ^ 2 ≤
      (1 - η * μ / 2) * nw ^ 2 + η * (8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)) * na ^ 2 +
        η ^ 2 * (4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4) := by
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have hG : 0 ≤ G := hna.trans hnaG
  have hLJG0 : 0 ≤ LJ * G := mul_nonneg hLJ hG
  have hΓ16 : Γ ≤ 1 / 16 := by linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by
    calc Γ ^ 2 = Γ * Γ := sq Γ
      _ ≤ 1 / 16 * (1 / 16) := mul_le_mul hΓ16 hΓ16 hΓ0 (by norm_num)
      _ = 1 / 256 := by norm_num
  have hημ : η * μ ≤ 1 / 8 := by have := mul_le_mul_of_nonneg_left hμLv hη0; linarith
  have hηLv : η * Lv ≤ 1 / 8 := by linarith
  have hη2Lv2 : η ^ 2 * Lv ^ 2 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ (mul_nonneg hη0 hLv.le) hηLv 2
    have e : (η * Lv) ^ 2 = η ^ 2 * Lv ^ 2 := by ring
    linarith
  have hnY0 : 0 ≤ 2 * nw + η * Γ * μ * na := by positivity
  have p1 : 2 * nY * nr0 ≤ 2 * ((2 * nw + η * Γ * μ * na) *
      (4 * Lv * LJ * η ^ 2 * na ^ 2 + 4 * Γ * Luv * η * nw)) := by
    rcases le_total 0 nY with hy | hy
    · have := mul_le_mul hnY' hnr0b hnr0 hnY0; linarith
    · have : 0 ≤ (2 * nw + η * Γ * μ * na) * (4 * Lv * LJ * η ^ 2 * na ^ 2 + 4 * Γ * Luv * η * nw) :=
        mul_nonneg hnY0 (le_trans hnr0 hnr0b)
      nlinarith
  have pa : 2 * (2 * nw * (4 * Lv * LJ * η ^ 2 * na ^ 2)) ≤
      η * μ * nw ^ 2 / 16 + η * (16 * (LJ * G) ^ 2 / μ) * na ^ 2 := by
    have b1 : 2 * (2 * nw * (4 * Lv * LJ * η ^ 2 * na ^ 2)) ≤ 16 * Lv * (LJ * G) * η ^ 2 * na * nw := by
      have := mul_le_mul_of_nonneg_left hnaG
        (by positivity : (0:ℝ) ≤ 16 * Lv * LJ * η ^ 2 * na * nw)
      linear_combination this
    have b2 : 16 * Lv * (LJ * G) * η ^ 2 * na * nw ≤
        η * μ * nw ^ 2 / 16 + 1024 * Lv ^ 2 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ := by
      have h0 : 0 ≤ η / (16 * μ) * (μ * nw - 128 * Lv * (LJ * G) * η * na) ^ 2 := by positivity
      have e : η / (16 * μ) * (μ * nw - 128 * Lv * (LJ * G) * η * na) ^ 2 =
          η * μ * nw ^ 2 / 16 + 1024 * Lv ^ 2 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ -
            16 * Lv * (LJ * G) * η ^ 2 * na * nw := by field_simp; ring
      linarith
    have b3 : 1024 * Lv ^ 2 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ ≤
        η * (16 * (LJ * G) ^ 2 / μ) * na ^ 2 := by
      have e1 : 1024 * Lv ^ 2 * (LJ * G) ^ 2 * η ^ 3 * na ^ 2 / μ =
          (1024 * (LJ * G) ^ 2 * η * na ^ 2 / μ) * (η ^ 2 * Lv ^ 2) := by field_simp
      have e2 : η * (16 * (LJ * G) ^ 2 / μ) * na ^ 2 =
          (1024 * (LJ * G) ^ 2 * η * na ^ 2 / μ) * (1 / 64) := by field_simp; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hη2Lv2 (by positivity)
    linarith
  have pb : 2 * (2 * nw * (4 * Γ * Luv * η * nw)) ≤ η * μ * nw ^ 2 / 16 := by
    rw [hLuv]
    have := mul_le_mul_of_nonneg_left hΓ2 (by positivity : (0:ℝ) ≤ 16 * η * μ * nw ^ 2)
    linarith
  have pc : 2 * (η * Γ * μ * na * (4 * Lv * LJ * η ^ 2 * na ^ 2)) ≤ η * (Γ * (LJ * G)) * na ^ 2 := by
    have b1 : 2 * (η * Γ * μ * na * (4 * Lv * LJ * η ^ 2 * na ^ 2)) ≤
        8 * Γ * (LJ * G) * (η * Lv) * (η * μ) * η * na ^ 2 := by
      have := mul_le_mul_of_nonneg_left hnaG
        (by positivity : (0:ℝ) ≤ 8 * Γ * μ * Lv * LJ * η ^ 3 * na ^ 2)
      linear_combination this
    have b2 : (η * Lv) * (η * μ) ≤ 1 / 64 := by
      have := mul_le_mul hηLv hημ (by positivity) (by norm_num); linarith
    have h3 := mul_le_mul_of_nonneg_left b2 (by positivity : (0:ℝ) ≤ 8 * Γ * (LJ * G) * η * na ^ 2)
    have h4 : 0 ≤ Γ * (LJ * G) * η * na ^ 2 := by positivity
    linarith
  have pd : 2 * (η * Γ * μ * na * (4 * Γ * Luv * η * nw)) ≤
      η * μ * nw ^ 2 / 64 + η * (Γ ^ 2 * μ) * na ^ 2 := by
    rw [hLuv]
    have b1 : 2 * (η * Γ * μ * na * (4 * Γ * (Γ * μ) * η * nw)) ≤ Γ ^ 3 * μ * η * na * nw := by
      have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 8 * Γ ^ 3 * μ * η * na * nw)
      linarith
    have b2 : Γ ^ 3 * μ * η * na * nw ≤ η * μ * nw ^ 2 / 64 + 16 * Γ ^ 6 * μ * η * na ^ 2 := by
      have h0 : 0 ≤ η / (64 * μ) * (μ * nw - 32 * Γ ^ 3 * μ * na) ^ 2 := by positivity
      have e : η / (64 * μ) * (μ * nw - 32 * Γ ^ 3 * μ * na) ^ 2 =
          η * μ * nw ^ 2 / 64 + 16 * Γ ^ 6 * μ * η * na ^ 2 - Γ ^ 3 * μ * η * na * nw := by
        field_simp; ring
      linarith
    have b3 : 16 * Γ ^ 6 * μ * η * na ^ 2 ≤ η * (Γ ^ 2 * μ) * na ^ 2 := by
      have g4 : Γ ^ 4 ≤ 1 / 16 := by
        have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; linarith
      have := mul_le_mul_of_nonneg_left g4 (by positivity : (0:ℝ) ≤ 16 * Γ ^ 2 * μ * η * na ^ 2)
      linear_combination this
    linarith
  have hsplit : 2 * ((2 * nw + η * Γ * μ * na) * (4 * Lv * LJ * η ^ 2 * na ^ 2 + 4 * Γ * Luv * η * nw)) =
      2 * (2 * nw * (4 * Lv * LJ * η ^ 2 * na ^ 2)) + 2 * (2 * nw * (4 * Γ * Luv * η * nw)) +
      2 * (η * Γ * μ * na * (4 * Lv * LJ * η ^ 2 * na ^ 2)) +
      2 * (η * Γ * μ * na * (4 * Γ * Luv * η * nw)) := by ring
  have hY2 : nY ≤ 2 * nw + η * Γ * μ * G :=
    hnY'.trans (by have := mul_le_mul_of_nonneg_left hnaG (by positivity : (0:ℝ) ≤ η * Γ * μ)
                   linarith)
  have q1 : 2 * nY * (Lv * LJ * η ^ 2 * σu ^ 2) ≤
      2 * (2 * nw + η * Γ * μ * G) * (Lv * LJ * η ^ 2 * σu ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have q2 : 4 * Lv * LJ * η ^ 2 * σu ^ 2 * nw ≤
      η * μ * nw ^ 2 / 16 + 64 * Lv ^ 2 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ := by
    have h0 : 0 ≤ η / (16 * μ) * (μ * nw - 32 * Lv * LJ * η * σu ^ 2) ^ 2 := by positivity
    have e : η / (16 * μ) * (μ * nw - 32 * Lv * LJ * η * σu ^ 2) ^ 2 =
        η * μ * nw ^ 2 / 16 + 64 * Lv ^ 2 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ -
          4 * Lv * LJ * η ^ 2 * σu ^ 2 * nw := by field_simp; ring
    linarith
  have q3 : 64 * Lv ^ 2 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ ≤ η ^ 2 * (8 * Lv * LJ ^ 2 * σu ^ 4 / μ) := by
    have e1 : 64 * Lv ^ 2 * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ =
        (64 * Lv * LJ ^ 2 * η ^ 2 * σu ^ 4 / μ) * (η * Lv) := by field_simp
    have e2 : η ^ 2 * (8 * Lv * LJ ^ 2 * σu ^ 4 / μ) =
        (64 * Lv * LJ ^ 2 * η ^ 2 * σu ^ 4 / μ) * (1 / 8) := by field_simp; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hηLv (by positivity)
  have q4 : 2 * (η * Γ * μ * G) * (Lv * LJ * η ^ 2 * σu ^ 2) ≤
      η ^ 2 * (Γ * μ * G * LJ * σu ^ 2 / 4) := by
    have := mul_le_mul_of_nonneg_left hηLv
      (by positivity : (0:ℝ) ≤ 2 * Γ * μ * G * LJ * η ^ 2 * σu ^ 2)
    nlinarith
  have r1 : 16 * Luv ^ 2 * nd0 ^ 2 ≤ η * (4 * Γ ^ 2 * μ) * na ^ 2 + η * μ * nw ^ 2 / 64 := by
    have hd2 : nd0 ^ 2 ≤ 2 * η ^ 2 * (na ^ 2 + Γ ^ 2 * nw ^ 2) := by
      have h1 := pow_le_pow_left₀ hnd0 hnd0' 2
      have hs : (na + Γ * nw) ^ 2 ≤ 2 * (na ^ 2 + Γ ^ 2 * nw ^ 2) := by
        nlinarith [sq_nonneg (na - Γ * nw)]
      have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg η)
      have e : (η * (na + Γ * nw)) ^ 2 = η ^ 2 * (na + Γ * nw) ^ 2 := by ring
      linarith
    rw [hLuv]
    have h1 := mul_le_mul_of_nonneg_left hd2 (by positivity : (0:ℝ) ≤ 16 * (Γ * μ) ^ 2)
    have h2 : 32 * Γ ^ 2 * μ ^ 2 * η ^ 2 * na ^ 2 ≤ η * (4 * Γ ^ 2 * μ) * na ^ 2 := by
      have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 32 * Γ ^ 2 * μ * η * na ^ 2)
      linarith
    have h3 : 32 * Γ ^ 4 * μ ^ 2 * η ^ 2 * nw ^ 2 ≤ η * μ * nw ^ 2 / 64 := by
      have g4 : Γ ^ 4 ≤ 1 / 65536 := by
        have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; linarith
      have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 32 * Γ ^ 4 * η * μ * nw ^ 2)
      have := mul_le_mul_of_nonneg_left g4 (by positivity : (0:ℝ) ≤ 4 * η * μ * nw ^ 2)
      nlinarith
    nlinarith
  have hq : 2 * nY * (nr0 + Lv * LJ * η ^ 2 * σu ^ 2) =
      2 * nY * nr0 + 2 * nY * (Lv * LJ * η ^ 2 * σu ^ 2) := by ring
  have e4 : 2 * (2 * nw + η * Γ * μ * G) * (Lv * LJ * η ^ 2 * σu ^ 2) =
      4 * Lv * LJ * η ^ 2 * σu ^ 2 * nw + 2 * (η * Γ * μ * G) * (Lv * LJ * η ^ 2 * σu ^ 2) := by ring
  have : 0 ≤ η * μ * nw ^ 2 := by positivity
  have e3 : 3 * η * Γ ^ 2 * μ * na ^ 2 + η * (4 * Γ ^ 2 * μ) * na ^ 2 + η * (Γ ^ 2 * μ) * na ^ 2 +
      η * (16 * (LJ * G) ^ 2 / μ) * na ^ 2 + η * (Γ * (LJ * G)) * na ^ 2 =
      η * (8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)) * na ^ 2 := by ring
  linarith

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma AJ_norm (y u : E) : ‖A (Jr K Jφ y u)‖ ≤ Luv * ‖u‖ :=
  (H.cross y u).trans (mul_le_mul_of_nonneg_left (starProj_norm_le _ _) H.Luv_nn)

omit [MeasurableSpace E] [BorelSpace E] in
lemma adjJ_norm (y u : E) : ‖ContinuousLinearMap.adjoint (Jr K Jφ y) u‖ ≤ Luv / μ * ‖u‖ :=
  ((ContinuousLinearMap.adjoint (Jr K Jφ y)).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (by rw [adjoint_norm]; exact H.Jr_norm y) (norm_nonneg _))

omit [MeasurableSpace E] [BorelSpace E] in
lemma Aφ_diff (y d : E) (hd : d ∈ Kᗮ) : ‖A (φ (y + d) - φ y)‖ ≤ Luv * ‖d‖ := by
  have hg : ∀ z, HasFDerivAt (fun z => A (φ z)) (A.comp (Jφ z)) z :=
    fun z => A.hasFDerivAt.comp z (H.hJφ z)
  have hdir : ∀ z, ‖(A.comp (Jφ z)) d‖ ≤ Luv * ‖d‖ := by
    intro z
    have := H.cross z d
    rwa [Q_of_orth hd] at this
  have := diff_le_of_dir hg y d hdir
  simpa [map_sub] using this

omit [MeasurableSpace E] [BorelSpace E] in
lemma Ar_river (y d : E) (hd : d ∈ Kᗮ) : ‖A (φ (y + d) - φ y - Jφ y d)‖ ≤ 2 * Luv * ‖d‖ := by
  have h1 := H.Aφ_diff y d hd
  have h2 : ‖A (Jφ y d)‖ ≤ Luv * ‖d‖ := by
    have := H.cross y d; rwa [Q_of_orth hd] at this
  rw [map_sub]
  calc ‖A (φ (y + d) - φ y) - A (Jφ y d)‖ ≤ ‖A (φ (y + d) - φ y)‖ + ‖A (Jφ y d)‖ := norm_sub_le _ _
    _ ≤ Luv * ‖d‖ + Luv * ‖d‖ := add_le_add h1 h2
    _ = 2 * Luv * ‖d‖ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
lemma Ar_taylor (y d : E) : ‖A (φ (y + d) - φ y - Jφ y d)‖ ≤ Lv * (LJ * ‖d‖ ^ 2) := by
  have hmem : φ (y + d) - φ y - Jφ y d ∈ K :=
    K.sub_mem (K.sub_mem (H.φK _) (H.φK _)) (H.Jφ_mem _ _)
  exact (H.A_upper _ hmem).trans (mul_le_mul_of_nonneg_left (H.φ_taylor y d)
    (le_trans H.μpos.le H.μ_le))

lemma exp_Ar {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (y d0 : E) (η : ℝ) :
    Integrable (fun ω => A (φ (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) - φ y -
        Jφ y (d0 + -η • Kᗮ.starProjection (ζ ω)))) p ∧
      ‖∫ ω, A (φ (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) - φ y -
        Jφ y (d0 + -η • Kᗮ.starProjection (ζ ω))) ∂p - A (φ (y + d0) - φ y - Jφ y d0)‖ ≤
        Lv * LJ * η ^ 2 * σu ^ 2 := by
  have hLv : 0 ≤ Lv := le_trans H.μpos.le H.μ_le
  set e : Ω → E := fun ω => -η • Kᗮ.starProjection (ζ ω)
  set L : E →L[ℝ] E := A.comp ((Jφ (y + d0) - Jφ y).comp ((-η) • Kᗮ.starProjection))
  set q : Ω → E := fun ω => A (φ (y + d0 + e ω) - φ (y + d0) - Jφ (y + d0) (e ω))
  have hdec : ∀ ω, A (φ (y + (d0 + e ω)) - φ y - Jφ y (d0 + e ω)) =
      A (φ (y + d0) - φ y - Jφ y d0) + L (ζ ω) + q ω := by
    intro ω
    simp only [L, q, e, ContinuousLinearMap.comp_apply, smul_apply, sub_apply, map_add,
      map_sub, add_assoc]
    abel
  have hem : Measurable e := (Kᗮ.starProjection.continuous.measurable.comp N.meas).const_smul _
  have hqm : Measurable q :=
    A.continuous.measurable.comp (((H.φ_cont.measurable.comp (measurable_const.add hem)).sub
      measurable_const).sub ((Jφ (y + d0)).continuous.measurable.comp hem))
  have hqb : ∀ ω, ‖q ω‖ ≤ Lv * LJ * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by
    intro ω
    have := H.Ar_taylor (y + d0) (e ω)
    simp only [e, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs] at this
    simp only [q]; linarith
  have hqi : Integrable q p :=
    Integrable.mono' (N.intQ.const_mul (Lv * LJ * η ^ 2)) hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall hqb)
  have hLi : Integrable (fun ω => L (ζ ω)) p := L.integrable_comp N.int
  have hint : Integrable (fun ω => A (φ (y + (d0 + e ω)) - φ y - Jφ y (d0 + e ω))) p := by
    simp_rw [hdec]; exact ((integrable_const _).add hLi).add hqi
  refine ⟨hint, ?_⟩
  change ‖∫ ω, A (φ (y + (d0 + e ω)) - φ y - Jφ y (d0 + e ω)) ∂p - _‖ ≤ _
  simp_rw [hdec]
  have hc : Integrable (fun ω => A (φ (y + d0) - φ y - Jφ y d0) + L (ζ ω)) p :=
    (integrable_const _).add hLi
  rw [integral_add hc hqi, integral_add (integrable_const _) hLi, N.clm_mean L, integral_const]
  simp only [probReal_univ, one_smul, add_zero, add_sub_cancel_left]
  calc ‖∫ ω, q ω ∂p‖ ≤ ∫ ω, ‖q ω‖ ∂p := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, Lv * LJ * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p :=
        integral_mono hqi.norm (N.intQ.const_mul _) hqb
    _ = Lv * LJ * η ^ 2 * ∫ ω, ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p := integral_const_mul _ _
    _ ≤ Lv * LJ * η ^ 2 * σu ^ 2 :=
        mul_le_mul_of_nonneg_left N.varQ (by have := H.LJ_nn; positivity)

omit [MeasurableSpace E] [BorelSpace E] in
lemma hillA_bounds (x : E) {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (hΓ : 16 * Luv ≤ μ) :
    ‖A (Yv K gh φ Jφ A η x)‖ ^ 2 ≤ (1 - η * μ) * ‖A (wv K φ x)‖ ^ 2 +
        3 * η * (Luv / μ) ^ 2 * μ * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 ∧
      ‖A (Yv K gh φ Jφ A η x)‖ ≤ 2 * ‖A (wv K φ x)‖ +
        η * (Luv / μ) * μ * ‖ar K gh (Kᗮ.starProjection x)‖ := by
  set y := Kᗮ.starProjection x
  set w := wv K φ x
  set a := ar K gh y
  set J := Jr K Jφ y
  set v := ContinuousLinearMap.adjoint J (A w)
  set Γ := Luv / μ
  have hμ := H.μpos
  have hμLv := H.μ_le
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn hμ.le
  have hΓ16 : 16 * Γ ≤ 1 := by
    simp only [Γ]; rw [← mul_div_assoc, div_le_one hμ]; exact hΓ
  have hLuv : Luv = Γ * μ := by simp only [Γ]; field_simp
  have hwK : w ∈ K := wv_mem H x
  have hAwK : A w ∈ K := H.A_K w hwK
  have hv : ‖v‖ ≤ Γ * ‖A w‖ := H.adjJ_norm y (A w)
  have hAJv : ‖A (J v)‖ ≤ Γ * Luv * ‖A w‖ := by
    have := H.AJ_norm y v
    have h2 := mul_le_mul_of_nonneg_left hv H.Luv_nn
    linarith
  have hAJa : ‖A (J a)‖ ≤ Γ * (μ * ‖a‖) := by
    have := H.AJ_norm y a
    rw [hLuv] at this; linarith
  have hAAw2 : ‖A (A w)‖ ^ 2 ≤ Lv * ⟪A (A w), A w⟫ := H.A_cocoercive hAwK
  have hAAw : ‖A (A w)‖ ≤ Lv * ‖A w‖ := H.A_upper _ hAwK
  have hD : μ * ‖A w‖ ^ 2 ≤ ⟪A (A w), A w⟫ := H.A_lower _ hAwK
  set z := A w + J v - J a
  have hYz : A (Yv K gh φ Jφ A η x) = A w - η • A z := by
    have : Yv K gh φ Jφ A η x = w - η • z := by
      simp only [Yv, z, smul_sub, smul_add]; abel
    rw [this, map_sub, map_smul]
  have hiwz : ⟪A (A w), A w⟫ - Γ * Luv * ‖A w‖ ^ 2 - Γ * ‖A w‖ * (μ * ‖a‖) ≤ ⟪A w, A z⟫ := by
    simp only [z, map_sub, map_add, inner_sub_right, inner_add_right]
    have e1 : ⟪A w, A (A w)⟫ = ⟪A (A w), A w⟫ := real_inner_comm _ _
    have e2 : -⟪A w, A (J v)⟫ ≤ Γ * Luv * ‖A w‖ ^ 2 := by
      have := abs_real_inner_le_norm (A w) (A (J v))
      have h2 := mul_le_mul_of_nonneg_left hAJv (norm_nonneg (A w))
      have := neg_abs_le ⟪A w, A (J v)⟫
      nlinarith
    have e3 : ⟪A w, A (J a)⟫ ≤ Γ * ‖A w‖ * (μ * ‖a‖) := by
      have := real_inner_le_norm (A w) (A (J a))
      have h2 := mul_le_mul_of_nonneg_left hAJa (norm_nonneg (A w))
      nlinarith
    linarith
  have hnz : ‖A z‖ ^ 2 ≤ 3 * (Lv * ⟪A (A w), A w⟫ + Γ ^ 2 * Luv ^ 2 * ‖A w‖ ^ 2 +
      Γ ^ 2 * (μ * ‖a‖) ^ 2) := by
    have h1 : ‖A z‖ ≤ ‖A (A w)‖ + ‖A (J v)‖ + ‖A (J a)‖ := by
      simp only [z, map_sub, map_add]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have h2 : ‖A z‖ ^ 2 ≤ 3 * (‖A (A w)‖ ^ 2 + ‖A (J v)‖ ^ 2 + ‖A (J a)‖ ^ 2) := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖A (A w)‖ - ‖A (J v)‖), sq_nonneg (‖A (A w)‖ - ‖A (J a)‖),
        sq_nonneg (‖A (J v)‖ - ‖A (J a)‖)]
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hAJv 2
    have h4 := pow_le_pow_left₀ (norm_nonneg _) hAJa 2
    have e3 : (Γ * Luv * ‖A w‖) ^ 2 = Γ ^ 2 * Luv ^ 2 * ‖A w‖ ^ 2 := by ring
    have e4 : (Γ * (μ * ‖a‖)) ^ 2 = Γ ^ 2 * (μ * ‖a‖) ^ 2 := by ring
    linarith
  have hYsq : ‖A (Yv K gh φ Jφ A η x)‖ ^ 2 =
      ‖A w‖ ^ 2 - 2 * η * ⟪A w, A z⟫ + η ^ 2 * ‖A z‖ ^ 2 := by
    rw [hYz, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have key := Y_real hμ hμLv hη0 hη hΓ0 hΓ16 hLuv hD hYsq hiwz hnz
  refine ⟨?_, ?_⟩
  · have e : 3 * η * Γ ^ 2 * (μ * ‖a‖) ^ 2 / μ = 3 * η * Γ ^ 2 * μ * ‖a‖ ^ 2 := by
      field_simp
    linarith
  · rw [hYz]
    have hηLv : η * Lv ≤ 1 / 8 := by linarith
    have hΓLuv : Γ * Luv ≤ Lv := by
      rw [hLuv]; have : Γ ≤ 1 / 16 := by linarith
      nlinarith [mul_le_mul this hμLv hμ.le (by norm_num : (0:ℝ) ≤ 1 / 16)]
    have h1 : ‖A z‖ ≤ (Lv + Γ * Luv) * ‖A w‖ + Γ * μ * ‖a‖ := by
      have : ‖A z‖ ≤ ‖A (A w)‖ + ‖A (J v)‖ + ‖A (J a)‖ := by
        simp only [z, map_sub, map_add]
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      calc ‖A z‖ ≤ ‖A (A w)‖ + ‖A (J v)‖ + ‖A (J a)‖ := this
        _ ≤ Lv * ‖A w‖ + Γ * Luv * ‖A w‖ + Γ * (μ * ‖a‖) := by gcongr
        _ = _ := by ring
    calc ‖A w - η • A z‖ ≤ ‖A w‖ + η * ‖A z‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
      _ ≤ ‖A w‖ + η * ((Lv + Γ * Luv) * ‖A w‖ + Γ * μ * ‖a‖) := by gcongr
      _ ≤ 2 * ‖A w‖ + η * Γ * μ * ‖a‖ := by
          have hh := mul_le_mul_of_nonneg_left hΓLuv hη0
          have := mul_le_mul_of_nonneg_left (by linarith : η * (Lv + Γ * Luv) ≤ 1)
            (norm_nonneg (A w))
          nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma Ar0_bounds (x : E) {η : ℝ} (hη0 : 0 ≤ η) :
    ‖A (φ (Kᗮ.starProjection x + d0v K gh φ Jφ A η x) - φ (Kᗮ.starProjection x) -
        Jφ (Kᗮ.starProjection x) (d0v K gh φ Jφ A η x))‖ ≤
      4 * Lv * LJ * η ^ 2 * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 +
        4 * (Luv / μ) * Luv * η * ‖A (wv K φ x)‖ ∧
      ‖d0v K gh φ Jφ A η x‖ ≤
        η * (‖ar K gh (Kᗮ.starProjection x)‖ + Luv / μ * ‖A (wv K φ x)‖) := by
  set y := Kᗮ.starProjection x
  set d0 := d0v K gh φ Jφ A η x
  set a := ar K gh y
  set v := ContinuousLinearMap.adjoint (Jr K Jφ y) (A (wv K φ x))
  have hv : ‖v‖ ≤ Luv / μ * ‖A (wv K φ x)‖ := H.adjJ_norm y _
  have hd0 : d0 = -(η • (a - v)) := rfl
  have hmem : d0 ∈ Kᗮ := by
    rw [hd0]; exact Kᗮ.neg_mem (Kᗮ.smul_mem _ (Kᗮ.sub_mem (Q_mem _) (adjJ_mem Jφ _ _)))
  have hnd : ‖d0‖ ≤ η * (‖a‖ + ‖v‖) := by
    rw [hd0, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
    gcongr; exact norm_sub_le _ _
  have hLv : 0 ≤ Lv := le_trans H.μpos.le H.μ_le
  have hΓ0 : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  refine ⟨?_, hnd.trans (by gcongr)⟩
  have t1 := H.Ar_taylor y d0
  have t2 := H.Ar_river y d0 hmem
  rcases le_total ‖v‖ ‖a‖ with hva | hav
  · have h1 : ‖d0‖ ≤ 2 * η * ‖a‖ := by nlinarith
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hLv H.LJ_nn)
    have : 0 ≤ 4 * (Luv / μ) * Luv * η * ‖A (wv K φ x)‖ := by
      have := H.Luv_nn; positivity
    nlinarith
  · have h1 : ‖d0‖ ≤ 2 * η * (Luv / μ * ‖A (wv K φ x)‖) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by have := H.Luv_nn; positivity : (0:ℝ) ≤ 2 * Luv)
    have : 0 ≤ 4 * Lv * LJ * η ^ 2 * ‖a‖ ^ 2 := by have := H.LJ_nn; positivity
    nlinarith

lemma Aw_exp {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (x : E) (η : ℝ) :
    Integrable (fun ω => ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2) p ∧
    ∫ ω, ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2 ∂p ≤
      ‖A (Yv K gh φ Jφ A η x)‖ ^ 2 + 2 * ‖A (Yv K gh φ Jφ A η x)‖ *
        (‖A (φ (Kᗮ.starProjection x + d0v K gh φ Jφ A η x) - φ (Kᗮ.starProjection x) -
          Jφ (Kᗮ.starProjection x) (d0v K gh φ Jφ A η x))‖ + Lv * LJ * η ^ 2 * σu ^ 2) +
        4 * η ^ 2 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) +
        16 * Luv ^ 2 * ‖d0v K gh φ Jφ A η x‖ ^ 2 + 16 * Luv ^ 2 * η ^ 2 * σu ^ 2 := by
  set y := Kᗮ.starProjection x
  set d0 := d0v K gh φ Jφ A η x
  set AY := A (Yv K gh φ Jφ A η x)
  set J := Jr K Jφ y
  set Qz : Ω → E := fun ω => Kᗮ.starProjection (ζ ω)
  set Pz : Ω → E := fun ω => K.starProjection (ζ ω)
  set dd : Ω → E := fun ω => d0 + -η • Qz ω
  set r : Ω → E := fun ω => A (φ (y + dd ω) - φ y - Jφ y (dd ω))
  set ξ : Ω → E := fun ω => A (Pz ω - J (Qz ω))
  have hLuv0 := H.Luv_nn
  have hw' : ∀ ω, A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω))) = AY - η • ξ ω - r ω := by
    intro ω; rw [H.w_next x (ζ ω) η, map_sub, map_sub, map_smul]
  have hddmem : ∀ ω, dd ω ∈ Kᗮ := by
    intro ω
    refine Kᗮ.add_mem ?_ (Kᗮ.smul_mem _ (Q_mem _))
    show -(η • (ar K gh y - ContinuousLinearMap.adjoint J (A (wv K φ x)))) ∈ Kᗮ
    exact Kᗮ.neg_mem (Kᗮ.smul_mem _ (Kᗮ.sub_mem (Q_mem _) (adjJ_mem Jφ _ _)))
  have hr2 : ∀ ω, ‖r ω‖ ^ 2 ≤ 4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2) := by
    intro ω
    have h1 := H.Ar_river y (dd ω) (hddmem ω)
    have h2 : ‖dd ω‖ ^ 2 ≤ 2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2 := by
      have := norm_add_le d0 (-η • Qz ω)
      rw [norm_smul, norm_neg, Real.norm_eq_abs] at this
      have h3 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (‖d0‖ - |η| * ‖Qz ω‖), sq_abs η]
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e : (2 * Luv * ‖dd ω‖) ^ 2 = 4 * Luv ^ 2 * ‖dd ω‖ ^ 2 := by ring
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 4 * Luv ^ 2)
    show ‖A (φ (y + dd ω) - φ y - Jφ y (dd ω))‖ ^ 2 ≤ _
    linarith
  have hLv : 0 ≤ Lv := le_trans H.μpos.le H.μ_le
  have hξ2 : ∀ ω, ‖ξ ω‖ ^ 2 ≤ 2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2 := by
    intro ω
    have h1 : ‖A (J (Qz ω))‖ ≤ Luv * ‖Qz ω‖ := H.AJ_norm y _
    have h0 : ‖A (Pz ω)‖ ≤ Lv * ‖Pz ω‖ := H.A_upper _ (K.starProjection_apply_mem _)
    have : ‖ξ ω‖ ≤ Lv * ‖Pz ω‖ + Luv * ‖Qz ω‖ := by
      rw [show ξ ω = A (Pz ω) - A (J (Qz ω)) from map_sub _ _ _]
      exact (norm_sub_le _ _).trans (add_le_add h0 h1)
    have hsq : (Lv * ‖Pz ω‖ + Luv * ‖Qz ω‖) ^ 2 ≤
        2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2 := by
      nlinarith [sq_nonneg (Lv * ‖Pz ω‖ - Luv * ‖Qz ω‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) this 2).trans hsq
  set U : Ω → ℝ := fun ω => ‖AY‖ ^ 2 - 2 * η * ⟪AY, ξ ω⟫ - 2 * ⟪AY, r ω⟫ +
    (2 * η ^ 2 * (2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2) +
      2 * (4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)))
  have hpath : ∀ ω, ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2 ≤ U ω := by
    intro ω
    rw [hw' ω]
    have e1 : AY - η • ξ ω - r ω = AY - (η • ξ ω + r ω) := by abel
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
  obtain ⟨hri, hrE⟩ := H.exp_Ar N y d0 η
  set Lξ : E →L[ℝ] E := A.comp (K.starProjection - J.comp Kᗮ.starProjection)
  have hξe : ∀ ω, ξ ω = Lξ (ζ ω) := fun ω => by
    simp [ξ, Lξ, Pz, Qz, map_sub]
  have hξi : Integrable ξ p :=
    (Lξ.integrable_comp N.int).congr (Filter.Eventually.of_forall fun ω => (hξe ω).symm)
  have hrI : Integrable r p := hri
  have i1 : Integrable (fun ω => 2 * η * ⟪AY, ξ ω⟫) p :=
    ((innerSL ℝ AY).integrable_comp hξi).const_mul _
  have i2 : Integrable (fun ω => 2 * ⟪AY, r ω⟫) p :=
    ((innerSL ℝ AY).integrable_comp hrI).const_mul _
  have j1 : Integrable (fun ω => 2 * η ^ 2 * (2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2)) p :=
    ((N.intP.const_mul _).add (N.intQ.const_mul _)).const_mul _
  have j2 : Integrable (fun ω => 2 * (4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2))) p :=
    (((integrable_const _).add (N.intQ.const_mul _)).const_mul _).const_mul _
  have j12 : Integrable (fun ω => 2 * η ^ 2 * (2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2) +
      2 * (4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2))) p := j1.add j2
  have i0 : Integrable (fun ω => ‖AY‖ ^ 2 - 2 * η * ⟪AY, ξ ω⟫) p := (integrable_const _).sub i1
  have i3 : Integrable (fun ω => ‖AY‖ ^ 2 - 2 * η * ⟪AY, ξ ω⟫ - 2 * ⟪AY, r ω⟫) p := i0.sub i2
  have hUi : Integrable U p := i3.add j12
  have hwm : Measurable (fun ω => ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2) :=
    (((A.continuous.comp H.wv_cont).measurable.comp (measurable_const.sub
      ((measurable_const.add N.meas).const_smul η))).norm).pow_const 2
  have hFi : Integrable (fun ω => ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2) p :=
    Integrable.mono' hUi hwm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpath ω)
  refine ⟨hFi, (integral_mono hFi hUi hpath).trans ?_⟩
  have e1 : ∫ ω, 2 * η * ⟪AY, ξ ω⟫ ∂p = 0 := by
    rw [integral_const_mul]; simp_rw [hξe]; rw [N.inner_mean Lξ AY, mul_zero]
  have e2 : ∫ ω, 2 * ⟪AY, r ω⟫ ∂p = 2 * ⟪AY, ∫ ω, r ω ∂p⟫ := by
    rw [integral_const_mul, integral_inner hrI AY]
  have e3 : ∫ ω, 2 * η ^ 2 * (2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2) ∂p ≤
      4 * η ^ 2 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) := by
    rw [integral_const_mul, integral_add (N.intP.const_mul _) (N.intQ.const_mul _),
      integral_const_mul, integral_const_mul]
    have k1 := mul_le_mul_of_nonneg_left N.varP (by positivity : (0:ℝ) ≤ 4 * η ^ 2 * Lv ^ 2)
    have k2 := mul_le_mul_of_nonneg_left N.varQ (by positivity : (0:ℝ) ≤ 4 * η ^ 2 * Luv ^ 2)
    linarith
  have e4 : ∫ ω, 2 * (4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)) ∂p ≤
      16 * Luv ^ 2 * ‖d0‖ ^ 2 + 16 * Luv ^ 2 * η ^ 2 * σu ^ 2 := by
    rw [integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) (N.intQ.const_mul _), integral_const, integral_const_mul]
    simp only [probReal_univ, one_smul]
    have k := mul_le_mul_of_nonneg_left N.varQ (by positivity : (0:ℝ) ≤ 16 * Luv ^ 2 * η ^ 2)
    linarith
  have e5 : -(2 * ⟪AY, ∫ ω, r ω ∂p⟫) ≤
      2 * ‖AY‖ * (‖A (φ (y + d0) - φ y - Jφ y d0)‖ + Lv * LJ * η ^ 2 * σu ^ 2) := by
    have h1 := real_inner_le_norm (-AY) (∫ ω, r ω ∂p)
    rw [inner_neg_left, norm_neg] at h1
    have h2 : ‖∫ ω, r ω ∂p‖ ≤ ‖A (φ (y + d0) - φ y - Jφ y d0)‖ + Lv * LJ * η ^ 2 * σu ^ 2 := by
      have := norm_sub_norm_le (∫ ω, r ω ∂p) (A (φ (y + d0) - φ y - Jφ y d0))
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg AY)
    linarith
  have hU : ∫ ω, U ω ∂p = ‖AY‖ ^ 2 - ∫ ω, 2 * η * ⟪AY, ξ ω⟫ ∂p - ∫ ω, 2 * ⟪AY, r ω⟫ ∂p +
      (∫ ω, 2 * η ^ 2 * (2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2) ∂p +
        ∫ ω, 2 * (4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)) ∂p) := by
    show ∫ ω, (‖AY‖ ^ 2 - 2 * η * ⟪AY, ξ ω⟫ - 2 * ⟪AY, r ω⟫ +
      (2 * η ^ 2 * (2 * Lv ^ 2 * ‖Pz ω‖ ^ 2 + 2 * Luv ^ 2 * ‖Qz ω‖ ^ 2) +
        2 * (4 * Luv ^ 2 * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2)))) ∂p = _
    rw [integral_add i3 j12, integral_add j1 j2, integral_sub i0 i2,
      integral_sub (integrable_const _) i1, integral_const]
    simp
  rw [hU, e1, e2]
  linarith

lemma Aw_step {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (x : E) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : 8 * η * Lv ≤ 1) (hΓ : 16 * Luv ≤ μ) :
    Integrable (fun ω => ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2) p ∧
    ∫ ω, ‖A (wv K φ (x - η • (gradF K gh φ Jφ A x + ζ ω)))‖ ^ 2 ∂p ≤
      (1 - η * μ / 2) * ‖A (wv K φ x)‖ ^ 2 +
        η * (8 * (Luv / μ) ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Luv / μ * (LJ * G)) *
          ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 +
        η ^ 2 * (4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Luv / μ * μ * G * LJ * σu ^ 2 / 4) := by
  obtain ⟨hi, hE⟩ := H.Aw_exp N x η
  refine ⟨hi, hE.trans ?_⟩
  have hμ := H.μpos
  have hΓ0 : 0 ≤ Luv / μ := div_nonneg H.Luv_nn hμ.le
  have hΓ16 : 16 * (Luv / μ) ≤ 1 := by rw [← mul_div_assoc, div_le_one hμ]; exact hΓ
  have hLuv : Luv = Luv / μ * μ := by field_simp
  obtain ⟨hY2, hY1⟩ := H.hillA_bounds x hη0 hη hΓ
  obtain ⟨hr, hd0⟩ := H.Ar0_bounds x hη0
  have hr' : ‖A (φ (Kᗮ.starProjection x + d0v K gh φ Jφ A η x) - φ (Kᗮ.starProjection x) -
      Jφ (Kᗮ.starProjection x) (d0v K gh φ Jφ A η x))‖ ≤
      4 * Lv * LJ * η ^ 2 * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 +
        4 * (Luv / μ) * Luv * η * ‖A (wv K φ x)‖ := hr
  exact Aw_real hμ H.μ_le hη0 hη hΓ0 hΓ16 hLuv H.LJ_nn (norm_nonneg _) (H.ar_norm _)
    (norm_nonneg _) hY2 hY1 (norm_nonneg _) hr' (norm_nonneg _) hd0

end Model

end OracleTemplate.RiverValley
