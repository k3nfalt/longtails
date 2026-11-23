import LongTails.Proofs.RobustCenteredClipping
import LongTails.Proofs.AdaptivePilotConfidence
import LongTails.Setups.DistributedContaminatedSmoothNonconvex

open MeasureTheory
open OracleTemplate.RobustGradient
open LongTails.Setups.DistributedContaminatedSmoothNonconvex

namespace LongTails.Proofs.DistributedContaminationMoments

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_mixture {μ ν : Measure Ω} {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1)
    {Y : Ω → E} (hμ : Integrable Y μ) (hν : Integrable Y ν) :
    (∫ ω, Y ω ∂mixture η μ ν) = (1 - η) • (∫ ω, Y ω ∂μ) + η • (∫ ω, Y ω ∂ν) := by
  rw [mixture, integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hν.smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, ENNReal.toReal_ofReal hη, ENNReal.toReal_ofReal (sub_nonneg.mpr hη')]

section Moments

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma mixture_probability {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) :
    IsProbabilityMeasure (mixture η μ ν) := by
  constructor
  simp only [mixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one, ← ENNReal.ofReal_add (sub_nonneg.mpr hη') hη, sub_add_cancel, ENNReal.ofReal_one]

omit [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma contaminated_pilot {X : Ω → V} (hX : Measurable X) {u : V} {σ η : ℝ}
    (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hη' : η ≤ 1 / 16)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) μ)
    (hv : (∫ ω, ‖X ω - u‖ ^ 2 ∂μ) ≤ σ ^ 2) (k : ℕ) :
    (Measure.pi fun _ : Fin k => mixture η μ ν)
      {ξ | 12 * σ < ‖pilotCenter (24 * σ) (fun i => X (ξ i)) - u‖} ≤
        ENNReal.ofReal ((3 / 4 : ℝ) ^ k) := by
  let A := {ω | 4 * σ < ‖X ω - u‖}
  have hclean : μ.real A ≤ 1 / 16 := by
    rcases hσ.eq_or_lt with hz | hp
    · subst σ
      have he := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg ‖X ω-u‖) hi).mp
        (le_antisymm (by simpa using hv) (integral_nonneg fun _ => sq_nonneg _))
      have hna : ∀ᵐ ω ∂μ, ω ∉ A := by
        filter_upwards [he] with ω hω
        change ¬ 4 * 0 < ‖X ω - u‖
        change ‖X ω-u‖ ^ 2 = 0 at hω
        nlinarith
      have hn : μ A = 0 := by simpa using ae_iff.mp hna
      simp [measureReal_def, hn]
    · apply (norm_tail_le_second_moment (X := fun ω => X ω - u) hi
        (show 0 < 4 * σ by positivity) hv).trans
      apply (div_le_iff₀ (by positivity)).mpr
      ring_nf
      rfl
  let _ := mixture_probability (μ := μ) (ν := ν) hη (by linarith)
  have hm : (mixture η μ ν).real A ≤ 1 / 8 := by
    rw [mixture, measureReal_add_apply (by simp only [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (by simp only [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), measureReal_ennreal_smul_apply,
      measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal hη]
    have h1 := mul_le_of_le_one_left (measureReal_nonneg (μ := μ) (s := A)) (show 1-η ≤ 1 by linarith)
    have h2 := mul_le_mul_of_nonneg_left (measureReal_le_one (μ := ν) (s := A)) hη
    linarith
  have hh := pilotCenter_failure_probability_le (P := mixture η μ ν) hX u (24 * σ)
    (θ := 1 / 8) (by norm_num) (by norm_num) (by rw [show 24 * σ / 6 = 4 * σ by ring]; exact hm) k
  rw [show 24 * σ / 2 = 12 * σ by ring] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
    (show 0 ≤ 2 * Real.sqrt (1 / 8 : ℝ) by positivity)
    (show 2 * Real.sqrt (1 / 8 : ℝ) ≤ 3 / 4 by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 8 by norm_num)]) k))

lemma clipped_mixture {X : Ω → V} (hX : Measurable X) (hXi : Integrable X μ)
    {u c : V} (hmean : ∫ ω, X ω ∂μ = u) {B σ η : ℝ} (hB0 : 0 ≤ B)
    (hc : ‖u - c‖ ≤ B / 2) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (h2i : Integrable (fun ω => ‖X ω - u‖ ^ 2) μ)
    (h2 : (∫ ω, ‖X ω - u‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    let Z := fun ω => centeredClip B c (X ω) - u
    Integrable Z (mixture η μ ν) ∧
      Integrable (fun ω => ‖Z ω‖ ^ 2) (mixture η μ ν) ∧
      ‖∫ ω, Z ω ∂mixture η μ ν‖ ≤ 2 * σ ^ 2 / B + η * (3 * B / 2) ∧
      (∫ ω, ‖Z ω‖ ^ 2 ∂mixture η μ ν) ≤ σ ^ 2 + η * (3 * B / 2) ^ 2 := by
  rcases hB0.eq_or_lt with hzero | hB
  · subst B
    have hcu : u = c := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hc))
    subst c
    have he (ω) : centeredClip 0 u (X ω) - u = 0 := by
      have h := norm_le_zero_iff.mp (OracleTemplate.norm_clip_le (le_refl (0 : ℝ)) (X ω-u))
      simp [centeredClip, h]
    simp [he, sq_nonneg]
  let Z := fun ω => centeredClip B c (X ω) - u
  have hm : Measurable Z := ((measurable_centeredClip B c).comp hX).sub_const u
  have hbound (ω) : ‖Z ω‖ ≤ 3 * B / 2 := centeredClip_error_bounded hB.le hc _
  have hzi : Integrable Z ν := Integrable.of_bound hm.aestronglyMeasurable _
    (Filter.Eventually.of_forall hbound)
  have hsquare (ω) : ‖Z ω‖ ^ 2 ≤ (3 * B / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2
  have hsi : Integrable (fun ω => ‖Z ω‖ ^ 2) ν :=
    Integrable.of_bound ((hm.norm.pow_const 2).aestronglyMeasurable) _
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hsquare ω))
  obtain ⟨hYi, hY2i, hY2, hYbias⟩ := centeredClip_moments hX hXi hmean hB hc h2i h2
  have hclean : Integrable Z μ := hYi.sub (integrable_const u)
  have hbad : ‖∫ ω, Z ω ∂ν‖ ≤ 3 * B / 2 := by
    simpa using norm_integral_le_of_norm_le (integrable_const (μ := ν) (3 * B / 2))
      (Filter.Eventually.of_forall hbound)
  have hgood : ‖∫ ω, Z ω ∂μ‖ ≤ 2 * σ ^ 2 / B := by
    simpa [Z, integral_sub hYi (integrable_const u)] using hYbias
  have hbad2 : (∫ ω, ‖Z ω‖ ^ 2 ∂ν) ≤ (3 * B / 2) ^ 2 := by
    simpa using integral_mono hsi (integrable_const (μ := ν) ((3 * B / 2) ^ 2)) hsquare
  refine ⟨(hclean.smul_measure ENNReal.ofReal_ne_top).add_measure (hzi.smul_measure ENNReal.ofReal_ne_top),
    (hY2i.smul_measure ENNReal.ofReal_ne_top).add_measure (hsi.smul_measure ENNReal.ofReal_ne_top), ?_, ?_⟩
  · change ‖∫ ω, Z ω ∂mixture η μ ν‖ ≤ _
    rw [integral_mixture hη hη' hclean hzi]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hη,
      abs_of_nonneg (sub_nonneg.mpr hη')]
    exact add_le_add ((mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans hgood)
      (mul_le_mul_of_nonneg_left hbad hη)
  · change (∫ ω, ‖Z ω‖ ^ 2 ∂mixture η μ ν) ≤ _
    rw [integral_mixture hη hη' hY2i hsi, smul_eq_mul, smul_eq_mul]
    exact add_le_add ((mul_le_of_le_one_left (integral_nonneg (fun _ => sq_nonneg _))
      (by linarith : 1 - η ≤ 1)).trans hY2) (mul_le_mul_of_nonneg_left hbad2 hη)

end Moments

end LongTails.Proofs.DistributedContaminationMoments
