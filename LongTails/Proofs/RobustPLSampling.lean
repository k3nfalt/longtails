import LongTails.Proofs.RobustPLMoments
import LongTails.Proofs.RobustEstimatorMoments

open MeasureTheory

namespace OracleTemplate.RobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

lemma random_center_heavy_second {C : Ω → E} {X : Ξ → E}
    (hC : Measurable C) (hX : Measurable X) (u : E) {B p : ℝ}
    (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hCi : Integrable (fun ω => ‖C ω - u‖ ^ 4) P)
    (hXi : Integrable (fun ξ => ‖X ξ - u‖ ^ p) Q) :
    Integrable (fun w : Ω × Ξ => ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 2) (P.prod Q) ∧
    (∫ w : Ω × Ξ, ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 2 ∂P.prod Q) ≤
      (3 * B / 2) ^ (2 - p) * (∫ ξ, ‖X ξ - u‖ ^ p ∂Q) +
      36 / B ^ 2 * (∫ ω, ‖C ω - u‖ ^ 4 ∂P) := by
  let a : ℝ := (3 * B / 2) ^ (2 - p)
  let b : ℝ := 36 / B ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hm : Measurable (fun w : Ω × Ξ => centeredClip B (C w.1) (X w.2)) :=
    measurable_centeredClip_joint.comp (measurable_const.prodMk
      ((hC.comp measurable_fst).prodMk (hX.comp measurable_snd)))
  have hdom (w : Ω × Ξ) : ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 2 ≤
      a * ‖X w.2 - u‖ ^ p + b * ‖C w.1 - u‖ ^ 4 := by
    by_cases hc : ‖u - C w.1‖ ≤ B / 2
    · exact (centeredClip_second_moment_pointwise hB.le hp hp2 hc _).trans
        (le_add_of_nonneg_right (mul_nonneg hb (by positivity)))
    · have hc' : B / 2 ≤ ‖C w.1 - u‖ := by
        rw [norm_sub_rev]
        exact (lt_of_not_ge hc).le
      have hh := (centeredClip_bad_moments hB hc' (X w.2)).2.1
      have he : 36 * ‖C w.1 - u‖ ^ 4 / B ^ 2 = b * ‖C w.1 - u‖ ^ 4 := by dsimp [b]; ring
      rw [he] at hh
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg ha (by positivity)))
  have hi := ((hXi.comp_snd P).const_mul a).add ((hCi.comp_fst Q).const_mul b)
  have hy : Integrable (fun w : Ω × Ξ =>
      ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 2) (P.prod Q) := by
    apply hi.mono' ((hm.sub_const u).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom w
  refine ⟨hy, (integral_mono hy hi hdom).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add ((hXi.comp_snd P).const_mul a) ((hCi.comp_fst Q).const_mul b),
    integral_const_mul, integral_const_mul]
  simp only [integral_prod (fun w : Ω × Ξ => ‖X w.2 - u‖ ^ p) (hXi.comp_snd P),
    integral_prod (fun w : Ω × Ξ => ‖C w.1 - u‖ ^ 4) (hCi.comp_fst Q),
    integral_const, probReal_univ, one_smul]
  rfl

lemma random_center_heavy_fourth {C : Ω → E} {X : Ξ → E}
    (hC : Measurable C) (hX : Measurable X) (u : E) {B p : ℝ}
    (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hCi : Integrable (fun ω => ‖C ω - u‖ ^ 4) P)
    (hXi : Integrable (fun ξ => ‖X ξ - u‖ ^ p) Q) :
    Integrable (fun w : Ω × Ξ => ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 4) (P.prod Q) ∧
    (∫ w : Ω × Ξ, ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 4 ∂P.prod Q) ≤
      (3 * B / 2) ^ 2 * ((3 * B / 2) ^ (2 - p) * (∫ ξ, ‖X ξ - u‖ ^ p ∂Q)) +
      81 * (∫ ω, ‖C ω - u‖ ^ 4 ∂P) := by
  let a : ℝ := (3 * B / 2) ^ 2 * (3 * B / 2) ^ (2 - p)
  let b : ℝ := 81
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hm : Measurable (fun w : Ω × Ξ => centeredClip B (C w.1) (X w.2)) :=
    measurable_centeredClip_joint.comp (measurable_const.prodMk
      ((hC.comp measurable_fst).prodMk (hX.comp measurable_snd)))
  have hdom (w : Ω × Ξ) : ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 4 ≤
      a * ‖X w.2 - u‖ ^ p + b * ‖C w.1 - u‖ ^ 4 := by
    by_cases hc : ‖u - C w.1‖ ≤ B / 2
    · exact (show ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 4 ≤ a * ‖X w.2 - u‖ ^ p from by
          simpa only [a, mul_assoc] using centeredClip_fourth_moment_pointwise hB.le hp hp2 hc (X w.2)).trans
        (le_add_of_nonneg_right (mul_nonneg hb (by positivity)))
    · have hc' : B / 2 ≤ ‖C w.1 - u‖ := by
        rw [norm_sub_rev]
        exact (lt_of_not_ge hc).le
      have hh := (centeredClip_bad_moments hB hc' (X w.2)).2.2
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg ha (by positivity)))
  have hi := ((hXi.comp_snd P).const_mul a).add ((hCi.comp_fst Q).const_mul b)
  have hy : Integrable (fun w : Ω × Ξ =>
      ‖centeredClip B (C w.1) (X w.2) - u‖ ^ 4) (P.prod Q) := by
    apply hi.mono' ((hm.sub_const u).norm.pow_const 4).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hdom w
  refine ⟨hy, (integral_mono hy hi hdom).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add ((hXi.comp_snd P).const_mul a) ((hCi.comp_fst Q).const_mul b),
    integral_const_mul, integral_const_mul]
  simp only [integral_prod (fun w : Ω × Ξ => ‖X w.2 - u‖ ^ p) (hXi.comp_snd P),
    integral_prod (fun w : Ω × Ξ => ‖C w.1 - u‖ ^ 4) (hCi.comp_fst Q),
    integral_const, probReal_univ, one_smul]
  dsimp [a, b]
  ring

lemma random_center_heavy_bias [CompleteSpace E] {C : Ω → E} {X : Ξ → E}
    (hC : Measurable C) (hX : Measurable X) (hXi : Integrable X Q) (u : E)
    (hmean : ∫ ξ, X ξ ∂Q = u) {B p : ℝ} (hB : 0 < B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hCi : Integrable (fun ω => ‖C ω - u‖ ^ 4) P)
    (hpi : Integrable (fun ξ => ‖X ξ - u‖ ^ p) Q) :
    Integrable (fun w : Ω × Ξ => centeredClip B (C w.1) (X w.2) - u) (P.prod Q) ∧
    ‖∫ w : Ω × Ξ, centeredClip B (C w.1) (X w.2) - u ∂P.prod Q‖ ≤
      (∫ ξ, ‖X ξ - u‖ ^ p ∂Q) / (B / 2) ^ (p - 1) +
      24 / B ^ 3 * (∫ ω, ‖C ω - u‖ ^ 4 ∂P) := by
  let a := (∫ ξ, ‖X ξ - u‖ ^ p ∂Q) / (B / 2) ^ (p - 1)
  let b := 24 / B ^ 3
  have ha : 0 ≤ a := div_nonneg (integral_nonneg fun _ => by positivity) (by positivity)
  have hb : 0 ≤ b := by positivity
  let Y : Ω × Ξ → E := fun w => centeredClip B (C w.1) (X w.2) - u
  have hY : Measurable Y := (measurable_centeredClip_joint.comp (measurable_const.prodMk
    ((hC.comp measurable_fst).prodMk (hX.comp measurable_snd)))).sub_const u
  have hC1 : Integrable (fun ω => ‖C ω - u‖) P := by
    simpa only [Real.rpow_one] using
      (LongTails.Proofs.StochasticEnvelopeSampling.lower_power_from_fourth
        (hC.sub_const u) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 4) hCi).1
  have hbound (w : Ω × Ξ) : ‖Y w‖ ≤ ‖C w.1 - u‖ + B := by
    have he : Y w = clip B (X w.2 - C w.1) + (C w.1 - u) := by
      dsimp [Y, centeredClip]
      abel
    rw [he]
    exact (norm_add_le _ _).trans (by have := norm_clip_le hB.le (X w.2 - C w.1); linarith)
  have hYi : Integrable Y (P.prod Q) :=
    ((hC1.comp_fst Q).add (integrable_const B)).mono' hY.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hcond (ω : Ω) : ‖∫ ξ, Y (ω, ξ) ∂Q‖ ≤ a + b * ‖C ω - u‖ ^ 4 := by
    by_cases hc : ‖u - C ω‖ ≤ B / 2
    · have hh := centeredClip_heavy_moments hX hXi hmean hB hp hp2 hc hpi le_rfl
      have he : (∫ ξ, Y (ω, ξ) ∂Q) = (∫ ξ, centeredClip B (C ω) (X ξ) ∂Q) - u := by
        dsimp [Y]
        rw [integral_sub hh.1 (integrable_const u)]
        simp
      rw [he]
      exact hh.2.2.2.2.2.trans (le_add_of_nonneg_right (mul_nonneg hb (by positivity)))
    · have hc' : B / 2 ≤ ‖C ω - u‖ := by
        rw [norm_sub_rev]
        exact (lt_of_not_ge hc).le
      have hh := norm_integral_le_of_norm_le
        (integrable_const (b * ‖C ω - u‖ ^ 4) : Integrable (fun _ : Ξ => b * ‖C ω - u‖ ^ 4) Q)
        (f := fun ξ => Y (ω, ξ)) (Filter.Eventually.of_forall fun ξ => by
          have ht := (centeredClip_bad_moments hB hc' (X ξ)).1
          dsimp [Y]
          exact ht.trans_eq (by dsimp [b]; ring))
      simp only [integral_const, probReal_univ, one_smul] at hh
      exact hh.trans (le_add_of_nonneg_left ha)
  refine ⟨hYi, ?_⟩
  change ‖∫ w, Y w ∂P.prod Q‖ ≤ _
  rw [integral_prod _ hYi]
  have hh := norm_integral_le_of_norm_le ((integrable_const a).add (hCi.const_mul b))
    (f := fun ω => ∫ ξ, Y (ω, ξ) ∂Q) (Filter.Eventually.of_forall hcond)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const a) (hCi.const_mul b), integral_const_mul] at hh
  simpa only [integral_const, probReal_univ, one_smul, a, b] using hh

end OracleTemplate.RobustGradient
