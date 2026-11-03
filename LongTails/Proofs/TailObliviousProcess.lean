import LongTails.Proofs.TailObliviousStage
import LongTails.Proofs.TailObliviousAnchoring
import LongTails.Proofs.QuadraticNoiseMoments
import LongTails.Proofs.AdaptiveIID
import Mathlib.Analysis.MeanInequalities

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.TailObliviousProcess

open LongTails.Setups.TailObliviousMonotoneRootFinding
open LongTails.Algorithms.TailObliviousExtragradient
open TailObliviousAnchoring TailObliviousStage
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

variable {d : Public} {Ω : Type*} [MeasurableSpace Ω]

structure Problem (d : Public) (F : d.E → d.E) : Prop where
  pos : 0 < d.L
  mono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫
  lip : ∀ x y, ‖F x - F y‖ ≤ d.L * ‖x - y‖

noncomputable def root {F : d.E → d.E} (hF : Problem d F) (k j : ℕ) (b : d.E) : d.E :=
  anchoredRoot F hF.mono d.L hF.lip hF.pos.le (strength d k j) (strength_pos d hF.pos k j) b

lemma root_equation {F : d.E → d.E} (hF : Problem d F) (k j : ℕ) (b : d.E) :
    F (root hF k j b) + strength d k j • root hF k j b - b = 0 :=
  anchoredRoot_equation F hF.mono d.L hF.lip hF.pos.le _ _ b

lemma root_continuous {F : d.E → d.E} (hF : Problem d F) (k j : ℕ) :
    Continuous (root hF k j) :=
  (anchoredRoot_lipschitz F hF.mono d.L hF.lip hF.pos.le _ (strength_pos d hF.pos k j)).continuous

noncomputable def energy {F : d.E → d.E} (hF : Problem d F) (α : ℝ) (k : ℕ)
    (s : ℕ × d.E × d.E) : ℝ :=
  strength d k s.1 ^ α * ‖s.2.2 - root hF k s.1 s.2.1‖ ^ α

lemma energy_nonneg {F : d.E → d.E} (hF : Problem d F) (α : ℝ) (k : ℕ)
    (s : ℕ × d.E × d.E) : 0 ≤ energy hF α k s := by
  unfold energy
  exact mul_nonneg (Real.rpow_nonneg (strength_pos d hF.pos k s.1).le _)
    (Real.rpow_nonneg (norm_nonneg _) _)

lemma energy_measurable {F : d.E → d.E} (hF : Problem d F) (α : ℝ) (k : ℕ) :
    Measurable (energy hF α k) := by
  apply measurable_from_prod_countable_right
  intro j
  have hr := (root_continuous hF k j).measurable
  change Measurable (fun s : d.E × d.E =>
    strength d k j ^ α * ‖s.2 - root hF k j s.1‖ ^ α)
  fun_prop

lemma next_root_distance {F : d.E → d.E} (hF : Problem d F) (k j : ℕ) (b z : d.E) :
    ‖z - root hF k (j + 1) (b + strength d k j • z)‖ ≤
      (3 / 2 : ℝ) * ‖z - root hF k j b‖ := by
  have hn := root_equation hF k (j + 1) (b + strength d k j • z)
  rw [strength_succ] at hn
  have hm := doubled_anchor_root_movement F hF.mono (strength d k j) (strength_pos d hF.pos k j)
    b z (root hF k j b) (root hF k (j + 1) (b + strength d k j • z))
    (root_equation hF k j b) hn
  have ht := norm_sub_le_norm_sub_add_norm_sub z (root hF k j b)
    (root hF k (j + 1) (b + strength d k j • z))
  linarith

lemma next_energy_bound {F : d.E → d.E} (hF : Problem d F) (α : ℝ) (hα1 : 1 < α)
    (hα2 : α ≤ 2) (k j : ℕ) (b z : d.E) :
    energy hF α k (j + 1, b + strength d k j • z, z) ≤
      9 * (strength d k j ^ α * ‖z - root hF k j b‖ ^ α) := by
  have hn := next_root_distance hF k j b z
  have ha := strength_pos d hF.pos k j
  unfold energy
  simp only [strength_succ]
  have h1 : (2 * strength d k j) ^ α * ‖z - root hF k (j + 1) (b + strength d k j • z)‖ ^ α =
      (2 * strength d k j * ‖z - root hF k (j + 1) (b + strength d k j • z)‖) ^ α := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
  have h2 : (2 * strength d k j * ‖z - root hF k (j + 1) (b + strength d k j • z)‖) ≤
      3 * (strength d k j * ‖z - root hF k j b‖) := by nlinarith
  have h3 : (3 * (strength d k j * ‖z - root hF k j b‖)) ^ α =
      3 ^ α * (strength d k j ^ α * ‖z - root hF k j b‖ ^ α) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow ha.le (norm_nonneg _)]
  have h9 : (3 : ℝ) ^ α ≤ 9 := by
    calc (3 : ℝ) ^ α ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα2
      _ = 9 := by norm_num
  rw [h1]
  calc _ ≤ (3 * (strength d k j * ‖z - root hF k j b‖)) ^ α :=
        Real.rpow_le_rpow (by positivity) h2 (by linarith)
    _ = _ := h3
    _ ≤ _ := mul_le_mul_of_nonneg_right h9 (by positivity)

set_option maxHeartbeats 4000000 in
lemma epochAdvance_measurable (g : d.E → Ω → d.E) (hg : Measurable (Function.uncurry g))
    (k : ℕ) : Measurable (Function.uncurry (epochAdvance d g k)) := by
  have hslice (j : ℕ) : Measurable
      (fun w : (d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω) =>
        epochAdvance d g k (j, w.1) w.2) := by
    have hz0 := stageRun_parameter_measurable g hg k j
    have hpair : Measurable (fun w : (d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω) =>
        ((w.1.1, w.1.2, w.2) : d.E × d.E × (Fin (innerSteps k) → Fin 2 → Ω))) := by
      fun_prop
    have hz : Measurable (fun w : (d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω) =>
        stageRun d g k j w.1.1 w.1.2 w.2) := Measurable.comp hz0 hpair
    have hb : Measurable (fun w : (d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω) =>
        w.1.1 + strength d k j • stageRun d g k j w.1.1 w.1.2 w.2) :=
      (measurable_fst.comp measurable_fst).add (hz.const_smul (strength d k j))
    have heq : (fun w : (d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω) =>
        epochAdvance d g k (j, w.1) w.2) = fun w =>
        (j + 1, w.1.1 + strength d k j • stageRun d g k j w.1.1 w.1.2 w.2,
          stageRun d g k j w.1.1 w.1.2 w.2) := rfl
    rw [heq]
    exact measurable_const.prodMk (hb.prodMk hz)
  have hall : Measurable
      (fun w : ℕ × ((d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω)) =>
        epochAdvance d g k (w.1, w.2.1) w.2.2) :=
    measurable_from_prod_countable_right hslice
  exact hall.comp
    (show Measurable (fun w : (ℕ × d.E × d.E) × (Fin (innerSteps k) → Fin 2 → Ω) =>
      (w.1.1, (w.1.2, w.2))) from by fun_prop)

noncomputable def floorTerm (σ α : ℝ) (k : ℕ) : ℝ := σ ^ α * relaxation k ^ (α - 1)

noncomputable def envelope (d : Public) (R σ α : ℝ) (k : ℕ) : ℝ :=
  (2 * strength d k 0 * R) ^ α + 324 * floorTerm σ α k

lemma floorTerm_nonneg (σ α : ℝ) (hσ : 0 ≤ σ) (k : ℕ) : 0 ≤ floorTerm σ α k :=
  mul_nonneg (Real.rpow_nonneg hσ _) (Real.rpow_nonneg (relaxation_pos k).le _)

lemma initial_energy_bound {F : d.E → d.E} (hF : Problem d F) (α R : ℝ) (hα1 : 1 < α)
    (k : ℕ) (xstar : d.E) (hstar : F xstar = 0) (hR : ‖d.x0 - xstar‖ ≤ R) :
    energy hF α k (0, strength d k 0 • d.x0, d.x0) ≤ (2 * strength d k 0 * R) ^ α := by
  have ha := strength_pos d hF.pos k 0
  have hd := initial_root_distance F hF.mono (strength d k 0) R ha
    d.x0 xstar (root hF k 0 (strength d k 0 • d.x0)) hstar hR
    (root_equation hF k 0 (strength d k 0 • d.x0))
  rw [norm_sub_rev] at hd
  unfold energy
  dsimp only
  rw [← Real.mul_rpow ha.le (norm_nonneg _)]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hd ha.le]

lemma epoch_output_moment {F : d.E → d.E} (hF : Problem d F)
    (p : ProbabilityMeasure Ω) (g : d.E → Ω → d.E) (σ α : ℝ) (hσ : 0 ≤ σ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (k : ℕ) (s : ℕ × d.E × d.E) :
    Integrable (fun ξ => strength d k s.1 ^ α *
      ‖(epochAdvance d g k s ξ).2.2 - root hF k s.1 s.2.1‖ ^ α)
      (Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ∧
    (∫ ξ, strength d k s.1 ^ α *
      ‖(epochAdvance d g k s ξ).2.2 - root hF k s.1 s.2.1‖ ^ α
      ∂Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ≤
      (1 / 18) * energy hF α k s + 18 * floorTerm σ α k := by
  have h := stage_moment hF.pos F hF.mono hF.lip p g σ α hσ hg hα1 hα2 k s.1 s.2.1 s.2.2
    (root hF k s.1 s.2.1) (root_equation hF k s.1 s.2.1)
  have he : (1 / 18) * energy hF α k s + 18 * floorTerm σ α k =
      (1 / 18) * (strength d k s.1 ^ α * ‖s.2.2 - root hF k s.1 s.2.1‖ ^ α) +
        18 * σ ^ α * relaxation k ^ (α - 1) := by
    unfold energy floorTerm; ring
  rw [he]
  exact h

lemma epoch_energy_drift {F : d.E → d.E} (hF : Problem d F)
    (p : ProbabilityMeasure Ω) (g : d.E → Ω → d.E) (σ α : ℝ) (hσ : 0 ≤ σ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (k : ℕ) (s : ℕ × d.E × d.E) :
    Integrable (fun ξ => energy hF α k (epochAdvance d g k s ξ))
      (Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ∧
    (∫ ξ, energy hF α k (epochAdvance d g k s ξ)
      ∂Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ≤
      (1 / 2 : ℝ) * energy hF α k s + 162 * floorTerm σ α k := by
  let W := fun ξ => strength d k s.1 ^ α *
    ‖(epochAdvance d g k s ξ).2.2 - root hF k s.1 s.2.1‖ ^ α
  have hi := epoch_output_moment hF p g σ α hσ hg hα1 hα2 k s
  have hb (ξ : Fin (innerSteps k) → Fin 2 → Ω) :
      energy hF α k (epochAdvance d g k s ξ) ≤ 9 * W ξ := by
    simpa only [epochAdvance, W] using
      next_energy_bound hF α hα1 hα2 k s.1 s.2.1 (epochAdvance d g k s ξ).2.2
  have hm : Measurable (fun ξ => energy hF α k (epochAdvance d g k s ξ)) :=
    (energy_measurable hF α k).comp ((epochAdvance_measurable g hg.measurable k).comp
      measurable_prodMk_left)
  have he : Integrable (fun ξ => energy hF α k (epochAdvance d g k s ξ))
      (Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) := by
    apply (hi.1.const_mul 9).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg hF α k _)] using hb ξ)
  refine ⟨he, ?_⟩
  have hI := integral_mono he (hi.1.const_mul 9) hb
  rw [integral_const_mul] at hI
  have hV := energy_nonneg hF α k s
  linarith [hi.2]

lemma geometric_weight_identity (r : ℝ) (n : ℕ) :
    r ^ n + (1 - r) * ∑ j ∈ Finset.range n, r ^ j = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ r n]
    nlinarith

lemma epoch_energy_bound {F : d.E → d.E} (hF : Problem d F)
    (p : ProbabilityMeasure Ω) (g : d.E → Ω → d.E) (σ α R : ℝ) (hσ : 0 ≤ σ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (xstar : d.E) (hstar : F xstar = 0) (hR : ‖d.x0 - xstar‖ ≤ R) (k n : ℕ) :
    Integrable (fun ξ => energy hF α k (iterateSamples (epochAdvance d g k) n
      (0, strength d k 0 • d.x0, d.x0) ξ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (innerSteps k) =>
        Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ∧
    (∫ ξ, energy hF α k (iterateSamples (epochAdvance d g k) n
      (0, strength d k 0 • d.x0, d.x0) ξ)
      ∂Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (innerSteps k) =>
        Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ≤ envelope d R σ α k := by
  let Q : ProbabilityMeasure (Fin (innerSteps k) → Fin 2 → Ω) :=
    ⟨Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω),
      inferInstance⟩
  have h := OracleTemplate.GapStrongGrowth.iterateSamples_measurable_integral
    (epochAdvance_measurable g hg.measurable k) Q (energy hF α k)
    (energy_measurable hF α k) (energy_nonneg hF α k) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (epoch_energy_drift hF p g σ α hσ hg hα1 hα2 k) n
    (0, strength d k 0 • d.x0, d.x0)
  refine ⟨h.1, h.2.trans ?_⟩
  have hi := initial_energy_bound hF α R hα1 k xstar hstar hR
  have he := geometric_weight_identity (1 / 2 : ℝ) n
  have hf := floorTerm_nonneg σ α hσ k
  have hp := mul_le_mul_of_nonneg_left hi (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hA : 0 ≤ (2 * strength d k 0 * R) ^ α := by
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
    have := strength_pos d hF.pos k 0
    positivity
  have hs : 0 ≤ ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (by norm_num) _)
  have hsum : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ 2 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hV0 := energy_nonneg hF α k (0, strength d k 0 • d.x0, d.x0)
  unfold envelope
  have h1 : (1 / 2 : ℝ) ^ n * energy hF α k (0, strength d k 0 • d.x0, d.x0) ≤
      (2 * strength d k 0 * R) ^ α := by
    calc _ ≤ 1 * energy hF α k (0, strength d k 0 • d.x0, d.x0) :=
          mul_le_mul_of_nonneg_right hpow hV0
      _ ≤ _ := by linarith
  have h2 : 162 * floorTerm σ α k * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤
      324 * floorTerm σ α k := by nlinarith
  linarith

lemma epochState_measurable (g : d.E → Ω → d.E) (hg : Measurable (Function.uncurry g))
    (k n : ℕ) : Measurable (epochState d g k n) := by
  unfold epochState
  exact (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
    (epochAdvance_measurable g hg k) n).comp
      (show Measurable (fun ξ : ℕ → Fin (innerSteps k) → Fin 2 → Ω =>
        ((0, strength d k 0 • d.x0, d.x0), (fun i : Fin n => ξ i))) from by fun_prop)

omit [MeasurableSpace Ω] in
lemma epochState_succ (g : d.E → Ω → d.E) (k n : ℕ)
    (ξ : ℕ → Fin (innerSteps k) → Fin 2 → Ω) :
    epochState d g k (n + 1) ξ = epochAdvance d g k (epochState d g k n ξ) (ξ n) := by
  unfold epochState
  rw [OracleTemplate.GapStrongGrowth.iterateSamples_succ_last]
  rfl

omit [MeasurableSpace Ω] in
lemma epoch_iterate_stage (g : d.E → Ω → d.E) (k n : ℕ)
    (s : ℕ × d.E × d.E) (ξ : Fin n → Fin (innerSteps k) → Fin 2 → Ω) :
    (iterateSamples (epochAdvance d g k) n s ξ).1 = s.1 + n := by
  induction n generalizing s with
  | zero => simp [iterateSamples]
  | succ n ih =>
    simp only [iterateSamples]
    rw [ih]
    simp only [epochAdvance]
    omega

omit [MeasurableSpace Ω] in
lemma epochState_stage (g : d.E → Ω → d.E) (k n : ℕ)
    (ξ : ℕ → Fin (innerSteps k) → Fin 2 → Ω) : (epochState d g k n ξ).1 = n := by
  simpa only [epochState, zero_add] using epoch_iterate_stage g k n
    (0, strength d k 0 • d.x0, d.x0) (fun i => ξ i)

omit [MeasurableSpace Ω] in
lemma epochState_anchor_succ (g : d.E → Ω → d.E) (k n : ℕ)
    (ξ : ℕ → Fin (innerSteps k) → Fin 2 → Ω) :
    (epochState d g k (n + 1) ξ).2.1 =
      (epochState d g k n ξ).2.1 + strength d k n • (epochState d g k (n + 1) ξ).2.2 := by
  rw [epochState_succ]
  simp only [epochAdvance, epochState_stage]

end LongTails.Proofs.TailObliviousProcess
