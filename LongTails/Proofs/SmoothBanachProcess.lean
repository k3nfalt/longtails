import LongTails.Proofs.SmoothBanachIteration
import LongTails.Proofs.SmoothBanachTuning

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SmoothBanachProcess

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open SmoothBanachAnchoring SmoothBanachTuning
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

noncomputable def root (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (j : ℕ) (b : q.E) : q.E :=
  anchoredRoot T hT (strength q j) (strength_pos q j) b

lemma root_equation (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (j : ℕ) (b : q.E) :
    (1 + strength q j) • root q T hT j b - T (root q T hT j b) - b = 0 :=
  anchoredRoot_equation T hT (strength q j) (strength_pos q j) b

lemma root_continuous (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (j : ℕ) :
    Continuous (root q T hT j) :=
  (anchoredRoot_lipschitz T hT (strength q j) (strength_pos q j)).continuous

noncomputable def energy (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (s : ℕ × q.E × q.E) : ℝ :=
  strength q s.1 ^ 2 * ‖s.2.2 - root q T hT s.1 s.2.1‖ ^ 2

lemma energy_nonneg (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (s : ℕ × q.E × q.E) :
    0 ≤ energy q T hT s := by
  unfold energy
  positivity

lemma energy_measurable (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) : Measurable (energy q T hT) := by
  apply measurable_from_prod_countable_right
  intro j
  have hr := (root_continuous q T hT j).measurable
  change Measurable (fun s : q.E × q.E => strength q j ^ 2 * ‖s.2 - root q T hT j s.1‖ ^ 2)
  fun_prop

lemma next_root_distance (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (j : ℕ) (b z : q.E) :
    ‖z - root q T hT (j + 1) (b + strength q j • z)‖ ≤
      (3 / 2 : ℝ) * ‖z - root q T hT j b‖ := by
  have hn := root_equation q T hT (j + 1) (b + strength q j • z)
  rw [strength_double] at hn
  have hm := doubled_anchor_root_movement T hT (strength q j) (strength_pos q j)
    b z (root q T hT j b) (root q T hT (j + 1) (b + strength q j • z))
    (root_equation q T hT j b) hn
  have ht := norm_sub_le_norm_sub_add_norm_sub z (root q T hT j b)
    (root q T hT (j + 1) (b + strength q j • z))
  linarith

lemma next_energy_bound (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (j : ℕ) (b z : q.E) :
    energy q T hT (j + 1, b + strength q j • z, z) ≤
      9 * strength q j ^ 2 * ‖z - root q T hT j b‖ ^ 2 := by
  have hn := next_root_distance q T hT j b z
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  unfold energy
  simp only [strength_double]
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (strength q j))]

lemma epochAdvance_measurable (q : Params) (g : q.E → q.Ω → q.E)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (epochAdvance q g)) := by
  have hslice (j : ℕ) : Measurable
      (fun w : (q.E × q.E) × (Fin (innerSteps q) → q.Ω) =>
        epochAdvance q g (j, w.1) w.2) := by
    have hi := SmoothBanachIteration.picard_iterates_parameter_measurable
      (strength q j) (relaxation q / strength q j) hg (innerSteps q)
    have hz : Measurable (fun w : (q.E × q.E) × (Fin (innerSteps q) → q.Ω) =>
        OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
          (fun x ω => picardStep (strength q j) (relaxation q / strength q j) w.1.1 x (g x ω))
          (innerSteps q) w.1.2 w.2) := hi.comp
      (show Measurable (fun w : (q.E × q.E) × (Fin (innerSteps q) → q.Ω) =>
        (w.1.1, w.1.2, w.2)) from by fun_prop)
    unfold epochAdvance
    dsimp only
    exact measurable_const.prodMk
      (((measurable_fst.comp measurable_fst).add (hz.const_smul (strength q j))).prodMk hz)
  have hall : Measurable
      (fun w : ℕ × ((q.E × q.E) × (Fin (innerSteps q) → q.Ω)) =>
        epochAdvance q g (w.1, w.2.1) w.2.2) :=
    measurable_from_prod_countable_right hslice
  exact hall.comp
    (show Measurable (fun w : (ℕ × q.E × q.E) × (Fin (innerSteps q) → q.Ω) =>
      (w.1.1, (w.1.2, w.2))) from by fun_prop)

lemma initial_energy_bound (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hε : 0 < q.ε)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) :
    energy q T hT (0, strength q 0 • q.x0, q.x0) ≤ q.ε ^ 2 / 64 := by
  have hd := initial_root_distance T hT (strength q 0) q.R (strength_pos q 0)
    q.x0 xstar (root q T hT 0 (strength q 0 • q.x0)) hstar hR
    (root_equation q T hT 0 (strength q 0 • q.x0))
  rw [norm_sub_rev] at hd
  have hr := initial_strength_radius q hε
  have ha := (strength_pos q 0).le
  have hR0 : 0 ≤ q.R := (norm_nonneg _).trans hR
  have hn : strength q 0 * ‖q.x0 - root q T hT 0 (strength q 0 • q.x0)‖ ≤ q.ε / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hd ha]
  have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr hn
  unfold energy
  dsimp only
  nlinarith

lemma epoch_output_moment (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure _) T g q.σ) (s : ℕ × q.E × q.E) :
    Integrable (fun ξ => strength q s.1 ^ 2 *
      ‖(epochAdvance q g s ξ).2.2 - root q T hT s.1 s.2.1‖ ^ 2)
      (Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _)) ∧
    (∫ ξ, strength q s.1 ^ 2 *
      ‖(epochAdvance q g s ξ).2.2 - root q T hT s.1 s.2.1‖ ^ 2
      ∂Measure.pi (fun _ : Fin (innerSteps q) => (p : Measure _))) ≤
      energy q T hT s / (64 * (levels q + 1 : ℝ) ^ 2) + q.C * relaxation q * q.σ ^ 2 := by
  exact SmoothBanachIteration.normalized_inner_bound p q.C hC J hsmooth T hT
    (strength q s.1) (relaxation q) q.σ (levels q + 1 : ℝ)
    (strength_pos q s.1) (relaxation_pos q hC) (relaxation_le_one q hC)
    (by positivity) (picard_step_size q hC s.1) (innerSteps q) (innerSteps_contraction q hC)
    s.2.1 s.2.2 (root q T hT s.1 s.2.1) (root_equation q T hT s.1 s.2.1)
    g hg.measurable hg.integrable hg.variance_integrable hg.unbiased hg.variance

lemma epoch_energy_drift (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C) (hε : 0 < q.ε)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure _) T g q.σ) (s : ℕ × q.E × q.E) :
    Integrable (fun ξ => energy q T hT (epochAdvance q g s ξ))
      (Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _)) ∧
    (∫ ξ, energy q T hT (epochAdvance q g s ξ)
      ∂Measure.pi (fun _ : Fin (innerSteps q) => (p : Measure _))) ≤
      (1 / 4 : ℝ) * energy q T hT s + 3 * q.ε ^ 2 / 256 := by
  let W := fun ξ => strength q s.1 ^ 2 *
    ‖(epochAdvance q g s ξ).2.2 - root q T hT s.1 s.2.1‖ ^ 2
  have hi := epoch_output_moment q T hT hC J hsmooth p g hg s
  have hb (ξ : Fin (innerSteps q) → q.Ω) :
      energy q T hT (epochAdvance q g s ξ) ≤ 9 * W ξ := by
    simpa only [epochAdvance, W, mul_assoc] using
      next_energy_bound q T hT s.1 s.2.1 (epochAdvance q g s ξ).2.2
  have hm : Measurable (fun ξ => energy q T hT (epochAdvance q g s ξ)) :=
    (energy_measurable q T hT).comp ((epochAdvance_measurable q g hg.measurable).comp
      measurable_prodMk_left)
  have he : Integrable (fun ξ => energy q T hT (epochAdvance q g s ξ))
      (Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _)) := by
    apply (hi.1.const_mul 9).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg q T hT _)] using hb ξ)
  refine ⟨he, ?_⟩
  have hI := integral_mono he (hi.1.const_mul 9) hb
  rw [integral_const_mul] at hI
  have hS : 1 ≤ (levels q + 1 : ℝ) ^ 2 := by
    have h0 : 0 ≤ (levels q : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hV := energy_nonneg q T hT s
  have hv : energy q T hT s / (64 * (levels q + 1 : ℝ) ^ 2) ≤ energy q T hT s / 64 :=
    div_le_div_of_nonneg_left hV (by norm_num) (by nlinarith)
  have hn := normalized_noise_floor q hC hε
  have hn' : q.ε ^ 2 / (1024 * (levels q + 1 : ℝ) ^ 2) ≤ q.ε ^ 2 / 1024 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith)
  nlinarith [hi.2]

lemma geometric_weight_identity (r : ℝ) (n : ℕ) :
    r ^ n + (1 - r) * ∑ j ∈ Finset.range n, r ^ j = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ r n]
    nlinarith

lemma epoch_energy_bound (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C) (hε : 0 < q.ε)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure _) T g q.σ)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) (n : ℕ) :
    Integrable (fun ξ => energy q T hT (iterateSamples (epochAdvance q g) n
      (0, strength q 0 • q.x0, q.x0) ξ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _)) ∧
    (∫ ξ, energy q T hT (iterateSamples (epochAdvance q g) n
      (0, strength q 0 • q.x0, q.x0) ξ)
      ∂Measure.pi (fun _ : Fin n => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _))) ≤
      q.ε ^ 2 / 64 := by
  let Q : ProbabilityMeasure (Fin (innerSteps q) → q.Ω) :=
    ⟨Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _), inferInstance⟩
  have h := OracleTemplate.GapStrongGrowth.iterateSamples_measurable_integral
    (epochAdvance_measurable q g hg.measurable) Q (energy q T hT)
    (energy_measurable q T hT) (energy_nonneg q T hT) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (epoch_energy_drift q T hT hC hε J hsmooth p g hg) n
    (0, strength q 0 • q.x0, q.x0)
  refine ⟨h.1, h.2.trans ?_⟩
  have hi := initial_energy_bound q T hT hε xstar hstar hR
  have he := geometric_weight_identity (1 / 4 : ℝ) n
  have he' := congrArg (fun t => q.ε ^ 2 / 64 * t) he
  have hp := mul_le_mul_of_nonneg_left hi (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n)
  nlinarith

lemma epochState_measurable (q : Params) (g : q.E → q.Ω → q.E)
    (hg : Measurable (Function.uncurry g)) (n : ℕ) : Measurable (epochState q g n) := by
  unfold epochState
  exact (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
    (epochAdvance_measurable q g hg) n).comp
      (show Measurable (fun ξ : ℕ → Fin (innerSteps q) → q.Ω =>
        ((0, strength q 0 • q.x0, q.x0), (fun i : Fin n => ξ i))) from by fun_prop)

lemma epochState_succ (q : Params) (g : q.E → q.Ω → q.E)
    (n : ℕ) (ξ : ℕ → Fin (innerSteps q) → q.Ω) :
    epochState q g (n + 1) ξ = epochAdvance q g (epochState q g n ξ) (ξ n) := by
  unfold epochState
  rw [OracleTemplate.GapStrongGrowth.iterateSamples_succ_last]
  rfl

lemma epoch_iterate_stage (q : Params) (g : q.E → q.Ω → q.E) (n : ℕ)
    (s : ℕ × q.E × q.E) (ξ : Fin n → Fin (innerSteps q) → q.Ω) :
    (iterateSamples (epochAdvance q g) n s ξ).1 = s.1 + n := by
  induction n generalizing s with
  | zero => simp [iterateSamples]
  | succ n ih =>
    simp only [iterateSamples]
    rw [ih]
    simp only [epochAdvance]
    omega

lemma epochState_stage (q : Params) (g : q.E → q.Ω → q.E)
    (n : ℕ) (ξ : ℕ → Fin (innerSteps q) → q.Ω) : (epochState q g n ξ).1 = n := by
  simpa only [epochState, zero_add] using epoch_iterate_stage q g n
    (0, strength q 0 • q.x0, q.x0) (fun i => ξ i)

lemma epochState_anchor_succ (q : Params) (g : q.E → q.Ω → q.E)
    (n : ℕ) (ξ : ℕ → Fin (innerSteps q) → q.Ω) :
    (epochState q g (n + 1) ξ).2.1 =
      (epochState q g n ξ).2.1 + strength q n • (epochState q g (n + 1) ξ).2.2 := by
  rw [epochState_succ]
  simp only [epochAdvance, epochState_stage]

end LongTails.Proofs.SmoothBanachProcess
