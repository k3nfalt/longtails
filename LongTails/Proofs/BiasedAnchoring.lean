import LongTails.Proofs.SmoothBanachTerminal

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.BiasedAnchoring

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open LongTails.Proofs.SmoothBanachAnchoring LongTails.Proofs.SmoothBanachTuning
open LongTails.Proofs.SmoothBanachProcess LongTails.Proofs.SmoothBanachSampling
open LongTails.Proofs.SmoothBanachTerminal
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

structure IsBiasedOperator {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    (T : E → E) (g : E → Ω → E) (σ b : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) p
  variance_integrable : ∀ x, Integrable (fun ω => ‖g x ω - ∫ w, g x w ∂p‖ ^ 2) p
  variance : ∀ x, (∫ ω, ‖g x ω - ∫ w, g x w ∂p‖ ^ 2 ∂p) ≤ σ ^ 2
  bias : ∀ x, ‖(∫ w, g x w ∂p) - T x‖ ≤ b

section OneStep

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma biased_picard_moment (C : ℝ) (J : E → E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2) (hC : 0 ≤ C)
    (T : E → E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (a δ σ β : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hβ : 0 ≤ β)
    (hstep : δ / a * (1 + a) ≤ 1)
    (b x u : E) (hu : (1 + a) • u - T u - b = 0)
    (g : Ω → E) (hg : Measurable g) (hgi : Integrable g P)
    (hg2 : Integrable (fun ω => ‖g ω - ∫ w, g w ∂P‖ ^ 2) P)
    (hvar : (∫ ω, ‖g ω - ∫ w, g w ∂P‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hbias : ‖(∫ w, g w ∂P) - T x‖ ≤ β) :
    Integrable (fun ω => ‖(1 - δ / a * (1 + a)) • x + (δ / a) • g ω + (δ / a) • b - u‖ ^ 2) P ∧
    (∫ ω, ‖(1 - δ / a * (1 + a)) • x + (δ / a) • g ω + (δ / a) • b - u‖ ^ 2 ∂P) ≤
      (1 - δ) * ‖x - u‖ ^ 2 + (δ / a) ^ 2 * (β ^ 2 / δ + C * σ ^ 2) := by
  set η := δ / a with hηd
  have hη : 0 ≤ η := by positivity
  have hηa : η * a = δ := by rw [hηd]; field_simp
  set m := ∫ w, g w ∂P with hm
  let X : Ω → E := fun ω => η • (g ω - m)
  let y0 := (1 - η * (1 + a)) • x + η • T x + η • b - u
  let y := y0 + η • (m - T x)
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hXi : Integrable X P := (hgi.sub (integrable_const _)).smul η
  have hsq (ω : Ω) : ‖X ω‖ ^ 2 = η ^ 2 * ‖g ω - m‖ ^ 2 := by
    simp only [X, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P := by
    simp_rw [hsq]
    exact hg2.const_mul _
  have hzero : (∫ ω, X ω ∂P) = 0 := by
    dsimp [X]
    rw [integral_smul, integral_sub hgi (integrable_const _)]
    simp [← hm]
  have hn := LongTails.Proofs.SmoothBanachNoise.centered_second_moment C J hsmooth hX hXi hX2 hzero y
  have he (ω : Ω) : (1 - η * (1 + a)) • x + η • g ω + η • b - u = y + X ω := by
    dsimp [y, y0, X]
    module
  simp_rw [he]
  refine ⟨hn.1, hn.2.trans ?_⟩
  have hfix : (1 - η * (1 + a)) • u + η • T u + η • b = u := by
    have hb : (1 + a) • u - T u = b := sub_eq_zero.mp hu
    rw [← hb]
    module
  have hy0 : ‖y0‖ ≤ (1 - η * a) * ‖x - u‖ := by
    simpa only [hfix, y0] using
      LongTails.Proofs.SmoothBanachAnchoring.damped_picard_contraction T hT a η hη hstep b x u
  rw [hηa] at hy0
  have hyb : ‖y‖ ≤ (1 - δ) * ‖x - u‖ + η * β := by
    refine (norm_add_le _ _).trans (add_le_add hy0 ?_)
    rw [norm_smul, Real.norm_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hbias hη
  have hconv : ((1 - δ) * ‖x - u‖ + η * β) ^ 2 ≤ (1 - δ) * ‖x - u‖ ^ 2 + η ^ 2 * β ^ 2 / δ := by
    have hA := norm_nonneg (x - u)
    have hid : (1 - δ) * ‖x - u‖ ^ 2 + η ^ 2 * β ^ 2 / δ - ((1 - δ) * ‖x - u‖ + η * β) ^ 2 =
        (1 - δ) * (δ * ‖x - u‖ - η * β) ^ 2 / δ := by
      field_simp
      ring
    have hnn : 0 ≤ (1 - δ) * (δ * ‖x - u‖ - η * β) ^ 2 / δ := by
      apply div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hδ.le
    linarith
  have hy2 : ‖y‖ ^ 2 ≤ (1 - δ) * ‖x - u‖ ^ 2 + η ^ 2 * β ^ 2 / δ := by
    have hnn : 0 ≤ (1 - δ) * ‖x - u‖ + η * β :=
      add_nonneg (mul_nonneg (by linarith) (norm_nonneg _)) (mul_nonneg hη hβ)
    exact ((sq_le_sq₀ (norm_nonneg _) hnn).mpr hyb).trans hconv
  have hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ η ^ 2 * σ ^ 2 := by
    simp_rw [hsq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hvar (sq_nonneg η)
  have hCv := mul_le_mul_of_nonneg_left hv hC
  have hid : η ^ 2 * (β ^ 2 / δ + C * σ ^ 2) = η ^ 2 * β ^ 2 / δ + C * (η ^ 2 * σ ^ 2) := by
    field_simp
  rw [hid]
  linarith

lemma contraction_pow_le (δ S : ℝ) (hδ1 : δ ≤ 1) (hS : 0 < S) (n : ℕ)
    (hn : 8 * S ≤ δ * n) : (1 - δ) ^ n ≤ 1 / (64 * S ^ 2) := by
  have h1 : (1 - δ) ^ n ≤ Real.exp (-δ) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ)]) n
  have h2 : Real.exp (-δ) ^ n = Real.exp (-(δ * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : Real.exp (-(δ * n)) ≤ Real.exp (-(8 * S)) := Real.exp_le_exp.mpr (by linarith)
  have h4 : 8 * S ≤ Real.exp (4 * S) := by
    have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4 * S by positivity)
    nlinarith [sq_nonneg (4 * S - 1)]
  have h5 : 64 * S ^ 2 ≤ Real.exp (8 * S) := by
    have : Real.exp (8 * S) = Real.exp (4 * S) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [this]
    nlinarith
  have h6 : Real.exp (-(8 * S)) ≤ 1 / (64 * S ^ 2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) h5
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h6

lemma biased_inner_bound (P : ProbabilityMeasure Ω)
    (C : ℝ) (hC : 0 ≤ C) (J : E → E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2)
    (T : E → E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (a δ σ β S : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hβ : 0 ≤ β) (hS : 0 < S)
    (hstep : δ / a * (1 + a) ≤ 1) (n : ℕ) (hn : 8 * S ≤ δ * n)
    (b x u : E) (hu : (1 + a) • u - T u - b = 0)
    (g : E → Ω → E)
    (hg : IsBiasedOperator (P : Measure Ω) T g σ β) :
    Integrable (fun ξ => a ^ 2 *
      ‖iterateSamples (fun z ω => picardStep a (δ / a) b z (g z ω)) n x ξ - u‖ ^ 2)
      (Measure.pi fun _ : Fin n => (P : Measure Ω)) ∧
    (∫ ξ, a ^ 2 *
      ‖iterateSamples (fun z ω => picardStep a (δ / a) b z (g z ω)) n x ξ - u‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => (P : Measure Ω))) ≤
      (a ^ 2 * ‖x - u‖ ^ 2) / (64 * S ^ 2) + (C * δ * σ ^ 2 + β ^ 2) := by
  have hi := OracleTemplate.GapStrongGrowth.iterateSamples_measurable_integral
    (LongTails.Proofs.SmoothBanachIteration.picard_measurable a (δ / a) b hg.measurable) P
    (fun z => ‖z - u‖ ^ 2) (by fun_prop) (fun z => sq_nonneg _)
    (show 0 ≤ 1 - δ by linarith) (r := (δ / a) ^ 2 * (β ^ 2 / δ + C * σ ^ 2)) (fun z => by
      have := biased_picard_moment C J hsmooth hC T hT a δ σ β ha hδ hδ1 hβ hstep b z u hu
        (g z) (hg.measurable.comp measurable_prodMk_left) (hg.integrable z)
        (hg.variance_integrable z) (hg.variance z) (hg.bias z)
      simpa only [picardStep] using this) n x
  refine ⟨hi.1.const_mul (a ^ 2), ?_⟩
  rw [integral_const_mul]
  have hdecay := contraction_pow_le δ S hδ1 hS n hn
  have hgeom := LongTails.Proofs.SmoothBanachProcess.geometric_weight_identity (1 - δ) n
  have hsum : δ * ∑ j ∈ Finset.range n, (1 - δ) ^ j ≤ 1 := by
    have hp : 0 ≤ (1 - δ) ^ n := pow_nonneg (by linarith) n
    have : (1 - (1 - δ)) = δ := by ring
    rw [this] at hgeom
    linarith
  have hA : 0 ≤ β ^ 2 / δ + C * σ ^ 2 := by positivity
  have hmain := mul_le_mul_of_nonneg_left hi.2 (sq_nonneg a)
  refine hmain.trans ?_
  have hid : a ^ 2 * ((1 - δ) ^ n * ‖x - u‖ ^ 2 + (δ / a) ^ 2 * (β ^ 2 / δ + C * σ ^ 2) *
      ∑ j ∈ Finset.range n, (1 - δ) ^ j) =
      (1 - δ) ^ n * (a ^ 2 * ‖x - u‖ ^ 2) +
        (δ * (β ^ 2 / δ + C * σ ^ 2)) * (δ * ∑ j ∈ Finset.range n, (1 - δ) ^ j) := by
    field_simp
  rw [hid]
  have hB : δ * (β ^ 2 / δ + C * σ ^ 2) = C * δ * σ ^ 2 + β ^ 2 := by
    field_simp
    ring
  rw [hB]
  have hnn : 0 ≤ C * δ * σ ^ 2 + β ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hdecay (show 0 ≤ a ^ 2 * ‖x - u‖ ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsum hnn
  calc _ ≤ 1 / (64 * S ^ 2) * (a ^ 2 * ‖x - u‖ ^ 2) + (C * δ * σ ^ 2 + β ^ 2) * 1 :=
        add_le_add h1 h2
    _ = _ := by ring

end OneStep

section Process

variable (q : Params) (T : q.E → q.E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)

lemma epoch_output_moment (hC : 0 ≤ q.C) (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E) (β : ℝ) (hβ : 0 ≤ β)
    (hg : IsBiasedOperator (p : Measure _) T g q.σ β) (s : ℕ × q.E × q.E) :
    Integrable (fun ξ => strength q s.1 ^ 2 *
      ‖(epochAdvance q g s ξ).2.2 - root q T hT s.1 s.2.1‖ ^ 2)
      (Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _)) ∧
    (∫ ξ, strength q s.1 ^ 2 *
      ‖(epochAdvance q g s ξ).2.2 - root q T hT s.1 s.2.1‖ ^ 2
      ∂Measure.pi (fun _ : Fin (innerSteps q) => (p : Measure _))) ≤
      energy q T hT s / (64 * (levels q + 1 : ℝ) ^ 2) +
        (q.C * relaxation q * q.σ ^ 2 + β ^ 2) := by
  exact biased_inner_bound p q.C hC J hsmooth T hT
    (strength q s.1) (relaxation q) q.σ β (levels q + 1 : ℝ)
    (strength_pos q s.1) (relaxation_pos q hC) (relaxation_le_one q hC) hβ
    (by positivity) (picard_step_size q hC s.1) (innerSteps q) (innerSteps_contraction q hC)
    s.2.1 s.2.2 (root q T hT s.1 s.2.1) (root_equation q T hT s.1 s.2.1)
    g hg

lemma epoch_energy_drift (hC : 0 ≤ q.C) (hε : 0 < q.ε) (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E) (β : ℝ) (hβ : 0 ≤ β)
    (hβε : β ^ 2 ≤ q.ε ^ 2 / (6400 * (levels q + 1 : ℝ) ^ 2))
    (hg : IsBiasedOperator (p : Measure _) T g q.σ β) (s : ℕ × q.E × q.E) :
    Integrable (fun ξ => energy q T hT (epochAdvance q g s ξ))
      (Measure.pi fun _ : Fin (innerSteps q) => (p : Measure _)) ∧
    (∫ ξ, energy q T hT (epochAdvance q g s ξ)
      ∂Measure.pi (fun _ : Fin (innerSteps q) => (p : Measure _))) ≤
      (1 / 4 : ℝ) * energy q T hT s + 3 * q.ε ^ 2 / 256 := by
  have hi := epoch_output_moment q T hT hC J hsmooth p g β hβ hg s
  have hb (ξ : Fin (innerSteps q) → q.Ω) :
      energy q T hT (epochAdvance q g s ξ) ≤ 9 * (strength q s.1 ^ 2 *
        ‖(epochAdvance q g s ξ).2.2 - root q T hT s.1 s.2.1‖ ^ 2) := by
    simpa only [epochAdvance, mul_assoc] using
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
  have hb' : q.ε ^ 2 / (6400 * (levels q + 1 : ℝ) ^ 2) ≤ q.ε ^ 2 / 6400 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith)
  nlinarith [hi.2, sq_nonneg q.ε]

lemma epoch_energy_bound (hC : 0 ≤ q.C) (hε : 0 < q.ε) (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E) (β : ℝ) (hβ : 0 ≤ β)
    (hβε : β ^ 2 ≤ q.ε ^ 2 / (6400 * (levels q + 1 : ℝ) ^ 2))
    (hg : IsBiasedOperator (p : Measure _) T g q.σ β)
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
    (epoch_energy_drift q T hT hC hε J hsmooth p g β hβ hβε hg) n
    (0, strength q 0 • q.x0, q.x0)
  refine ⟨h.1, h.2.trans ?_⟩
  have hi := initial_energy_bound q T hT hε xstar hstar hR
  have he := geometric_weight_identity (1 / 4 : ℝ) n
  have he' := congrArg (fun t => q.ε ^ 2 / 64 * t) he
  have hp := mul_le_mul_of_nonneg_left hi (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n)
  nlinarith

lemma epoch_error_bound (hC : 0 ≤ q.C) (hε : 0 < q.ε) (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E) (β : ℝ) (hβ : 0 ≤ β)
    (hβε : β ^ 2 ≤ q.ε ^ 2 / (6400 * (levels q + 1 : ℝ) ^ 2))
    (hg : IsBiasedOperator (p : Measure _) T g q.σ β)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) (n : ℕ) :
    Integrable (epochError q T hT g n)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) ∧
    (∫ ξ, epochError q T hT g n ξ
      ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω))) ≤
      q.ε ^ 2 / (256 * (levels q + 1 : ℝ) ^ 2) := by
  let B := Fin (innerSteps q) → q.Ω
  let Q : Measure B := Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)
  let state := fun ξ : Fin n → B => iterateSamples (epochAdvance q g) n
    (0, strength q 0 • q.x0, q.x0) ξ
  let F : (Fin n → B) × B → ℝ := fun w =>
    energy q T hT ((state w.1).1, (state w.1).2.1,
      (epochAdvance q g (state w.1) w.2).2.2)
  let G : (Fin n → B) → ℝ := fun ξ =>
    energy q T hT (state ξ) / (64 * (levels q + 1 : ℝ) ^ 2) +
      (q.C * relaxation q * q.σ ^ 2 + β ^ 2)
  have hstate : Measurable state :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
      (epochAdvance_measurable q g hg.measurable) n).comp measurable_prodMk_left
  have hnew := (epochAdvance_measurable q g hg.measurable).comp
    ((hstate.comp measurable_fst).prodMk measurable_snd)
  have hF : Measurable F := (energy_measurable q T hT).comp
    ((hstate.comp measurable_fst).fst.prodMk
      ((hstate.comp measurable_fst).snd.fst.prodMk hnew.snd.snd))
  have hi := epoch_energy_bound q T hT hC hε J hsmooth p g β hβ hβε hg xstar hstar hR n
  have hG : Integrable G (Measure.pi fun _ : Fin n => Q) :=
    (hi.1.div_const _).add (integrable_const _)
  have hfiber (ξ : Fin n → B) := epoch_output_moment q T hT hC J hsmooth p g β hβ hg (state ξ)
  have hp := OracleTemplate.StochasticConvexQuadratic.nonnegative_product_control hF
    (fun w => energy_nonneg q T hT _) (fun ξ => (hfiber ξ).1) hG (fun ξ => (hfiber ξ).2)
  have hpres := prefix_next_preserving Q n
  refine ⟨hpres.integrable_comp_of_integrable hp.1, ?_⟩
  have hchange : (∫ ξ, epochError q T hT g n ξ ∂Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ w, F w ∂(Measure.pi fun _ : Fin n => Q).prod Q := by
    have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => Q)
      hpres.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hpres.map_eq] at he
    exact he.symm
  rw [hchange]
  apply hp.2.trans
  dsimp only [G]
  rw [integral_add (hi.1.div_const _) (integrable_const _), integral_div]
  simp only [integral_const, probReal_univ, one_smul]
  have hden : 0 < 64 * (levels q + 1 : ℝ) ^ 2 := by positivity
  have hv := div_le_div_of_nonneg_right hi.2 hden.le
  have hn := normalized_noise_floor q hC hε
  calc
    _ ≤ (q.ε ^ 2 / 64) / (64 * (levels q + 1 : ℝ) ^ 2) +
        (q.ε ^ 2 / (1024 * (levels q + 1 : ℝ) ^ 2) +
          q.ε ^ 2 / (6400 * (levels q + 1 : ℝ) ^ 2)) := add_le_add hv (add_le_add hn hβε)
    _ ≤ _ := by
      have hS : (levels q + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith [sq_nonneg q.ε]

include hT in
lemma block_accuracy (hC : 0 ≤ q.C) (hε : 0 < q.ε) (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E) (β : ℝ) (hβ : 0 ≤ β)
    (hβε : β ^ 2 ≤ q.ε ^ 2 / (6400 * (levels q + 1 : ℝ) ^ 2))
    (hg : IsBiasedOperator (p : Measure _) T g q.σ β)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) :
    Integrable (fun ξ => ‖T (epochState q g (levels q + 1) ξ).2.2 -
      (epochState q g (levels q + 1) ξ).2.2‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) ∧
    (∫ ξ, ‖T (epochState q g (levels q + 1) ξ).2.2 -
      (epochState q g (levels q + 1) ξ).2.2‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω))) ≤
      q.ε ^ 2 := by
  let Q := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)
  let S := levels q + 1
  let F := fun ξ : ℕ → Fin (innerSteps q) → q.Ω =>
    ‖T (epochState q g S ξ).2.2 - (epochState q g S ξ).2.2‖ ^ 2
  let G := fun ξ => 128 * (S : ℝ) * ∑ j ∈ Finset.range S, epochError q T hT g j ξ + q.ε ^ 2 / 32
  have he (j : ℕ) := epoch_error_bound q T hT hC hε J hsmooth p g β hβ hβε hg xstar hstar hR j
  have hsum : Integrable (fun ξ => ∑ j ∈ Finset.range S, epochError q T hT g j ξ) Q :=
    integrable_finsetSum _ (fun j _ => (he j).1)
  have hG : Integrable G Q := (hsum.const_mul _).add (integrable_const _)
  have hmT : Continuous T := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hT x y)).continuous
  have hF : Measurable F :=
    ((hmT.measurable.comp (epochState_measurable q g hg.measurable S).snd.snd).sub
      (epochState_measurable q g hg.measurable S).snd.snd).norm.pow_const 2
  have hbound (ξ) : F ξ ≤ G ξ := by
    simpa only [F, G, S, Nat.cast_add, Nat.cast_one] using
      terminal_residual_square q T hT hε g xstar hstar hR ξ
  have hi : Integrable F Q := hG.mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ F ξ from sq_nonneg _)] using hbound ξ)
  refine ⟨hi, (integral_mono hi hG hbound).trans ?_⟩
  change (∫ ξ, G ξ ∂Q) ≤ _
  dsimp only [G]
  rw [integral_add (hsum.const_mul _) (integrable_const _), integral_const_mul,
    integral_finsetSum _ (fun j _ => (he j).1)]
  simp only [integral_const, probReal_univ, one_smul]
  have hs : (∑ j ∈ Finset.range S, ∫ ξ, epochError q T hT g j ξ ∂Q) ≤
      (S : ℝ) * (q.ε ^ 2 / (256 * (S : ℝ) ^ 2)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, S, Nat.cast_add, Nat.cast_one] using
      Finset.sum_le_sum (s := Finset.range S) (fun j _ => (he j).2)
  have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 128 * (S : ℝ))
  have hS : (S : ℝ) ≠ 0 := by dsimp [S]; positivity
  have hid : 128 * (S : ℝ) * ((S : ℝ) * (q.ε ^ 2 / (256 * (S : ℝ) ^ 2))) = q.ε ^ 2 / 2 := by
    field_simp
    ring
  rw [hid] at hp
  nlinarith [sq_nonneg q.ε]

end Process

end LongTails.Proofs.BiasedAnchoring
