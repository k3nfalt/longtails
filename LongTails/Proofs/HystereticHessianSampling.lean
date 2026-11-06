import LongTails.Proofs.HystereticHessianExpectation
import LongTails.Proofs.MultiplicativeAccelerationExecution

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianSampling

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianMoments HystereticHessianBlocks HystereticHessianAnchorBlocks
open HystereticHessianMeasurable HeavyTailedProductProcess
open LongTails.Algorithms.GuardedHessianTransport (uniformLaw)

lemma measurable_trial_output (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (n : ℕ) :
    Measurable (fun ξ : ℕ → ℝ × Ω => output p c (path p c answer (initial p c) ξ n)) := by
  have hsample : Measurable (fun ξ : ℕ → ℝ × Ω => fun i : Fin n => ξ i) :=
    Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ))
  have hrun := (finiteRun_measurable (anchoredTimedAdvance p c answer)
    (measurable_anchoredTimedAdvance p c answer ha) n).comp
    ((measurable_const (a := ((⟨initial p c, p.x0⟩, 0) : AnchoredTimedState p c))).prodMk hsample)
  have hpath : Measurable (fun ξ : ℕ → ℝ × Ω => path p c answer (initial p c) ξ n) := by
    have hv := (measurable_value p c).comp (measurable_fst.comp hrun)
    convert hv using 1
    funext ξ
    simp only [Function.comp_def, Function.uncurry_def, finiteRun_eq_trajectory,
      anchored_timed_trajectory, anchoredPath_projection]
  unfold output
  exact Measurable.ite (measurableSet_eq_fun ((measurable_success p c).comp hpath) measurable_const)
    ((measurable_point p c).comp hpath) measurable_const

lemma execution_transfer (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (P : ProbabilityMeasure (ℕ → Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P0 (P : Measure _))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (n : ℕ)
    (φ : Space p → ℝ) (hφ : Measurable φ) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
    let F := fun w : (Unit × (ℕ → ℝ)) × (ℕ → Ω) =>
      OracleTemplate.execute O (trial p c) (fun _ => n) w.1 w.2
    let J := ((Measure.dirac ()).prod
      (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ))).prod (P : Measure _)
    let X := fun ξ : ℕ → ℝ × Ω => output p c (path p c answer (initial p c) ξ n)
    Measurable F ∧
      (Integrable (fun w => φ (F w)) J ↔
        Integrable (fun ξ => φ (X ξ)) (Measure.infinitePi fun _ : ℕ =>
          (uniformLaw : Measure ℝ).prod P0)) ∧
      (∫ w, φ (F w) ∂J) = ∫ ξ, φ (X ξ) ∂Measure.infinitePi (fun _ : ℕ =>
        (uniformLaw : Measure ℝ).prod P0) := by
  intro O F J X
  let Z := fun w : (Unit × (ℕ → ℝ)) × (ℕ → Ω) => fun k => (w.1.2 k, w.2 k)
  have hPlaw : (P : Measure _) = Measure.infinitePi fun _ : ℕ => P0 := by
    have hh := h_samples.stream_law.map_eq
    change (P : Measure (ℕ → Ω)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  have hZ : MeasurePreserving Z J
      (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ).prod P0) := by
    change MeasurePreserving Z
      (((Measure.dirac ()).prod (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ))).prod
        (P : Measure _)) _
    rw [hPlaw]
    exact (measurePreserving_snd (μ := Measure.dirac ())).comp
      (HeavyTailedTapeExecution.initial_zip_streams_preserving (Measure.dirac ())
        (uniformLaw : Measure ℝ) P0)
  have heq : F = X ∘ Z := by
    funext w
    exact execute_eq_path p c P answer w.1 w.2 n
  have hX : Measurable X := measurable_trial_output p c answer ha n
  have hG := hφ.comp hX
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact hX.comp hZ.measurable
  · rw [heq]
    exact hZ.integrable_comp hG.aestronglyMeasurable
  · have he := integral_map (μ := J) hZ.measurable.aemeasurable hG.aestronglyMeasurable
    rw [hZ.map_eq] at he
    simpa only [heq, Function.comp_def] using he.symm

lemma execution_second_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (P : ProbabilityMeasure (ℕ → Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P0 (P : Measure _))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hthreshold : c.guardThreshold = 3 * M / 2)
    (hi : ∀ x, Integrable (answer (x, none)) P0)
    (hmean : ∀ x, (∫ ω, answer (x, none) ω ∂P0) = g x)
    (hpi : ∀ x, Integrable (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p) P0)
    (hb : ∀ x, (∫ ω, ‖answer (x, none) ω - g x‖ ^ p.p ∂P0) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    : let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
        { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
      let A : OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) := trial p c
      let F := fun w : A.Seed × (ℕ → Ω) =>
        OracleTemplate.execute O A (fun _ => trialCalls c) w.1 w.2
      let J := (A.law : Measure _).prod (P : Measure _)
      Integrable (fun w => ‖g (F w)‖ ^ 2) J ∧
        (∫ w, ‖g (F w)‖ ^ 2 ∂J) ≤ 2 * ‖g p.x0‖ ^ 2 + (blockCap c : ℝ) * (4 * M ^ 2) := by
  intro O A F J
  let Q := (uniformLaw : Measure ℝ).prod P0
  have hi' (x : Space p) : Integrable (fun z : ℝ × Ω => answer (x, none) z.2) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hi x)
  have hmean' (x : Space p) : (∫ z : ℝ × Ω, answer (x, none) z.2 ∂Q) = g x := by
    simpa only [Q, integral_fun_snd, probReal_univ, one_smul] using hmean x
  have hpi' (x : Space p) : Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hpi x)
  have hb' (x : Space p) : (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p := by
    have heq := integral_fun_snd (μ := (uniformLaw : Measure ℝ)) (ν := P0)
      (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p)
    simp only [probReal_univ, one_smul] at heq
    exact heq.trans_le (hb x)
  have hm := HystereticHessianExpectation.trial_output_second_moment p c Q answer ha g hg
    hp hp2 hσ hα hM hthreshold hi' hmean' hpi' hb' hsize hgroups hcoarse hfine
  have ht := execution_transfer p c P0 P h_samples answer ha (trialCalls c)
    (fun x => ‖g x‖ ^ 2) (hg.norm.pow_const 2)
  exact ⟨ht.2.1.mpr hm.1, ht.2.2.trans_le hm.2⟩

lemma execute_bounded_trial_eq (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (B : ℕ) (hB : trialCalls c ≤ B) (seed : Unit × (ℕ → ℝ)) (ξ : ℕ → Ω) :
    OracleTemplate.execute
      { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
      (boundedTrial p c) (fun _ => B) seed ξ =
      output p c (path p c answer (initial p c) (fun k => (seed.2 k, ξ k)) (trialCalls c)) := by
  have hh := OracleTemplate.SplitRobustAcceleration.execute_capped P answer (trial p c)
    (trialCalls c) B hB seed ξ
  exact hh.trans (execute_eq_path p c P answer seed ξ (trialCalls c))

end LongTails.Proofs.HystereticHessianSampling
