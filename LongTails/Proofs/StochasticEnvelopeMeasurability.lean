import LongTails.Proofs.StochasticEnvelopeApproximation
import LongTails.Proofs.StochasticEnvelopeTransport
open MeasureTheory OracleTemplate
namespace LongTails.Proofs.StochasticEnvelopeMeasurability
open LongTails.Algorithms.StochasticEnvelopePilot
open LongTails.Algorithms.StochasticEnvelopeLocalization
open HeavyTailedMarkovGradient
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
lemma measurable_clippedRun_family {A : Type*} [MeasurableSpace A]
    {g : A → E → Ω → E} (hg : Measurable (fun w : A × E × Ω => g w.1 w.2.1 w.2.2))
    {D R C : A → ℝ} {anchor : A → E} {ξ : A → ℕ → Ω}
    (hD : Measurable D) (hR : Measurable R) (hC : Measurable C)
    (ha : Measurable anchor) (hξ : Measurable ξ) (K : ℕ) :
    Measurable (fun ω => (clippedRun (g ω) (D ω) (R ω) (C ω) 1 (anchor ω) (ξ ω) K).2) := by
  induction K with
  | zero => exact ha.prodMk ha
  | succ K ih =>
    let state := fun ω => clippedRun (g ω) (D ω) (R ω) (C ω) 1 (anchor ω) (ξ ω) K
    have hq : Measurable (fun ω => OracleTemplate.Gradient.acceleratedQuery (state ω)) := by
      simp only [state, clippedRun_index, OracleTemplate.Gradient.acceleratedQuery]
      exact (ih.fst.const_smul _).add (ih.snd.const_smul _)
    have hgq := hg.comp (measurable_id.prodMk (hq.prodMk ((measurable_pi_apply (K * 1)).comp hξ)))
    have hr := StochasticEnvelopePilot.measurable_variable_clip hC hgq
    have hz := ha.add (StochasticEnvelopePilot.measurable_variable_clip hR
      ((ih.snd.sub (((measurable_const : Measurable (fun _ : A => ((K : ℝ) + 1) / 2)).div hD).smul hr)).sub ha))
    simp only [clippedRun, projectedClippedUpdate, clippedRun_index,
      OracleTemplate.Gradient.acceleratedQuery]
    simpa only [state, OracleTemplate.Gradient.acceleratedQuery, clippedRun_index,
      id_eq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply', Pi.div_apply, Function.comp_apply, Function.uncurry_apply_pair] using
      (((ih.fst.const_smul (((K : ℝ) * ((K : ℝ) + 1) / 4) /
        ((K : ℝ) * ((K : ℝ) + 1) / 4 + ((K : ℝ) + 1) / 2))).add
        (hz.const_smul ((((K : ℝ) + 1) / 2) /
        ((K : ℝ) * ((K : ℝ) + 1) / 4 + ((K : ℝ) + 1) / 2)))).prodMk hz)

lemma measurable_stage_center {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a : ℝ) {center : A → E} (hc : Measurable center) {U D : A → ℝ} {anchor : A → E}
    (hU : Measurable U) (hD : Measurable D) (ha : Measurable anchor)
    (K replicas : ℕ) {ξ : A → Fin (replicas + 1) → ℕ → Ω} (hξ : Measurable ξ) :
    Measurable (fun ω => LongTails.Algorithms.StochasticEnvelopeLocalization.stage
      g L μ p s a (U ω) (D ω) (center ω) (anchor ω) K replicas (ξ ω)) := by
  let σ := fun ω => s + a * μ * U ω + 2 * a * L * D ω
  let e := fun ω => μ * D ω ^ 2 / 131072
  let Λ := fun ω => 2 * (L + μ) + e ω * (K : ℝ) ^ 2 / (16 * D ω ^ 2)
  let C := fun ω => 4 * (L + μ) * D ω + e ω / D ω *
    (256 * σ ω * D ω / e ω) ^ (p / (p - 1))
  have hσ : Measurable σ := by dsimp [σ]; fun_prop
  have he : Measurable e := by dsimp [e]; fun_prop
  have hΛ : Measurable Λ := by dsimp [Λ]; fun_prop
  have hC : Measurable C := by dsimp [C]; fun_prop
  have hg' : Measurable (fun w : A × E × Ω => g w.2.1 w.2.2 + μ • (w.2.1 - center w.1)) :=
    (hg.comp measurable_snd).add (by fun_prop)
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro i
  exact (measurable_clippedRun_family hg' hΛ hD hC ha
    ((measurable_pi_apply i).comp hξ) K).fst

lemma measurable_refineRun_center {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a n : ℝ) {center : A → E} (hc : Measurable center) {U : A → ℝ} {start : A → E}
    (hU : Measurable U) (hstart : Measurable start) (K replicas : ℕ)
    {ξ : A → ℕ → Fin (replicas + 1) → ℕ → Ω} (hξ : Measurable ξ) (J : ℕ) :
    Measurable (fun ω => LongTails.Algorithms.StochasticEnvelopeLocalization.refineRun
      g L μ p s a (U ω) n (center ω) (start ω) K replicas (ξ ω) J) := by
  induction J with
  | zero => exact hstart
  | succ J ih =>
    have hD : Measurable (fun ω => U ω / (2 : ℝ) ^ J) := hU.div_const _
    have hτ : Measurable (fun ω => (s / μ + a * U ω) * n ^ (-(p - 1) / p)) := by fun_prop
    exact Measurable.ite (measurableSet_le hD hτ) ih
      (measurable_stage_center hg L μ p s a hc hU hD ih K replicas
        ((measurable_pi_apply J).comp hξ))

lemma measurable_sampledRun_center {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ β : ℝ) {center : A → E} (hc : Measurable center) {b n : ℕ} {R : A → ℝ}
    {ξ : A → ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω}
    (hR : Measurable R) (hξ : Measurable ξ) (N : ℕ) :
    Measurable (fun ω => sampledRun g L μ β (R ω) (center ω) (ξ ω) N) := by
  induction N with
  | zero => exact hc.prodMk hc
  | succ N ih =>
    have hsample : Measurable (fun ω => ξ ω N) := (measurable_pi_apply N).comp hξ
    have hr := (StochasticEnvelopePilot.measurable_sampledReply hg
      (InexactGradient.momentum (L + μ) μ (2 * β)) b n).comp (ih.prodMk hsample)
    have hu : Measurable (fun w : A × (E × E) × E => update L μ β (center w.1) w.2.1 w.2.2) := by
      unfold update InexactGradient.step InexactGradient.query
      fun_prop
    have hn := hu.comp (measurable_id.prodMk (ih.prodMk hr))
    have hh := (hc.add (StochasticEnvelopePilot.measurable_variable_clip hR
      (hn.fst.sub hc))).prodMk
      (hc.add (StochasticEnvelopePilot.measurable_variable_clip hR (hn.snd.sub hc)))
    convert hh using 1
    funext ω
    unfold sampledRun
    rw [HeavyTailedMarkovGradient.advance_add, Nat.zero_add]
    rfl

lemma measurable_localizedRadius_center {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (L μ s β : ℝ)
    {center : A → E} (hc : Measurable center) (b n N : ℕ)
    {rough : A → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω}
    {ξ : A → ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω}
    (hrough : Measurable rough) (hξ : Measurable ξ) :
    Measurable (fun w => localizedRadius g L μ s β (center w) (rough w) (ξ w) N) := by
  let estimate := fun w : A => robustMean (fun i j k => g (center w) (rough w i j k))
  have he : Measurable estimate := by
    apply (StochasticEnvelopeSampling.measurable_robustMean b n).comp
    refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => Measurable.of_eval (fun k => ?_)))
    exact hg.comp (hc.prodMk (by fun_prop))
  have hR : Measurable (fun w => 72 * Real.sqrt ((L + μ) / μ) *
      (4 * (‖estimate w‖ + s) / μ)) := by fun_prop
  have hY := measurable_sampledRun_center hg L μ β hc hR hξ N
  change Measurable (fun w => 2 * ‖center w -
    (sampledRun g L μ β (72 * Real.sqrt ((L + μ) / μ) *
      (4 * (‖estimate w‖ + s) / μ)) (center w) (ξ w) N).1‖ + 128 * s / μ)
  fun_prop

lemma measurable_approximate_center {A : Type*} [MeasurableSpace A]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (L μ p s a n β : ℝ)
    {center : A → E} (hc : Measurable center) (b h v N K J : ℕ)
    {rough : A → Fin (h + 1) → Fin 8 → Fin (b + 1) → Ω}
    {pilot : A → ℕ → Fin (h + 1) → Fin 8 → Fin (b + 1) → Ω}
    {inner : A → ℕ → Fin (v + 1) → ℕ → Ω}
    (hr : Measurable rough) (hp : Measurable pilot) (hi : Measurable inner) :
    Measurable (fun w => approximate g L μ p s a n β (center w) b h v N K J
      (rough w) (pilot w) (inner w)) := by
  have hU := measurable_localizedRadius_center hg L μ s β hc b h N hr hp
  exact measurable_refineRun_center hg L μ p s a n hc hU hc K v hi J

lemma measurable_approximatePlan {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a n β : ℝ) (b h v N K J : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) => RecursiveEnvelopeExecution.evalAt
      (fun k x => g x (w.2 k))
      (LongTails.Algorithms.StochasticEnvelopeProgram.approximatePlan L μ p s a n β w.1 b h v N K J) 0) := by
  have hc : Measurable (StochasticEnvelopeTransport.coupledApproximation (Ω := Ω) b h v N K J) := by
    unfold StochasticEnvelopeTransport.coupledApproximation StochasticEnvelopeTransport.groupApproximation
    fun_prop
  simp_rw [StochasticEnvelopeTransport.evalAt_approximatePlan_coupled]
  exact measurable_approximate_center hg L μ p s a n β measurable_fst b h v N K J
    ((hc.comp measurable_snd).fst.fst) ((hc.comp measurable_snd).fst.snd) ((hc.comp measurable_snd).snd)

end LongTails.Proofs.StochasticEnvelopeMeasurability
