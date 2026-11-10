import LongTails.Proofs.ProximalEf21SetupGeometry
import LongTails.Proofs.ProximalEf21ConditionalBatch

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

noncomputable section

namespace LongTails.Proofs.ProximalEf21Regularity

open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21SetupGeometry
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21Regularization

variable {p : Params} {I : Instance p}
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma extended_regularizer_measurable (h : ProblemAssumptions p I) : Measurable I.ψ := by
  apply measurable_of_Iic
  intro a
  induction a using EReal.rec with
  | bot =>
      have he : I.ψ ⁻¹' Set.Iic ⊥ = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_empty_iff_false]
        exact iff_false_intro (h.regularizerNoBottom x)
      rw [he]
      exact MeasurableSet.empty
  | coe a =>
      have hc : Continuous (fun x : Point p => (x, a)) := continuous_id.prodMk continuous_const
      have he : I.ψ ⁻¹' Set.Iic (a : EReal) =
          (fun x : Point p => (x, a)) ⁻¹' {z : Point p × ℝ | I.ψ z.1 ≤ (z.2 : EReal)} := rfl
      rw [he]
      exact (h.regularizerClosed.preimage hc).measurableSet
  | top => simp

lemma regularizer_measurable (h : ProblemAssumptions p I) : Measurable (psiValue I) := by
  exact measurable_ereal_toReal.comp (extended_regularizer_measurable h)

lemma gradient_continuous (h : ProblemAssumptions p I) (i : Fin p.workers) :
    Continuous (gradient (I.f i)) := by
  have hl : LipschitzWith ⟨I.localL i, h.localNonnegative i⟩ (gradient (I.f i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm] using h.localSmooth i x y
  exact hl.continuous

lemma smooth_objective_continuous (h : ProblemAssumptions p I) :
    Continuous (smoothObjective I) := by
  unfold smoothObjective
  apply Continuous.const_mul
  apply continuous_finset_sum
  intro i hi
  exact continuous_iff_continuousAt.mpr (fun x => (h.localGradient i x).continuousAt)

lemma norm_square_integrable {E : Type*} [NormedAddCommGroup E]
    {x : Ω → E} (hx : MemLp x 2 P) : Integrable (fun ω => ‖x ω‖ ^ 2) P :=
  (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx

lemma memLp_of_integrable_square {E : Type*} [NormedAddCommGroup E]
    {x : Ω → E} (hx : AEStronglyMeasurable x P)
    (hi : Integrable (fun ω => ‖x ω‖ ^ 2) P) : MemLp x 2 P :=
  (memLp_two_iff_integrable_sq_norm hx).mpr hi

lemma integrable_sandwich {f lo hi : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) (hlo : Integrable lo P) (hhi : Integrable hi P)
    (hl : ∀ᵐ ω ∂P, lo ω ≤ f ω) (hu : ∀ᵐ ω ∂P, f ω ≤ hi ω) :
    Integrable f P := by
  apply (hlo.norm.add hhi.norm).mono' hf
  filter_upwards [hl, hu] with ω hl hu
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (lo ω), abs_nonneg (hi ω)]
  · linarith [le_abs_self (hi ω), abs_nonneg (lo ω)]

lemma gradient_memLp (h : ProblemAssumptions p I) (i : Fin p.workers)
    {x : Ω → Point p} (hx : MemLp x 2 P) :
    MemLp (fun ω => gradient (I.f i) (x ω)) 2 P := by
  have hm := (gradient_continuous h i).comp_aestronglyMeasurable hx.aestronglyMeasurable
  have hb : MemLp (fun ω => ‖gradient (I.f i) (0 : Point p)‖ +
      I.localL i * ‖x ω‖) 2 P :=
    (memLp_const _).add (hx.norm.const_smul (I.localL i))
  apply hb.mono' hm
  filter_upwards [] with ω
  have hn := norm_add_le (gradient (I.f i) (x ω) - gradient (I.f i) 0)
    (gradient (I.f i) 0)
  have hl := h.localSmooth i (x ω) 0
  simpa only [sub_add_cancel, sub_zero] using le_trans hn (by linarith)

lemma prox_memLp (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) {u : Ω → Point p} (hu : MemLp u 2 P) :
    MemLp (fun ω => I.prox τ (u ω)) 2 P := by
  have hl : LipschitzWith 1 (I.prox τ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using prox_nonexpansive hp h hτ x y
  have hm := hl.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hb : MemLp (fun ω => ‖I.prox τ 0‖ + ‖u ω‖) 2 P := (memLp_const _).add hu.norm
  apply hb.mono' hm
  filter_upwards [] with ω
  have hn := norm_add_le (I.prox τ (u ω) - I.prox τ 0) (I.prox τ 0)
  have hl' := prox_nonexpansive hp h hτ (u ω) 0
  simp only [sub_add_cancel, sub_zero] at hn hl'
  linarith

lemma regularizer_at_prox_integrable (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) {u : Ω → Point p} (hu : MemLp u 2 P) :
    Integrable (fun ω => psiValue I (I.prox τ (u ω))) P := by
  have hy := prox_memLp P hp h hτ hu
  have hm := (regularizer_measurable h).comp_aemeasurable hy.aestronglyMeasurable.aemeasurable
  let a := workerMean (fun i => gradient (I.f i) I.xstar)
  have hlo : Integrable (fun ω => psiValue I I.xstar +
      ⟪-a, I.prox τ (u ω) - I.xstar⟫_ℝ) P :=
    (integrable_const _).add (integrable_inner_of_memLp_two P _ _ (memLp_const _)
      (hy.sub (memLp_const _)))
  have hhi : Integrable (fun ω => psiValue I I.xstar +
      ‖I.xstar - u ω‖ ^ 2 / (2 * τ)) P :=
    (integrable_const _).add
      ((norm_square_integrable P ((memLp_const I.xstar).sub hu)).div_const _)
  apply integrable_sandwich P hm.aestronglyMeasurable hlo hhi
  · filter_upwards [] with ω
    exact composite_optimum_support h hp.1 _ (h.proximalFinite τ hτ _)
  · filter_upwards [] with ω
    have hmin := finite_prox_min h hτ (u ω) I.xstar h.optimumFinite
    have hn : 0 ≤ ‖I.prox τ (u ω) - u ω‖ ^ 2 / (2 * τ) := by positivity
    linarith

lemma local_objective_integrable (h : ProblemAssumptions p I)
    (i : Fin p.workers) {x : Ω → Point p} (hx : MemLp x 2 P) :
    Integrable (fun ω => I.f i (x ω)) P := by
  have hc : Continuous (I.f i) :=
    continuous_iff_continuousAt.mpr (fun z => (h.localGradient i z).continuousAt)
  have hm := hc.comp_aestronglyMeasurable hx.aestronglyMeasurable
  have ha : Integrable (fun ω => I.f i 0 + ⟪gradient (I.f i) 0, x ω⟫_ℝ) P :=
    (integrable_const _).add (integrable_inner_of_memLp_two P _ _ (memLp_const _) hx)
  have hq := (norm_square_integrable P hx).const_mul (I.localL i / 2)
  apply integrable_sandwich P hm ha (ha.add hq)
  · filter_upwards [] with ω
    simpa using convex_gradient_lower (I.f i) (gradient (I.f i))
      (h.localConvex i) (h.localGradient i) 0 (x ω)
  · filter_upwards [] with ω
    simpa using smooth_gradient_upper (I.f i) (gradient (I.f i)) (I.localL i)
      (h.localNonnegative i) (h.localGradient i) (h.localSmooth i) 0 (x ω)

lemma smooth_objective_integrable (h : ProblemAssumptions p I)
    {x : Ω → Point p} (hx : MemLp x 2 P) :
    Integrable (fun ω => smoothObjective I (x ω)) P := by
  exact (integrable_finset_sum _ (fun i _ => local_objective_integrable P h i hx)).const_mul _

lemma gap_integrable (hp : spec.valid p) (h : ProblemAssumptions p I)
    {x : Ω → Point p} (hx : MemLp x 2 P)
    (hψ : Integrable (fun ω => psiValue I (x ω)) P) :
    Integrable (fun ω => (geometry hp h).gap (x ω)) P := by
  exact ((smooth_objective_integrable P h hx).add hψ).sub (integrable_const _)

lemma regularized_gap_integrable (hp : spec.valid p) (h : ProblemAssumptions p I)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * p.L)
    {x : Ω → Point p} (hx : MemLp x 2 P)
    (hψ : Integrable (fun ω => psiValue I (x ω)) P) :
    Integrable (fun ω => ((geometry hp h).regularized μ hμ hμL).gap (x ω)) P := by
  simp_rw [ConvexCompositeGeometry.regularized_gap]
  exact (gap_integrable P hp h hx hψ).add
    ((norm_square_integrable P (hx.sub (memLp_const _))).const_mul _)

lemma regularized_gradient_memLp (hp : spec.valid p) (h : ProblemAssumptions p I)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * p.L) (i : Fin p.workers)
    {x : Ω → Point p} (hx : MemLp x 2 P) :
    MemLp (fun ω => ((geometry hp h).regularized μ hμ hμL).grad i (x ω)) 2 P := by
  exact (gradient_memLp P h i hx).add ((hx.sub (memLp_const _)).const_smul μ)

lemma auxiliary_memLp (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) {x : Ω → Point p} {m : Fin p.workers → Ω → Point p}
    (hx : MemLp x 2 P) (hm : ∀ i, MemLp (m i) 2 P) :
    MemLp (fun ω => I.prox τ (x ω - τ • workerMean (fun i => m i ω))) 2 P := by
  apply prox_memLp P hp h hτ
  exact hx.sub ((workerMean_memLp P m hm).const_smul τ)

lemma initial_momentum_memLp (h : ProblemAssumptions p I)
    (O : OracleTemplate.Oracle (Query p) (Reply p) 4) (i : Fin p.workers) :
    MemLp (fun ω : Randomness p O => ω.1.1 i) 2 (executionMeasure p O) := by
  have hm : Measurable (fun z : InitialMemories p => z.1 i - gradient (I.f i) p.x0) := by
    fun_prop
  have he : MemLp (fun z : InitialMemories p => z.1 i - gradient (I.f i) p.x0) 2
      (p.initialLaw : Measure _) :=
    memLp_of_integrable_square (p.initialLaw : Measure _) hm.aestronglyMeasurable
      (h.momentumInitiallyIntegrable i)
  have hi := (h.momentumInitiallyIntegrable i).comp_fst (ν := (O.law : Measure _))
  have he' : MemLp (fun ω : Randomness p O => ω.1.1 i - gradient (I.f i) p.x0) 2
      (executionMeasure p O) := by
    apply memLp_of_integrable_square (executionMeasure p O) (by fun_prop)
    exact hi
  simpa only [sub_add_cancel] using he'.add (memLp_const (gradient (I.f i) p.x0))

lemma initial_compressed_memLp (h : ProblemAssumptions p I)
    (O : OracleTemplate.Oracle (Query p) (Reply p) 4) (i : Fin p.workers) :
    MemLp (fun ω : Randomness p O => ω.1.2 i) 2 (executionMeasure p O) := by
  have hi := (h.compressionInitiallyIntegrable i).comp_fst (ν := (O.law : Measure _))
  have he : MemLp (fun ω : Randomness p O => ω.1.2 i - ω.1.1 i) 2
      (executionMeasure p O) := by
    apply memLp_of_integrable_square (executionMeasure p O) (by fun_prop)
    exact hi
  simpa only [sub_add_cancel] using he.add (initial_momentum_memLp h O i)

end LongTails.Proofs.ProximalEf21Regularity
