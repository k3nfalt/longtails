import LongTails.Proofs.MultiplicativeRobustConfidence
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.ValidatedHessianSampling
import LongTails.Proofs.RegularizedProxEgRepeat
import LongTails.Proofs.StochasticQuasarCleanupExecution
import LongTails.Proofs.StochasticQuasarInnerSampling
import LongTails.Proofs.StochasticQuasarCleanupGeometry

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.StochasticQuasar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma medoid_rms_confidence {X : Ω → E} (hX : Measurable X) (u : E) {r : ℝ}
    (hr : 0 < r) (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ r ^ 2) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | 96 * r < ‖MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have ht := RobustGradient.norm_tail_le_second_moment hi
    (by positivity : 0 < 16 * r) hm
  have he : r ^ 2 / (16 * r) ^ 2 = (1 / 256 : ℝ) := by
    field_simp
    ring
  rw [he] at ht
  have hh := MultiplicativeRobustEstimator.medoid_failure_probability hX u
    (by positivity : 0 ≤ 16 * r) ht n
  simpa only [show 6 * (16 * r) = 96 * r by ring] using hh

lemma medoid_variance_confidence {X : Ω → E} (hX : Measurable X) (u : E) {r : ℝ}
    (hr : 0 < r) (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ r ^ 2 / 256) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | 6 * r < ‖MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  apply MultiplicativeRobustEstimator.medoid_failure_probability hX u hr.le
  have ht := RobustGradient.norm_tail_le_second_moment hi hr hm
  apply ht.trans_eq
  field_simp

lemma block_medoid_confidence (μ : Measure Ω) [IsProbabilityMeasure μ] (k n : ℕ)
    {X : (Fin k → Ω) → E} (hX : Measurable X) (u : E) {r : ℝ} (hr : 0 ≤ r)
    (hp : (Measure.pi fun _ : Fin k => μ).real {ω | r < ‖X ω - u‖} ≤ 1 / 256) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | 6 * r < ‖MultiplicativeRobustEstimator.medoid
        (fun j : Fin (n + 1) => X (fun i : Fin k => ξ (j.val * k + i.val))) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hpre := LongTails.Proofs.ValidatedHessianSampling.finite_blocks_preserving μ (n + 1) k
  have hm : MeasurableSet {ξ : Fin (n + 1) → Fin k → Ω |
      6 * r < ‖MultiplicativeRobustEstimator.medoid (fun j => X (ξ j)) - u‖} :=
    measurableSet_lt measurable_const ((MultiplicativeRobustEstimator.measurable_medoid.comp
      (Measurable.of_eval (fun j => hX.comp (measurable_pi_apply j)))).sub measurable_const).norm
  exact (hpre.measure_preimage hm.nullMeasurableSet).trans_le
    (MultiplicativeRobustEstimator.medoid_failure_probability hX u hr hp n)

lemma stream_medoid_confidence (μ : Measure Ω) [IsProbabilityMeasure μ] (ω0 : Ω) (k n : ℕ)
    {X : (ℕ → Ω) → E} (hX : Measurable X)
    (hdep : ∀ ξ ζ, (∀ i, i < k → ξ i = ζ i) → X ξ = X ζ)
    (u : E) {r : ℝ} (hr : 0 ≤ r)
    (hp : (Measure.infinitePi fun _ : ℕ => μ).real {ω | r < ‖X ω - u‖} ≤ 1 / 256) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | 6 * r < ‖MultiplicativeRobustEstimator.medoid
        (fun j : Fin (n + 1) => X (fun i => ξ (j.val * k + i))) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let Y : (Fin k → Ω) → E := fun ξ => X (StochasticCohypomonotone.extendP ω0 k ξ)
  have hY : Measurable Y := hX.comp (StochasticCohypomonotone.measurable_extendP ω0 k)
  have he (ξ : ℕ → Ω) : X ξ = Y (fun i => ξ i) := by
    apply hdep
    intro i hi
    simp [StochasticCohypomonotone.extendP, hi]
  have hpre := StochasticGeneralized.prefix_preserving μ k
  have hm : MeasurableSet {ξ : Fin k → Ω | r < ‖Y ξ - u‖} :=
    measurableSet_lt measurable_const ((hY.sub measurable_const).norm)
  have hpY : (Measure.pi fun _ : Fin k => μ).real {ξ | r < ‖Y ξ - u‖} ≤ 1 / 256 := by
    rw [← hpre.measureReal_preimage hm.nullMeasurableSet]
    simpa only [Set.preimage_ofPred_eq, ← he] using hp
  have hb := block_medoid_confidence μ k n hY u hr hpY
  have hout (ξ : ℕ → Ω) :
      (fun j : Fin (n + 1) => X (fun i => ξ (j.val * k + i))) =
        (fun j : Fin (n + 1) => Y (fun i : Fin k => ξ (j.val * k + i.val))) := by
    funext j
    exact he (fun i => ξ (j.val * k + i))
  simp_rw [hout]
  exact hb

lemma sampled_medoid_confidence {Q : Type*} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ω0 : Ω) (g : Q → Ω → E) {k : ℕ} (plan : QueryPlan Q E E k) (n : ℕ)
    (hm : Measurable (fun ξ => QueryPlan.sampledEval g ξ plan 0))
    (u : E) {r : ℝ} (hr : 0 ≤ r)
    (hp : (Measure.infinitePi fun _ : ℕ => μ).real
      {ξ | r < ‖QueryPlan.sampledEval g ξ plan 0 - u‖} ≤ 1 / 256) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | 6 * r < ‖MultiplicativeRobustEstimator.medoid
        (QueryPlan.sampledEval g ξ
          (LongTails.Algorithms.StochasticEnvelopeProgram.collectPlans (n + 1) (fun _ => plan)) 0) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hd (ξ ζ : ℕ → Ω) (h : ∀ i, i < k → ξ i = ζ i) :
      QueryPlan.sampledEval g ξ plan 0 = QueryPlan.sampledEval g ζ plan 0 :=
    StochasticCohypomonotone.sampledEval_congr g plan ξ ζ 0 (by simpa only [Nat.zero_add] using h)
  have hb := stream_medoid_confidence μ ω0 k n hm hd u hr hp
  have he (ξ : ℕ → Ω) (j : Fin (n + 1)) :
      QueryPlan.sampledEval g ξ plan (0 + k * j.val) =
        QueryPlan.sampledEval g (fun i => ξ (j.val * k + i)) plan 0 := by
    simpa only [Nat.zero_add, Nat.mul_comm] using
      StochasticCohypomonotone.sampledEval_shift g plan ξ (k * j.val)
  simpa only [sampled_collect_plans, he] using hb

lemma fresh_failure_bound {V : Type*} [MeasurableSpace V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (k : ℕ)
    (X : (ℕ → Ω) → V) (hX : Measurable X)
    (hdep : ∀ ξ ζ, (∀ i, i < k → ξ i = ζ i) → X ξ = X ζ)
    (bad : Set (V × (ℕ → Ω))) (hbad : MeasurableSet bad) {a : ℝ≥0∞}
    (hp : ∀ ξ, (Measure.infinitePi fun _ : ℕ => μ) {ζ | (X ξ, ζ) ∈ bad} ≤ a) :
    (Measure.infinitePi fun _ : ℕ => μ) {ξ | (X ξ, fun i => ξ (k + i)) ∈ bad} ≤ a := by
  let F : V × (ℕ → Ω) → ℝ≥0∞ := bad.indicator 1
  have hF : Measurable F := measurable_const.indicator hbad
  have hm : MeasurableSet {ξ : ℕ → Ω | (X ξ, fun i => ξ (k + i)) ∈ bad} :=
    hbad.preimage (hX.prodMk (by fun_prop))
  have he := LongTails.Proofs.StochasticEnvelopeFreshness.prefix_tail_lintegral μ k X hX hdep F hF
  have hl : (∫⁻ ξ, F (X ξ, fun i => ξ (k + i)) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      (Measure.infinitePi fun _ : ℕ => μ) {ξ | (X ξ, fun i => ξ (k + i)) ∈ bad} := by
    exact lintegral_indicator_one hm
  have hr (ξ : ℕ → Ω) :
      (∫⁻ ζ, F (X ξ, ζ) ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ a := by
    have hm' : MeasurableSet {ζ : ℕ → Ω | (X ξ, ζ) ∈ bad} :=
      hbad.preimage (measurable_const.prodMk measurable_id)
    exact (lintegral_indicator_one hm').trans_le (hp ξ)
  rw [← hl, he]
  calc
    _ ≤ ∫⁻ _ξ : ℕ → Ω, a ∂Measure.infinitePi (fun _ : ℕ => μ) := lintegral_mono hr
    _ = a := by simp

section Prox
variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma robust_prox_confidence (μ : Measure Ω) [IsProbabilityMeasure μ] (ω0 : Ω)
    {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E} {g : E → Ω → E}
    {x0 c : E} {L σ D r : ℝ} (hP : ConstrainedMonotone.Proj Q P)
    (hL : 0 < L) (hD0 : 0 < D) (hr : 0 < r) (hx0 : x0 ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hG : ∀ x ∈ Q, HasGradientAt f (G x) x)
    (hlip : ∀ x ∈ Q, ∀ y ∈ Q, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | 96 * r < ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (robustProxPlan L σ D r c x0 n) 0 - constrainedProx Q f L c‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let X := fun ξ : ℕ → Ω => QueryPlan.sampledEval
    (ProjectedClippedExtragradient.channelReply P g) ξ (approximationPlan L σ D r c x0) 0
  have hX : Measurable X :=
    (measurable_sampled_inner_plan hP.lipschitz.continuous.measurable hgm L σ D c
      (innerStageCount D r) 0).comp (measurable_const.prodMk measurable_id)
  have hp := constrainedProx_spec hQ ⟨x0, hx0⟩ hG L c
  have hi := integrable_feasible_squared (ν := Measure.infinitePi fun _ : ℕ => μ) hp.1 hD hX
    (fun ξ => sampled_inner_plan_mem hP.mem g ξ L σ D c hx0 (innerStageCount D r) 0)
  have hm := prox_approximation_integral (StochasticGeneralized.infinitePi_iid μ)
    hP hL hD0 hr hx0 hQ hcv hD hG hlip hgm hgi hmean hg2 hvar (c := c)
  have ht := RobustGradient.norm_tail_le_second_moment hi (by positivity : 0 < 16 * r) hm
  have he : r ^ 2 / (16 * r) ^ 2 = (1 / 256 : ℝ) := by
    field_simp
    ring
  rw [he] at ht
  have hb := sampled_medoid_confidence μ ω0 (ProjectedClippedExtragradient.channelReply P g)
    (approximationPlan L σ D r c x0) n hX (constrainedProx Q f L c)
    (by positivity : 0 ≤ 16 * r) ht
  simpa only [robustProxPlan, QueryPlan.sampledEval_map,
    show 6 * (16 * r) = 96 * r by ring] using hb

lemma robust_gradient_confidence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : E → E) (g : E → Ω → E) (x u : E) (hgm : Measurable (g x))
    (hgi : Integrable (g x) μ) (hmean : (∫ ω, g x ω ∂μ) = u)
    (hg2 : Integrable (fun ω => ‖g x ω - u‖ ^ 2) μ)
    {σ r : ℝ} (hvar : (∫ ω, ‖g x ω - u‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (hr : 0 < r) (b n : ℕ) (hb : 0 < b) (htune : σ ^ 2 / b ≤ r ^ 2 / 256) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | 6 * r < ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (robustGradientPlan x b n) 0 - u‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let X : (Fin b → Ω) → E := fun ξ => (1 / (b : ℝ)) • ∑ i, g x (ξ i)
  have hX : Measurable X := by
    exact (Finset.measurable_sum _ (fun i _ => hgm.comp (measurable_pi_apply i))).const_smul _
  have hv := RobustGradient.finite_mean_variance hgm hgi u hg2 hmean b hb
  have hm : (∫ ξ, ‖X ξ - u‖ ^ 2 ∂Measure.pi (fun _ : Fin b => μ)) ≤ r ^ 2 / 256 := by
    rw [show (∫ ξ, ‖X ξ - u‖ ^ 2 ∂Measure.pi (fun _ : Fin b => μ)) =
      (∫ ω, ‖g x ω - u‖ ^ 2 ∂μ) / b from hv.2]
    exact (div_le_div_of_nonneg_right hvar (Nat.cast_nonneg b)).trans htune
  have ht := RobustGradient.norm_tail_le_second_moment hv.1 hr hm
  have he : (r ^ 2 / 256) / r ^ 2 = (1 / 256 : ℝ) := by field_simp
  rw [he] at ht
  have hh := block_medoid_confidence μ b n hX u hr.le ht
  simpa only [sampled_robust_gradient, ProjectedClippedExtragradient.sampled_meanPlan,
    Nat.zero_add, Nat.mul_comm, X] using hh

lemma cleanup_gradient_confidence (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Q : Set E} {P G : E → E} {g : E → Ω → E} {L σ D r s : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (c : E) {x0 : E} (hx0 : x0 ∈ Q) (hs : 0 < s) (b n : ℕ)
    (hb : 0 < b) (htune : σ ^ 2 / b ≤ s ^ 2 / 256) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | let x := QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
              (robustProxPlan L σ D r c x0 n) 0
           6 * s < ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
              (robustGradientPlan x b n) (innerCalls L σ D (innerStageCount D r) * (n + 1)) - G x‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let k := innerCalls L σ D (innerStageCount D r) * (n + 1)
  let X := fun ξ : ℕ → Ω => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
    (robustProxPlan L σ D r c x0 n) 0
  have hX : Measurable X :=
    (measurable_robust_prox_joint hP.lipschitz.continuous.measurable hgm L σ D r n 0).comp
      ((measurable_const (a := (c, x0))).prodMk measurable_id)
  have hmem (ξ : ℕ → Ω) : X ξ ∈ Q := sampled_robust_prox_mem hP.mem g ξ L σ D r c hx0 n 0
  have hdep (ξ ζ : ℕ → Ω) (h : ∀ i, i < k → ξ i = ζ i) : X ξ = X ζ :=
    StochasticCohypomonotone.sampledEval_congr _ _ ξ ζ 0 (by simpa only [Nat.zero_add] using h)
  let bad : Set (E × (ℕ → Ω)) := {w | 6 * s < ‖QueryPlan.sampledEval
    (ProjectedClippedExtragradient.channelReply P g) w.2 (robustGradientPlan w.1 b n) 0 - G (P w.1)‖}
  have hGm := (projected_gradient_lipschitz hP hL hlip).continuous.measurable
  have hbad : MeasurableSet bad := measurableSet_lt measurable_const
    (((measurable_robust_gradient_joint P hgm b n 0).sub (hGm.comp measurable_fst)).norm)
  have hp (ξ : ℕ → Ω) : (Measure.infinitePi fun _ : ℕ => μ) {ζ | (X ξ, ζ) ∈ bad} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
    have hh := robust_gradient_confidence μ P g (X ξ) (G (X ξ))
      (hgm.comp (measurable_const.prodMk measurable_id)) (hgi _ (hmem ξ))
      (hmean _ (hmem ξ)) (hg2 _ (hmem ξ)) (hvar _ (hmem ξ)) hs b n hb htune
    simpa only [bad, Set.mem_ofPred_eq, hP.fixed (hmem ξ)] using hh
  have hh := fresh_failure_bound μ k X hX hdep bad hbad hp
  have he (ξ : ℕ → Ω) : QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (robustGradientPlan (X ξ) b n) k =
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) (fun i => ξ (k + i))
        (robustGradientPlan (X ξ) b n) 0 := StochasticCohypomonotone.sampledEval_shift _ _ ξ k
  simpa only [bad, Set.mem_ofPred_eq, hP.fixed (hmem _), ← he, X, k] using hh

lemma cleanup_failure_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (ω0 : Ω)
    {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E} {g : E → Ω → E}
    {x0 c u : E} {L σ D r s ε : ℝ} (hP : ConstrainedMonotone.Proj Q P)
    (hL : 0 < L) (hD0 : 0 < D) (hr : 0 < r) (hs : 0 < s) (hε : 0 < ε) (hx0 : x0 ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hG : ∀ x ∈ Q, HasGradientAt f (G x) x)
    (hlip : ∀ x ∈ Q, ∀ y ∈ Q, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (b n : ℕ) (hb : 0 < b) (htune : σ ^ 2 / b ≤ s ^ 2 / 256)
    (hprox : (96 * r) ^ 2 ≤ ε / (12 * L)) (hraw : 6 * s ≤ ε / (4 * D))
    (hgap : f (constrainedProx Q f L c) + L * ‖constrainedProx Q f L c - c‖ ^ 2 - f u ≤ ε / 8) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | ε < f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (cleanupPlan L σ D r c x0 b n) 0) - f u} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  let X := fun ξ : ℕ → Ω => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
    (robustProxPlan L σ D r c x0 n) 0
  let R := fun ξ : ℕ → Ω => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
    (robustGradientPlan (X ξ) b n) (innerCalls L σ D (innerStageCount D r) * (n + 1))
  let A : Set (ℕ → Ω) := {ξ | 96 * r < ‖X ξ - constrainedProx Q f L c‖}
  let B : Set (ℕ → Ω) := {ξ | 6 * s < ‖R ξ - G (X ξ)‖}
  have hA : (Measure.infinitePi fun _ : ℕ => μ) A ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) :=
    robust_prox_confidence μ ω0 hP hL hD0 hr hx0 hQ hcv hD hG hlip hgm hgi hmean hg2 hvar n
  have hB : (Measure.infinitePi fun _ : ℕ => μ) B ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) :=
    cleanup_gradient_confidence μ hP hL.le hlip hgm hgi hmean hg2 hvar c hx0 hs b n hb htune
  apply (measure_mono (t := A ∪ B) ?_).trans ((measure_union_le A B).trans (add_le_add hA hB))
  intro ξ hξ
  by_contra hout
  have ha : ‖X ξ - constrainedProx Q f L c‖ ≤ 96 * r := by
    exact le_of_not_gt (fun h => hout (Or.inl h))
  have hb' : ‖R ξ - G (X ξ)‖ ≤ 6 * s := by
    exact le_of_not_gt (fun h => hout (Or.inr h))
  have hp := constrainedProx_spec hQ ⟨x0, hx0⟩ hG L c
  have hx := sampled_robust_prox_mem hP.mem g ξ L σ D r c hx0 n 0
  have hh := cleanup_accurate hP hL hD0 hε hcv hG hlip hD hx hp.1
    ((pow_le_pow_left₀ (norm_nonneg _) ha 2).trans hprox) (hb'.trans hraw) hgap
  have he : QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (cleanupPlan L σ D r c x0 b n) 0 =
      P (X ξ - (1 / (3 * L)) • (R ξ + (2 * L) • (X ξ - c))) := by
    simpa only [Nat.zero_add, X, R] using sampled_cleanup P g ξ L σ D r c x0 b n 0
  simp only [Set.mem_ofPred_eq] at hξ
  rw [he] at hξ
  exact (not_lt_of_ge hh) hξ

lemma initial_cleanup_failure_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E} {g : E → Ω → E}
    {x0 u : E} {L σ D s ε : ℝ} (hP : ConstrainedMonotone.Proj Q P)
    (hL : 0 < L) (hD0 : 0 < D) (hs : 0 < s) (hx0 : x0 ∈ Q) (hu : u ∈ Q)
    (hcv : Convex ℝ Q) (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hG : ∀ x ∈ Q, HasGradientAt f (G x) x)
    (hlip : ∀ x ∈ Q, ∀ y ∈ Q, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hgm : Measurable (g x0)) (hgi : Integrable (g x0) μ)
    (hmean : (∫ ω, g x0 ω ∂μ) = G x0)
    (hg2 : Integrable (fun ω => ‖g x0 ω - G x0‖ ^ 2) μ)
    (hvar : (∫ ω, ‖g x0 ω - G x0‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (b n : ℕ) (hb : 0 < b) (htune : σ ^ 2 / b ≤ s ^ 2 / 256)
    (hraw : 6 * s ≤ ε / (4 * D)) (he : 4 * L * D ^ 2 ≤ ε) :
    (Measure.infinitePi fun _ : ℕ => μ)
      {ξ | ε < f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (initialCleanupPlan L x0 b n) 0) - f u} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  apply (measure_mono ?_).trans
    (robust_gradient_confidence μ P g x0 (G x0) hgm hgi hmean hg2 hvar hs b n hb htune)
  intro ξ hξ
  by_contra hbad
  have hh := initial_cleanup_accurate hP hL hD0 hcv hG hlip hD hx0 hu he
    ((le_of_not_gt hbad).trans hraw)
  simp only [Set.mem_ofPred_eq] at hξ
  rw [sampled_initial_cleanup] at hξ
  exact (not_lt_of_ge hh) hξ

end Prox

end OracleTemplate.StochasticQuasar
