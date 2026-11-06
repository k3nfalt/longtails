import LongTails.Proofs.StochasticQuasarInnerExecution
import LongTails.Proofs.StochasticEnvelopeFreshness
import LongTails.Proofs.RegularizedProxEgRepeat
import LongTails.Proofs.ConstrainedRegularization

open MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma inner_step_stream_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {G : E → E} {g : E → Ω → E} {u v c : E} {L σ : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hPm : Measurable P) (hL : 0 < L)
    (hlip : ‖G u - G v‖ ≤ L * ‖u - v‖)
    (hfix : P (v - (1 / (3 * L)) • (G v + (2 * L) • (v - c))) = v)
    (hgm : Measurable (g u)) (hgi : Integrable (g u) μ)
    (hmean : (∫ ω, g u ω ∂μ) = G u)
    (hg2 : Integrable (fun ω => ‖g u ω - G u‖ ^ 2) μ)
    (hvar : (∫ ω, ‖g u ω - G u‖ ^ 2 ∂μ) ≤ σ ^ 2) (b : ℕ) (hb : 0 < b) :
    (∫ ξ : ℕ → Ω, ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (innerStepPlan L c u b) 0 - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤
      (4 / 9 : ℝ) * ‖u - v‖ ^ 2 + (1 / (3 * L)) ^ 2 * (σ ^ 2 / b) := by
  let F : (Fin b → Ω) → ℝ := fun ξ =>
    ‖P (u - (1 / (3 * L)) •
      ((1 / (b : ℝ)) • ∑ i, g u (ξ i) + (2 * L) • (u - c))) - v‖ ^ 2
  have hFm : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub _ measurable_const
    apply hPm.comp
    apply Measurable.sub measurable_const
    apply Measurable.const_smul
    apply Measurable.add _ measurable_const
    apply Measurable.const_smul
    exact Finset.measurable_sum _ (fun i _ => hgm.comp (measurable_pi_apply i))
  have hpre := StochasticGeneralized.prefix_preserving μ b
  have he : (∫ ξ : ℕ → Ω, F (fun i => ξ i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫ ξ, F ξ ∂Measure.pi (fun _ : Fin b => μ) := by
    rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hFm.aestronglyMeasurable]
  simp_rw [sampled_inner_step, Nat.zero_add]
  change (∫ ξ : ℕ → Ω, F (fun i => ξ i) ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ _
  rw [he]
  exact inner_batch_integral hP hPm hL hlip hfix hgm hgi hmean hg2 hvar b hb

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_feasible_squared {S : Type*} [MeasurableSpace S]
    {ν : Measure S} [IsProbabilityMeasure ν] {Q : Set E} {D : ℝ} {v : E}
    (hv : v ∈ Q) (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    {Y : S → E} (hY : Measurable Y) (hmem : ∀ s, Y s ∈ Q) :
    Integrable (fun s => ‖Y s - v‖ ^ 2) ν := by
  apply (integrable_const (D ^ 2)).mono' ((hY.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hD _ (hmem s) _ hv) 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma fresh_squared_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {D a b : ℝ} {v : E} (hv : v ∈ Q)
    (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) (Y : (ℕ → Ω) → E) (hY : Measurable Y) (hYm : ∀ ξ, Y ξ ∈ Q)
    (hdep : ∀ ξ ζ, (∀ j, j < n → ξ j = ζ j) → Y ξ = Y ζ)
    (F : E × (ℕ → Ω) → E) (hF : Measurable F)
    (hFm : ∀ x ∈ Q, ∀ ξ, F (x, ξ) ∈ Q)
    (hbound : ∀ x ∈ Q,
      (∫ ξ, ‖F (x, ξ) - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ a * ‖x - v‖ ^ 2 + b) :
    (∫ ξ, ‖F (Y ξ, fun j => ξ (n + j)) - v‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤
      a * (∫ ξ, ‖Y ξ - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) + b := by
  let ν := Measure.infinitePi fun _ : ℕ => μ
  let Z : (ℕ → Ω) → E := fun ξ => F (Y ξ, fun j => ξ (n + j))
  have htail : Measurable (fun ξ : ℕ → Ω => fun j => ξ (n + j)) := by fun_prop
  have hZ : Measurable Z := hF.comp (hY.prodMk htail)
  have hZi := integrable_feasible_squared (ν := ν) hv hD hZ (fun ξ => hFm _ (hYm ξ) _)
  have hYi := integrable_feasible_squared (ν := ν) hv hD hY hYm
  have hCi : Integrable (fun ξ => a * ‖Y ξ - v‖ ^ 2 + b) ν :=
    (hYi.const_mul a).add (integrable_const b)
  have he := LongTails.Proofs.StochasticEnvelopeFreshness.prefix_tail_lintegral μ n Y hY hdep
    (fun w => ENNReal.ofReal (‖F w - v‖ ^ 2))
    (ENNReal.measurable_ofReal.comp ((hF.sub measurable_const).norm.pow_const 2))
  have hi : (∫⁻ ξ, ENNReal.ofReal (‖Z ξ - v‖ ^ 2) ∂ν) ≤
      ∫⁻ ξ, ENNReal.ofReal (a * ‖Y ξ - v‖ ^ 2 + b) ∂ν := by
    rw [show (∫⁻ ξ, ENNReal.ofReal (‖Z ξ - v‖ ^ 2) ∂ν) =
      ∫⁻ ξ, ∫⁻ ζ, ENNReal.ofReal (‖F (Y ξ, ζ) - v‖ ^ 2) ∂ν ∂ν from he]
    apply lintegral_mono
    intro ξ
    have hFi := integrable_feasible_squared (ν := ν) hv hD
      (hF.comp (measurable_const.prodMk measurable_id)) (hFm _ (hYm ξ))
    change Integrable (fun ζ => ‖F (Y ξ, ζ) - v‖ ^ 2) ν at hFi
    change (∫⁻ ζ, ENNReal.ofReal (‖F (Y ξ, ζ) - v‖ ^ 2) ∂ν) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound _ (hYm ξ))
  rw [← ofReal_integral_eq_lintegral_ofReal hZi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hCi (Filter.Eventually.of_forall fun _ => by positivity)] at hi
  rw [integral_add (hYi.const_mul a) (integrable_const b), integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hi

lemma inner_repeat_two_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {G : E → E} {g : E → Ω → E} {u v c : E} {L σ D : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hPm : Measurable P) (hL : 0 < L)
    (hu : u ∈ Q) (hv : v ∈ Q) (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hlip : ∀ x ∈ Q, ‖G x - G v‖ ≤ L * ‖x - v‖)
    (hfix : P (v - (1 / (3 * L)) • (G v + (2 * L) • (v - c))) = v)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) (b : ℕ) (hb : 0 < b) :
    (∫ ξ : ℕ → Ω, ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (ProjectedClippedExtragradient.repeatPlan (fun x => innerStepPlan L c x b) 2 u) 0 - v‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤
      (16 / 81 : ℝ) * ‖u - v‖ ^ 2 + (13 / 9 : ℝ) * (1 / (3 * L)) ^ 2 * (σ ^ 2 / b) := by
  let Y : (ℕ → Ω) → E := fun ξ => QueryPlan.sampledEval
    (ProjectedClippedExtragradient.channelReply P g) ξ (innerStepPlan L c u b) 0
  let F : E × (ℕ → Ω) → E := fun w => QueryPlan.sampledEval
    (ProjectedClippedExtragradient.channelReply P g) w.2 (innerStepPlan L c w.1 b) 0
  have hF : Measurable F := measurable_sampled_inner_step hPm hgm L c b 0
  have hY : Measurable Y := hF.comp (measurable_const.prodMk measurable_id)
  have hYm : ∀ ξ, Y ξ ∈ Q := fun ξ => sampled_inner_step_mem hP.mem g ξ L c u b 0
  have hFm : ∀ x ∈ Q, ∀ ξ, F (x, ξ) ∈ Q := fun x _ ξ =>
    sampled_inner_step_mem hP.mem g ξ L c x b 0
  have hdep : ∀ ξ ζ, (∀ j, j < 1 + b → ξ j = ζ j) → Y ξ = Y ζ := by
    intro ξ ζ hh
    exact StochasticCohypomonotone.sampledEval_congr
      (ProjectedClippedExtragradient.channelReply P g) (innerStepPlan L c u b) ξ ζ 0
      (by simpa only [Nat.zero_add] using hh)
  have hbound (x : E) (hx : x ∈ Q) :
      (∫ ξ, ‖F (x, ξ) - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤
      (4 / 9 : ℝ) * ‖x - v‖ ^ 2 + (1 / (3 * L)) ^ 2 * (σ ^ 2 / b) :=
    inner_step_stream_integral hP hPm hL (hlip x hx) hfix
      (hgm.comp measurable_prodMk_left) (hgi x hx) (hmean x hx) (hg2 x hx) (hvar x hx) b hb
  have hh := fresh_squared_bound hv hD (by norm_num : (0 : ℝ) ≤ 4 / 9)
    (by positivity : 0 ≤ (1 / (3 * L)) ^ 2 * (σ ^ 2 / b)) (1 + b) Y hY hYm hdep F hF hFm hbound
  have hu' := hbound u hu
  have he (ξ : ℕ → Ω) :
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (ProjectedClippedExtragradient.repeatPlan (fun x => innerStepPlan L c x b) 2 u) 0 =
        F (Y ξ, fun j => ξ (1 + b + j)) := by
    simp only [ProjectedClippedExtragradient.repeatPlan, QueryPlan.sampledEval_bind,
      QueryPlan.sampledEval, Nat.zero_add]
    exact StochasticCohypomonotone.sampledEval_shift _ _ ξ (1 + b)
  simp_rw [he]
  change (∫ ξ, ‖F (Y ξ, fun j => ξ (1 + b + j)) - v‖ ^ 2
    ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ _
  change (∫ ξ, ‖Y ξ - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ _ at hu'
  nlinarith

lemma inner_plan_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {G : E → E} {g : E → Ω → E} {x0 v c : E} {L σ D : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hPm : Measurable P) (hL : 0 < L) (hD0 : 0 < D)
    (hx0 : x0 ∈ Q) (hv : v ∈ Q) (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hlip : ∀ x ∈ Q, ‖G x - G v‖ ≤ L * ‖x - v‖)
    (hfix : P (v - (1 / (3 * L)) • (G v + (2 * L) • (v - c))) = v)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) (k : ℕ) :
    (∫ ξ : ℕ → Ω, ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (innerPlan L σ D c x0 k) 0 - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤
      (D / (2 : ℝ) ^ k) ^ 2 := by
  induction k with
  | zero =>
    simp only [innerPlan, QueryPlan.sampledEval, integral_const, probReal_univ, one_smul,
      pow_zero, div_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD _ hx0 _ hv) 2
  | succ k ih =>
    let b := innerBatch L σ D k
    let Y : (ℕ → Ω) → E := fun ξ => QueryPlan.sampledEval
      (ProjectedClippedExtragradient.channelReply P g) ξ (innerPlan L σ D c x0 k) 0
    let F : E × (ℕ → Ω) → E := fun w => QueryPlan.sampledEval
      (ProjectedClippedExtragradient.channelReply P g) w.2
      (ProjectedClippedExtragradient.repeatPlan (fun x => innerStepPlan L c x b) 2 w.1) 0
    have hY : Measurable Y := (measurable_sampled_inner_plan hPm hgm L σ D c k 0).comp
      (measurable_const.prodMk measurable_id)
    have hYm : ∀ ξ, Y ξ ∈ Q := fun ξ => sampled_inner_plan_mem hP.mem g ξ L σ D c hx0 k 0
    have hF : Measurable F := measurable_sampled_inner_repeat hPm hgm L c b 2 0
    have hFm : ∀ x ∈ Q, ∀ ξ, F (x, ξ) ∈ Q := fun x hx ξ =>
      sampled_inner_repeat_mem hP.mem g ξ L c b 2 hx 0
    have hdep : ∀ ξ ζ, (∀ j, j < innerCalls L σ D k → ξ j = ζ j) → Y ξ = Y ζ := by
      intro ξ ζ hh
      exact StochasticCohypomonotone.sampledEval_congr
        (ProjectedClippedExtragradient.channelReply P g) (innerPlan L σ D c x0 k) ξ ζ 0
        (by simpa only [Nat.zero_add] using hh)
    have hbound (x : E) (hx : x ∈ Q) :
        (∫ ξ, ‖F (x, ξ) - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤
        (16 / 81 : ℝ) * ‖x - v‖ ^ 2 + (13 / 9 : ℝ) * (1 / (3 * L)) ^ 2 * (σ ^ 2 / b) :=
      inner_repeat_two_integral hP hPm hL hx hv hD hlip hfix hgm hgi hmean hg2 hvar b
        (inner_batch_positive L σ D k)
    have hh := fresh_squared_bound hv hD (by norm_num : (0 : ℝ) ≤ 16 / 81)
      (by positivity : 0 ≤ (13 / 9 : ℝ) * (1 / (3 * L)) ^ 2 * (σ ^ 2 / b))
      (innerCalls L σ D k) Y hY hYm hdep F hF hFm hbound
    have he (ξ : ℕ → Ω) : QueryPlan.sampledEval
        (ProjectedClippedExtragradient.channelReply P g) ξ (innerPlan L σ D c x0 (k + 1)) 0 =
        F (Y ξ, fun j => ξ (innerCalls L σ D k + j)) := by
      rw [innerPlan]
      erw [QueryPlan.sampledEval_bind]
      simp only [Nat.zero_add]
      exact StochasticCohypomonotone.sampledEval_shift _ _ ξ (innerCalls L σ D k)
    simp_rw [he]
    have hn := inner_batch_noise (σ := σ) (j := k) hL hD0
    have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg (1 / (3 * L)))
    have hscale : (1 / (3 * L)) ^ 2 * (L ^ 2 * innerRadius D k ^ 2) =
        innerRadius D k ^ 2 / 9 := by field_simp; ring
    rw [hscale] at hm
    have hr : (D / (2 : ℝ) ^ k) ^ 2 = 4 * innerRadius D k ^ 2 := by
      unfold innerRadius
      rw [pow_succ]
      field_simp
      ring
    rw [hr] at ih
    change (∫ ξ, ‖Y ξ - v‖ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ _ at ih
    change _ ≤ innerRadius D k ^ 2
    change (1 / (3 * L)) ^ 2 * (σ ^ 2 / (b : ℝ)) ≤ _ at hm
    nlinarith [sq_nonneg (innerRadius D k)]

lemma approximation_iid_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] {ν : Measure S} {ξ : ℕ → S → Ω}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ ν)
    {Q : Set E} {P : E → E} {G : E → E} {g : E → Ω → E} {x0 v c : E} {L σ D r : ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hPm : Measurable P) (hL : 0 < L) (hD0 : 0 < D)
    (hr : 0 < r) (hx0 : x0 ∈ Q) (hv : v ∈ Q)
    (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hlip : ∀ x ∈ Q, ‖G x - G v‖ ≤ L * ‖x - v‖)
    (hfix : P (v - (1 / (3 * L)) • (G v + (2 * L) • (v - c))) = v)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    (∫ s, ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g)
      (fun k => ξ k s) (approximationPlan L σ D r c x0) 0 - v‖ ^ 2 ∂ν) ≤ r ^ 2 := by
  let F : (ℕ → Ω) → ℝ := fun ζ => ‖QueryPlan.sampledEval
    (ProjectedClippedExtragradient.channelReply P g) ζ (approximationPlan L σ D r c x0) 0 - v‖ ^ 2
  have hFm : Measurable F :=
    (((measurable_sampled_inner_plan hPm hgm L σ D c (innerStageCount D r) 0).comp
      (measurable_const.prodMk measurable_id)).sub measurable_const).norm.pow_const 2
  have he : (∫ s, F (fun k => ξ k s) ∂ν) =
      ∫ ζ, F ζ ∂Measure.infinitePi (fun _ : ℕ => μ) := by
    rw [← hIID.stream_law.map_eq,
      integral_map hIID.stream_law.measurable.aemeasurable hFm.aestronglyMeasurable]
  change (∫ s, F (fun k => ξ k s) ∂ν) ≤ _
  rw [he]
  have hh := inner_plan_integral hP hPm hL hD0 hx0 hv hD hlip hfix hgm hgi hmean hg2 hvar
    (innerStageCount D r)
  exact hh.trans (pow_le_pow_left₀ (by positivity) (inner_stage_target hr) 2)

lemma prox_approximation_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] {ν : Measure S} {ξ : ℕ → S → Ω}
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ ν)
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
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    (∫ s, ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g)
      (fun k => ξ k s) (approximationPlan L σ D r c x0) 0 - constrainedProx Q f L c‖ ^ 2 ∂ν) ≤ r ^ 2 := by
  have hp := constrainedProx_spec hQ ⟨x0, hx0⟩ hG L c
  have hfix := regularized_projection_fixed hcv hP hp.1 (hG _ hp.1)
    (by positivity : 0 ≤ 1 / (3 * L)) hp.2
  exact approximation_iid_integral hIID hP hP.lipschitz.continuous.measurable hL hD0 hr hx0 hp.1
    hD (fun x hx => hlip x hx _ hp.1) hfix hgm hgi hmean hg2 hvar

end OracleTemplate.StochasticQuasar
