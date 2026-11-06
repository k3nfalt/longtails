import LongTails.Proofs.StochasticQuasarInnerSampling
import LongTails.Proofs.StochasticQuasarMlmcMoments
import LongTails.Proofs.GeneralNormClipping

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_feasible {S : Type*} [MeasurableSpace S]
    {ν : Measure S} [IsProbabilityMeasure ν] {Q : Set E} {D : ℝ} {v : E}
    (hv : v ∈ Q) (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    {Y : S → E} (hY : Measurable Y) (hmem : ∀ s, Y s ∈ Q) : Integrable Y ν := by
  apply (integrable_const (D + ‖v‖)).mono' hY.aestronglyMeasurable
  filter_upwards with s
  calc
    ‖Y s‖ = ‖(Y s - v) + v‖ := by rw [sub_add_cancel]
    _ ≤ ‖Y s - v‖ + ‖v‖ := norm_add_le _ _
    _ ≤ D + ‖v‖ := add_le_add_left (hD _ (hmem s) _ hv) _

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampled_mlmc_plan (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D r : ℝ) (c x0 : E) (m : ℕ) (j : Fin (m + 1)) (call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (mlmcPlan L σ D r c x0 m j) call =
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (approximationPlan L σ D r c x0) call + (mlmcWeight m j)⁻¹ •
      (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (approximationPlan L σ D (mlmcRadius r (j.val + 1)) c x0)
        (call + innerCalls L σ D (innerStageCount D r)) -
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (approximationPlan L σ D (mlmcRadius r j.val) c x0)
        (call + innerCalls L σ D (innerStageCount D r) +
          innerCalls L σ D (innerStageCount D (mlmcRadius r (j.val + 1))))) := by
  unfold mlmcPlan
  erw [QueryPlan.sampledEval_bind, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]

omit [CompleteSpace E] in
lemma measurable_mlmc_joint {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D r : ℝ) (m : ℕ) (j : Fin (m + 1)) (call : ℕ) :
    Measurable (fun w : (E × E) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (mlmcPlan L σ D r w.1.1 w.1.2 m j) call) := by
  simp_rw [sampled_mlmc_plan]
  exact (measurable_inner_plan_joint hP hg L σ D (innerStageCount D r) call).add
    (((measurable_inner_plan_joint hP hg L σ D (innerStageCount D (mlmcRadius r (j.val + 1)))
      (call + innerCalls L σ D (innerStageCount D r))).sub
      (measurable_inner_plan_joint hP hg L σ D (innerStageCount D (mlmcRadius r j.val))
        (call + innerCalls L σ D (innerStageCount D r) +
          innerCalls L σ D (innerStageCount D (mlmcRadius r (j.val + 1)))))).const_smul (mlmcWeight m j)⁻¹)

lemma iid_shift_preserving (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun j => ξ (n + j))
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.infinitePi fun _ : ℕ => μ) :=
  measurePreserving_snd.comp (StochasticGeneralized.splitStream_preserving μ n)

lemma mlmc_radius_sq (r : ℝ) (j : ℕ) :
    mlmcRadius r j ^ 2 = r ^ 2 * (1 / 4 : ℝ) ^ j := by
  rw [mlmcRadius, div_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num, div_eq_mul_inv, ← inv_pow]
  norm_num

lemma mlmc_plan_moments {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {g : E → Ω → E} {x0 v c : E} {L σ D r : ℝ}
    (hP : ∀ z, P z ∈ Q) (hPm : Measurable P) (hgm : Measurable (Function.uncurry g))
    (hx0 : x0 ∈ Q) (hv : v ∈ Q) (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hRMS : ∀ k : ℕ,
      (∫ ξ : ℕ → Ω, ‖QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (approximationPlan L σ D (mlmcRadius r k) c x0) 0 - v‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ mlmcRadius r k ^ 2) (m : ℕ) :
    let ν := Measure.infinitePi fun _ : ℕ => μ
    let Z := fun w : Fin (m + 1) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (mlmcPlan L σ D r c x0 m w.1) 0
    Integrable Z ((mlmcLevelLaw m : Measure _).prod ν) ∧
      (∫ w, Z w ∂((mlmcLevelLaw m : Measure _).prod ν)) =
        (∫ ξ, QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (approximationPlan L σ D (mlmcRadius r (m + 1)) c x0) 0 ∂ν) ∧
      Integrable (fun w => ‖Z w - v‖ ^ 2) ((mlmcLevelLaw m : Measure _).prod ν) ∧
      (∫ w, ‖Z w - v‖ ^ 2 ∂((mlmcLevelLaw m : Measure _).prod ν)) ≤ 10 * (m + 1 : ℝ) * r ^ 2 ∧
      ‖(∫ w, Z w ∂((mlmcLevelLaw m : Measure _).prod ν)) - v‖ ≤ |mlmcRadius r (m + 1)| := by
  dsimp only
  let ν := Measure.infinitePi fun _ : ℕ => μ
  let X (k : ℕ) (ξ : ℕ → Ω) := QueryPlan.sampledEval
    (ProjectedClippedExtragradient.channelReply P g) ξ
    (approximationPlan L σ D (mlmcRadius r k) c x0) 0
  let n0 := innerCalls L σ D (innerStageCount D r)
  let n1 (j : Fin (m + 1)) := innerCalls L σ D (innerStageCount D (mlmcRadius r (j.val + 1)))
  let upper (j : Fin (m + 1)) (ξ : ℕ → Ω) := X (j.val + 1) (fun i => ξ (n0 + i))
  let lower (j : Fin (m + 1)) (ξ : ℕ → Ω) := X j.val (fun i => ξ (n0 + n1 j + i))
  have hXm (k : ℕ) : Measurable (X k) :=
    (measurable_sampled_inner_plan hPm hgm L σ D c (innerStageCount D (mlmcRadius r k)) 0).comp
      (measurable_const.prodMk measurable_id)
  have hXmem (k : ℕ) (ξ : ℕ → Ω) : X k ξ ∈ Q :=
    sampled_inner_plan_mem hP g ξ L σ D c hx0 _ 0
  have hXi (k : ℕ) : Integrable (X k) ν := integrable_feasible hv hD (hXm k) (hXmem k)
  have hX2i (k : ℕ) : Integrable (fun ξ => ‖X k ξ - v‖ ^ 2) ν :=
    integrable_feasible_squared hv hD (hXm k) (hXmem k)
  have hlaw (n : ℕ) : HasLaw (fun ξ : ℕ → Ω => fun i => ξ (n + i)) ν ν :=
    ⟨(iid_shift_preserving μ n).measurable.aemeasurable, (iid_shift_preserving μ n).map_eq⟩
  have hUm (j : Fin (m + 1)) : Measurable (upper j) :=
    (hXm (j.val + 1)).comp (iid_shift_preserving μ n0).measurable
  have hLm (j : Fin (m + 1)) : Measurable (lower j) :=
    (hXm j.val).comp (iid_shift_preserving μ (n0 + n1 j)).measurable
  have hUi (j : Fin (m + 1)) : Integrable (upper j) ν :=
    (iid_shift_preserving μ n0).integrable_comp_of_integrable (hXi (j.val + 1))
  have hLi (j : Fin (m + 1)) : Integrable (lower j) ν :=
    (iid_shift_preserving μ (n0 + n1 j)).integrable_comp_of_integrable (hXi j.val)
  have hUmean (j : Fin (m + 1)) : (∫ ξ, upper j ξ ∂ν) = ∫ ξ, X (j.val + 1) ξ ∂ν :=
    (hlaw n0).integral_comp (hXm (j.val + 1)).aestronglyMeasurable
  have hLmean (j : Fin (m + 1)) : (∫ ξ, lower j ξ ∂ν) = ∫ ξ, X j.val ξ ∂ν :=
    (hlaw (n0 + n1 j)).integral_comp (hXm j.val).aestronglyMeasurable
  have hU2i (j : Fin (m + 1)) : Integrable (fun ξ => ‖upper j ξ - v‖ ^ 2) ν :=
    (iid_shift_preserving μ n0).integrable_comp_of_integrable (hX2i (j.val + 1))
  have hL2i (j : Fin (m + 1)) : Integrable (fun ξ => ‖lower j ξ - v‖ ^ 2) ν :=
    (iid_shift_preserving μ (n0 + n1 j)).integrable_comp_of_integrable (hX2i j.val)
  have hR (k : ℕ) : (∫ ξ, ‖X k ξ - v‖ ^ 2 ∂ν) ≤ r ^ 2 * (1 / 4 : ℝ) ^ k := by
    simpa only [mlmc_radius_sq] using hRMS k
  have hUb (j : Fin (m + 1)) : (∫ ξ, ‖upper j ξ - v‖ ^ 2 ∂ν) ≤
      r ^ 2 * (1 / 4 : ℝ) ^ (j.val + 1) := by
    have he := (hlaw n0).integral_comp (((hXm (j.val + 1)).sub_const v).norm.pow_const 2).aestronglyMeasurable
    exact he.trans_le (hR (j.val + 1))
  have hLb (j : Fin (m + 1)) : (∫ ξ, ‖lower j ξ - v‖ ^ 2 ∂ν) ≤
      r ^ 2 * (1 / 4 : ℝ) ^ j.val := by
    have he := (hlaw (n0 + n1 j)).integral_comp (((hXm j.val).sub_const v).norm.pow_const 2).aestronglyMeasurable
    exact he.trans_le (hR j.val)
  have hm := mlmc_random_mean m (fun k => ∫ ξ, X k ξ ∂ν) (X 0) upper lower
    (hXm 0) hUm hLm (hXi 0) hUi hLi rfl hUmean hLmean
  have hs := mlmc_random_second m r v (X 0) upper lower (hXm 0) hUm hLm
    (hX2i 0) hU2i hL2i (by simpa using hR 0) hUb hLb
  have he (j : Fin (m + 1)) (ξ : ℕ → Ω) :
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (mlmcPlan L σ D r c x0 m j) 0 =
        X 0 ξ + (mlmcWeight m j)⁻¹ • (upper j ξ - lower j ξ) := by
    rw [sampled_mlmc_plan]
    simp only [Nat.zero_add]
    have hb : QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (approximationPlan L σ D r c x0) 0 = X 0 ξ := by
      change _ = QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (approximationPlan L σ D (mlmcRadius r 0) c x0) 0
      rw [show mlmcRadius r 0 = r by simp [mlmcRadius]]
    rw [hb, StochasticCohypomonotone.sampledEval_shift _
      (approximationPlan L σ D (mlmcRadius r (j.val + 1)) c x0) ξ n0,
      StochasticCohypomonotone.sampledEval_shift _
      (approximationPlan L σ D (mlmcRadius r j.val) c x0) ξ (n0 + n1 j)]
  have hsq := GeneralNormClipping.norm_integral_sq_le
    ((hXi (m + 1)).sub (integrable_const v)) (hX2i (m + 1))
  simp only [Pi.sub_apply] at hsq
  rw [integral_sub (hXi (m + 1)) (integrable_const v)] at hsq
  simp only [integral_const, probReal_univ, one_smul] at hsq
  have hbias : ‖(∫ ξ, X (m + 1) ξ ∂ν) - v‖ ≤ |mlmcRadius r (m + 1)| := by
    apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    simpa only [sq_abs] using hsq.trans (hRMS (m + 1))
  simp_rw [he]
  refine ⟨hm.1, hm.2, hs.1, hs.2, ?_⟩
  rw [hm.2]
  exact hbias

lemma prox_mlmc_plan_moments {μ : Measure Ω} [IsProbabilityMeasure μ]
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
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) (m : ℕ) :
    let ν := Measure.infinitePi fun _ : ℕ => μ
    let Z := fun w : Fin (m + 1) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (mlmcPlan L σ D r c x0 m w.1) 0
    Integrable Z ((mlmcLevelLaw m : Measure _).prod ν) ∧
      (∫ w, Z w ∂((mlmcLevelLaw m : Measure _).prod ν)) =
        (∫ ξ, QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (approximationPlan L σ D (mlmcRadius r (m + 1)) c x0) 0 ∂ν) ∧
      Integrable (fun w => ‖Z w - constrainedProx Q f L c‖ ^ 2) ((mlmcLevelLaw m : Measure _).prod ν) ∧
      (∫ w, ‖Z w - constrainedProx Q f L c‖ ^ 2 ∂((mlmcLevelLaw m : Measure _).prod ν)) ≤
        10 * (m + 1 : ℝ) * r ^ 2 ∧
      ‖(∫ w, Z w ∂((mlmcLevelLaw m : Measure _).prod ν)) - constrainedProx Q f L c‖ ≤
        mlmcRadius r (m + 1) := by
  have hp := constrainedProx_spec hQ ⟨x0, hx0⟩ hG L c
  have hh := mlmc_plan_moments hP.mem hP.lipschitz.continuous.measurable hgm hx0 hp.1 hD
    (fun k => prox_approximation_integral (StochasticGeneralized.infinitePi_iid μ) hP hL hD0
      (by unfold mlmcRadius; positivity : 0 < mlmcRadius r k) hx0 hQ hcv hD hG hlip hgm hgi hmean hg2 hvar) m
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, ?_⟩
  simpa only [abs_of_pos (by unfold mlmcRadius; positivity : 0 < mlmcRadius r (m + 1))] using hh.2.2.2.2

omit [CompleteSpace E] in
lemma measurable_mlmc_level_joint {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D r : ℝ) (m call : ℕ) :
    Measurable (fun w : (E × E) × (Fin (m + 1) × (ℕ → Ω)) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2.2
        (mlmcPlan L σ D r w.1.1 w.1.2 m w.2.1) call) := by
  have hh : Measurable (fun w : Fin (m + 1) × ((E × E) × (ℕ → Ω)) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2.2
        (mlmcPlan L σ D r w.2.1.1 w.2.1.2 m w.1) call) :=
    measurable_from_prod_countable_right (fun j => measurable_mlmc_joint hP hg L σ D r m j call)
  exact hh.comp ((measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma scaled_estimator_moments {S : Type*} [MeasurableSpace S] {ν : Measure S}
    [IsProbabilityMeasure ν] {Z : S → E} {c v : E} {L r V : ℝ} (hL : 0 ≤ L)
    (hi : Integrable Z ν) (h2i : Integrable (fun ω => ‖Z ω - v‖ ^ 2) ν)
    (hb : ‖(∫ ω, Z ω ∂ν) - v‖ ≤ r) (hs : (∫ ω, ‖Z ω - v‖ ^ 2 ∂ν) ≤ V) :
    Integrable (fun ω => (2 * L) • (c - Z ω)) ν ∧
      ‖(∫ ω, (2 * L) • (c - Z ω) ∂ν) - (2 * L) • (c - v)‖ ≤ 2 * L * r ∧
      Integrable (fun ω => ‖(2 * L) • (c - Z ω) - (2 * L) • (c - v)‖ ^ 2) ν ∧
      (∫ ω, ‖(2 * L) • (c - Z ω) - (2 * L) • (c - v)‖ ^ 2 ∂ν) ≤ 4 * L ^ 2 * V := by
  have he (ω : S) : ‖(2 * L) • (c - Z ω) - (2 * L) • (c - v)‖ ^ 2 =
      4 * L ^ 2 * ‖Z ω - v‖ ^ 2 := by
    rw [← smul_sub, show (c - Z ω) - (c - v) = -(Z ω - v) by abel,
      norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * L), mul_pow]
    ring
  refine ⟨((integrable_const c).sub hi).smul (2 * L), ?_, ?_, ?_⟩
  · rw [integral_smul, integral_sub (integrable_const c) hi, integral_const,
      probReal_univ, one_smul, ← smul_sub,
      show (c - ∫ ω, Z ω ∂ν) - (c - v) = -((∫ ω, Z ω ∂ν) - v) by abel,
      norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * L)]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  · simpa only [he] using h2i.const_mul (4 * L ^ 2)
  · simp_rw [he]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hs (by positivity)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sampled_envelope_estimate (P : E → E) (g : E → Ω → E) (ξ : ℕ → Ω)
    (L σ D r : ℝ) (c x0 : E) (m : ℕ) (j : Fin (m + 1)) (call : ℕ) :
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (envelopeEstimatePlan L σ D r c x0 m j) call =
      (2 * L) • (c - QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
        (mlmcPlan L σ D r c x0 m j) call) := by
  rw [envelopeEstimatePlan, QueryPlan.sampledEval_map]

omit [CompleteSpace E] in
lemma measurable_envelope_estimate_joint {P : E → E} {g : E → Ω → E}
    (hP : Measurable P) (hg : Measurable (Function.uncurry g))
    (L σ D r : ℝ) (m call : ℕ) :
    Measurable (fun w : (E × E) × (Fin (m + 1) × (ℕ → Ω)) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2.2
        (envelopeEstimatePlan L σ D r w.1.1 w.1.2 m w.2.1) call) := by
  simp_rw [sampled_envelope_estimate]
  exact ((measurable_fst.comp measurable_fst).sub
    (measurable_mlmc_level_joint hP hg L σ D r m call)).const_smul (2 * L)

end OracleTemplate.StochasticQuasar
