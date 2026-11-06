import LongTails.Algorithms.AffineSoftmaxFiniteMaximum
import LongTails.Proofs.AffineSoftmaxPublicBudget
import LongTails.Proofs.AffineSoftmaxCompilerExecution
import LongTails.Proofs.SmoothFiniteMaximumOracle

namespace LongTails.Proofs.AffineSoftmaxFiniteMaximum

open MeasureTheory
open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Setups.SmoothFiniteMaximum
open LongTails.Algorithms.AffineSoftmaxFiniteMaximum
open LongTails.Algorithms.AffineSoftmaxRadius
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxBudget
open LongTails.Algorithms.AffineSoftmaxAmplification
open AffineSoftmaxQuerySafety
open scoped ENNReal

lemma domain_geometry (p : Public) (hR : 0 < p.R) :
    Convex ℝ (domain p) ∧ IsCompact (domain p) ∧ p.x0 ∈ domain p ∧
      ∀ x ∈ domain p, ∀ y ∈ domain p, ‖x - y‖ ≤ 2 * p.R := by
  refine ⟨convex_closedBall p.x0 p.R, isCompact_closedBall p.x0 p.R, Metric.mem_closedBall_self hR.le, ?_⟩
  intro x hx y hy
  have hxd := Metric.mem_closedBall.mp hx
  have hyd := Metric.mem_closedBall.mp hy
  have ht := dist_triangle x p.x0 y
  rw [dist_comm p.x0 y] at ht
  rw [← dist_eq_norm]
  linarith

lemma tuning (p : Public) (hp : spec.valid p) (hsmall : p.ε < 2 * p.G * p.R) :
    let r := publicRadius p.m p.G p.L p.R p.ε
    let τ := p.ε / (2 * Real.log p.m)
    let D := 2 * p.R
    let ε := p.ε / 2
    0 < r ∧ r ≤ D ∧ 0 < τ ∧ 0 < ε ∧ ε < p.G * D ∧ p.L * r ^ 2 ≤ τ ∧
      0 < compilerFloor p.G D r ε ∧ compilerFloor p.G D r ε ≤ compilerCap p.G D r ε := by
  rcases hp with ⟨hG, hL, hR, hε⟩
  have hr := AffineSoftmaxRadius.publicRadius_bounds (m := p.m) (G := p.G) (L := p.L) (ε := p.ε) hR
  have he : 0 < p.ε / 2 := by positivity
  have hs : p.ε / 2 < p.G * (2 * p.R) := by nlinarith
  exact ⟨hr.1, hr.2, AffineSoftmaxRadius.public_temperature_pos p.hm hε, he, hs,
    AffineSoftmaxRadius.publicRadius_local p.hm hL hε,
    AffineSoftmaxOuterParameters.compilerFloor_pos hr.1 hr.2 he,
    (AffineSoftmaxOuterParameters.compiler_search_conditions hG hr.1 hr.2 he hs).1⟩

lemma plan_queries (p : Public) (hp : spec.valid p) (seed : Seeds) (reply : Fin p.m × p.E → ℝ × p.E) :
    QueriesWithin reply (fun q => q.2 ∈ domain p) (plan p seed) := by
  have hd := domain_geometry p hp.2.2.1
  unfold LongTails.Algorithms.AffineSoftmaxFiniteMaximum.plan
  split_ifs with hlarge
  · trivial
  · obtain ⟨hr, _, _, _, _, _, hf, hfc⟩ := tuning p hp (lt_of_not_ge hlarge)
    exact amplifiedOuterPlan_queries p.m hd.1 hd.2.1 p.x0 hd.2.2.1
      (p.ε / (2 * Real.log p.m)) p.L p.G (2 * p.R) (p.ε / 2) hr.le hf hfc _ _ _ _ _ seed reply

lemma plan_cost (p : Public) (hp : spec.valid p) (seed : Seeds) (reply : Fin p.m × p.E → ℝ × p.E) :
    Program.cost reply (plan p seed) ≤ 6 * (Nat.ceil (6 * meanCostBound p.m p.G p.L p.R p.ε) + p.m) := by
  unfold LongTails.Algorithms.AffineSoftmaxFiniteMaximum.plan
  split_ifs with hlarge
  · exact Nat.zero_le _
  · obtain ⟨hr, hrD, hτ, hε, hs, _, _, _⟩ := tuning p hp (lt_of_not_ge hlarge)
    exact AffineSoftmaxAmplification.amplifiedOuterPlan_cost p.m (domain p) p.x0 hτ hp.2.1 hp.1 hr hrD hε hs _ seed reply

lemma plan_mem (p : Public) (hp : spec.valid p) (seed : Seeds) (reply : Fin p.m × p.E → ℝ × p.E) :
    Program.eval reply (plan p seed) ∈ domain p := by
  have hd := domain_geometry p hp.2.2.1
  unfold LongTails.Algorithms.AffineSoftmaxFiniteMaximum.plan
  split_ifs with hlarge
  · exact hd.2.2.1
  · obtain ⟨hr, _, _, _, _, _, hf, hfc⟩ := tuning p hp (lt_of_not_ge hlarge)
    apply AffineSoftmaxAmplification.repeatedPlan_mem
    intro j
    exact AffineSoftmaxBudgetGuarantee.budgetedOuterPlan_mem p.m hd.1 hd.2.1 p.x0 hd.2.2.1
      (p.ε / (2 * Real.log p.m)) p.L p.G (2 * p.R) (p.ε / 2) hr.le hf hfc _ _ _ _ _ (seed j) reply

lemma plan_measurable (p : Public) (hp : spec.valid p) (reply : Fin p.m × p.E → ℝ × p.E) (hm : Measurable reply) :
    Measurable (fun seed => Program.eval reply (plan p seed)) := by
  have hd := domain_geometry p hp.2.2.1
  unfold LongTails.Algorithms.AffineSoftmaxFiniteMaximum.plan
  split_ifs with hlarge
  · exact measurable_const
  · obtain ⟨hr, _, _, _, _, _, hf, hfc⟩ := tuning p hp (lt_of_not_ge hlarge)
    apply AffineSoftmaxAmplification.repeatedPlan_measurable _ _ reply hm
    intro j
    exact (AffineSoftmaxBudgetGuarantee.budgetedOuterPlan_measurable p.m hd.1 hd.2.1 p.x0 hd.2.2.1
      (p.ε / (2 * Real.log p.m)) p.L p.G (2 * p.R) (p.ε / 2) hr hf hfc _ _ _ _ _ reply hm).comp (measurable_pi_apply j)

lemma plan_failure (p : Public) (hp : spec.valid p) (I : Instance p)
    (hc : ∀ i, ConvexOn ℝ (domain p) (I.loss i))
    (hg : ∀ i x, x ∈ domain p → HasGradientAt (I.loss i) (gradient (I.loss i) x) x)
    (hb : ∀ i x, x ∈ domain p → ‖gradient (I.loss i) x‖ ≤ p.G)
    (hl : ∀ i x y, x ∈ domain p → y ∈ domain p →
      ‖gradient (I.loss i) x - gradient (I.loss i) y‖ ≤ p.L * ‖x - y‖)
    (hx : I.xstar ∈ domain p)
    (reply : Fin p.m × p.E → ℝ × p.E) (hm : Measurable reply)
    (ht : ∀ i x, x ∈ domain p → reply (i, x) = (I.loss i x, gradient (I.loss i) x)) :
    (law : Measure Seeds) {seed | p.ε < objective I (Program.eval reply (plan p seed)) - objective I I.xstar} ≤
      (1 / 64 : ℝ≥0∞) := by
  have hd := domain_geometry p hp.2.2.1
  by_cases hlarge : 2 * p.G * p.R ≤ p.ε
  · have hgap := SmoothFiniteMaximumOracle.maximum_value_difference_le p.m I.loss p.G hc hg hb hd.2.2.1 hx
    have hnorm := hd.2.2.2 p.x0 hd.2.2.1 I.xstar hx
    have hle : objective I p.x0 - objective I I.xstar ≤ p.ε := by
      change maximumValue (fun i => I.loss i p.x0) - maximumValue (fun i => I.loss i I.xstar) ≤ p.ε
      exact hgap.trans ((mul_le_mul_of_nonneg_left hnorm hp.1.le).trans (by nlinarith))
    have he : {seed : Seeds | p.ε < objective I (Program.eval reply (plan p seed)) - objective I I.xstar} = ∅ := by
      ext seed
      simp only [LongTails.Algorithms.AffineSoftmaxFiniteMaximum.plan, ite_eq_left hlarge, Program.eval]
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge hle
    rw [he, measure_empty]
    exact bot_le
  · obtain ⟨hr, hrD, hτ, hε, hs, hlocal, _, _⟩ := tuning p hp (lt_of_not_ge hlarge)
    obtain ⟨xs, hxs, hmin⟩ := SmoothFiniteMaximumOracle.exists_smooth_minimizer p.m
      ⟨p.x0, hd.2.2.1⟩ hd.2.1 I.loss hτ hg
    have hh := AffineSoftmaxAmplification.amplifiedOuterPlan_failure p.m hd.1 hd.2.1 I.loss
      hτ hp.2.1 hp.1 hr hrD hε hs hlocal hd.2.2.2 hc hg hl hb reply hm ht p.x0 xs I.xstar
      hd.2.2.1 hxs hx hmin
    have hlog : 0 < Real.log (p.m : ℝ) := Real.log_pos (by have := p.hm; exact_mod_cast (show 1 < p.m by omega))
    have he : p.ε / 2 + p.ε / (2 * Real.log p.m) * Real.log p.m = p.ε := by
      field_simp [hlog.ne']
      ring
    dsimp only at hh
    rw [he] at hh
    simpa only [LongTails.Algorithms.AffineSoftmaxFiniteMaximum.plan, ite_eq_right hlarge, law,
      ProbabilityMeasure.coe_mk, objective, maximumValue, meanCostBound] using hh

lemma successful_execution (p : Public) (hp : spec.valid p) (I : Instance p)
    (oracle : Oracle (Fin p.m × p.E) (ℝ × p.E)) (ha : spec.admissible p I oracle)
    (K : ℕ) (hK : 6 * (Nat.ceil (6 * meanCostBound p.m p.G p.L p.R p.ε) + p.m) ≤ K) :
    spec.successful p I (fun w : Seeds × ((k : ℕ) → oracle.Seed k) =>
      LongTails.Algorithms.AffineSoftmaxFiniteMaximum.output p oracle K w.1 w.2)
      ⟨(law : Measure Seeds).prod (oracle.law : Measure _), inferInstance⟩ := by
  rcases ha with ⟨hc, hg, hb, hl, hx, _, ho⟩
  have hd := domain_geometry p hp.2.2.1
  obtain ⟨reply, hm, ht⟩ := SmoothFiniteMaximumOracle.exists_measurable_reply p.m
    ⟨p.x0, hd.2.2.1⟩ hd.1 hd.2.1 I.loss hp.2.1 hg hl
  let out := fun seed : Seeds => Program.eval reply (plan p seed)
  have he seed oracleSeed : LongTails.Algorithms.AffineSoftmaxFiniteMaximum.output p oracle K seed oracleSeed = out seed := by
    apply AffineSoftmaxCompilerExecution.execute_program_eq_eval law p.m p.x0 (plan p) oracle reply
      (domain p) hd.2.2.1
    · intro history seed i x hx
      exact (ho history seed i x hx).trans (ht i x hx).symm
    · exact plan_queries p hp seed reply
    · exact (plan_cost p hp seed reply).trans hK
  have hmout : Measurable out := plan_measurable p hp reply hm
  have hmem seed : out seed ∈ domain p := plan_mem p hp seed reply
  have hgap : Measurable (fun seed => objective I (out seed) - objective I I.xstar) := by
    have hh := (AffineSoftmaxAmplification.maximumScorePlan_measurable p.m out hmout reply hm).sub_const
      (objective I I.xstar)
    have hfun : (fun seed => Program.eval reply (maximumScorePlan p.m (out seed)) - objective I I.xstar) =
        (fun seed => objective I (out seed) - objective I I.xstar) := by
      funext seed
      rw [AffineSoftmaxAmplification.maximumScorePlan_eval,
        AffineSoftmaxAmplification.maximum_reply_eq p.m I.loss reply ht (out seed) (hmem seed)]
      rfl
    rw [hfun] at hh
    exact hh
  let A : Set Seeds := {seed | p.ε < objective I (out seed) - objective I I.xstar}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hgap
  have hbad : (law : Measure Seeds) A ≤ (1 / 64 : ℝ≥0∞) := plan_failure p hp I hc hg hb hl hx reply hm ht
  let P : Measure (Seeds × ((k : ℕ) → oracle.Seed k)) :=
    (law : Measure Seeds).prod (oracle.law : Measure ((k : ℕ) → oracle.Seed k))
  have hprod : P (Prod.fst ⁻¹' A) ≤ (1 / 64 : ℝ≥0∞) := by
    rw [show P (Prod.fst ⁻¹' A) = (law : Measure Seeds) A from
      measurePreserving_fst.measure_preimage hA.nullMeasurableSet]
    exact hbad
  change Measurable _ ∧ _ ∧ _
  constructor
  · have hh := hmout.comp (measurable_fst : Measurable (Prod.fst : Seeds × ((k : ℕ) → oracle.Seed k) → Seeds))
    convert hh using 1
    funext w
    exact he w.1 w.2
  constructor
  · apply Filter.Eventually.of_forall
    intro w
    change LongTails.Algorithms.AffineSoftmaxFiniteMaximum.output p oracle K w.1 w.2 ∈ domain p
    rw [he w.1 w.2]
    exact hmem w.1
  · have hset : {w : Seeds × ((k : ℕ) → oracle.Seed k) |
          objective I (LongTails.Algorithms.AffineSoftmaxFiniteMaximum.output p oracle K w.1 w.2) - objective I I.xstar ≤ p.ε} =
        (Prod.fst ⁻¹' A)ᶜ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, A, he, not_lt]
    change (9 : ℝ≥0∞) / 10 ≤ P _
    rw [hset, measure_compl (hA.preimage measurable_fst) (measure_ne_top _ _), measure_univ]
    have hfrac : (9 : ℝ≥0∞) / 10 ≤ 1 - 1 / 64 := by
      have hh := ENNReal.ofReal_le_ofReal (show (9 : ℝ) / 10 ≤ 1 - 1 / 64 by norm_num)
      rw [ENNReal.ofReal_sub (1 : ℝ) (by norm_num : 0 ≤ (1 / 64 : ℝ)),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)] at hh
      simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using hh
    exact hfrac.trans (tsub_le_tsub_left hprod 1)

end LongTails.Proofs.AffineSoftmaxFiniteMaximum
