import LongTails.Proofs.BirchNonEuclideanRecords
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace LongTails.Proofs.BirchNonEuclideanCertificate

open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanExecution (interpret queryCount)
open LongTails.Proofs.BirchNonEuclideanSymbolic
open LongTails.Proofs.BirchNonEuclideanCausality
open LongTails.Proofs.BirchNonEuclideanRecords
open LongTails.Proofs.BirchNonEuclideanEnergy
open LongTails.Proofs.BirchNonEuclideanMoments
open MeasureTheory
open OracleTemplate.NormBallLMO

lemma traceEvaluation_supported {d : ℕ} (m : Memory d) (s : SymbolicMemory)
    (hsharp : s.units = ∅) (v : LinearValue) (hv : v ∈ coefficientSpace s) :
    traceEvaluation m v = (∑ q ∈ s.queries, v.1 q • m.vectors q) +
      ∑ e ∈ s.sharps, v.2 e • m.vectors e := by
  have hv2 : v.2 ∈ (Finsupp.supported ℝ ℝ (s.sharps : Set ℕ) : Set (ℕ →₀ ℝ)) := by
    simpa only [hsharp, Finset.union_empty] using hv.2
  change Finsupp.linearCombination ℝ m.vectors v.1 +
    Finsupp.linearCombination ℝ m.vectors v.2 = _
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ hv.1,
    Finsupp.linearCombination_apply_of_mem_supported ℝ hv2]

lemma interpret_old_point (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code : List Instruction) (m : Memory p.d)
    (j : ℕ) (hj : j < m.next) :
    (interpret p lmo response code m).points j = m.points j := by
  induction code generalizing m with
  | nil => rfl
  | cons i rest ih =>
      have hne : j ≠ m.next := ne_of_lt hj
      cases i <;> simp only [interpret] <;>
        rw [ih _ (by rw [perform_next]; omega)] <;>
        simp [perform, storeVector, hne]

lemma evaluated_initial (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) :
    p.x0 + traceEvaluation (interpret p lmo response a.instructions (initialMemory p))
      (a.symbolic.points 0) = p.x0 := by
  rw [← (symbolic_represents_sampled_execution p a lmo response).2.1 0]
  exact interpret_old_point p lmo response a.instructions (initialMemory p) 0 (by simp [initialMemory])

lemma evaluated_estimator (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) {K : ℕ} {η D V : ℝ}
    (c : ProgramCertificate a K η D V) (e : ℕ) (he : e ∈ a.symbolic.sharps) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    traceEvaluation m (a.symbolic.sharpInputs e) =
      ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q • m.vectors q := by
  dsimp only
  rw [traceEvaluation_supported _ _ c.sharp_only _ ((symbolic_maps_supported a).sharpInputs e)]
  simp [c.estimator_linear e he]

lemma evaluated_chain (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) {K : ℕ} {η D V : ℝ}
    (c : ProgramCertificate a K η D V) (k : ℕ) (hk : k < K) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    p.x0 + traceEvaluation m (a.symbolic.points (c.main (k + 1))) =
      p.x0 + traceEvaluation m (a.symbolic.points (c.main k)) +
        η • ∑ e ∈ a.symbolic.sharps.filter (fun e => c.owner e = k),
          c.weight e • (dualNorm p.N (traceEvaluation m (a.symbolic.sharpInputs e)) •
            lmo (traceEvaluation m (a.symbolic.sharpInputs e))) := by
  dsimp only
  have hsum : (∑ e ∈ a.symbolic.sharps.filter (fun e => c.owner e = k), c.weight e •
      (interpret p lmo response a.instructions (initialMemory p)).vectors e) =
      ∑ e ∈ a.symbolic.sharps.filter (fun e => c.owner e = k), c.weight e •
        (dualNorm p.N (traceEvaluation (interpret p lmo response a.instructions (initialMemory p))
          (a.symbolic.sharpInputs e)) •
        lmo (traceEvaluation (interpret p lmo response a.instructions (initialMemory p))
          (a.symbolic.sharpInputs e))) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [sampled_sharp_identity p a lmo response e (Finset.mem_filter.mp he).1]
  simp only [traceEvaluation, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, c.main_linear k hk.le,
    c.main_linear (k + 1) (by omega), map_zero, zero_add, c.chain k hk,
    map_add, map_smul, map_sum, Finsupp.linearCombination_single, one_smul]
  rw [hsum]
  simp [add_assoc, traceEvaluation]

lemma evaluated_displacement (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) {K : ℕ} {η D V : ℝ}
    (c : ProgramCertificate a K η D V) (hη : 0 < η)
    (e q : ℕ) (he : e ∈ a.symbolic.sharps) (hq : q ∈ a.symbolic.queries) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    (p.x0 + traceEvaluation m (a.symbolic.queryPoints q)) -
        (p.x0 + traceEvaluation m (a.symbolic.points (c.main (c.owner e)))) =
      η • ∑ t ∈ a.symbolic.sharps,
        (((a.symbolic.queryPoints q).2 t - (a.symbolic.points (c.main (c.owner e))).2 t) / η) •
          m.vectors t := by
  dsimp only
  rw [traceEvaluation_supported _ _ c.sharp_only _ ((symbolic_maps_supported a).queryPoints q),
    traceEvaluation_supported _ _ c.sharp_only _
      ((symbolic_maps_supported a).points (c.main (c.owner e)))]
  simp only [c.query_linear q hq, c.main_linear (c.owner e) (c.owner_lt e he).le,
    Finsupp.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [smul_smul, mul_div_cancel₀ _ hη.ne', sub_smul]

lemma certificate_energy (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) {K : ℕ} {η D V R : ℝ}
    (c : ProgramCertificate a K η D V) (I : Instance p.d) (ho : Objective p I)
    (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hlmo : IsBallLMO p.N 1 lmo) (hL : 0 ≤ p.L) (hη : 0 < η) (hD : 0 ≤ D)
    (hstep : η * p.L ≤ 1 / 2) (hsmall : η * p.L * D ≤ 1 / 4) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    let E := traceEvaluation m
    (∑ k ∈ Finset.range K, dualNorm p.N (gradient I.f (p.x0 + E (a.symbolic.points (c.main k)))) ^ 2) ≤
      6 * p.Δ / η + 16 * ∑ e ∈ a.symbolic.sharps, c.weight e * dualNorm p.N
        (∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q •
          (m.vectors q - gradient I.f (p.x0 + E (a.symbolic.queryPoints q)))) ^ 2 := by
  dsimp only
  let m := interpret p lmo response a.instructions (initialMemory p)
  let E := traceEvaluation m
  refine trajectory_energy hR hdef hlmo hL hη hD hstep hsmall ho.differentiable ho.smooth
    a.symbolic.sharps a.symbolic.queries K c.owner c.weight
    (fun e q => (a.symbolic.sharpInputs e).1 q) (transportCoefficient a c.main c.owner η)
    m.vectors (fun q => p.x0 + E (a.symbolic.queryPoints q))
    (fun k => p.x0 + E (a.symbolic.points (c.main k)))
    (fun e => E (a.symbolic.sharpInputs e)) c.weight_nonneg c.owner_lt c.partition
    (fun k hk => evaluated_chain p a lmo response c k hk) ?_
    (fun e he => evaluated_estimator p a lmo response c e he) c.estimator_mass ?_ ?_ c.transport
  · rw [c.main_initial, evaluated_initial]
    exact (sub_le_sub_left (ho.lower _) _).trans ho.gap
  · intro e _ t _
    exact Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · intro e he
    apply gradient_transport hR hL hη.le ho.smooth a.symbolic.queries a.symbolic.sharps
      (fun q => (a.symbolic.sharpInputs e).1 q)
      (fun q t => ((a.symbolic.queryPoints q).2 t -
        (a.symbolic.points (c.main (c.owner e))).2 t) / η)
      (fun q => p.x0 + E (a.symbolic.queryPoints q))
      (p.x0 + E (a.symbolic.points (c.main (c.owner e)))) m.vectors
      (fun t => dualNorm p.N (E (a.symbolic.sharpInputs t)))
    · intro t ht
      rw [sampled_sharp_identity p a lmo response t ht]
      exact sharp_direction_bound hR hlmo _
    · intro q hq
      exact evaluated_displacement p a lmo response c hη e q he hq

lemma sum_queries_range {M : Type*} [AddCommMonoid M] (a : Program) (F : ℕ → M)
    (hzero : ∀ q, q ∉ a.symbolic.queries → F q = 0) :
    (∑ q ∈ a.symbolic.queries, F q) = ∑ q ∈ Finset.range a.symbolic.next, F q := by
  apply Finset.sum_subset
  · intro q hq
    exact Finset.mem_range.mpr ((symbolic_beforeNext a).1 q hq)
  · intro q _ hq
    exact hzero q hq

lemma coefficient_noise {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : StochasticGradient p (μ : Measure Ω) f g)
    (w : DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (b : ℕ →₀ ℝ) (hb : b ∈ (Finsupp.supported ℝ ℝ
      (a.symbolic.queries : Set ℕ) : Set (ℕ →₀ ℝ))) :
    Integrable (fun ξ => dualNorm p.N (∑ q ∈ a.symbolic.queries, b q •
      (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
        gradient f (sampledQueryPoint p a lmo g q ξ))) ^ 2) (P : Measure (ℕ → Ω)) ∧
    (∫ ξ, dualNorm p.N (∑ q ∈ a.symbolic.queries, b q •
      (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
        gradient f (sampledQueryPoint p a lmo g q ξ))) ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      p.κ * p.σ ^ 2 * ∑ q ∈ a.symbolic.queries, b q ^ 2 := by
  have hz : ∀ q, q ∉ a.symbolic.queries → b q = 0 :=
    (Finsupp.mem_supported' ℝ b).mp hb
  have hindex : ∀ j k, j < k → b j ≠ 0 → b k ≠ 0 →
      queryCount (a.instructions.take (j - 1)) < queryCount (a.instructions.take (k - 1)) := by
    intro j k hjk hj _
    apply query_indices_strict a j k _ hjk
    exact Classical.byContradiction (fun hn => hj (hz j hn))
  have hh := iid_indexed_noise_bound p μ P hiid f g ho w hR hR0
    (fun q => queryCount (a.instructions.take (q - 1))) (sampledQueryPoint p a lmo g)
    (sampledQueryPoint_measurable p a lmo hlmo hR hR0 g ho.measurable)
    (sampledQueryPoint_past p a lmo g) b hindex a.symbolic.next
  have hs (ξ : ℕ → Ω) : (∑ q ∈ Finset.range a.symbolic.next, b q •
      (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
        gradient f (sampledQueryPoint p a lmo g q ξ))) =
      ∑ q ∈ a.symbolic.queries, b q •
      (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
        gradient f (sampledQueryPoint p a lmo g q ξ)) := by
    symm
    apply sum_queries_range a
    intro q hq
    rw [hz q hq, zero_smul]
  have ht : (∑ q ∈ Finset.range a.symbolic.next, b q ^ 2) =
      ∑ q ∈ a.symbolic.queries, b q ^ 2 := by
    symm
    apply sum_queries_range a
    intro q hq
    rw [hz q hq, zero_pow (by decide)]
  simpa only [hs, ht] using hh

lemma certificate_expected_energy {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) {K : ℕ} {η D V R : ℝ}
    (c : ProgramCertificate a K η D V) (I : Instance p.d) (ho : Objective p I)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (hg : StochasticGradient p (μ : Measure Ω) I.f g)
    (w : DualRegularityWitness p.N p.κ)
    (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hlmo : IsBallLMO p.N 1 lmo) (hL : 0 ≤ p.L) (hη : 0 < η) (hD : 0 ≤ D)
    (hstep : η * p.L ≤ 1 / 2) (hsmall : η * p.L * D ≤ 1 / 4) :
    let m := fun ξ : ℕ → Ω => interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p)
    Integrable (fun ξ => ∑ k ∈ Finset.range K,
      dualNorm p.N (gradient I.f ((m ξ).points (c.main k))) ^ 2) (P : Measure (ℕ → Ω)) ∧
    (∫ ξ, ∑ k ∈ Finset.range K,
      dualNorm p.N (gradient I.f ((m ξ).points (c.main k))) ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      6 * p.Δ / η + 16 * p.κ * p.σ ^ 2 * K * V := by
  let m := fun ξ : ℕ → Ω => interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p)
  let T := fun e (ξ : ℕ → Ω) => dualNorm p.N (∑ q ∈ a.symbolic.queries,
    (a.symbolic.sharpInputs e).1 q •
      (g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) -
        gradient I.f (sampledQueryPoint p a lmo g q ξ))) ^ 2
  let W := fun ξ => ∑ e ∈ a.symbolic.sharps, c.weight e * T e ξ
  let G := fun ξ => ∑ k ∈ Finset.range K,
    dualNorm p.N (gradient I.f ((m ξ).points (c.main k))) ^ 2
  have hT (e : ℕ) : Integrable (T e) (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, T e ξ ∂(P : Measure (ℕ → Ω))) ≤
        p.κ * p.σ ^ 2 * ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2 :=
    coefficient_noise p a lmo hlmo.measurable μ P hiid I.f g hg w hR hR0
      (a.symbolic.sharpInputs e).1 ((symbolic_maps_supported a).sharpInputs e).1
  have hWI : Integrable W (P : Measure (ℕ → Ω)) :=
    integrable_finsetSum _ (fun e _ => (hT e).1.const_mul (c.weight e))
  have hκ : 0 ≤ p.κ := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (w.smoothness_lower.trans w.smoothness_upper)
  have hWB : (∫ ξ, W ξ ∂(P : Measure (ℕ → Ω))) ≤ p.κ * p.σ ^ 2 * K * V := by
    dsimp only [W]
    rw [integral_finsetSum _ (fun e _ => (hT e).1.const_mul (c.weight e))]
    simp only [integral_const_mul]
    calc
      _ ≤ ∑ e ∈ a.symbolic.sharps, c.weight e *
          (p.κ * p.σ ^ 2 * ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2) :=
        Finset.sum_le_sum (fun e he => mul_le_mul_of_nonneg_left (hT e).2 (c.weight_nonneg e he))
      _ = p.κ * p.σ ^ 2 * (∑ e ∈ a.symbolic.sharps, c.weight e *
          ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ ≤ p.κ * p.σ ^ 2 * ((K : ℝ) * V) :=
        mul_le_mul_of_nonneg_left c.noise (mul_nonneg hκ (sq_nonneg _))
      _ = _ := by ring
  have hpoint (ξ : ℕ → Ω) : G ξ ≤ 6 * p.Δ / η + 16 * W ξ := by
    have hh := certificate_energy p a lmo (fun k x => g x (ξ k)) c I ho
      hR hdef hlmo hL hη hD hstep hsmall
    dsimp only at hh
    have hp := (symbolic_represents_sampled_execution p a lmo (fun k x => g x (ξ k))).2.1
    simp_rw [← hp] at hh
    have ht (e : ℕ) : dualNorm p.N (∑ q ∈ a.symbolic.queries,
        (a.symbolic.sharpInputs e).1 q • ((m ξ).vectors q - gradient I.f (p.x0 +
          traceEvaluation (m ξ) (a.symbolic.queryPoints q)))) ^ 2 = T e ξ := by
      congr 2
      apply Finset.sum_congr rfl
      intro q hq
      rw [sampled_query_identity p a lmo g q hq ξ,
        ← sampledQueryPoint_identity p a lmo g q hq ξ]
    simpa only [G, W, m, ht] using hh
  have hm := interpret_prefix_measurable p lmo hlmo.measurable hR hR0 g hg.measurable a.instructions
  have hGM : Measurable G := by
    apply Finset.measurable_sum
    intro k _
    exact (((continuous_dualNorm hR hR0).measurable.comp
      ((measurable_gradient_space I.f).comp (hm.1 (c.main k)))).pow_const 2)
  have hGI : Integrable G (P : Measure (ℕ → Ω)) := by
    apply ((integrable_const (6 * p.Δ / η)).add (hWI.const_mul 16)).mono'
      hGM.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
      exact hpoint ξ)
  refine ⟨hGI, ?_⟩
  have hh := integral_mono hGI ((integrable_const (6 * p.Δ / η)).add (hWI.const_mul 16)) hpoint
  change (∫ ξ, G ξ ∂(P : Measure (ℕ → Ω))) ≤
    ∫ ξ, 6 * p.Δ / η + 16 * W ξ ∂(P : Measure (ℕ → Ω)) at hh
  rw [integral_add (integrable_const _) (hWI.const_mul 16), integral_const_mul] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (by nlinarith [hWB])

lemma uniform_integral {Ω : Type} [MeasurableSpace Ω] (N : ℕ)
    (P : ProbabilityMeasure Ω) (F : Fin (N + 1) → Ω → ℝ)
    (hi : ∀ j, Integrable (F j) (P : Measure Ω)) :
    Integrable (fun z : Fin (N + 1) × Ω => F z.1 z.2)
      ((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure Ω)) ∧
    (∫ z : Fin (N + 1) × Ω, F z.1 z.2
      ∂((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod (P : Measure Ω))) =
      (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1), ∫ ω, F j ω ∂(P : Measure Ω) := by
  classical
  let U := (PMF.uniformOfFintype (Fin (N + 1))).toMeasure
  let Q := U.prod (P : Measure Ω)
  have hind (j : Fin (N + 1)) : Integrable
      ({z : Fin (N + 1) × Ω | z.1 = j}.indicator (fun z => F j z.2)) Q :=
    ((hi j).comp_snd U).indicator (measurable_fst (measurableSet_singleton j))
  have hsplit : (fun z : Fin (N + 1) × Ω => F z.1 z.2) =
      fun z => ∑ j : Fin (N + 1), {z : Fin (N + 1) × Ω | z.1 = j}.indicator (fun z => F j z.2) z := by
    funext z
    simp [Set.indicator, eq_comm]
  have hprod : Integrable (fun z : Fin (N + 1) × Ω => F z.1 z.2) Q := by
    rw [hsplit]
    exact integrable_finsetSum Finset.univ (fun j _ => hind j)
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum, one_div]

lemma certificate_execute_success {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) {K : ℕ} {η D V R : ℝ}
    (c : ProgramCertificate a K η D V) (I : Instance p.d) (ho : Objective p I)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (g : Point p.d → Ω → Point p.d) (hg : StochasticGradient p (μ : Measure Ω) I.f g)
    (w : DualRegularityWitness p.N p.κ)
    (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hlmo : IsBallLMO p.N 1 lmo) (hL : 0 ≤ p.L) (hη : 0 < η) (hD : 0 ≤ D)
    (hstep : η * p.L ≤ 1 / 2) (hsmall : η * p.L * D ≤ 1 / 4)
    (hbound : 6 * p.Δ / (η * K) + 16 * p.κ * p.σ ^ 2 * V ≤ p.ε) :
    spec.successful p I
      (fun z : Fin (a.outputCount + 1) × (ℕ → Ω) =>
        OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
          (programAlgorithm p a lmo) (fun _ => a.oracleCalls) z.1 z.2)
      ⟨(PMF.uniformOfFintype (Fin (a.outputCount + 1))).toMeasure.prod
        (P : Measure (ℕ → Ω)), inferInstance⟩ := by
  classical
  let m := fun ξ : ℕ → Ω => interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p)
  let F := fun k (ξ : ℕ → Ω) => dualNorm p.N (gradient I.f ((m ξ).points (c.main k))) ^ 2
  have he := certificate_expected_energy p a lmo c I ho μ P hiid g hg w
    hR hR0 hdef hlmo hL hη hD hstep hsmall
  have hm := interpret_prefix_measurable p lmo hlmo.measurable hR hR0 g hg.measurable a.instructions
  have hfm (k : ℕ) : Measurable (F k) :=
    (((continuous_dualNorm hR hR0).measurable.comp
      ((measurable_gradient_space I.f).comp (hm.1 (c.main k)))).pow_const 2)
  have hfi (k : ℕ) (hk : k < K) : Integrable (F k) (P : Measure (ℕ → Ω)) := by
    apply he.1.mono' (hfm k).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun j _ => sq_nonneg
      (dualNorm p.N (gradient I.f ((m ξ).points (c.main j))))) (Finset.mem_range.mpr hk)
  have hu := uniform_integral a.outputCount P (fun j => F j.val)
    (fun j => hfi j.val (by rw [← c.output_count]; exact j.isLt))
  have hsum : (∑ j : Fin (a.outputCount + 1), ∫ ξ, F j.val ξ ∂(P : Measure (ℕ → Ω))) =
      ∫ ξ, ∑ k ∈ Finset.range K, F k ξ ∂(P : Measure (ℕ → Ω)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, F j ξ ∂(P : Measure (ℕ → Ω))), c.output_count,
      integral_finsetSum _ (fun k hk => hfi k (Finset.mem_range.mp hk))]
  have hK : (0 : ℝ) < K := Nat.cast_pos.mpr c.positive_horizon
  have ha : (1 / ((a.outputCount + 1 : ℕ) : ℝ)) *
      (∑ j : Fin (a.outputCount + 1), ∫ ξ, F j.val ξ ∂(P : Measure (ℕ → Ω))) ≤ p.ε := by
    rw [hsum, c.output_count]
    calc
      _ ≤ (1 / (K : ℝ)) * (6 * p.Δ / η + 16 * p.κ * p.σ ^ 2 * K * V) :=
        mul_le_mul_of_nonneg_left he.2 (by positivity)
      _ = 6 * p.Δ / (η * K) + 16 * p.κ * p.σ ^ 2 * V := by field_simp
      _ ≤ p.ε := hbound
  have hx (j : Fin (a.outputCount + 1)) (ξ : ℕ → Ω) :
      OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
        (programAlgorithm p a lmo) (fun _ => a.oracleCalls) j ξ =
          (m ξ).points (c.main j.val) := by
    rw [LongTails.Proofs.BirchNonEuclideanExecution.execute_interpret, c.output_indices]
  change Measurable _ ∧ Integrable _ _ ∧ _
  simp_rw [hx]
  exact ⟨measurable_from_prod_countable_right (fun j => hm.1 (c.main j.val)),
    hu.1, hu.2.le.trans ha⟩

end LongTails.Proofs.BirchNonEuclideanCertificate
