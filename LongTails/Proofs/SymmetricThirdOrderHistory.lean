import LongTails.Proofs.SymmetricThirdOrderMeasurability
import LongTails.Proofs.SymmetricThirdOrderOuter

namespace LongTails.Proofs.SymmetricThirdOrderHistory

open OracleTemplate LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderExecution

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma sampledState_eq_eval (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ) :
    sampledState cfg oracle ξ t = QueryPlan.sampledEval oracle ξ
      (roundsPlan cfg t (outerInitial cfg.x0 cfg.gridTop)) 0 := by
  symm
  exact roundsPlan_follow oracle ξ cfg t 0 (sampledState cfg oracle ξ)
    (fun j _ => by simp only [sampledState, Nat.zero_add, roundCalls])

lemma sampledState_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (t : ℕ) (ξ η : ℕ → Ω) (hξ : ∀ i < roundCalls cfg * t, ξ i = η i) :
    sampledState cfg oracle ξ t = sampledState cfg oracle η t := by
  rw [sampledState_eq_eval, sampledState_eq_eval]
  exact roundsPlan_prefix oracle cfg t _ ξ η hξ

lemma sampledCenter_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (t : ℕ) (ξ η : ℕ → Ω) (hξ : ∀ i < roundCalls cfg * t, ξ i = η i) :
    sampledCenter cfg oracle ξ t = sampledCenter cfg oracle η t := by
  unfold sampledCenter
  rw [sampledState_prefix cfg oracle t ξ η hξ]

lemma sampledMatrix_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (t : ℕ) (ξ η : ℕ → Ω) (hξ : ∀ i < roundCalls cfg * t + cfg.groups, ξ i = η i) :
    sampledMatrix cfg oracle ξ t = sampledMatrix cfg oracle η t := by
  unfold sampledMatrix
  congr 1
  apply sampledEval_adaptive_prefix oracle (fun ζ => hessianPlan cfg (sampledCenter cfg oracle ζ t)) _ ξ η hξ
  intro ζ θ hζ
  rw [sampledCenter_prefix cfg oracle t ζ θ hζ]

lemma sampledInner_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (t j : ℕ) (ξ η : ℕ → Ω)
    (hξ : ∀ i < roundCalls cfg * t + cfg.groups +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j, ξ i = η i) :
    sampledInner cfg oracle ξ t j = sampledInner cfg oracle η t j := by
  unfold sampledInner
  apply sampledEval_adaptive_prefix oracle
    (fun ζ => innerPlan cfg (sampledCenter cfg oracle ζ t) (sampledMatrix cfg oracle ζ t) j cfg.x0)
    _ ξ η hξ
  intro ζ θ hζ
  rw [sampledCenter_prefix cfg oracle t ζ θ (fun i hi => hζ i (by omega)),
    sampledMatrix_prefix cfg oracle t ζ θ hζ]

lemma sampledEndpoint_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (t j start : ℕ) (reflected : Bool)
    (hstart : roundCalls cfg * t + cfg.groups +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j ≤ start)
    (ξ η : ℕ → Ω) (hξ : ∀ i < start, ξ i = η i) :
    (if reflected then sampledCenter cfg oracle ξ t - (sampledInner cfg oracle ξ t j - sampledCenter cfg oracle ξ t)
      else sampledInner cfg oracle ξ t j) =
    (if reflected then sampledCenter cfg oracle η t - (sampledInner cfg oracle η t j - sampledCenter cfg oracle η t)
      else sampledInner cfg oracle η t j) := by
  rw [sampledCenter_prefix cfg oracle t ξ η (fun i hi => hξ i (by omega)),
    sampledInner_prefix cfg oracle t j ξ η (fun i hi => hξ i (by omega))]

lemma sampledCleanup_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (t : ℕ) (ξ η : ℕ → Ω)
    (hξ : ∀ i < roundCalls cfg * t + cfg.groups +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
      ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)), ξ i = η i) :
    sampledCleanup cfg oracle ξ t = sampledCleanup cfg oracle η t := by
  unfold sampledCleanup
  apply sampledEval_adaptive_prefix oracle
    (fun ζ => cleanupPlan cfg (sampledCenter cfg oracle ζ t) (sampledInner cfg oracle ζ t cfg.innerRounds)
      (sampledMatrix cfg oracle ζ t)) _ ξ η hξ
  intro ζ θ hζ
  rw [sampledCenter_prefix cfg oracle t ζ θ (fun i hi => hζ i (by omega)),
    sampledInner_prefix cfg oracle t cfg.innerRounds ζ θ hζ,
    sampledMatrix_prefix cfg oracle t ζ θ (fun i hi => hζ i (by omega))]

omit [CompleteSpace E] in
lemma correction_start (cfg : Config E) (t : ℕ) :
    roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
      ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)) =
      roundCalls cfg * (t + 1) - cfg.batch := by
  have he : roundCalls cfg * t + cfg.groups +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
      ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)) + cfg.batch =
      roundCalls cfg * (t + 1) := by unfold roundCalls; ring
  omega

lemma sampledState_step (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ) :
    sampledState cfg oracle ξ (t + 1) = outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop
      (sampledState cfg oracle ξ t) (sampledCleanup cfg oracle ξ t).1
      (QueryPlan.sampledEval oracle ξ (meanPlan cfg.batch (sampledCleanup cfg oracle ξ t).1)
        (roundCalls cfg * (t + 1) - cfg.batch) + (sampledCleanup cfg oracle ξ t).2) := by
  rw [sampledState, roundPlan_eval]
  change outerAdvance _ _ _ _ _ _ _ _
    (QueryPlan.sampledEval oracle ξ (meanPlan cfg.batch (sampledCleanup cfg oracle ξ t).1)
      (roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
        ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups))) + _) = _
  rw [correction_start]
  rfl

lemma sampledInner_mem (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (hC : IsCompact cfg.C) (hx : cfg.x0 ∈ cfg.C) (t j : ℕ) :
    sampledInner cfg oracle ξ t j ∈ cfg.C := by
  rw [sampledInner, innerPlan_eval_iterate]
  exact SymmetricThirdOrderInner.innerIterate_mem cfg.C cfg.x0 _ _ cfg.L cfg.δ _ hC hx j

lemma sampledCleanup_mem (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (t : ℕ) :
    (sampledCleanup cfg oracle ξ t).1 ∈ cfg.C := by
  rw [sampledCleanup, cleanupPlan_eval]
  exact (SymmetricThirdOrderMinimizers.cleanupPoint_spec cfg.C cfg.x0 _ _ cfg.δ _ hC hne).1

lemma sampledState_weight_nonneg (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t : ℕ) :
    0 ≤ (sampledState cfg oracle ξ t).weight := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [sampledState_step]
    exact ih.trans (SymmetricThirdOrderOuter.outerAdvance_weight_mono cfg.C cfg.x0 cfg.gridTop hL hδ _ _ _ ih)

lemma sampledState_weight_mono (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) :
    Monotone (fun t => (sampledState cfg oracle ξ t).weight) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [sampledState_step]
  exact SymmetricThirdOrderOuter.outerAdvance_weight_mono cfg.C cfg.x0 cfg.gridTop hL hδ _ _ _
    (sampledState_weight_nonneg cfg oracle ξ hL hδ t)

lemma sampledState_grid_le (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ) :
    (sampledState cfg oracle ξ t).grid ≤ cfg.gridTop := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [sampledState_step]
    exact SymmetricThirdOrderOuter.outerAdvance_grid_le cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop _ _ _ ih

lemma sampledState_feasible (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C) (hx : cfg.x0 ∈ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t : ℕ) :
    (sampledState cfg oracle ξ t).point ∈ cfg.C ∧ (sampledState cfg oracle ξ t).momentum ∈ cfg.C := by
  induction t with
  | zero => exact ⟨hx, hx⟩
  | succ t ih =>
    rw [sampledState_step]
    exact SymmetricThirdOrderOuter.outerAdvance_feasible cfg.C cfg.x0 cfg.gridTop hC ⟨cfg.x0, hx⟩
      hconv hL hδ _ _ _ (sampledState_weight_nonneg cfg oracle ξ hL hδ t) ih.1 ih.2
      (sampledCleanup_mem cfg oracle ξ hC ⟨cfg.x0, hx⟩ t)

lemma sampledState_weight_bound (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (hX : 0 ≤ cfg.threshold)
    (hδX : 1 ≤ cfg.δ * cfg.threshold) (t : ℕ) :
    (sampledState cfg oracle ξ t).weight ≤ 3 * cfg.threshold := by
  induction t with
  | zero => change 0 ≤ 3 * cfg.threshold; positivity
  | succ t ih =>
    rw [sampledState_step]
    exact SymmetricThirdOrderOuter.outerAdvance_weight_bound cfg.C cfg.x0 cfg.gridTop hδ hδX _ _ _
      (sampledState_weight_nonneg cfg oracle ξ hL hδ t) ih

lemma output_eq_sampledState [MeasurableSpace Ω] (cfg : Config E) (oracle : E → Ω → Reply E)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (T K : ℕ)
    (hK : roundCalls cfg * T ≤ K) :
    output cfg T K { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
      (sampledState cfg oracle ξ T).point := by
  rw [output_eq_sampledPlan cfg T K oracle P ξ hK, sampledState_eq_eval]

lemma sampledMatrix_symmetric (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (t : ℕ) (x y : E) :
    inner ℝ x (sampledMatrix cfg oracle ξ t y) = inner ℝ (sampledMatrix cfg oracle ξ t x) y := by
  unfold sampledMatrix
  apply SymmetricThirdOrderHessian.shiftedHessian_symmetric
  intro v w
  rw [hessianPlan_eval]
  exact SymmetricThirdOrderHessian.symmetricHessian_symmetric _ v w

lemma sampledMatrix_nonneg (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (t : ℕ) (v : E) : 0 ≤ inner ℝ v (sampledMatrix cfg oracle ξ t v) := by
  unfold sampledMatrix
  rw [real_inner_comm]
  exact SymmetricThirdOrderHessian.shiftedHessian_nonneg _ _ v

section Measurable

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

open MeasureTheory SymmetricThirdOrderMeasurability

lemma measurable_sampledState (cfg : Config E) (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t : ℕ) :
    MeasurableState (fun ξ : ℕ → Ω => sampledState cfg oracle ξ t) := by
  simp_rw [sampledState_eq_eval]
  exact measurable_roundsPlan oracle ho (fun ξ : ℕ → Ω => ξ) (fun j => measurable_pi_apply j)
    cfg hC hne hconv hL hδ t _
    ⟨measurable_const, measurable_const, measurable_const, measurable_const⟩ 0

lemma measurable_sampledCenter (cfg : Config E) (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => sampledCenter cfg oracle ξ t) :=
  measurable_outerCenter cfg.δ _ (measurable_sampledState cfg oracle ho hC hne hconv hL hδ t)

lemma measurable_sampledMatrix (cfg : Config E) (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => sampledMatrix cfg oracle ξ t) := by
  have hc := measurable_sampledCenter cfg oracle ho hC hne hconv hL hδ t
  have hH := measurable_hessianPlan oracle ho (fun ξ : ℕ → Ω => ξ) (fun j => measurable_pi_apply j)
    cfg _ hc (roundCalls cfg * t)
  exact SymmetricThirdOrderHessian.continuous_shiftedHessian.measurable.comp (hH.prodMk measurable_const)

lemma measurable_sampledInner (cfg : Config E) (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t j : ℕ) :
    Measurable (fun ξ : ℕ → Ω => sampledInner cfg oracle ξ t j) := by
  exact measurable_innerPlan oracle ho (fun ξ : ℕ → Ω => ξ) (fun j => measurable_pi_apply j)
    cfg hC hne hconv hL hδ _ _ (measurable_sampledCenter cfg oracle ho hC hne hconv hL hδ t)
    (measurable_sampledMatrix cfg oracle ho hC hne hconv hL hδ t)
    (fun ξ => sampledMatrix_symmetric cfg oracle ξ t) (fun ξ => sampledMatrix_nonneg cfg oracle ξ t)
    j (roundCalls cfg * t + cfg.groups)

lemma measurable_sampledEndpoint (cfg : Config E) (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t j : ℕ) (reflected : Bool) :
    Measurable (fun ξ : ℕ → Ω => if reflected then
      sampledCenter cfg oracle ξ t - (sampledInner cfg oracle ξ t j - sampledCenter cfg oracle ξ t)
      else sampledInner cfg oracle ξ t j) := by
  have hc := measurable_sampledCenter cfg oracle ho hC hne hconv hL hδ t
  have hy := measurable_sampledInner cfg oracle ho hC hne hconv hL hδ t j
  split_ifs
  · exact hc.sub (hy.sub hc)
  · exact hy

lemma measurable_sampledCleanup (cfg : Config E) (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => sampledCleanup cfg oracle ξ t) := by
  exact measurable_cleanupPlan oracle ho (fun ξ : ℕ → Ω => ξ) (fun j => measurable_pi_apply j)
    cfg hC hne hconv hδ _ _ _ (measurable_sampledCenter cfg oracle ho hC hne hconv hL hδ t)
    (measurable_sampledInner cfg oracle ho hC hne hconv hL hδ t cfg.innerRounds)
    (measurable_sampledMatrix cfg oracle ho hC hne hconv hL hδ t)
    (fun ξ => sampledMatrix_symmetric cfg oracle ξ t) _

end Measurable

end LongTails.Proofs.SymmetricThirdOrderHistory
