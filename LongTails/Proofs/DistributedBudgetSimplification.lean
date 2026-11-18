import LongTails.Theorems.DistributedCurvatureNormalized
import LongTails.Proofs.DistributedBudgetAlgebra
import LongTails.Proofs.DistributedBudgetWidths

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedBudgetSimplification

open DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTuning
open DistributedBudgetAlgebra

noncomputable def downArgument (p : Params) : ℝ := accuracyScale p * Real.sqrt p.d

noncomputable def upArgument (p : Params) : ℝ :=
  ((p.d : ℝ) ^ 2 * accuracyScale p + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n

noncomputable def logDown (p : Params) : ℝ := (p.b : ℝ) * (1 + Real.log (1 + downArgument p))

noncomputable def logUp (p : Params) : ℝ := (p.b : ℝ) * (1 + Real.log (1 + upArgument p))

noncomputable def curvature (p : Params) : ℝ := min 1 (Real.sqrt (p.Q * p.ε) / p.L)

noncomputable def oldFrontier (p : Params) : ℝ :=
  DistributedBudgetAlgebra.frontier (computationTime p) (p.σ ^ 2 / p.ε ^ 2) (uplinkCost p) (downlinkCost p) p.d p.n (curvature p)

noncomputable def newFrontier (p : Params) : ℝ :=
  compact (computationTime p) (p.σ ^ 2 / p.ε ^ 2) (logUp p) (logDown p) p.d p.n (curvature p)

noncomputable def simplifiedBudget (p : Params) : Time :=
  Real.toNNReal (2 ^ 32 * accuracyScale p * ((p.l : ℝ) + newFrontier p))

lemma simplified_budget_explicit (p : Params) :
    simplifiedBudget p = Real.toNNReal (2 ^ 32 * (1 + p.L * p.Δ / p.ε ^ 2) * ((p.l : ℝ) + ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) * (1 + p.σ ^ 2 / (p.n * p.ε ^ 2)) + (p.b : ℝ) * (2 + Real.log (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d) + Real.log (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)) * (1 + p.d / (p.n : ℝ) ^ (1 / 3 : ℝ)) + p.d * (p.b : ℝ) * (1 + Real.log (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)) * min 1 (Real.sqrt (p.Q * p.ε) / p.L) + Real.sqrt (p.d * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) * p.σ ^ 2 * (p.b : ℝ) * (1 + Real.log (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)) / (p.n * p.ε ^ 2)))) := by
  unfold simplifiedBudget newFrontier compact logUp logDown upArgument downArgument
    computationTime curvature
  simp only [accuracyScale]
  congr 1
  ring_nf

lemma arguments_nonneg (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    0 ≤ downArgument p ∧ 0 ≤ upArgument p := by
  have hA : 0 ≤ accuracyScale p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DistributedNormalizedPrecision.accuracyScale_ge_one p hL hΔ)
  unfold downArgument upArgument
  constructor <;> positivity

lemma log_cost_bounds (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    logUp p ≤ uplinkCost p ∧ uplinkCost p ≤ 128 * logUp p ∧
      logDown p ≤ downlinkCost p ∧ downlinkCost p ≤ 128 * logDown p := by
  obtain ⟨hs, hu⟩ := arguments_nonneg p hL hΔ
  obtain ⟨hu1, hu2⟩ := DistributedBudgetPrecision.width_log_bounds (upArgument p) hu
  obtain ⟨hs1, hs2⟩ := DistributedBudgetPrecision.width_log_bounds (downArgument p) hs
  have hu1' := mul_le_mul_of_nonneg_left hu1 p.b.property
  have hu2' := mul_le_mul_of_nonneg_left hu2 p.b.property
  have hs1' := mul_le_mul_of_nonneg_left hs1 p.b.property
  have hs2' := mul_le_mul_of_nonneg_left hs2 p.b.property
  unfold logUp logDown uplinkCost downlinkCost uplinkWidth downlinkWidth
  simp only [upArgument, downArgument] at hu1' hu2' hs1' hs2' ⊢
  norm_num only [Nat.add_assoc, Nat.reduceAdd] at *
  constructor
  · exact hu1'
  constructor
  · calc
      _ ≤ (p.b : ℝ) * (128 * (1 + Real.log (1 + upArgument p))) := hu2'
      _ = _ := by unfold upArgument; ring
  constructor
  · exact hs1'
  · calc
      _ ≤ (p.b : ℝ) * (128 * (1 + Real.log (1 + downArgument p))) := hs2'
      _ = _ := by unfold downArgument; ring

lemma log_cost_nonneg (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    0 ≤ logUp p ∧ 0 ≤ logDown p := by
  obtain ⟨hs, hu⟩ := arguments_nonneg p hL hΔ
  have hls := Real.log_nonneg (show 1 ≤ 1 + downArgument p by linarith)
  have hlu := Real.log_nonneg (show 1 ≤ 1 + upArgument p by linarith)
  unfold logUp logDown
  constructor <;> positivity

lemma log_cost_comparison (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ)
    (hnd : (p.n : ℝ) ≤ (p.d : ℝ) ^ 3) :
    logDown p ≤ logUp p ∧ logUp p ≤ 8 * logDown p := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.property
  have hd : (1 : ℝ) ≤ p.d := by
    by_cases hz : p.d = 0
    · simp only [hz, Nat.cast_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)] at hnd
      linarith
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hA := DistributedNormalizedPrecision.accuracyScale_ge_one p hL hΔ
  have hR : 0 ≤ p.σ ^ 2 / p.ε ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := DistributedBudgetWidths.width_comparison hA hR hd hn hnd
  constructor
  · exact mul_le_mul_of_nonneg_left h1 p.b.property
  · have ht := mul_le_mul_of_nonneg_left h2 p.b.property
    unfold logUp logDown upArgument downArgument
    nlinarith

lemma frontier_bounds (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    oldFrontier p ≤ 128 * newFrontier p ∧ newFrontier p ≤ 16 * oldFrontier p := by
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n.property
  have hnp : (0 : ℝ) < p.n := by linarith
  have hR : 0 ≤ p.σ ^ 2 / p.ε ^ 2 := by positivity
  have hd : (0 : ℝ) ≤ p.d := by positivity
  have hH : (0 : ℝ) ≤ computationTime p := (computationTime p).property
  have hq : 0 ≤ curvature p := by unfold curvature; positivity
  obtain ⟨hU, hS⟩ := log_cost_nonneg p hL hΔ
  obtain ⟨hu1, hu2, hs1, hs2⟩ := log_cost_bounds p hL hΔ
  have hu0 : 0 ≤ uplinkCost p := hU.trans hu1
  have hs0 : 0 ≤ downlinkCost p := hS.trans hs1
  have hscale := frontier_scale hH hR hU hu0 hs0 hd hnp hq (by norm_num : (1 : ℝ) ≤ 128) hu2 hs2
  have hl := frontier_le_compact hH hR hU hS hd hn hq
  have hr := compact_le_frontier (R := p.σ ^ 2 / p.ε ^ 2) (q := curvature p) hH hU hS hd hn (log_cost_comparison p hL hΔ)
  have hm := frontier_mono hH hR hU hS hd hnp hq hu1 hs1
  constructor
  · exact hscale.trans (mul_le_mul_of_nonneg_left hl (by norm_num))
  · exact hr.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

lemma old_budget_eq (p : Params) :
    LongTails.Theorems.DistributedCurvatureNormalized.budget p =
      Real.toNNReal (2 ^ 25 * accuracyScale p * ((p.l : ℝ) + oldFrontier p)) := by
  unfold LongTails.Theorems.DistributedCurvatureNormalized.budget oldFrontier DistributedBudgetAlgebra.frontier
    curvature computationTime uplinkCost downlinkCost uplinkWidth downlinkWidth
  simp only [accuracyScale]
  congr 1
  norm_num only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_ofNat]
  ring_nf

lemma old_frontier_nonneg (p : Params) : 0 ≤ oldFrontier p := by
  unfold oldFrontier DistributedBudgetAlgebra.frontier
  exact le_max_of_le_left (computationTime p).property

lemma budget_bounds (p : Params) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) :
    LongTails.Theorems.DistributedCurvatureNormalized.budget p ≤ simplifiedBudget p ∧
      simplifiedBudget p ≤ 2048 * LongTails.Theorems.DistributedCurvatureNormalized.budget p := by
  obtain ⟨hl, hr⟩ := frontier_bounds p hL hΔ
  have hF := old_frontier_nonneg p
  have hG : 0 ≤ newFrontier p := by linarith
  have hA : 0 ≤ accuracyScale p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DistributedNormalizedPrecision.accuracyScale_ge_one p hL hΔ)
  have hell : (0 : ℝ) ≤ p.l := p.l.property
  rw [old_budget_eq]
  unfold simplifiedBudget
  have ho : 0 ≤ (2 : ℝ) ^ 25 * accuracyScale p * ((p.l : ℝ) + oldFrontier p) := by positivity
  have hn : 0 ≤ (2 : ℝ) ^ 32 * accuracyScale p * ((p.l : ℝ) + newFrontier p) := by positivity
  constructor
  · apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ ho, Real.coe_toNNReal _ hn]
    have ht := mul_le_mul_of_nonneg_left hl hA
    norm_num
    nlinarith [mul_nonneg hA hell]
  · apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul, Real.coe_toNNReal _ ho, Real.coe_toNNReal _ hn]
    have ht := mul_le_mul_of_nonneg_left hr hA
    norm_num
    nlinarith [mul_nonneg hA hell]

lemma execution_time_simplified (p : Params) (hd : 0 < p.d) (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ)
    (hε : 0 < p.ε) (hh : ∀ i, 0 < p.h i) :
    LongTails.Algorithms.DistributedNormalizedProtocol.executionTime p (config p) ≤ simplifiedBudget p :=
  (DistributedNormalizedRuntime.execution_time_explicit p hd hL hΔ hε hh).trans
    (budget_bounds p hL hΔ).1

end LongTails.Proofs.DistributedBudgetSimplification
