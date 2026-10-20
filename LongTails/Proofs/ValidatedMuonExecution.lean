import LongTails.Algorithms.ValidatedMuon
import LongTails.Proofs.SampledQueryPlan

namespace LongTails.Proofs.ValidatedMuonExecution

open OracleTemplate MeasureTheory
open LongTails.Setups.MatrixGeometry LongTails.Algorithms.ValidatedMuon

lemma sampledEval_collect {Q R U Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)
    {c : ℕ} (k : ℕ) (plans : Fin k → QueryPlan Q R U c) (call : ℕ) :
    QueryPlan.sampledEval g ξ (collect k plans) call =
      fun i => QueryPlan.sampledEval g ξ (plans i) (call + c * i.val) := by
  induction k generalizing call with
  | zero => ext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [collect, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map, ih]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ, Fin.val_succ]
      congr 1
      simp only [Nat.mul_add, Nat.mul_one]
      omega

lemma sampledEval_batchSumPlan {Ω : Type*} {m n : ℕ}
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (x : Space m n)
    (b : ℕ) (s : Space m n) (call : ℕ) :
    QueryPlan.sampledEval g ξ (batchSumPlan x b s) call =
      s + ∑ j ∈ Finset.range b, g x (ξ (call + j)) := by
  induction b generalizing s call with
  | zero => simp [batchSumPlan, QueryPlan.sampledEval]
  | succ b ih =>
    simp only [batchSumPlan, QueryPlan.sampledEval, ih, Finset.sum_range_succ', Nat.add_zero]
    have he : (∑ j ∈ Finset.range b, g x (ξ (call + 1 + j))) =
        ∑ j ∈ Finset.range b, g x (ξ (call + (j + 1))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show call + 1 + j = call + (j + 1) by omega]
    rw [he]
    abel

lemma sampledEval_batchMeanPlan {Ω : Type*} {m n : ℕ}
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (x : Space m n)
    (b call : ℕ) :
    QueryPlan.sampledEval g ξ (batchMeanPlan x b) call =
      (1 / (b : ℝ)) • ∑ j ∈ Finset.range b, g x (ξ (call + j)) := by
  rw [batchMeanPlan, QueryPlan.sampledEval_map, sampledEval_batchSumPlan, zero_add]

lemma sampledEval_batchMean_centered {Ω : Type*} {m n : ℕ}
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (x μ : Space m n)
    {b : ℕ} (hb : 0 < b) (call : ℕ) :
    QueryPlan.sampledEval g ξ (batchMeanPlan x b) call - μ =
      ∑ j ∈ Finset.range b, (1 / (b : ℝ)) • (g x (ξ (call + j)) - μ) := by
  rw [sampledEval_batchMeanPlan, ← Finset.smul_sum, Finset.sum_sub_distrib]
  simp only [smul_sub, Finset.sum_const, Finset.card_range, one_div]
  rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (show (b : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hb)]

lemma sampledEval_validationPlan {Ω : Type*} {m n : ℕ}
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (ρ : ℝ) (b k q call : ℕ) (x : Fin (q + 1) → Space m n) :
    QueryPlan.sampledEval g ξ (validationPlan ρ b k q x) call =
      x (bestIndex (fun i => representative ρ (fun j : Fin (k + 1) =>
        QueryPlan.sampledEval g ξ (batchMeanPlan (x i) b)
          (call + b * (k + 1) * i.val + b * j.val)))) := by
  simp only [validationPlan, QueryPlan.sampledEval_map, sampledEval_collect]

lemma execute_validatedMuon {Ω : Type} [MeasurableSpace Ω] {m n : ℕ}
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    (α η ρ : ℝ) (T b k q K : ℕ) (x0 : Space m n)
    (seed : Fin (q + 1) → Fin (T + 1)) (ξ : ℕ → Ω)
    (hK : (b * (k + 1)) * (q + 1) + (T + 1) ≤ K) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (validatedMuon α η ρ T b k q x0) (fun _ => K) seed ξ =
      QueryPlan.sampledEval g ξ
        (validationPlan ρ b k q (fun i =>
          (QueryPlan.sampledEval g ξ (trainingPlan α η (T + 1) x0 0) 0) (seed i)))
        (T + 1) := by
  unfold validatedMuon
  erw [QueryPlan.execute_sampledPlan_of_le _ _ _ _ _ _ _ _ _ _ hK,
    QueryPlan.sampledEval_bind]
  simp only [Nat.zero_add]

end LongTails.Proofs.ValidatedMuonExecution
