import LongTails.Algorithms.ValidatedMuon
import LongTails.Proofs.SampledQueryPlan

namespace LongTails.Algorithms.ValidatedMuon

open OracleTemplate
open LongTails.Algorithms.MatrixPolar

noncomputable def trainingPlan {m n : ℕ} (α η : ℝ) :
    (T : ℕ) → Space m n → Space m n → QueryPlan (Space m n) (Space m n) (Fin T → Space m n) T
  | 0, _, _ => .done Fin.elim0
  | T + 1, x, M => .ask x fun g =>
      (trainingPlan α η T (x - η • polar ((1 - α) • M + α • g))
        ((1 - α) • M + α • g)).map (Fin.cons x)

noncomputable def batchSumPlan {m n : ℕ} (x : Space m n) :
    (b : ℕ) → Space m n → QueryPlan (Space m n) (Space m n) (Space m n) b
  | 0, s => .done s
  | b + 1, s => .ask x fun g => batchSumPlan x b (s + g)

noncomputable def batchMeanPlan {m n : ℕ} (x : Space m n) (b : ℕ) :
    QueryPlan (Space m n) (Space m n) (Space m n) b :=
  (batchSumPlan x b 0).map fun s => (1 / (b : ℝ)) • s

def collect {Q R U : Type*} {c : ℕ} : (k : ℕ) → (Fin k → QueryPlan Q R U c) →
    QueryPlan Q R (Fin k → U) (c * k)
  | 0, _ => .done Fin.elim0
  | k + 1, plans => (plans 0).bind fun a =>
      (collect k (fun i => plans i.succ)).map (Fin.cons a)

noncomputable def validationPlan {m n : ℕ} (ρ : ℝ) (b k q : ℕ)
    (x : Fin (q + 1) → Space m n) :
    QueryPlan (Space m n) (Space m n) (Space m n) ((b * (k + 1)) * (q + 1)) :=
  (collect (q + 1) (fun i =>
    (collect (k + 1) (fun _ => batchMeanPlan (x i) b)).map (representative ρ))).map
      (fun G => x (bestIndex G))

end LongTails.Algorithms.ValidatedMuon

namespace LongTails.Proofs.MuonSimulation

open OracleTemplate
open MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon
open LongTails.Setups.FiniteVarianceSpectralSmooth

noncomputable def validationStart {m n T b k q : ℕ} (ρ : ℝ)
    (sources : Fin (q + 1) → Space m n) : ValidatedMuonState m n T b k q := by
  classical
  by_cases hb : 0 < b
  · exact .validating sources ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, hb⟩ 0
      (fun _ => 0) (fun _ => 0)
  · exact .done (sources (LongTails.Setups.FiniteVarianceSpectralSmooth.bestIndex
      (m := m) (n := n) (q := q)
      (fun _ : Fin (q + 1) =>
        LongTails.Setups.FiniteVarianceSpectralSmooth.representative ρ
          (m := m) (n := n) (k := k) (fun _ : Fin (k + 1) => (0 : Space m n)))))

noncomputable def resumeMuonPlan {m n T b k q : ℕ} (α η ρ : ℝ) (x0 : Space m n) :
    (fuel : ℕ) → ValidatedMuonState m n T b k q →
      QueryPlan (Space m n) (Space m n) (Space m n) fuel := by
  intro fuel
  induction fuel with
  | zero => exact fun state => .done ((validatedMuon α η ρ T b k q x0).output state)
  | succ fuel ih =>
      exact fun state => .ask ((validatedMuon α η ρ T b k q x0).query state).2
        (fun reply => ih ((validatedMuon α η ρ T b k q x0).update state reply))

lemma sampledEval_resumeMuonPlan {m n T b k q : ℕ} {Ω : Type*}
    (α η ρ : ℝ) (x0 : Space m n) (g : Space m n → Ω → Space m n)
    (ξ : ℕ → Ω) (fuel call : ℕ) (state : ValidatedMuonState m n T b k q) :
    QueryPlan.sampledEval g ξ (resumeMuonPlan α η ρ x0 fuel state) call =
      (validatedMuon α η ρ T b k q x0).output
        (OracleTemplate.StochasticGradient.advance
          (fun j s => (validatedMuon α η ρ T b k q x0).update s
            (g ((validatedMuon α η ρ T b k q x0).query s).2 (ξ j))) fuel call state) := by
  induction fuel generalizing call state with
  | zero => rfl
  | succ fuel ih =>
      simp only [resumeMuonPlan, QueryPlan.sampledEval,
        OracleTemplate.StochasticGradient.advance]
      exact ih (call + 1) _

lemma sampledEval_resumeMuonPlan_done {m n T b k q : ℕ} {Ω : Type*}
    (α η ρ : ℝ) (x0 output : Space m n) (g : Space m n → Ω → Space m n)
    (ξ : ℕ → Ω) (fuel call : ℕ) :
    QueryPlan.sampledEval g ξ
      (resumeMuonPlan α η ρ x0 fuel (.done (T := T) (b := b) (k := k) (q := q) output)) call =
      output := by
  induction fuel generalizing call with
  | zero => rfl
  | succ fuel ih =>
      change QueryPlan.sampledEval g ξ
        (resumeMuonPlan α η ρ x0 fuel
          (.done (T := T) (b := b) (k := k) (q := q) output)) (call + 1) = output
      exact ih (call + 1)

lemma execute_validatedMuon_resume {Ω : Type} [MeasurableSpace Ω] {m n T b k : ℕ}
    {q K : ℕ} (P : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    (α η ρ : ℝ) (x0 : Space m n) (seed : (validatedMuon α η ρ T b k q x0).Seed)
    (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (validatedMuon α η ρ T b k q x0) (fun _ => K) seed ξ =
      QueryPlan.sampledEval g ξ
        (resumeMuonPlan α η ρ x0 K
          ((validatedMuon α η ρ T b k q x0).initial seed)) 0 := by
  rw [OracleTemplate.StochasticGradient.execute_advance]
  exact (sampledEval_resumeMuonPlan α η ρ x0 g ξ K 0 _).symm

end LongTails.Proofs.MuonSimulation

namespace LongTails.Proofs.ValidatedMuonExecution

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon

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

end LongTails.Proofs.ValidatedMuonExecution
