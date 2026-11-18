import LongTails.Proofs.HolderNoiseHardAdmissible
import LongTails.Proofs.HolderNoiseHiding
import LongTails.Proofs.Execution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.HolderNoiseHardExecution

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower
open HolderNoiseHardScaling HolderNoiseHardOracle HolderNoiseHardAdmissible HolderNoiseHiding
open FrontierChainOracle FrontierChainWall
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerExposure

abbrev Alg (q : LowerParams) : Type 1 := Algorithm (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d))
  (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) 1

noncomputable def queryData (q : LowerParams) (A : Alg q) (a b : ℝ) (seed : A.Seed) : QueryData A.State q.d where
  query := fun s => (A.query s).2
  output := A.output
  update := A.update
  normalize := normalize b q.x0
  response := fun v => (a / b) • v
  init := A.initial seed

lemma oracle_scaled {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (a b p : ℝ)
    (x0 x : EuclideanSpace ℝ (Fin d)) (ω : Bool) :
    oracleValue p (field π a b x0) (noise π a b x0) x ω =
      (a / b) • canonicalOracle π p (normalize b x0 x) ω := by
  simp only [oracleValue, field, noise, canonicalOracle]
  module

lemma execute_actualState (q : LowerParams) {k : ℕ} (π : Fin (k + 1) ↪ Fin q.d)
    (A : Alg q) (a b : ℝ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ)
    (seed : A.Seed) (β : ℕ → Bool) :
    execute (pairOracle q hp hp1 (oracleValue p (field π a b q.x0) (noise π a b q.x0)))
      A (fun _ => N) seed β = A.output (actualState (queryData q A a b seed) π p β N) := by
  let response := fun t (z : Fin 1 × (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d))) =>
    (oracleValue p (field π a b q.x0) (noise π a b q.x0) z.2.1 (β t),
      oracleValue p (field π a b q.x0) (noise π a b q.x0) z.2.2 (β t))
  rw [execute_indexed_of_answer (pairOracle q hp hp1
    (oracleValue p (field π a b q.x0) (noise π a b q.x0))) A N seed β response (fun _ _ => rfl)]
  have he (t : ℕ) :
      (fun sc : A.State × ℕ => (A.update sc.1 (response sc.2 (A.query sc.1)), sc.2 + 1))^[t]
        (A.initial seed, 0) = (actualState (queryData q A a b seed) π p β t, t) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [response, actualState, actualPair, queryData]
      rw [oracle_scaled, oracle_scaled]
  rw [he]

lemma execution_gradient_sum (q : LowerParams) {k : ℕ} (A : Alg q) {a b p : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ)
    (seed : A.Seed) (β : ℕ → Bool) (D : ℝ) (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ q.d)
    (hsize : 4 * ((3 * ((N : ℝ) + 1)) * (k + 1 : ℕ) * (radius k ^ 2 / (1 / 4) ^ 2)) ≤ D) :
    (a / b) * (3 / 8 : ℝ) * Fintype.card (CoordinateWords q.d k) *
      (1 - (exposure β N : ℝ) / (k + 1)) ≤
      ∑ w : CoordinateWords q.d k,
        ‖gradient (objective (coordinateEmbedding w) a b q.x0)
          (execute (pairOracle q hp hp1 (oracleValue p (field (coordinateEmbedding w) a b q.x0)
            (noise (coordinateEmbedding w) a b q.x0))) A (fun _ => N) seed β)‖ := by
  have h := gradient_sum_exposure (queryData q A a b seed) p β N D hD hDs hsize
  have hs := mul_le_mul_of_nonneg_left h (div_nonneg ha hb.le)
  rw [Finset.mul_sum] at hs
  convert hs using 1
  · ring
  · apply Finset.sum_congr rfl
    intro w _
    rw [(objective_gradient (coordinateEmbedding w) a b q.x0 _).gradient, execute_actualState]
    simp only [field, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hb.le), queryData]

end LongTails.Proofs.HolderNoiseHardExecution
