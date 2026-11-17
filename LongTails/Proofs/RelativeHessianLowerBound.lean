import LongTails.Proofs.RelativeHessianInstance
import LongTails.Proofs.RelativeHessianAveraging
import LongTails.Proofs.FiniteSumNondualLowerBound

namespace LongTails.Proofs.RelativeHessianLowerBound

open scoped BigOperators
open OracleTemplate MeasureTheory RelativeHessianScaling RelativeHessianInstance RelativeHessianSimulation
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound
open LongTails.Setups.PointwiseHessianStationarity (Params Point broadSpec)

abbrev Alg (p : Params) := Algorithm (Point p)
  (LongTails.Setups.PointwiseHessianStationarity.Reply p) (Point p)

noncomputable def error (p : Params) {m : ℕ} (a β : ℝ) (A : Alg p) (T : ℕ)
    (seed : A.Seed) (ξ : ℕ → Unit) (w : CoordinateWords p.d m) : ℝ :=
  ‖gradient (scaled a β (coordinateEmbedding w))
    (execute (oracle a β (coordinateEmbedding w)) A (fun _ => T) seed ξ)‖

lemma pointwise_average (p : Params) {m : ℕ} {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (A : Alg p) (T : ℕ) (hT : T < m) (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ p.d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D)
    (seed : A.Seed) (ξ : ℕ → Unit) :
    (a * β) * Fintype.card (CoordinateWords p.d m) ≤
      2 * ∑ w : CoordinateWords p.d m, error p a β A T seed ξ w := by
  have h := RelativeHessianAveraging.gradient_average (normalizedQuery β A)
    (fun state => β • A.output state) (normalizedUpdate a β A) (A.initial seed) T hT D hD hd hsize
  have hs := mul_le_mul_of_nonneg_left h (mul_nonneg ha hβ)
  simpa only [error, execution_gradient ha hβ, Finset.mul_sum, mul_assoc,
    mul_left_comm (a * β) 2] using hs

lemma exists_failure (p : Params) {m : ℕ} {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (A : Alg p) (P : ProbabilityMeasure (A.Seed × (ℕ → Unit))) (T : ℕ) (hT : T < m)
    (D : ℝ) (hD : 0 < D) (hd : D + (m + 1 : ℕ) ≤ p.d)
    (hsize : 4 * (T + 1 : ℕ) * (m + 1 : ℕ) *
      ((2 * RelativeHessianLocalized.radius m) ^ 2 / (1 / 20) ^ 2) ≤ D)
    (hgap : 2 * p.ε < a * β) :
    ∃ w : CoordinateWords p.d m, ¬ broadSpec.successful p (scaled a β (coordinateEmbedding w))
      (fun ω : A.Seed × (ℕ → Unit) => execute (oracle a β (coordinateEmbedding w)) A (fun _ => T) ω.1 ω.2) P := by
  classical
  by_contra h
  push Not at h
  have hi (w : CoordinateWords p.d m) : Integrable (fun ω : A.Seed × (ℕ → Unit) => error p a β A T ω.1 ω.2 w)
      (P : Measure _) := (h w).2.1
  have hl := finite_integral_lower P
    (fun ω : A.Seed × (ℕ → Unit) => fun _ : Unit => fun w : CoordinateWords p.d m => error p a β A T ω.1 ω.2 w)
    (16 * (a * β) * Fintype.card (CoordinateWords p.d m))
    (fun _ w => hi w) (fun ω => by
      have hp := pointwise_average p ha hβ A T hT D hD hd hsize ω.1 ω.2
      simp only [Fintype.sum_unique]
      linarith)
  simp only [Fintype.sum_unique] at hl
  have hu : (∑ w : CoordinateWords p.d m, ∫ ω : A.Seed × (ℕ → Unit), error p a β A T ω.1 ω.2 w ∂(P : Measure _)) ≤
      Fintype.card (CoordinateWords p.d m) * p.ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords p.d m, p.ε := Finset.sum_le_sum (fun w _ => (h w).2.2)
      _ = _ := by simp
  have hmd : m + 1 ≤ p.d := by
    have hh : ((m + 1 : ℕ) : ℝ) ≤ p.d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords p.d m) := by
    exact_mod_cast coordinateWords_card_pos p.d m hmd
  have hstrict := mul_lt_mul_of_pos_right hgap hc
  nlinarith

end LongTails.Proofs.RelativeHessianLowerBound
