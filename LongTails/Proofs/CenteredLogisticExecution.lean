import LongTails.Proofs.CenteredLogisticSteps
import LongTails.Proofs.BatchedExecution

open OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.CenteredLogisticExecution

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space Reply)
open LongTails.Setups.TwoSampleQuadraticPerceptron (margin)
open LongTails.Algorithms.CenteredLogisticDescent
open CenteredLogisticGeometry CenteredLogisticDynamics CenteredLogisticSteps

lemma algorithm_family (p : Params) : family p (algorithm p) := by
  refine ⟨tuning, id, ?_, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  intro b
  dsimp only [tuning]
  split_ifs with h
  · exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr h), div_pos (by norm_num) h⟩
  · exact ⟨zero_lt_one, zero_lt_one⟩

lemma output_positive (p : Params) (D : Data p) (G : Geometry p D)
    (O : Oracle (Query p) (Reply p.d))
    (ho : ∀ hist query seed, O.answer hist query seed = answer D query.2)
    (seed : (algorithm p).Seed) (ω : (k : ℕ) → O.Seed k) (i : Fin p.n) :
    0 < margin .conv p.d (D i) (output p O (2 * p.n) seed ω) := by
  have he := StochasticGradient.execute_advance_of_answer O (algorithm p) (2 * p.n) seed ω
    (fun _ q => answer D q.2) (fun hist q => ho hist q _)
  have hb := advance_batched p.n.pos (full p) (fun s i => (i, s.1)) (fun _ b => b)
    (emptyReply p.d) (fun q (_ : Unit) => answer D q) (fun _ => ()) 2 0
    ((full p).initial seed)
  simp only [Nat.zero_mul] at hb
  rw [output, he]
  change 0 < margin .conv p.d (D i) ((algorithm p).output (StochasticGradient.advance
    (fun _ s => (algorithm p).update s (answer D ((algorithm p).query s).2))
    (2 * p.n) 0 (0, (full p).initial seed, fun _ => emptyReply p.d)))
  rw [show StochasticGradient.advance
    (fun _ s => (algorithm p).update s (answer D ((algorithm p).query s).2))
    (2 * p.n) 0 (0, (full p).initial seed, fun _ => emptyReply p.d) = _ from hb]
  change 0 < margin .conv p.d (D i) (let θ := initialPoint p.d
    let s := batchStep tuning (θ, none) (replies D θ)
    (batchStep tuning s (replies D s.1)).1)
  rw [physical_two_steps G, row_scale G, margin_scale]
  have hr : G.R * (Real.sqrt G.R)⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt G.scale_pos.le, mul_inv_cancel₀ G.scale_pos.ne']
  rw [hr, one_mul]
  exact positive G i

end LongTails.Proofs.CenteredLogisticExecution
