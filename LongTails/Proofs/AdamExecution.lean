import LongTails.Algorithms.BatchedAdam

namespace LongTails.Proofs.AdamExecution

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedAdam
open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Setups.BatchedSpectralSmooth

lemma batchMean_congr {r B t : ℕ} {v w : ℕ → Space r r}
    (h : ∀ k < B * (t + 1), v k = w k) : batchMean B v t = batchMean B w t := by
  unfold batchMean
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply h
  have hj' := Finset.mem_range.mp hj
  rw [Nat.mul_succ]
  omega

lemma moments_congr {r B t : ℕ} (β : ℝ) {v w : ℕ → Space r r}
    (h : ∀ k < B * t, v k = w k) :
    firstMoment β B v t = firstMoment β B w t ∧
      secondMoment β B v t = secondMoment β B w t := by
  induction t with
  | zero => simp [firstMoment, secondMoment]
  | succ t ih =>
    have hi := ih (fun k hk => h k (by rw [Nat.mul_succ]; omega))
    have hb := batchMean_congr h
    simp only [firstMoment, secondMoment, hi.1, hi.2, hb, and_self]

lemma direction_congr {r B t : ℕ} (a : AdamTuning) {v w : ℕ → Space r r}
    (h : ∀ k < B * (t + 1), v k = w k) :
    adamDirection a B v t = adamDirection a B w t := by
  have h₁ := (moments_congr a.β₁ h).1
  have h₂ := (moments_congr a.β₂ h).2
  simp only [adamDirection, h₁, h₂]

lemma iterate_congr {r B t : ℕ} (a : AdamTuning) (x0 : Space r r)
    {v w : ℕ → Space r r} (h : ∀ k < B * t, v k = w k) :
    adamIterate a B x0 v t = adamIterate a B x0 w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun k hk => h k (by rw [Nat.mul_succ]; omega))
    rw [adamIterate, adamIterate, hi, direction_congr a h]

lemma reply_state {r : ℕ} (a : AdamTuning) (B T : ℕ) (x0 : Space r r)
    (seed : Fin (T + 1)) (reply : ℕ → Space r r) (n : ℕ) :
    LongTails.Setups.FiniteVarianceSpectralSmooth.replyState (method a B T x0) seed reply n =
      (seed, n, fun k => if k < n then reply k else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (method a B T x0).update
      (LongTails.Setups.FiniteVarianceSpectralSmooth.replyState (method a B T x0) seed reply n)
      (reply n) = _
    rw [ih]
    simp only [method]
    congr 2
    funext k
    by_cases hk : k = n
    · subst k
      simp
    · rw [Function.update_of_ne hk]
      by_cases hkn : k < n
      · simp only [ite_eq_left hkn, ite_eq_left (show k < n + 1 by omega)]
      · simp only [ite_eq_right hkn, ite_eq_right (show ¬k < n + 1 by omega)]

lemma method_follows {r : ℕ} (a : AdamTuning) {B : ℕ} (hB : 0 < B)
    (T : ℕ) (x0 : Space r r) : FollowsAdam a B T x0 (method a B T x0) := by
  refine ⟨id, measurable_id, ?_, ?_⟩
  · exact Measure.map_id
  · intro seed reply
    constructor
    · intro t j ht hj
      rw [reply_state a B T x0 seed reply (B * t + j)]
      change adamIterate a B x0 (fun k => if k < B * t + j then reply k else 0)
        ((B * t + j) / B) = adamIterate a B x0 reply t
      have hdiv : (B * t + j) / B = t := by
        rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hj, Nat.add_zero]
      rw [hdiv]
      apply iterate_congr
      intro k hk
      simp [show k < B * t + j by omega]
    · intro extra
      rw [reply_state a B T x0 seed reply (B * (T + 1) + extra)]
      change adamIterate a B x0 (fun k => if k < B * (T + 1) + extra then reply k else 0) (seed : Fin (T + 1)).val =
        adamIterate a B x0 reply (seed : Fin (T + 1)).val
      apply iterate_congr
      intro k hk
      have hs := (seed : Fin (T + 1)).isLt
      have hmul := Nat.mul_le_mul_left B (Nat.le_of_lt hs)
      simp [show k < B * (T + 1) + extra by omega]

end LongTails.Proofs.AdamExecution
