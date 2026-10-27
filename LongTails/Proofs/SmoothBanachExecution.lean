import LongTails.Proofs.SmoothBanachProcess
import LongTails.Proofs.SgdExecution

namespace LongTails.Proofs.SmoothBanachExecution

open OracleTemplate OracleTemplate.StochasticGradient
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open SmoothBanachProcess SmoothBanachTuning

lemma advance_add {S : Type*} (step : ℕ → S → S) (n m call : ℕ) (s : S) :
    advance step (n + m) call s = advance step m (call + n) (advance step n call s) := by
  induction n generalizing call s with
  | zero => simp [advance]
  | succ n ih =>
    rw [Nat.succ_add, advance, ih]
    simp only [advance, Nat.add_left_comm, Nat.add_comm]

lemma advance_frozen (q : Params) (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω)
    (s : State q) (hs : levels q < s.stage) (n call : ℕ) :
    advance (fun k state => update q state (g state.point (ξ k))) n call s = s := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih =>
    simpa only [advance, update, ite_eq_right (Nat.not_le.mpr hs)] using ih (call + 1)

lemma advance_finish (q : Params) (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω)
    (j : ℕ) (hj : j ≤ levels q) (b x : q.E) (k step call : ℕ)
    (hk : 0 < k) (hstep : step + k = innerSteps q) :
    advance (fun i state => update q state (g state.point (ξ i))) k call
      ⟨j, step, b, x⟩ =
    let z := iterateSamples
      (fun y ω => picardStep (strength q j) (relaxation q / strength q j) b y (g y ω))
      k x (fun i => ξ (call + i))
    ⟨j + 1, 0, b + strength q j • z, z⟩ := by
  induction k generalizing step call x with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have hn : ¬step + 1 < innerSteps q := by omega
      simp [advance, update, hj, hn, iterateSamples]
    | succ k =>
      have hn : step + 1 < innerSteps q := by omega
      have hu : update q ⟨j, step, b, x⟩ (g x (ξ call)) =
          ⟨j, step + 1, b, picardStep (strength q j) (relaxation q / strength q j) b x (g x (ξ call))⟩ := by
        simp only [update, ite_eq_left hj, ite_eq_left hn]
      rw [advance, hu, ih _ (step + 1) (call + 1) (by omega) (by omega)]
      simp [iterateSamples, Nat.add_left_comm, Nat.add_comm]

lemma advance_epochs (q : Params) (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω)
    (hC : 0 ≤ q.C) (n : ℕ) (hn : n ≤ levels q + 1) :
    advance (fun i state => update q state (g state.point (ξ i))) (n * innerSteps q) 0
      (initial q) =
    let s := epochState q g n (fun j i => ξ (j * innerSteps q + i))
    ⟨n, 0, s.2.1, s.2.2⟩ := by
  induction n with
  | zero => simp [advance, initial, epochState, iterateSamples]
  | succ n ih =>
    have hj : n ≤ levels q := by omega
    have hi := ih (by omega)
    rw [Nat.succ_mul, advance_add, hi]
    simp only [Nat.zero_add]
    rw [advance_finish q g ξ n hj _ _ (innerSteps q) 0 (n * innerSteps q)
      (innerSteps_pos q hC) (Nat.zero_add _)]
    rw [epochState_succ]
    simp only [epochAdvance, epochState_stage]

lemma advance_padded (q : Params) (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω)
    (hC : 0 ≤ q.C) (K : ℕ) (hK : (levels q + 1) * innerSteps q ≤ K) :
    (advance (fun i state => update q state (g state.point (ξ i))) K 0 (initial q)).point =
      (epochState q g (levels q + 1) (fun j i => ξ (j * innerSteps q + i))).2.2 := by
  conv_lhs => rw [← Nat.add_sub_of_le hK]
  rw [advance_add, advance_epochs q g ξ hC _ le_rfl, advance_frozen]
  exact Nat.lt_succ_self _

lemma execute_epochs (q : Params) (g : q.E → q.Ω → q.E)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → q.Ω)) (ξ : ℕ → q.Ω)
    (hC : 0 ≤ q.C) (K : ℕ) (hK : (levels q + 1) * innerSteps q ≤ K) :
    output q
      { Seed := fun _ => q.Ω
        law := P
        answer := fun _ query seed => g query.2 seed } (fun _ => K) ξ =
      (epochState q g (levels q + 1) (fun j i => ξ (j * innerSteps q + i))).2.2 := by
  unfold output
  erw [execute_advance]
  exact advance_padded q g ξ hC K hK

end LongTails.Proofs.SmoothBanachExecution
