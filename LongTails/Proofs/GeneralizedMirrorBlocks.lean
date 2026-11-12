import LongTails.Proofs.GeneralizedMirrorExecution
import LongTails.Proofs.FairExecution

open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorExecution
open OracleTemplate.StochasticGradient (advance)
open OracleTemplate.FairVarianceReduction (prefixValues)

namespace LongTails.Proofs.GeneralizedMirrorBlocks

noncomputable def pilotState {q : Public} {m : ℕ} (s : State q m) (v : ℕ → Dual q)
    (n : ℕ) : State q m := { s with
  stage := 0
  received := n
  pilot := fun i => prefixValues v n i.val }

lemma storePilot_prefix {q : Public} {m : ℕ} (s : State q m) (v : ℕ → Dual q) (n : ℕ) :
    storePilot (pilotState s v n) (v n) = fun i => prefixValues v (n + 1) i.val := by
  funext i
  change (if i.val = n then v n else prefixValues v n i.val) = prefixValues v (n + 1) i.val
  by_cases hi : i.val = n
  · simp [hi, prefixValues]
  · have he : i.val < n + 1 ↔ i.val < n := by omega
    simp [hi, prefixValues, he]

lemma pilotState_zero {q : Public} {m : ℕ} (s : State q m) (v : ℕ → Dual q) :
    pilotState s v 0 = { s with stage := 0, received := 0, pilot := fun _ => 0 } := by
  simp [pilotState, prefixValues]

lemma rawAdvance_pilot_prefix (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (s : State q m) (call j : ℕ)
    (hactive : s.A < q.R ^ 2 / q.ε) (hj : j < m) :
    rawAdvance q ell m I g ξ j call
      { s with stage := 0, received := 0, pilot := fun _ => 0 } =
      pilotState s (fun i => g (mix s.A (stepWeight q ell s.A) s.x s.z) (ξ (call + i))) j := by
  induction j with
  | zero => simp only [rawAdvance, advance, pilotState_zero]
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    change update q ell _ (oracleReply I g (query q ell _) (ξ (call + j))) = _
    have hn : j + 1 ≠ m := by omega
    simp only [query, pilotState, not_le.mpr hactive, Nat.reduceEqDiff, ↓reduceIte, oracleReply]
    simp only [update, not_le.mpr hactive, hn, ↓reduceIte]
    have hp := storePilot_prefix s
      (fun i => g (mix s.A (stepWeight q ell s.A) s.x s.z) (ξ (call + i))) j
    dsimp only [pilotState] at hp
    rw [hp]

lemma rawAdvance_pilot (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (s : State q m) (call : ℕ)
    (hactive : s.A < q.R ^ 2 / q.ε) (hm : 0 < m) :
    let v : Fin m → Dual q := fun i =>
      g (mix s.A (stepWeight q ell s.A) s.x s.z) (ξ (call + i.val))
    rawAdvance q ell m I g ξ m call
      { s with stage := 0, received := 0, pilot := fun _ => 0 } = { s with
        stage := 1
        received := m - 1
        pilot := v
        center := OracleTemplate.RobustGradient.pilotCenter (clipRadius q) v } := by
  cases m with
  | zero => omega
  | succ n =>
    dsimp only
    rw [rawAdvance_add, rawAdvance_pilot_prefix q ell (n + 1) I g ξ s call n hactive (by omega)]
    change update q ell _ (oracleReply I g (query q ell _) (ξ (call + n))) = _
    simp only [query, pilotState, not_le.mpr hactive, Nat.reduceEqDiff, ↓reduceIte, oracleReply]
    simp only [update, not_le.mpr hactive, ↓reduceIte]
    have hp := storePilot_prefix s
      (fun i => g (mix s.A (stepWeight q ell s.A) s.x s.z) (ξ (call + i))) n
    dsimp only [pilotState] at hp
    rw [hp]
    have hv : (fun i : Fin (n + 1) => prefixValues
        (fun j => g (mix s.A (stepWeight q ell s.A) s.x s.z) (ξ (call + j))) (n + 1) i.val) =
        (fun i : Fin (n + 1) => g (mix s.A (stepWeight q ell s.A) s.x s.z) (ξ (call + i.val))) := by
      funext i
      exact ite_eq_left i.isLt
    rw [hv]
    rfl

lemma rawAdvance_block (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (ξ : ℕ → q.Ω) (s : State q m) (call : ℕ)
    (hactive : s.A < q.R ^ 2 / q.ε) (hm : 0 < m) :
    let a := stepWeight q ell s.A
    let y := mix s.A a s.x s.z
    let center := OracleTemplate.RobustGradient.pilotCenter (clipRadius q)
      (fun i : Fin m => g y (ξ (call + i.val)))
    let direction := OracleTemplate.RobustGradient.centeredClip (clipRadius q) center (g y (ξ (call + m)))
    let p := I.prox a s.z direction
    rawAdvance q ell m I g ξ (m + 2) call
      { s with stage := 0, received := 0, pilot := fun _ => 0 } = { s with
        A := s.A + a
        x := mix s.A a s.x p
        z := p
        stage := 0
        received := 0
        pilot := fun _ => 0
        center := 0
        direction := 0 } := by
  dsimp only
  rw [rawAdvance_add, rawAdvance_pilot q ell m I g ξ s call hactive hm]
  simp only [rawAdvance, advance, query, update, oracleReply, not_le.mpr hactive,
    Nat.reduceEqDiff, ↓reduceIte]

end LongTails.Proofs.GeneralizedMirrorBlocks
