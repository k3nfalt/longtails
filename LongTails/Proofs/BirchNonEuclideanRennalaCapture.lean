import LongTails.Proofs.BirchNonEuclideanRennalaLegality

namespace LongTails.Proofs.BirchNonEuclideanRennalaCapture

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanRennalaScheduling
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality

def Captured {m : ℕ} (pub : State m) (regs : Registers m) : Prop :=
  ∀ w ∈ pub.live, regs.point w = regs.points (pub.source w)

lemma replyCode_points_old {m : ℕ} (K B : ℕ) (pub : State m) (regs : Registers m)
    (w : Fin m) (s : CodeState) (j : ℕ) (hj : j ≤ pub.round) :
    (replyCode K B w pub regs s).1.points j = regs.points j := by
  have hn : j ≠ pub.round + 1 := by omega
  simp only [replyCode, state_bind_apply]
  split_ifs <;> simp only [commitCode, relaunchCode, state_bind_apply, state_pure_apply,
    Function.update_of_ne hn]

lemma replyCode_point_other {m : ℕ} (K B : ℕ) (pub : State m) (regs : Registers m)
    (w v : Fin m) (s : CodeState) (hv : v ≠ w) :
    (replyCode K B w pub regs s).1.point v = regs.point v := by
  simp only [replyCode, state_bind_apply]
  split_ifs <;> simp only [commitCode, relaunchCode, state_bind_apply, state_pure_apply,
    Function.update_of_ne hv]

lemma replyCode_point_current {m : ℕ} (K B : ℕ) (pub : State m) (regs : Registers m)
    (w : Fin m) (s : CodeState) (ha : pub.round < K) (hn : (step K B pub (.reply w)).round < K) :
    (replyCode K B w pub regs s).1.point w =
      (replyCode K B w pub regs s).1.points (step K B pub (.reply w)).round := by
  simp only [replyCode, state_bind_apply, ite_eq_left ha, ite_eq_left hn]
  split_ifs <;> simp only [commitCode, relaunchCode, state_bind_apply, state_pure_apply,
    Function.update_self]

lemma step_live_subset {m : ℕ} (K B : ℕ) (pub : State m) (e : Event m) :
    (step K B pub e).live ⊆ pub.live := by
  cases e with
  | query w => exact Finset.Subset.refl _
  | reply w =>
      by_cases ha : pub.round < K
      · simp only [step, ite_eq_left ha]
        by_cases hn : pub.round + (if commits B pub w then 1 else 0) < K
        · rw [ite_eq_left hn]
        · rw [ite_eq_right hn]
          exact Finset.erase_subset _ _
      · simpa only [step, ite_eq_right ha] using Finset.erase_subset w pub.live

lemma reply_live_self {m : ℕ} (K B : ℕ) (pub : State m) (w : Fin m)
    (hw : w ∈ (step K B pub (.reply w)).live) :
    pub.round < K ∧ (step K B pub (.reply w)).round < K := by
  by_cases ha : pub.round < K
  · refine ⟨ha, ?_⟩
    by_contra hn
    have hf : ¬pub.round + (if commits B pub w then 1 else 0) < K := by
      simpa only [step, ite_eq_left ha] using hn
    simp only [step, ite_eq_left ha, ite_eq_right hf, Finset.mem_erase,
      ne_eq, not_true_eq_false, false_and] at hw
  · simp [step, ha] at hw

lemma reply_source_other {m : ℕ} (K B : ℕ) (pub : State m) (w v : Fin m) (hv : v ≠ w) :
    (step K B pub (.reply w)).source v = pub.source v := by
  unfold step
  split_ifs <;> simp only [Function.update_of_ne hv]

lemma reply_source_self {m : ℕ} (K B : ℕ) (pub : State m) (w : Fin m) (ha : pub.round < K) :
    (step K B pub (.reply w)).source w = (step K B pub (.reply w)).round := by
  simp only [step, ite_eq_left ha, Function.update_self]

lemma eventCode_captured {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m) (s : CodeState)
    (hi : Invariant K B state.1) (hc : Captured state.1 state.2) :
    let z := eventCode K B e state s
    Captured z.1.1 z.1.2 := by
  dsimp only
  rw [eventCode_public]
  cases e with
  | query w => exact hc
  | reply w =>
      intro v hv
      change (replyCode K B w state.1 state.2 s).1.point v =
        (replyCode K B w state.1 state.2 s).1.points ((step K B state.1 (.reply w)).source v)
      by_cases h : v = w
      · subst v
        have hl := reply_live_self K B state.1 w hv
        rw [reply_source_self K B state.1 w hl.1]
        exact replyCode_point_current K B state.1 state.2 w s hl.1 hl.2
      · rw [reply_source_other K B state.1 w v h, replyCode_point_other K B state.1 state.2 w v s h,
          replyCode_points_old K B state.1 state.2 w s _ (hi.source_le v)]
        exact hc v (step_live_subset K B state.1 (.reply w) hv)

lemma loop_captured {m : ℕ} (K B : ℕ) (events : List (Event m))
    (state : State m × Registers m) (s : CodeState)
    (hi : Invariant K B state.1) (hc : Captured state.1 state.2) (he : LegalFrom K B state.1 events) :
    let z := (forIn events state (fun e state => ForInStep.yield <$> eventCode K B e state) :
      StateM CodeState (State m × Registers m)) s
    Captured z.1.1 z.1.2 := by
  induction events generalizing state s with
  | nil => exact hc
  | cons e rest ih =>
      have hstep := eventCode_captured K B e state s hi hc
      have hinv : Invariant K B (eventCode K B e state s).1.1 := by
        rw [eventCode_public]
        exact step_invariant K B state.1 e hi he.1
      have hr : LegalFrom K B (eventCode K B e state s).1.1 rest := by rw [eventCode_public]; exact he.2
      rw [state_forIn_cons]
      exact ih _ _ hinv hstep hr

lemma eventsStateCode_captured {m : ℕ} (K B : ℕ) (events : List (Event m)) (hK : 0 < K) (hB : 0 < B)
    (he : LegalFrom K B {} events) :
    let z := eventsStateCode K B events {}
    Captured z.1.1 z.1.2 := by
  rw [eventsStateCode_run]
  apply loop_captured K B events _ _ (invariant_initial K B hK hB) _ he
  intro w _
  rw [initialCode_run]

lemma eventCode_main_old {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m) (s : CodeState)
    (j : ℕ) (hj : j ≤ state.1.round) : (eventCode K B e state s).1.2.points j = state.2.points j := by
  cases e with
  | query w => rfl
  | reply w => exact replyCode_points_old K B state.1 state.2 w s j hj

end LongTails.Proofs.BirchNonEuclideanRennalaCapture
