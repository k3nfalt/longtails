import LongTails.Algorithms.HystereticHessianTransport

namespace LongTails.Proofs.HystereticHessianPhases

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport

def batchRemaining (batch groups group index : ℕ) : ℕ :=
  (groups - group) * (batch + 1) + (batch + 1 - index)

lemma batchRemaining_initial (batch groups : ℕ) :
    batchRemaining batch groups 0 0 = (groups + 1) * (batch + 1) := by
  simp [batchRemaining, Nat.add_mul]

lemma batchRemaining_index {batch groups group index : ℕ} (hi : index < batch) :
    batchRemaining batch groups group (index + 1) + 1 =
      batchRemaining batch groups group index := by
  unfold batchRemaining
  omega

lemma batchRemaining_group {batch groups group : ℕ} (hj : group < groups) :
    batchRemaining batch groups (group + 1) 0 + 1 =
      batchRemaining batch groups group batch := by
  have he : groups - group = (groups - (group + 1)) + 1 := by omega
  simp [batchRemaining, he, Nat.add_mul]

lemma batchRemaining_last (batch groups : ℕ) :
    batchRemaining batch groups groups batch = 1 := by
  simp [batchRemaining]

def futureFineCalls (c : Config) (inner : ℕ) : ℕ :=
  (c.epoch + 1 - inner) * (c.transportBatch + 1) + (c.epoch - inner) * pilotCalls c

lemma futureFineCalls_last (c : Config) :
    futureFineCalls c c.epoch = c.transportBatch + 1 := by
  simp [futureFineCalls]

lemma futureFineCalls_step (c : Config) {inner : ℕ} (hi : inner < c.epoch) :
    futureFineCalls c inner = c.transportBatch + 1 + pilotCalls c + futureFineCalls c (inner + 1) := by
  have ha : c.epoch + 1 - inner = (c.epoch + 1 - (inner + 1)) + 1 := by omega
  have hb : c.epoch - inner = (c.epoch - (inner + 1)) + 1 := by omega
  unfold futureFineCalls
  rw [ha, hb, Nat.add_mul, Nat.add_mul]
  omega

def remainingWork (p : Params) (c : Config) (s : State p c) : ℕ :=
  if s.active then
    match s.phase with
    | .gradient refresh j i _ _ =>
        batchRemaining (if refresh then c.resetBatch else c.pilotBatch) c.groups j.val i +
          futureFineCalls c s.inner +
          (if refresh then 0 else if s.inner = 0 then resetCalls c else 0)
    | .transport i _ => c.transportBatch + 1 - i +
        (c.epoch - s.inner) * (pilotCalls c + (c.transportBatch + 1))
    | .padding => 0
  else 0

lemma futureFineCalls_expand (c : Config) {inner : ℕ} (hi : inner ≤ c.epoch) :
    futureFineCalls c inner = c.transportBatch + 1 +
      (c.epoch - inner) * (pilotCalls c + (c.transportBatch + 1)) := by
  have he : c.epoch + 1 - inner = c.epoch - inner + 1 := by omega
  simp only [futureFineCalls, he, Nat.add_mul, Nat.mul_add, one_mul]
  omega

lemma beginFineStep_work_le (p : Params) (c : Config) (s : State p c)
    (hi : s.inner ≤ c.epoch) :
    remainingWork p c (beginFineStep p c s) ≤ futureFineCalls c s.inner := by
  unfold beginFineStep
  split_ifs
  · simp [remainingWork]
  · cases s.active
    · simp [remainingWork]
    · simp [remainingWork, futureFineCalls_expand c hi]

lemma finishPilot_work_le (p : Params) (c : Config) (s : State p c) (v : Space p)
    (hi : s.inner ≤ c.epoch) :
    remainingWork p c (finishPilot p c s v) ≤
      futureFineCalls c s.inner + if s.inner = 0 then resetCalls c else 0 := by
  unfold finishPilot
  split_ifs
  all_goals try (simpa only [add_zero] using beginFineStep_work_le p c s hi)
  all_goals cases s.active <;> simp [remainingWork, batchRemaining, resetCalls, Nat.add_mul] <;> omega

def CounterValid (p : Params) (c : Config) (s : State p c) : Prop :=
  s.inner ≤ c.epoch + 1 ∧ match s.phase with
    | .gradient refresh _ i _ _ => s.inner ≤ c.epoch ∧
        i ≤ if refresh then c.resetBatch else c.pilotBatch
    | .transport i _ => s.inner ≤ c.epoch ∧ i ≤ c.transportBatch
    | .padding => True

lemma initial_counter_valid (p : Params) (c : Config) : CounterValid p c (initial p c) := by
  simp [CounterValid, initial]

lemma beginFineStep_counter_valid (p : Params) (c : Config) (s : State p c)
    (hi : s.inner ≤ c.epoch) : CounterValid p c (beginFineStep p c s) := by
  unfold beginFineStep
  split_ifs <;> simp [CounterValid] <;> omega

lemma finishPilot_counter_valid (p : Params) (c : Config) (s : State p c) (v : Space p)
    (hi : s.inner ≤ c.epoch) : CounterValid p c (finishPilot p c s v) := by
  unfold finishPilot
  split_ifs
  all_goals first
    | exact beginFineStep_counter_valid p c s hi
    | simp_all [CounterValid] <;> omega

lemma raw_counter_valid (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (reply : Space p) : CounterValid p c (rawUpdate p c s reply) := by
  cases hactive : s.active with
  | false => simpa [rawUpdate, hactive] using hs
  | true =>
    cases hphase : s.phase with
    | padding => simpa [rawUpdate, hactive, hphase] using hs
    | transport i sum =>
      have hh : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [hphase] using hs.2
      simp only [rawUpdate, hactive, hphase, ite_true]
      split_ifs <;> simp [CounterValid] <;> omega
    | gradient refresh j i sum values =>
      have hh : s.inner ≤ c.epoch ∧ i ≤ if refresh then c.resetBatch else c.pilotBatch := by
        simpa [hphase] using hs.2
      simp only [rawUpdate, hactive, hphase, ite_true]
      split_ifs
      all_goals first
        | exact beginFineStep_counter_valid p c _ hh.1
        | exact finishPilot_counter_valid p c s _ hh.1
        | simp_all [CounterValid]

lemma update_counter_valid (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (u : ℝ) (reply : Space p) :
    CounterValid p c (update p c s u reply) := by
  have hh := raw_counter_valid p c s hs reply
  unfold update
  split_ifs
  · exact hh
  · simp [CounterValid]

lemma raw_work_decreases (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (ha : s.active = true) (hp : s.phase ≠ .padding)
    (reply : Space p) : remainingWork p c (rawUpdate p c s reply) + 1 ≤ remainingWork p c s := by
  cases he : s.phase with
  | padding => exact (hp he).elim
  | transport i sum =>
    have hv : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hs.2
    simp only [rawUpdate, ha, he, ite_true]
    by_cases hi : i < c.transportBatch
    · rw [ite_eq_left hi]
      simp only [remainingWork, ha, he, ite_true]
      omega
    · rw [ite_eq_right hi]
      have hie : i = c.transportBatch := by omega
      by_cases hn : s.inner < c.epoch
      · rw [ite_eq_left hn]
        have hn0 : s.inner + 1 ≠ 0 := by omega
        simp only [remainingWork, ha, he, ite_true, Bool.false_eq_true, ite_false,
          hn0, Fin.val_zero, batchRemaining_initial]
        have hstep := futureFineCalls_step c hn
        have hstart := futureFineCalls_expand c hv.1
        simp only [pilotCalls] at hstep hstart ⊢
        omega
      · rw [ite_eq_right hn]
        simp only [remainingWork, ha, he, ite_true]
        omega
  | gradient refresh j i sum values =>
    let b := if refresh then c.resetBatch else c.pilotBatch
    have hv : s.inner ≤ c.epoch ∧ i ≤ b := by simpa [he, b] using hs.2
    have hjle : j.val ≤ c.groups := by have := j.isLt; omega
    simp only [rawUpdate, ha, he, ite_true]
    by_cases hi : i < b
    · rw [ite_eq_left hi]
      simp only [remainingWork, ha, he, ite_true]
      have hh := batchRemaining_index (groups := c.groups) (group := j.val) hi
      change batchRemaining b c.groups j.val (i + 1) + _ + _ + 1 ≤ batchRemaining b c.groups j.val i + _ + _
      omega
    · rw [ite_eq_right hi]
      have hie : i = b := by omega
      by_cases hj : j.val + 1 < c.groups + 1
      · rw [dite_eq_left hj]
        simp only [remainingWork, ha, he, ite_true]
        have hh := batchRemaining_group (batch := b) (by omega : j.val < c.groups)
        change batchRemaining b c.groups (j.val + 1) 0 + _ + _ + 1 ≤ batchRemaining b c.groups j.val i + _ + _
        rw [hie]
        omega
      · rw [dite_eq_right hj]
        have hje : j.val = c.groups := by omega
        have hlast : batchRemaining b c.groups j.val i = 1 := by rw [hie, hje, batchRemaining_last]
        cases hr : refresh with
        | true =>
          simp only [ite_true]
          have hh := beginFineStep_work_le p c
            { s with estimate := (OracleTemplate.MultiplicativeRobustEstimator.medoid
              (Function.update values j (((b + 1 : ℕ) : ℝ)⁻¹ • (sum + reply)))) } hv.1
          have hb : b = c.resetBatch := by simp [b, hr]
          rw [hb] at hh hlast
          simp only [remainingWork, ha, he, ite_true, hr, Nat.add_zero] at hh ⊢
          omega
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have hh := finishPilot_work_le p c s
            (OracleTemplate.MultiplicativeRobustEstimator.medoid
              (Function.update values j (((b + 1 : ℕ) : ℝ)⁻¹ • (sum + reply)))) hv.1
          have hb : b = c.pilotBatch := by simp [b, hr]
          rw [hb] at hh hlast
          simp only [remainingWork, ha, he, ite_true, hr, Bool.false_eq_true, ite_false] at hh ⊢
          omega

lemma initial_work_reserve (p : Params) (c : Config) :
    remainingWork p c (initial p c) + pilotCalls c = macroCalls c := by
  simp [remainingWork, initial, batchRemaining, futureFineCalls, macroCalls, pilotCalls,
    resetCalls, Nat.add_mul]
  ring

lemma work_pos (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (ha : s.active = true) (hp : s.phase ≠ .padding) :
    0 < remainingWork p c s := by
  cases he : s.phase with
  | padding => exact (hp he).elim
  | transport i sum =>
    have hh : s.inner ≤ c.epoch ∧ i ≤ c.transportBatch := by simpa [he] using hs.2
    simp only [remainingWork, ha, he, ite_true]
    omega
  | gradient refresh j i sum values =>
    have hh : s.inner ≤ c.epoch ∧ i ≤ if refresh then c.resetBatch else c.pilotBatch := by
      simpa [he] using hs.2
    simp only [remainingWork, ha, he, ite_true, batchRemaining]
    omega

lemma raw_work_zero (p : Params) (c : Config) (s : State p c)
    (hs : CounterValid p c s) (hz : remainingWork p c s = 0) (reply : Space p) :
    remainingWork p c (rawUpdate p c s reply) = 0 := by
  by_cases ha : s.active = true
  · have hp : s.phase = .padding := by
      by_contra hp
      have := work_pos p c s hs ha hp
      omega
    simpa [rawUpdate, ha, hp] using hz
  · simpa [rawUpdate, ha] using hz

def PhaseFits (p : Params) (c : Config) (s : State p c) : Prop :=
  s.slot < macroCalls c ∧
    (0 < remainingWork p c s → s.slot + remainingWork p c s + pilotCalls c ≤ macroCalls c)

lemma pilotCalls_pos (c : Config) : 0 < pilotCalls c := by
  exact Nat.mul_pos (by omega) (by omega)

lemma initial_phase_fits (p : Params) (c : Config) : PhaseFits p c (initial p c) := by
  have hr := initial_work_reserve p c
  have hp := pilotCalls_pos c
  constructor
  · simp only [initial]
    omega
  · simpa only [initial, Nat.zero_add] using (fun _ => Nat.le_of_eq hr)

lemma work_prevents_reset (p : Params) (c : Config) (s : State p c)
    (hs : PhaseFits p c s) (hw : 0 < remainingWork p c s) :
    s.slot + 1 < macroCalls c := by
  have := hs.2 hw
  have := pilotCalls_pos c
  omega

lemma update_phase_fits (p : Params) (c : Config) (s : State p c)
    (hc : CounterValid p c s) (hs : PhaseFits p c s) (u : ℝ) (reply : Space p) :
    PhaseFits p c (update p c s u reply) := by
  have hmono : remainingWork p c (rawUpdate p c s reply) ≤ remainingWork p c s := by
    by_cases hz : remainingWork p c s = 0
    · rw [raw_work_zero p c s hc hz reply, hz]
    · have ha : s.active = true := by
        by_contra ha
        exact hz (by simp [remainingWork, ha])
      have hp : s.phase ≠ .padding := by
        intro hp
        exact hz (by simp [remainingWork, hp])
      have := raw_work_decreases p c s hc ha hp reply
      omega
  unfold update
  split_ifs with hslot
  · constructor
    · exact hslot
    · intro hw
      change 0 < remainingWork p c (rawUpdate p c s reply) at hw
      have hpos : 0 < remainingWork p c s := by omega
      have ha : s.active = true := by
        by_contra ha
        simp [remainingWork, ha] at hpos
      have hp : s.phase ≠ .padding := by
        intro hp
        simp [remainingWork, hp] at hpos
      have hd := raw_work_decreases p c s hc ha hp reply
      have hr := hs.2 hpos
      change s.slot + 1 + remainingWork p c (rawUpdate p c s reply) + pilotCalls c ≤ _
      omega
  · have hm : 0 < macroCalls c := lt_of_le_of_lt (Nat.zero_le _) hs.1
    constructor
    · exact hm
    · intro hw
      cases ha : (rawUpdate p c s reply).active with
      | false => simp [remainingWork, ha] at hw
      | true =>
        have hr := initial_work_reserve p c
        simpa [remainingWork, initial, ha] using Nat.le_of_eq hr

def phaseRank (p : Params) (c : Config) (s : State p c) : ℕ :=
  if s.active then
    match s.phase with
    | .gradient refresh _ _ _ _ =>
        2 * (c.epoch + 1 - s.inner) + 1 +
          if refresh then 0 else if s.inner = 0 then 1 else 0
    | .transport _ _ => 2 * (c.epoch + 1 - s.inner)
    | .padding => 0
  else 0

lemma initial_phase_rank (p : Params) (c : Config) :
    phaseRank p c (initial p c) = 2 * (c.epoch + 1) + 2 := by
  simp [phaseRank, initial]

lemma beginFineStep_rank_le (p : Params) (c : Config) (s : State p c) :
    phaseRank p c (beginFineStep p c s) ≤ 2 * (c.epoch + 1 - s.inner) := by
  unfold beginFineStep
  split_ifs <;> cases s.active <;> simp [phaseRank]

lemma finishPilot_rank_le (p : Params) (c : Config) (s : State p c) (v : Space p) :
    phaseRank p c (finishPilot p c s v) ≤
      2 * (c.epoch + 1 - s.inner) + if s.inner = 0 then 1 else 0 := by
  unfold finishPilot
  split_ifs
  all_goals first
    | exact beginFineStep_rank_le p c s
    | cases s.active <;> simp_all [phaseRank]

end LongTails.Proofs.HystereticHessianPhases
