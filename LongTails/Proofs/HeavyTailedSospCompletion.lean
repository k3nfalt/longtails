import LongTails.Proofs.HeavyTailedSospInvariants

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Proofs.HeavyTailedSospInvariants

namespace LongTails.Proofs.HeavyTailedSospCompletion

def ResumeCycleValid (p : Params) (c : Config) (k : ℕ) : Resume p → Prop
  | .startCycle => k ≤ c.cycles
  | _ => k < c.cycles

def CycleValid (p : Params) (c : Config) (s : State p) : Prop :=
  match s.phase with
  | .reset _ _ r | .transport _ _ _ r => ResumeCycleValid p c s.cycleIndex r
  | .done => s.cycleIndex ≤ c.cycles
  | _ => s.cycleIndex < c.cycles

lemma startCycle_cycleValid (p : Params) (c : Config) (s : State p) (hk : s.cycleIndex ≤ c.cycles) :
    CycleValid p c (startCycle p c s) := by
  unfold startCycle
  split_ifs with h
  all_goals first | exact h | exact hk

lemma resume_cycleValid (p : Params) (c : Config) (s : State p) (r : Resume p)
    (hr : ResumeCycleValid p c s.cycleIndex r) : CycleValid p c (resume p c s r) := by
  cases r with
  | startCycle => exact startCycle_cycleValid p c s hr
  | detect => exact hr
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · apply startCycle_cycleValid
      change s.cycleIndex + 1 ≤ c.cycles
      exact hr
    · exact hr

lemma completeTransport_cycleValid (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) (hr : ResumeCycleValid p c s.cycleIndex r) :
    CycleValid p c (completeTransport p c s v z r) := by
  unfold completeTransport
  dsimp only
  split_ifs
  · exact hr
  · exact resume_cycleValid p c _ r hr

lemma transportReply_cycleValid (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hr : ResumeCycleValid p c s.cycleIndex r) :
    CycleValid p c (transportReply p c s v i z reply r) := by
  unfold transportReply
  split_ifs
  · exact hr
  · exact completeTransport_cycleValid p c s v (z + reply) r hr

lemma probeReply_cycleValid (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p)
    (hk : s.cycleIndex < c.cycles) : CycleValid p c (probeReply p c s trial accepted probe reply) := by
  unfold probeReply
  dsimp only
  split_ifs <;> exact hk

lemma update_cycleValid (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) (hv : CycleValid p c s) : CycleValid p c (update p c s a reply) := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [CycleValid, hp] at hv
    simp only [update, hp]
    split_ifs
    · exact hv
    · exact resume_cycleValid p c _ r hv
  | transport v i z r =>
    simp only [CycleValid, hp] at hv
    simp only [update, hp]
    exact transportReply_cycleValid p c s v i z reply r hv
  | probeInit trial accepted =>
    simp only [CycleValid, hp] at hv
    simp only [update, hp]
    exact probeReply_cycleValid p c s trial accepted _ reply hv
  | probe trial accepted probe =>
    simp only [CycleValid, hp] at hv
    simp only [update, hp]
    exact probeReply_cycleValid p c s trial accepted probe reply hv
  | validate trial accepted v values =>
    simp only [CycleValid, hp] at hv
    simp only [update, hp]
    split_ifs
    all_goals try exact hv
    all_goals split
    all_goals first | exact hv | exact startCycle_cycleValid p c _ hv
  | ncInit v =>
    simp only [CycleValid, hp] at hv
    simp only [update, hp]
    exact transportReply_cycleValid p c s _ 0 0 reply _ hv
  | done => simpa only [update, hp] using hv

lemma initial_cycleValid (p : Params) (c : Config) (target : ℕ) :
    CycleValid p c (initial p target) := Nat.zero_le _

def cycleWork (c : Config) : ℕ :=
  (max 1 c.transportBatch + max 1 c.resetBatch) +
    max 1 c.repeats * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
    max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch)

def futureWork (c : Config) (k : ℕ) : ℕ := (c.cycles - k - 1) * cycleWork c

def resumeWork (p : Params) (c : Config) (k : ℕ) : Resume p → ℕ
  | .startCycle => (c.cycles - k) * cycleWork c
  | .detect => max 1 c.repeats * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
      max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c k
  | .ncRest n _ => n * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c k

def phaseWork (p : Params) (c : Config) (s : State p) : ℕ :=
  match s.phase with
  | .reset i _ r => max 1 c.resetBatch - i + resumeWork p c s.cycleIndex r
  | .transport _ i _ r => max 1 c.transportBatch - i + max 1 c.resetBatch + resumeWork p c s.cycleIndex r
  | .probeInit trial _ =>
      (max 1 c.repeats - trial) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
      max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c s.cycleIndex
  | .probe trial _ probe => max 1 c.probeSteps - probe.index + max 1 c.meanBatch * max 1 c.groups +
      (max 1 c.repeats - trial - 1) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
      max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c s.cycleIndex
  | .validate trial _ _ values => max 1 c.meanBatch * max 1 c.groups - values.length +
      (max 1 c.repeats - trial - 1) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
      max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c s.cycleIndex
  | .ncInit _ => max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c s.cycleIndex
  | .done => 0

lemma startCycle_work (p : Params) (c : Config) (s : State p) :
    phaseWork p c (startCycle p c s) = (c.cycles - s.cycleIndex) * cycleWork c := by
  by_cases hk : s.cycleIndex < c.cycles
  · have he : c.cycles - s.cycleIndex = (c.cycles - s.cycleIndex - 1) + 1 := by omega
    simp only [startCycle, ite_eq_left hk, phaseWork, resumeWork, Nat.sub_zero, futureWork]
    conv_rhs => rw [he, Nat.add_mul, Nat.one_mul]
    unfold cycleWork
    omega
  · have he : c.cycles - s.cycleIndex = 0 := by omega
    simp [startCycle, hk, phaseWork, he]

lemma resume_work (p : Params) (c : Config) (s : State p) (r : Resume p) :
    phaseWork p c (resume p c s r) = resumeWork p c s.cycleIndex r := by
  cases r with
  | startCycle => exact startCycle_work p c s
  | detect => simp [resume, phaseWork, resumeWork]
  | ncRest n v =>
    by_cases hn : n = 0
    · simp [resume, hn, startCycle_work, resumeWork, futureWork, Nat.sub_sub]
    · have he : n = (n - 1) + 1 := by omega
      simp only [resume, ite_eq_right hn, phaseWork, resumeWork, Nat.sub_zero]
      conv_rhs => rw [he, Nat.add_mul, Nat.one_mul]
      omega

lemma completeTransport_work_le (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    phaseWork p c (completeTransport p c s v z r) ≤ max 1 c.resetBatch + resumeWork p c s.cycleIndex r := by
  unfold completeTransport
  dsimp only
  split_ifs
  · simp [phaseWork]
  · rw [resume_work]
    dsimp only
    omega

lemma transportReply_work_le (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hi : i < max 1 c.transportBatch) :
    phaseWork p c (transportReply p c s v i z reply r) + 1 ≤
      max 1 c.transportBatch - i + max 1 c.resetBatch + resumeWork p c s.cycleIndex r := by
  unfold transportReply
  split_ifs with h
  · simp only [phaseWork]
    omega
  · have hw := completeTransport_work_le p c s v (z + reply) r
    omega

lemma probeReply_work_le (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p)
    (hi : probe.index < max 1 c.probeSteps) :
    phaseWork p c (probeReply p c s trial accepted probe reply) + 1 ≤
      max 1 c.probeSteps - probe.index + max 1 c.meanBatch * max 1 c.groups +
      (max 1 c.repeats - trial - 1) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
      max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c s.cycleIndex := by
  unfold probeReply
  dsimp only
  split_ifs with h
  · simp only [phaseWork, LongTails.Algorithms.HeavyTailedEnergyProbe.step]
    omega
  · simp only [phaseWork, List.length_nil, Nat.sub_zero]
    omega

lemma finishTrials_work_le (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p)) :
    phaseWork p c
      (if trial + 1 < max 1 c.repeats then { s with phase := .probeInit (trial + 1) accepted }
       else match accepted with
         | none => startCycle p c { s with cycleIndex := s.cycleIndex + 1 }
         | some v => { s with phase := .ncInit v }) ≤
      (max 1 c.repeats - trial - 1) * (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) +
      max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) + futureWork c s.cycleIndex := by
  split_ifs
  · simp [phaseWork, Nat.sub_sub]
  · cases accepted with
    | none =>
      rw [startCycle_work]
      simp only [futureWork, Nat.sub_sub]
      omega
    | some v => simp only [phaseWork]; omega

lemma phaseWork_zero_done (p : Params) (c : Config) (s : State p)
    (hv : PhaseValid p c s.phase) (hz : phaseWork p c s = 0) : s.phase = .done := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [hp, PhaseValid] at hv
    simp only [phaseWork, hp] at hz
    omega
  | transport v i z r =>
    simp only [hp, PhaseValid] at hv
    simp only [phaseWork, hp] at hz
    omega
  | probeInit trial accepted =>
    simp only [hp, PhaseValid] at hv
    simp only [phaseWork, hp] at hz
    have hm : 0 < (max 1 c.repeats - trial) *
        (max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  | probe trial accepted probe =>
    simp only [hp, PhaseValid] at hv
    simp only [phaseWork, hp] at hz
    omega
  | validate trial accepted v values =>
    simp only [hp, PhaseValid] at hv
    simp only [phaseWork, hp] at hz
    omega
  | ncInit v =>
    simp only [phaseWork, hp] at hz
    have hm : 0 < max 1 c.ncSegments * (max 1 c.transportBatch + max 1 c.resetBatch) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  | done => rfl

lemma update_work_decrease (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) (hv : PhaseValid p c s.phase) (hd : s.phase ≠ .done) :
    phaseWork p c (update p c s a reply) + 1 ≤ phaseWork p c s := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    split_ifs
    · simp only [phaseWork, hp]
      omega
    · rw [resume_work]
      simp only [phaseWork, hp]
      omega
  | transport v i z r =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp, phaseWork]
    exact transportReply_work_le p c s v i z reply r hv.1
  | probeInit trial accepted =>
    simp only [hp, PhaseValid] at hv
    have hw := probeReply_work_le p c s trial accepted
      (LongTails.Algorithms.HeavyTailedEnergyProbe.initialState a.2.2.1 a.2.2.2.val) reply (by
        change 0 < max 1 c.probeSteps
        omega)
    have he : max 1 c.repeats - trial = (max 1 c.repeats - trial - 1) + 1 := by omega
    simp only [LongTails.Algorithms.HeavyTailedEnergyProbe.initialState, Nat.sub_zero] at hw
    simp only [update, hp]
    conv_rhs => simp only [phaseWork, hp]; rw [he, Nat.add_mul, Nat.one_mul]
    apply hw.trans
    omega
  | probe trial accepted probe =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp, phaseWork]
    exact probeReply_work_le p c s trial accepted probe reply hv.2
  | validate trial accepted v values =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    split
    · simp only [phaseWork, hp, List.length_cons]
      omega
    · have hw := finishTrials_work_le p c s trial
        (if LongTails.Algorithms.HeavyTailedRayleighMedian.output (max 1 c.meanBatch) (max 1 c.groups)
          (inner ℝ v reply :: values).reverse ≤ -2 * c.γ then accepted.or (some v) else accepted)
      conv_rhs => simp only [phaseWork, hp]
      simp only [hp] at hw
      have hh : 0 < max 1 c.meanBatch * max 1 c.groups - values.length := by omega
      exact (Nat.add_le_add_right hw 1).trans (by omega)
  | ncInit v =>
    have hw := transportReply_work_le p c s (signedSegment p c a v) 0 0 reply
      (.ncRest (max 1 c.ncSegments - 1) (signedSegment p c a v)) (by omega)
    have he : max 1 c.ncSegments = (max 1 c.ncSegments - 1) + 1 := by omega
    simp only [Nat.sub_zero, resumeWork] at hw
    simp only [update, hp]
    conv_rhs => simp only [phaseWork, hp]; rw [he, Nat.add_mul, Nat.one_mul]
    apply hw.trans
    omega
  | done => exact (hd hp).elim

lemma trajectory_work_le (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : PhaseValid p c s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    phaseWork p c (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ) ≤ phaseWork p c s - n := by
  induction n generalizing s ξ with
  | zero => simp [LongTails.Proofs.HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    by_cases hd : s.phase = .done
    · rw [LongTails.Proofs.HeavyTailedSospExecution.done_trajectory p c g H s hd]
      simp [phaseWork, hd]
    · have hn : PhaseValid p c
          (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H s (ξ 0)).phase :=
        update_valid p c s (ξ 0).1 _ hs
      have hw : phaseWork p c
          (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H s (ξ 0)) + 1 ≤ phaseWork p c s :=
        update_work_decrease p c s (ξ 0).1 _ hs hd
      have hi := ih _ hn (fun k => ξ (k + 1))
      rw [LongTails.Proofs.HeavyTailedProductProcess.trajectory]
      omega

lemma completed_by_work (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : PhaseValid p c s.phase) (ξ : ℕ → Aux p c × p.Ω) :
    (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) (phaseWork p c s) s ξ).phase = .done := by
  apply phaseWork_zero_done p c _ (trajectory_valid p c g H s hs _ ξ)
  have hw := trajectory_work_le p c g H s hs (phaseWork p c s) ξ
  omega

lemma initial_work (p : Params) (c : Config) (target : ℕ) :
    phaseWork p c (initial p target) = max 1 c.resetBatch + c.cycles * cycleWork c := by
  simp [initial, phaseWork, resumeWork]

lemma uncapped_completion (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H)
      (max 1 c.resetBatch + c.cycles * cycleWork c) (initial p target) ξ).phase = .done := by
  rw [← initial_work p c target]
  exact completed_by_work p c g H (initial p target) (initial_valid p c target) ξ

end LongTails.Proofs.HeavyTailedSospCompletion
