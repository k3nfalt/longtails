import LongTails.Proofs.HeavyTailedSospExecution

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp

namespace LongTails.Proofs.HeavyTailedSospInvariants

def ResumeValid (p : Params) (c : Config) : Resume p → Prop
  | .ncRest n _ => n < max 1 c.ncSegments
  | _ => True

def PhaseValid (p : Params) (c : Config) : Phase p → Prop
  | .reset i _ after => i < max 1 c.resetBatch ∧ ResumeValid p c after
  | .transport _ i _ after => i < max 1 c.transportBatch ∧ ResumeValid p c after
  | .probeInit trial _ => trial < max 1 c.repeats
  | .probe trial _ state => trial < max 1 c.repeats ∧ state.index < max 1 c.probeSteps
  | .validate trial _ _ values => trial < max 1 c.repeats ∧
      values.length < max 1 c.meanBatch * max 1 c.groups
  | _ => True

lemma startCycle_valid (p : Params) (c : Config) (state : State p) :
    PhaseValid p c (startCycle p c state).phase := by
  unfold startCycle
  split_ifs <;> simp only [PhaseValid, ResumeValid]
  all_goals exact ⟨by omega, trivial⟩

lemma resume_valid (p : Params) (c : Config) (state : State p) (after : Resume p)
    (ha : ResumeValid p c after) : PhaseValid p c (resume p c state after).phase := by
  cases after with
  | startCycle => exact startCycle_valid p c state
  | detect => change 0 < max 1 c.repeats; omega
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_valid p c _
    · change 0 < max 1 c.transportBatch ∧ n - 1 < max 1 c.ncSegments
      change n < max 1 c.ncSegments at ha
      constructor <;> omega

lemma completeTransport_valid (p : Params) (c : Config) (state : State p)
    (segment sum : Space p) (after : Resume p) (ha : ResumeValid p c after) :
    PhaseValid p c (completeTransport p c state segment sum after).phase := by
  unfold completeTransport
  dsimp only
  split_ifs
  · exact ⟨by omega, ha⟩
  · exact resume_valid p c _ after ha

lemma transportReply_valid (p : Params) (c : Config) (state : State p)
    (segment : Space p) (i : ℕ) (sum reply : Space p) (after : Resume p)
    (ha : ResumeValid p c after) :
    PhaseValid p c (transportReply p c state segment i sum reply after).phase := by
  unfold transportReply
  split_ifs with h
  · exact ⟨h, ha⟩
  · exact completeTransport_valid p c state segment (sum + reply) after ha

lemma probeReply_valid (p : Params) (c : Config) (state : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p)
    (ht : trial < max 1 c.repeats) :
    PhaseValid p c (probeReply p c state trial accepted probe reply).phase := by
  unfold probeReply
  dsimp only
  split_ifs with h
  · exact ⟨ht, h⟩
  · refine ⟨ht, ?_⟩
    change 0 < max 1 c.meanBatch * max 1 c.groups
    exact Nat.mul_pos (by omega) (by omega)

lemma initial_valid (p : Params) (c : Config) (target : ℕ) :
    PhaseValid p c (initial p target).phase := by
  exact ⟨by omega, trivial⟩

lemma update_valid (p : Params) (c : Config) (state : State p) (a : Aux p c)
    (reply : Space p) (hv : PhaseValid p c state.phase) :
    PhaseValid p c (update p c state a reply).phase := by
  cases hp : state.phase with
  | reset i sum after =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    split_ifs with h
    · exact ⟨h, hv.2⟩
    · exact resume_valid p c _ after hv.2
  | transport segment i sum after =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    exact transportReply_valid p c state segment i sum reply after hv.2
  | probeInit trial accepted =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    exact probeReply_valid p c state trial accepted _ reply hv
  | probe trial accepted probe =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    exact probeReply_valid p c state trial accepted probe reply hv.1
  | validate trial accepted candidate values =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    split_ifs with hlen hvalue htrial htrial
    all_goals try exact ⟨hv.1, hlen⟩
    all_goals try exact hvalue
    all_goals split
    all_goals first | exact startCycle_valid p c _ | trivial
  | ncInit candidate =>
    simp only [update, hp]
    exact transportReply_valid p c state _ 0 0 reply _ (by
      change max 1 c.ncSegments - 1 < max 1 c.ncSegments
      omega)
  | done => simp [update, hp, PhaseValid]

lemma trajectory_valid (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : PhaseValid p c s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    PhaseValid p c (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ).phase := by
  induction n generalizing s ξ with
  | zero => exact hs
  | succ n ih =>
    apply ih
    exact update_valid p c s (ξ 0).1 _ hs

@[simp] lemma startCycle_virtualIndex (p : Params) (c : Config) (s : State p) :
    (startCycle p c s).virtualIndex = s.virtualIndex := by
  unfold startCycle
  split_ifs <;> rfl

@[simp] lemma resume_virtualIndex (p : Params) (c : Config) (s : State p) (r : Resume p) :
    (resume p c s r).virtualIndex = s.virtualIndex := by
  cases r with
  | startCycle => exact startCycle_virtualIndex p c s
  | detect => rfl
  | ncRest n v => simp only [resume]; split_ifs <;> simp

@[simp] lemma completeTransport_virtualIndex (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    (completeTransport p c s v z r).virtualIndex = s.virtualIndex + 1 := by
  unfold completeTransport
  dsimp only
  split_ifs <;> simp

lemma transportReply_virtualIndex (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    (transportReply p c s v i z reply r).virtualIndex =
      s.virtualIndex + if i + 1 < max 1 c.transportBatch then 0 else 1 := by
  unfold transportReply
  split_ifs <;> simp

@[simp] lemma probeReply_virtualIndex (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    (probeReply p c s trial accepted probe reply).virtualIndex = s.virtualIndex := by
  unfold probeReply
  dsimp only
  split_ifs <;> rfl

lemma update_virtualIndex (p : Params) (c : Config) (s : State p) (a : Aux p c) (reply : Space p) :
    s.virtualIndex ≤ (update p c s a reply).virtualIndex ∧
      (update p c s a reply).virtualIndex ≤ s.virtualIndex + 1 := by
  cases hp : s.phase <;> simp only [update, hp]
  · split_ifs <;> simp
  · rw [transportReply_virtualIndex]; split_ifs <;> omega
  · simp
  · simp
  · split_ifs
    all_goals try simp
    all_goals split <;> simp
  · rw [transportReply_virtualIndex]
    split_ifs <;> omega
  · simp

def transportPartial (p : Params) : Phase p → ℕ
  | .transport _ i _ _ => i
  | _ => 0

@[simp] lemma transportPartial_reset (p : Params) (i : ℕ) (z : Space p) (r : Resume p) :
    transportPartial p (.reset i z r) = 0 := rfl

@[simp] lemma transportPartial_transport (p : Params) (v : Space p) (i : ℕ) (z : Space p) (r : Resume p) :
    transportPartial p (.transport v i z r) = i := rfl

@[simp] lemma transportPartial_probeInit (p : Params) (k : ℕ) (a : Option (Space p)) :
    transportPartial p (.probeInit k a) = 0 := rfl

@[simp] lemma transportPartial_probe (p : Params) (k : ℕ) (a : Option (Space p)) (s : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) :
    transportPartial p (.probe k a s) = 0 := rfl

@[simp] lemma transportPartial_validate (p : Params) (k : ℕ) (a : Option (Space p)) (v : Space p) (l : List ℝ) :
    transportPartial p (.validate k a v l) = 0 := rfl

@[simp] lemma transportPartial_ncInit (p : Params) (v : Space p) :
    transportPartial p (.ncInit v) = 0 := rfl

@[simp] lemma transportPartial_done (p : Params)  :
    transportPartial p .done = 0 := rfl

def transportCharge (p : Params) : Phase p → ℕ
  | .transport .. | .ncInit .. => 1
  | _ => 0

def transportProgress (p : Params) (c : Config) (s : State p) : ℕ :=
  s.virtualIndex * max 1 c.transportBatch + transportPartial p s.phase

@[simp] lemma startCycle_transportPartial (p : Params) (c : Config) (s : State p) :
    transportPartial p (startCycle p c s).phase = 0 := by
  unfold startCycle
  split_ifs <;> rfl

@[simp] lemma resume_transportPartial (p : Params) (c : Config) (s : State p) (r : Resume p) :
    transportPartial p (resume p c s r).phase = 0 := by
  cases r with
  | startCycle => exact startCycle_transportPartial p c s
  | detect => rfl
  | ncRest n v => simp only [resume]; split_ifs <;> simp

@[simp] lemma completeTransport_transportPartial (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    transportPartial p (completeTransport p c s v z r).phase = 0 := by
  unfold completeTransport
  dsimp only
  split_ifs <;> simp

@[simp] lemma probeReply_transportPartial (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    transportPartial p (probeReply p c s trial accepted probe reply).phase = 0 := by
  unfold probeReply
  dsimp only
  split_ifs <;> rfl

lemma transportReply_progress (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hi : i < max 1 c.transportBatch) :
    transportProgress p c (transportReply p c s v i z reply r) =
      s.virtualIndex * max 1 c.transportBatch + i + 1 := by
  unfold transportReply
  split_ifs with h
  · simp [transportProgress, transportPartial, Nat.add_assoc]
  · have he : i + 1 = max 1 c.transportBatch := by omega
    simp only [transportProgress, completeTransport_virtualIndex,
      completeTransport_transportPartial, Nat.add_zero, Nat.add_mul, one_mul]
    omega

lemma update_transportProgress (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) (hv : PhaseValid p c s.phase) :
    transportProgress p c (update p c s a reply) =
      transportProgress p c s + transportCharge p s.phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split_ifs <;> simp [transportProgress, hp, transportCharge]
  | transport v i z r =>
    simp only [hp, PhaseValid] at hv
    simp only [update, hp]
    rw [transportReply_progress p c s v i z reply r hv.1]
    simp [transportProgress, hp, transportCharge]
  | probeInit trial accepted =>
    simp [update, hp, transportProgress, transportCharge]
  | probe trial accepted probe =>
    simp [update, hp, transportProgress, transportCharge]
  | validate trial accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals try simp [transportProgress, hp, transportCharge]
    all_goals split <;> simp_all
  | ncInit v =>
    simp only [update, hp]
    rw [transportReply_progress p c s _ 0 0 reply _ (by omega)]
    simp [transportProgress, hp, transportCharge]
  | done => simp [update, hp, transportCharge]

lemma transportCharge_le_one (p : Params) (ph : Phase p) : transportCharge p ph ≤ 1 := by
  cases ph <;> simp [transportCharge]

lemma update_transport_allowance (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) (hv : PhaseValid p c s.phase) (cap : ℕ) :
    (cap - transportProgress p c (update p c s a reply)) +
      (if transportProgress p c s < cap then transportCharge p s.phase else 0) ≤
        cap - transportProgress p c s := by
  rw [update_transportProgress p c s a reply hv]
  have hc := transportCharge_le_one p s.phase
  split_ifs <;> omega

lemma trajectory_transportProgress (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : PhaseValid p c s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    transportProgress p c (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ) =
      transportProgress p c s + ∑ k ∈ Finset.range n, transportCharge p
        (LongTails.Proofs.HeavyTailedProductProcess.trajectory
          (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) k s ξ).phase := by
  induction n with
  | zero => simp [LongTails.Proofs.HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    rw [LongTails.Proofs.HeavyTailedProductProcess.trajectory_succ_last]
    rw [LongTails.Proofs.HeavyTailedSospExecution.sampleStep]
    rw [update_transportProgress p c _ _ _ (trajectory_valid p c g H s hs n ξ), ih]
    rw [Finset.sum_range_succ, Nat.add_assoc]

def resumeCycleFlag (p : Params) : Resume p → ℕ
  | .startCycle => 0
  | _ => 1

def phaseCycleFlag (p : Params) : Phase p → ℕ
  | .reset _ _ r => resumeCycleFlag p r
  | .transport _ i _ .detect => if i = 0 then 0 else 1
  | .transport _ _ _ r => resumeCycleFlag p r
  | .done => 0
  | _ => 1

def cycleProgress (p : Params) (s : State p) : ℕ := s.cycleIndex + phaseCycleFlag p s.phase

def markCharge (p : Params) : Phase p → ℕ
  | .transport _ i _ .detect => if i = 0 then 1 else 0
  | _ => 0

@[simp] lemma startCycle_cycleProgress (p : Params) (c : Config) (s : State p) :
    cycleProgress p (startCycle p c s) = s.cycleIndex := by
  unfold startCycle
  split_ifs <;> simp [cycleProgress, phaseCycleFlag]

@[simp] lemma resume_cycleProgress (p : Params) (c : Config) (s : State p) (r : Resume p) :
    cycleProgress p (resume p c s r) = s.cycleIndex + resumeCycleFlag p r := by
  cases r with
  | startCycle => simp [resume, resumeCycleFlag]
  | detect => rfl
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · simp [resumeCycleFlag]
    · rfl

@[simp] lemma completeTransport_cycleProgress (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    cycleProgress p (completeTransport p c s v z r) = s.cycleIndex + resumeCycleFlag p r := by
  unfold completeTransport
  dsimp only
  split_ifs
  · rfl
  · rw [resume_cycleProgress]

lemma transportReply_cycleProgress (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    cycleProgress p (transportReply p c s v i z reply r) = s.cycleIndex + resumeCycleFlag p r := by
  unfold transportReply
  split_ifs
  · cases r <;> simp [cycleProgress, phaseCycleFlag, resumeCycleFlag]
  · exact completeTransport_cycleProgress p c s v (z + reply) r

@[simp] lemma probeReply_cycleProgress (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    cycleProgress p (probeReply p c s trial accepted probe reply) = s.cycleIndex + 1 := by
  unfold probeReply
  dsimp only
  split_ifs <;> rfl

lemma update_cycleProgress (p : Params) (c : Config) (s : State p) (a : Aux p c) (reply : Space p) :
    cycleProgress p (update p c s a reply) = cycleProgress p s + markCharge p s.phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split_ifs
    · simp [cycleProgress, hp, phaseCycleFlag, markCharge]
    · rw [resume_cycleProgress]
      simp [cycleProgress, hp, phaseCycleFlag, markCharge]
  | transport v i z r =>
    simp only [update, hp, transportReply_cycleProgress]
    cases r <;> simp [cycleProgress, hp, phaseCycleFlag, resumeCycleFlag, markCharge]
    split_ifs <;> omega
  | probeInit trial accepted =>
    simp only [update, hp, probeReply_cycleProgress]
    simp [cycleProgress, hp, phaseCycleFlag, markCharge]
  | probe trial accepted probe =>
    simp only [update, hp, probeReply_cycleProgress]
    simp [cycleProgress, hp, phaseCycleFlag, markCharge]
  | validate trial accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals try split
    all_goals first
      | (rw [startCycle_cycleProgress]; simp [cycleProgress, hp, phaseCycleFlag, markCharge])
      | simp [cycleProgress, hp, phaseCycleFlag, markCharge]
  | ncInit v =>
    simp only [update, hp, transportReply_cycleProgress]
    simp [cycleProgress, hp, phaseCycleFlag, resumeCycleFlag, markCharge]
  | done => simp [update, hp, markCharge]

lemma trajectory_cycleProgress (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    cycleProgress p (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ) =
      cycleProgress p s + ∑ k ∈ Finset.range n, markCharge p
        (LongTails.Proofs.HeavyTailedProductProcess.trajectory
          (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) k s ξ).phase := by
  induction n with
  | zero => simp [LongTails.Proofs.HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    rw [LongTails.Proofs.HeavyTailedProductProcess.trajectory_succ_last]
    rw [LongTails.Proofs.HeavyTailedSospExecution.sampleStep, update_cycleProgress, ih]
    rw [Finset.sum_range_succ, Nat.add_assoc]

def gradientPending (p : Params) : Phase p → ℕ
  | .transport _ i _ .detect => if i = 0 then 0 else 1
  | _ => 0

@[simp] lemma startCycle_pending (p : Params) (c : Config) (s : State p) :
    gradientPending p (startCycle p c s).phase = 0 := by
  unfold startCycle
  split_ifs <;> rfl

@[simp] lemma resume_pending (p : Params) (c : Config) (s : State p) (r : Resume p) :
    gradientPending p (resume p c s r).phase = 0 := by
  cases r with
  | startCycle => exact startCycle_pending p c s
  | detect => rfl
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_pending p c _
    · rfl

@[simp] lemma completeTransport_pending (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    gradientPending p (completeTransport p c s v z r).phase = 0 := by
  unfold completeTransport
  dsimp only
  split_ifs
  · rfl
  · exact resume_pending p c _ r

lemma gradient_transport_balance (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) :
    (transportReply p c s v i z reply .detect).virtualIndex +
      gradientPending p (transportReply p c s v i z reply .detect).phase = s.virtualIndex + 1 := by
  unfold transportReply
  split_ifs
  · simp [gradientPending]
  · simp only [completeTransport_virtualIndex, completeTransport_pending, Nat.add_zero]

lemma update_mark_balance (p : Params) (c : Config) (s : State p) (a : Aux p c) (reply : Space p) :
    markCharge p s.phase + gradientPending p s.phase + s.virtualIndex ≤
      (update p c s a reply).virtualIndex + gradientPending p (update p c s a reply).phase := by
  have hv := (update_virtualIndex p c s a reply).1
  cases hp : s.phase with
  | transport v i z r =>
    cases r with
    | startCycle => simpa [hp, markCharge, gradientPending] using hv.trans (Nat.le_add_right _ _)
    | ncRest n u => simpa [hp, markCharge, gradientPending] using hv.trans (Nat.le_add_right _ _)
    | detect =>
      simp only [update, hp]
      rw [gradient_transport_balance]
      simp only [markCharge, gradientPending]
      split_ifs <;> omega
  | reset i z r => simpa only [hp, markCharge, gradientPending, Nat.zero_add] using hv.trans (Nat.le_add_right _ _)
  | probeInit trial accepted => simpa only [hp, markCharge, gradientPending, Nat.zero_add] using hv.trans (Nat.le_add_right _ _)
  | probe trial accepted probe => simpa only [hp, markCharge, gradientPending, Nat.zero_add] using hv.trans (Nat.le_add_right _ _)
  | validate trial accepted v values => simpa only [hp, markCharge, gradientPending, Nat.zero_add] using hv.trans (Nat.le_add_right _ _)
  | ncInit v => simpa only [hp, markCharge, gradientPending, Nat.zero_add] using hv.trans (Nat.le_add_right _ _)
  | done => simpa only [hp, markCharge, gradientPending, Nat.zero_add] using hv.trans (Nat.le_add_right _ _)

lemma trajectory_mark_balance (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let sn := LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ
    cycleProgress p sn + gradientPending p s.phase + s.virtualIndex ≤
      cycleProgress p s + sn.virtualIndex + gradientPending p sn.phase := by
  induction n with
  | zero => simp only [LongTails.Proofs.HeavyTailedProductProcess.trajectory]; omega
  | succ n ih =>
    let sn := LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ
    have hm : markCharge p sn.phase + gradientPending p sn.phase + sn.virtualIndex ≤
        (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H sn (ξ n)).virtualIndex +
          gradientPending p (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H sn (ξ n)).phase :=
      update_mark_balance p c sn (ξ n).1 _
    have hc : cycleProgress p (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H sn (ξ n)) =
        cycleProgress p sn + markCharge p sn.phase := update_cycleProgress p c sn (ξ n).1 _
    rw [LongTails.Proofs.HeavyTailedProductProcess.trajectory_succ_last]
    dsimp only [sn] at hm hc
    dsimp only at ih ⊢
    omega

lemma trajectory_mark_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let sn := LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ
    (∑ k ∈ Finset.range n, markCharge p
      (LongTails.Proofs.HeavyTailedProductProcess.trajectory
        (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) k s ξ).phase) +
        gradientPending p s.phase + s.virtualIndex ≤ sn.virtualIndex + gradientPending p sn.phase := by
  have hb := trajectory_mark_balance p c g H s n ξ
  dsimp only at hb ⊢
  rw [trajectory_cycleProgress] at hb
  omega

lemma mark_pending_zero (p : Params) (ph : Phase p) (hm : markCharge p ph = 1) :
    gradientPending p ph = 0 := by
  cases ph with
  | transport v i z r =>
    cases r <;> simp only [markCharge, gradientPending] at hm ⊢
    split_ifs at hm ⊢; omega
  | _ => simp [markCharge] at hm

lemma epoch_mark_ordinal_le (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n q : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hmark : markCharge p (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ).phase = 1)
    (hepoch : (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ).virtualIndex < s.virtualIndex + q) :
    (∑ k ∈ Finset.range n, markCharge p
      (LongTails.Proofs.HeavyTailedProductProcess.trajectory
        (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) k s ξ).phase) + 1 ≤ q := by
  have hb := trajectory_mark_count p c g H s n ξ
  have hp := mark_pending_zero p _ hmark
  dsimp only at hb
  omega

end LongTails.Proofs.HeavyTailedSospInvariants
