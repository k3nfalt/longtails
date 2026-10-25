import LongTails.Proofs.HeavyTailedSospEpoch
import LongTails.Proofs.HeavyTailedSospCompletion

namespace LongTails.Proofs.HeavyTailedSospWork

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedSospInvariants HeavyTailedProductProcess HeavyTailedSospExecution

def remaining (p : Params) : Resume p → ℕ
  | .ncRest n _ => n
  | _ => 0

def outstanding (p : Params) : Phase p → ℕ
  | .reset _ _ r => remaining p r
  | .transport _ i _ .detect => if i = 0 then 0 else 1
  | .transport _ _ _ r => 1 + remaining p r
  | _ => 0

def ncCharge (p : Params) : Phase p → ℕ
  | .ncInit _ => 1
  | _ => 0

lemma startCycle_outstanding (p : Params) (c : Config) (s : State p) :
    outstanding p (startCycle p c s).phase = 0 := by
  unfold startCycle
  split <;> rfl

lemma resume_outstanding (p : Params) (c : Config) (s : State p) (r : Resume p) :
    outstanding p (resume p c s r).phase = remaining p r := by
  cases r with
  | startCycle => exact startCycle_outstanding p c s
  | detect => rfl
  | ncRest n v =>
    by_cases hn : n = 0
    · subst n
      simpa only [resume, ↓reduceIte, remaining] using startCycle_outstanding p c
        { s with cycleIndex := s.cycleIndex + 1 }
    · simp only [resume, hn, ↓reduceIte, outstanding, remaining]
      omega

lemma completeTransport_outstanding (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    outstanding p (completeTransport p c s v z r).phase = remaining p r := by
  unfold completeTransport
  dsimp only
  split
  · rfl
  · exact resume_outstanding p c _ r

lemma transportReply_balance (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    (transportReply p c s v i z reply r).virtualIndex +
      outstanding p (transportReply p c s v i z reply r).phase =
      s.virtualIndex + 1 + remaining p r := by
  unfold transportReply
  split
  · cases r <;> simp [outstanding, remaining, Nat.add_assoc]
  · rw [completeTransport_virtualIndex, completeTransport_outstanding]

lemma update_outstanding_balance (p : Params) (c : Config) (s : State p)
    (a : Aux p c) (reply : Space p) :
    (update p c s a reply).virtualIndex + outstanding p (update p c s a reply).phase =
      s.virtualIndex + outstanding p s.phase + markCharge p s.phase +
        max 1 c.ncSegments * ncCharge p s.phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split
    · simp [outstanding, markCharge, ncCharge]
    · rw [resume_virtualIndex, resume_outstanding]
      simp [outstanding, markCharge, ncCharge]
  | transport v i z r =>
    simp only [update, hp, transportReply_balance]
    cases r <;> simp [outstanding, markCharge, ncCharge, remaining, Nat.add_assoc]
    split <;> omega
  | probeInit trial accepted =>
    simp only [update, hp, probeReply]
    split <;> simp [outstanding, markCharge, ncCharge]
  | probe trial accepted probe =>
    simp only [update, hp, probeReply]
    split <;> simp [outstanding, markCharge, ncCharge]
  | validate trial accepted v values =>
    simp only [update, hp]
    split
    · simp [outstanding, markCharge, ncCharge]
    · split
      · simp [outstanding, markCharge, ncCharge]
      · split
        · rw [startCycle_virtualIndex, startCycle_outstanding]
          simp [outstanding, markCharge, ncCharge]
        · simp [outstanding, markCharge, ncCharge]
  | ncInit v =>
    simp only [update, hp]
    rw [transportReply_balance]
    simp only [remaining, outstanding, markCharge, ncCharge]
    omega
  | done => simp [update, hp, outstanding, markCharge, ncCharge]

lemma trajectory_outstanding_balance (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let X := fun k => trajectory (sampleStep p c g H) k s ξ
    (X N).virtualIndex + outstanding p (X N).phase = s.virtualIndex + outstanding p s.phase +
      (∑ k ∈ Finset.range N, markCharge p (X k).phase) +
      max 1 c.ncSegments * ∑ k ∈ Finset.range N, ncCharge p (X k).phase := by
  intro X
  induction N with
  | zero => simp [X, trajectory]
  | succ N ih =>
    change (trajectory (sampleStep p c g H) (N + 1) s ξ).virtualIndex +
      outstanding p (trajectory (sampleStep p c g H) (N + 1) s ξ).phase = _
    rw [trajectory_succ_last, sampleStep, update_outstanding_balance]
    change (X N).virtualIndex + outstanding p (X N).phase + _ + _ = _
    rw [ih, Finset.sum_range_succ, Finset.sum_range_succ, Nat.mul_add]
    dsimp only [X]
    omega

def DoneLower (p : Params) (c : Config) (s : State p) : Prop :=
  s.phase = .done → c.cycles ≤ s.cycleIndex

lemma startCycle_doneLower (p : Params) (c : Config) (s : State p) :
    DoneLower p c (startCycle p c s) := by
  unfold startCycle
  split <;> simp_all [DoneLower]

lemma resume_doneLower (p : Params) (c : Config) (s : State p) (r : Resume p) :
    DoneLower p c (resume p c s r) := by
  cases r with
  | startCycle => exact startCycle_doneLower p c s
  | detect => simp [resume, DoneLower]
  | ncRest n v =>
    simp only [resume]
    split
    · exact startCycle_doneLower p c _
    · simp [DoneLower]

lemma completeTransport_doneLower (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) : DoneLower p c (completeTransport p c s v z r) := by
  unfold completeTransport
  dsimp only
  split
  · simp [DoneLower]
  · exact resume_doneLower p c _ r

lemma transportReply_doneLower (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    DoneLower p c (transportReply p c s v i z reply r) := by
  unfold transportReply
  split
  · simp [DoneLower]
  · exact completeTransport_doneLower p c s v (z + reply) r

lemma probeReply_doneLower (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    DoneLower p c (probeReply p c s trial accepted probe reply) := by
  unfold probeReply
  dsimp only
  split <;> simp [DoneLower]

lemma update_doneLower (p : Params) (c : Config) (s : State p)
    (a : Aux p c) (reply : Space p) (hs : DoneLower p c s) :
    DoneLower p c (update p c s a reply) := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split
    · simp [DoneLower]
    · exact resume_doneLower p c _ r
  | transport v i z r =>
    simpa only [update, hp] using transportReply_doneLower p c s v i z reply r
  | probeInit trial accepted =>
    simpa only [update, hp] using probeReply_doneLower p c s trial accepted
      (LongTails.Algorithms.HeavyTailedEnergyProbe.initialState a.2.2.1 a.2.2.2.val) reply
  | probe trial accepted probe =>
    simpa only [update, hp] using probeReply_doneLower p c s trial accepted probe reply
  | validate trial accepted v values =>
    simp only [update, hp]
    split
    · simp [DoneLower]
    · split
      · simp [DoneLower]
      · split
        · exact startCycle_doneLower p c _
        · simp [DoneLower]
  | ncInit v =>
    simpa only [update, hp] using transportReply_doneLower p c s (signedSegment p c a v)
      0 0 reply (.ncRest (max 1 c.ncSegments - 1) (signedSegment p c a v))
  | done => simpa only [update, hp] using hs

lemma trajectory_cycleBounds (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    HeavyTailedSospCompletion.CycleValid p c
      (trajectory (sampleStep p c g H) N (initial p target) ξ) ∧
    DoneLower p c (trajectory (sampleStep p c g H) N (initial p target) ξ) := by
  induction N with
  | zero =>
    exact ⟨HeavyTailedSospCompletion.initial_cycleValid p c target, by simp [trajectory, initial, DoneLower]⟩
  | succ N ih =>
    rw [trajectory_succ_last, sampleStep]
    exact ⟨HeavyTailedSospCompletion.update_cycleValid p c _ _ _ ih.1,
      update_doneLower p c _ _ _ ih.2⟩

lemma completed_cycleIndex (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (trajectory (sampleStep p c g H) N (initial p target) ξ).cycleIndex = c.cycles := by
  have hb := trajectory_cycleBounds p c g H target N ξ
  have hlo := hb.2 hdone
  have hhi := hb.1
  simp only [HeavyTailedSospCompletion.CycleValid, hdone] at hhi
  omega

lemma completed_mark_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range N, markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) = c.cycles := by
  have hc := completed_cycleIndex p c g H target N ξ hdone
  have ht := trajectory_cycleProgress p c g H (initial p target) N ξ
  rw [cycleProgress, hdone, phaseCycleFlag, hc] at ht
  simpa [cycleProgress, initial, phaseCycleFlag, resumeCycleFlag] using ht.symm

lemma completed_virtualIndex (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex = c.cycles +
      max 1 c.ncSegments * ∑ k ∈ Finset.range N, ncCharge p
        (trajectory (sampleStep p c g H) k (initial p target) ξ).phase := by
  have ht := trajectory_outstanding_balance p c g H (initial p target) N ξ
  dsimp only at ht
  rw [hdone, completed_mark_count p c g H target N ξ hdone] at ht
  simpa [initial, outstanding, remaining] using ht

def resetPartial (p : Params) (c : Config) : Phase p → ℕ
  | .reset i _ _ => i
  | _ => max 1 c.resetBatch

def resetCharge (p : Params) : Phase p → ℕ
  | .reset .. => 1
  | _ => 0

def resetProgress (p : Params) (c : Config) (s : State p) : ℕ :=
  max 1 c.resetBatch * (s.virtualIndex / max 1 c.epoch) + resetPartial p c s.phase

lemma startCycle_resetProgress (p : Params) (c : Config) (s : State p) :
    resetProgress p c (startCycle p c s) =
      max 1 c.resetBatch * (s.virtualIndex / max 1 c.epoch + 1) := by
  unfold startCycle
  split <;> simp [resetProgress, resetPartial, Nat.mul_add]

lemma resume_resetProgress (p : Params) (c : Config) (s : State p) (r : Resume p) :
    resetProgress p c (resume p c s r) =
      max 1 c.resetBatch * (s.virtualIndex / max 1 c.epoch + 1) := by
  cases r with
  | startCycle => exact startCycle_resetProgress p c s
  | detect => simp [resume, resetProgress, resetPartial, Nat.mul_add]
  | ncRest n v =>
    simp only [resume]
    split
    · exact startCycle_resetProgress p c _
    · simp [resetProgress, resetPartial, Nat.mul_add]

lemma completeTransport_resetProgress (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    resetProgress p c (completeTransport p c s v z r) =
      max 1 c.resetBatch * (s.virtualIndex / max 1 c.epoch + 1) := by
  unfold completeTransport
  dsimp only
  split_ifs with h
  · simp only [resetProgress, resetPartial, Nat.add_zero]
    rw [Nat.succ_div_of_mod_eq_zero h]
  · rw [resume_resetProgress]
    rw [Nat.succ_div_of_mod_ne_zero h]

lemma transportReply_resetProgress (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    resetProgress p c (transportReply p c s v i z reply r) =
      max 1 c.resetBatch * (s.virtualIndex / max 1 c.epoch + 1) := by
  unfold transportReply
  split
  · simp [resetProgress, resetPartial, Nat.mul_add]
  · exact completeTransport_resetProgress p c s v (z + reply) r

lemma probeReply_resetProgress (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    resetProgress p c (probeReply p c s trial accepted probe reply) =
      max 1 c.resetBatch * (s.virtualIndex / max 1 c.epoch + 1) := by
  unfold probeReply
  dsimp only
  split <;> simp [resetProgress, resetPartial, Nat.mul_add]

lemma update_resetProgress (p : Params) (c : Config) (s : State p)
    (a : Aux p c) (reply : Space p) (hv : PhaseValid p c s.phase) :
    resetProgress p c (update p c s a reply) = resetProgress p c s + resetCharge p s.phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [PhaseValid, hp] at hv
    simp only [update, hp]
    split_ifs with hi
    · simp [resetProgress, resetPartial, resetCharge, hp, Nat.add_assoc]
    · rw [resume_resetProgress]
      have heq : i + 1 = max 1 c.resetBatch := by omega
      simp only [resetProgress, resetPartial, resetCharge, hp, Nat.mul_add, Nat.mul_one]
      omega
  | transport v i z r =>
    simp only [update, hp]
    rw [transportReply_resetProgress]
    simp [resetProgress, resetPartial, resetCharge, hp, Nat.mul_add]
  | probeInit trial accepted =>
    simp only [update, hp]
    rw [probeReply_resetProgress]
    simp [resetProgress, resetPartial, resetCharge, hp, Nat.mul_add]
  | probe trial accepted probe =>
    simp only [update, hp]
    rw [probeReply_resetProgress]
    simp [resetProgress, resetPartial, resetCharge, hp, Nat.mul_add]
  | validate trial accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals solve
      | simp [resetProgress, resetPartial, resetCharge, hp]
      | (split
         · rw [startCycle_resetProgress]
           simp [resetProgress, resetPartial, resetCharge, hp, Nat.mul_add]
         · simp [resetProgress, resetPartial, resetCharge, hp])
  | ncInit v =>
    simp only [update, hp]
    rw [transportReply_resetProgress]
    simp [resetProgress, resetPartial, resetCharge, hp, Nat.mul_add]
  | done => simp [update, hp, resetCharge]

lemma trajectory_resetProgress (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : PhaseValid p c s.phase) (N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    resetProgress p c (trajectory (sampleStep p c g H) N s ξ) = resetProgress p c s +
      ∑ k ∈ Finset.range N, resetCharge p (trajectory (sampleStep p c g H) k s ξ).phase := by
  induction N with
  | zero => simp [trajectory]
  | succ N ih =>
    rw [trajectory_succ_last, sampleStep]
    rw [update_resetProgress p c _ _ _ (trajectory_valid p c g H s hs N ξ), ih]
    rw [Finset.sum_range_succ, Nat.add_assoc]

lemma completed_reset_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range N, resetCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) =
      max 1 c.resetBatch *
        ((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex / max 1 c.epoch + 1) := by
  have ht := trajectory_resetProgress p c g H (initial p target) (initial_valid p c target) N ξ
  rw [resetProgress, hdone] at ht
  simpa [resetProgress, resetPartial, initial, Nat.mul_add] using ht.symm

lemma completed_transport_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range N, transportCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) =
      (trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex * max 1 c.transportBatch := by
  have ht := trajectory_transportProgress p c g H (initial p target) (initial_valid p c target) N ξ
  rw [transportProgress, hdone] at ht
  simpa [transportProgress, transportPartial, initial] using ht.symm

def trialCalls (c : Config) : ℕ := max 1 c.probeSteps + max 1 c.meanBatch * max 1 c.groups

def detectorCalls (c : Config) : ℕ := max 1 c.repeats * trialCalls c

def resumeDetector (p : Params) (c : Config) : Resume p → ℕ
  | .ncRest .. => detectorCalls c
  | _ => 0

def detectorPartial (p : Params) (c : Config) : Phase p → ℕ
  | .probeInit trial _ => trial * trialCalls c
  | .probe trial _ probe => trial * trialCalls c + probe.index
  | .validate trial _ _ values => trial * trialCalls c + max 1 c.probeSteps + values.length
  | .ncInit _ => detectorCalls c
  | .reset _ _ r | .transport _ _ _ r => resumeDetector p c r
  | _ => 0

def detectorProgress (p : Params) (c : Config) (s : State p) : ℕ :=
  s.cycleIndex * detectorCalls c + detectorPartial p c s.phase

def detectorCharge (p : Params) : Phase p → ℕ
  | .probeInit .. | .probe .. | .validate .. => 1
  | _ => 0

lemma startCycle_detectorProgress (p : Params) (c : Config) (s : State p) :
    detectorProgress p c (startCycle p c s) = s.cycleIndex * detectorCalls c := by
  unfold startCycle
  split <;> simp [detectorProgress, detectorPartial, resumeDetector]

lemma resume_detectorProgress (p : Params) (c : Config) (s : State p) (r : Resume p) :
    detectorProgress p c (resume p c s r) = s.cycleIndex * detectorCalls c + resumeDetector p c r := by
  cases r with
  | startCycle => simpa [resume, resumeDetector] using startCycle_detectorProgress p c s
  | detect => simp [resume, detectorProgress, detectorPartial, resumeDetector]
  | ncRest n v =>
    simp only [resume]
    split
    · rw [startCycle_detectorProgress]
      simp [resumeDetector, Nat.add_mul]
    · rfl

lemma completeTransport_detectorProgress (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    detectorProgress p c (completeTransport p c s v z r) =
      s.cycleIndex * detectorCalls c + resumeDetector p c r := by
  unfold completeTransport
  dsimp only
  split
  · rfl
  · exact resume_detectorProgress p c _ r

lemma transportReply_detectorProgress (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    detectorProgress p c (transportReply p c s v i z reply r) =
      s.cycleIndex * detectorCalls c + resumeDetector p c r := by
  unfold transportReply
  split
  · rfl
  · exact completeTransport_detectorProgress p c s v (z + reply) r

lemma probeReply_detectorProgress (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p)
    (hi : probe.index < max 1 c.probeSteps) :
    detectorProgress p c (probeReply p c s trial accepted probe reply) =
      s.cycleIndex * detectorCalls c + trial * trialCalls c + probe.index + 1 := by
  unfold probeReply
  dsimp only
  split_ifs with h
  · simp [detectorProgress, detectorPartial, LongTails.Algorithms.HeavyTailedEnergyProbe.step, Nat.add_assoc]
  · have heq : probe.index + 1 = max 1 c.probeSteps := by
      simp only [LongTails.Algorithms.HeavyTailedEnergyProbe.step] at h
      omega
    simp only [detectorProgress, detectorPartial, List.length_nil, Nat.add_zero]
    omega

lemma startCycle_cycleIndex (p : Params) (c : Config) (s : State p) :
    (startCycle p c s).cycleIndex = s.cycleIndex := by
  unfold startCycle
  split <;> rfl

lemma startCycle_detectorPartial (p : Params) (c : Config) (s : State p) :
    detectorPartial p c (startCycle p c s).phase = 0 := by
  unfold startCycle
  split <;> rfl

lemma update_detectorProgress (p : Params) (c : Config) (s : State p)
    (a : Aux p c) (reply : Space p) (hv : PhaseValid p c s.phase) :
    detectorProgress p c (update p c s a reply) =
      detectorProgress p c s + detectorCharge p s.phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split
    · simp [hp, detectorProgress, detectorPartial, detectorCharge]
    · rw [resume_detectorProgress]
      simp [hp, detectorProgress, detectorPartial, detectorCharge]
  | transport v i z r =>
    simp only [update, hp]
    rw [transportReply_detectorProgress]
    simp [hp, detectorProgress, detectorPartial, detectorCharge]
  | probeInit trial accepted =>
    simp only [update, hp]
    rw [probeReply_detectorProgress p c s trial accepted _ reply (by
      simp [LongTails.Algorithms.HeavyTailedEnergyProbe.initialState])]
    simp [hp, detectorProgress, detectorPartial, detectorCharge,
      LongTails.Algorithms.HeavyTailedEnergyProbe.initialState]
  | probe trial accepted probe =>
    have hi : probe.index < max 1 c.probeSteps := (show
      trial < max 1 c.repeats ∧ probe.index < max 1 c.probeSteps from by simpa [PhaseValid, hp] using hv).2
    simp only [update, hp]
    rw [probeReply_detectorProgress p c s trial accepted probe reply hi]
    simp [hp, detectorProgress, detectorPartial, detectorCharge, Nat.add_assoc]
  | validate trial accepted v values =>
    have hv' : trial < max 1 c.repeats ∧ values.length < max 1 c.meanBatch * max 1 c.groups := by
      simpa [PhaseValid, hp] using hv
    simp only [update, hp]
    split_ifs with hvalues haccept htrial
    all_goals try simp only [List.length_cons] at hvalues
    all_goals try simp [hp, detectorProgress, detectorPartial, detectorCharge, Nat.add_assoc]
    all_goals try split
    all_goals try simp only [resumeDetector]
    all_goals
      have hlen : values.length + 1 = max 1 c.meanBatch * max 1 c.groups := by omega
      first
      | (simp only [Nat.add_mul, Nat.one_mul, trialCalls]; omega)
      | (have ht : trial + 1 = max 1 c.repeats := by omega
         have hb : trial * trialCalls c + max 1 c.probeSteps + values.length + 1 = detectorCalls c := by
           rw [detectorCalls, ← ht, Nat.add_mul, Nat.one_mul]
           dsimp only [trialCalls]
           omega
         try simp only [startCycle_cycleIndex, Nat.add_mul, Nat.one_mul]
         first
         | omega
         | (have hz := startCycle_detectorPartial p c { s with cycleIndex := s.cycleIndex + 1 }
            simp only [hp, detectorPartial, resumeDetector, Nat.add_assoc] at hz
            omega))
  | ncInit v =>
    simp only [update, hp]
    rw [transportReply_detectorProgress]
    simp [hp, detectorProgress, detectorPartial, detectorCharge, resumeDetector]
  | done => simp [update, hp, detectorCharge]

lemma trajectory_detectorProgress (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : PhaseValid p c s.phase) (N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    detectorProgress p c (trajectory (sampleStep p c g H) N s ξ) = detectorProgress p c s +
      ∑ k ∈ Finset.range N, detectorCharge p (trajectory (sampleStep p c g H) k s ξ).phase := by
  induction N with
  | zero => simp [trajectory]
  | succ N ih =>
    rw [trajectory_succ_last, sampleStep]
    rw [update_detectorProgress p c _ _ _ (trajectory_valid p c g H s hs N ξ), ih]
    rw [Finset.sum_range_succ, Nat.add_assoc]

lemma completed_detector_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range N, detectorCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) =
      c.cycles * detectorCalls c := by
  have ht := trajectory_detectorProgress p c g H (initial p target) (initial_valid p c target) N ξ
  rw [detectorProgress, hdone, completed_cycleIndex p c g H target N ξ hdone] at ht
  simpa [detectorProgress, detectorPartial, resumeDetector, initial] using ht.symm

def activeCharge (p : Params) : Phase p → ℕ
  | .done => 0
  | _ => 1

lemma activeCharge_partition (p : Params) (phase : Phase p) :
    activeCharge p phase = resetCharge p phase + transportCharge p phase + detectorCharge p phase := by
  cases phase <;> rfl

noncomputable def unpaddedWork (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) : ℕ :=
  ∑ k ∈ Finset.range N, activeCharge p
    (trajectory (sampleStep p c g H) k (initial p target) ξ).phase

lemma completed_unpaddedWork (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let V := (trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex
    unpaddedWork p c g H target N ξ =
      max 1 c.resetBatch * (V / max 1 c.epoch + 1) + V * max 1 c.transportBatch +
        c.cycles * detectorCalls c := by
  intro V
  simp only [unpaddedWork, activeCharge_partition, Finset.sum_add_distrib]
  rw [completed_reset_count p c g H target N ξ hdone,
    completed_transport_count p c g H target N ξ hdone,
    completed_detector_count p c g H target N ξ hdone]

lemma completion_of_work_le (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N C : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done)
    (hwork : unpaddedWork p c g H target N ξ ≤ C) :
    (trajectory (sampleStep p c g H) C (initial p target) ξ).phase = .done := by
  let X := fun k => trajectory (sampleStep p c g H) k (initial p target) ξ
  have habs (k l : ℕ) (hkl : k ≤ l) (hk : (X k).phase = .done) : X l = X k := by
    have he := completion_absorbing p c g H (initial p target) ξ k (l - k) hk
    simpa only [Nat.add_sub_of_le hkl] using he
  by_contra hC
  have hCN : C < N := by
    by_contra hn
    have hnC : N ≤ C := by omega
    have he := habs N C hnC hdone
    exact hC (by simpa only [X, he] using hdone)
  have hcharge (k : ℕ) (hk : k ∈ Finset.range (C + 1)) : activeCharge p (X k).phase = 1 := by
    have hkC : k ≤ C := by simp only [Finset.mem_range] at hk; omega
    cases hp : (X k).phase <;> try rfl
    exact (hC (by rw [show trajectory (sampleStep p c g H) C (initial p target) ξ = X k from habs k C hkC hp]; exact hp)).elim
  have hprefix : (∑ k ∈ Finset.range (C + 1), activeCharge p (X k).phase) = C + 1 := by
    simp only [Finset.sum_congr rfl hcharge, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hle : (∑ k ∈ Finset.range (C + 1), activeCharge p (X k).phase) ≤
      ∑ k ∈ Finset.range N, activeCharge p (X k).phase :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; omega)
  change (∑ k ∈ Finset.range N, activeCharge p (X k).phase) ≤ C at hwork
  omega

lemma capped_state_eq_completed (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N C : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done)
    (hwork : unpaddedWork p c g H target N ξ ≤ C) :
    trajectory (sampleStep p c g H) C (initial p target) ξ =
      trajectory (sampleStep p c g H) N (initial p target) ξ := by
  have hC := completion_of_work_le p c g H target N C ξ hdone hwork
  by_cases hNC : N ≤ C
  · simpa only [Nat.add_sub_of_le hNC] using
      completion_absorbing p c g H (initial p target) ξ N (C - N) hdone
  · have hCN : C ≤ N := by omega
    symm
    simpa only [Nat.add_sub_of_le hCN] using
      completion_absorbing p c g H (initial p target) ξ C (N - C) hC

def resumeStarted (p : Params) : Resume p → ℕ
  | .ncRest .. => 1
  | _ => 0

def detectorStarted (p : Params) : Phase p → ℕ
  | .reset _ _ r => resumeStarted p r
  | .transport _ _ _ r => resumeStarted p r
  | .probeInit .. | .probe .. | .validate .. | .ncInit .. => 1
  | .done => 0

def detectorStart (p : Params) : Phase p → ℕ
  | .probeInit 0 none => 1
  | _ => 0

def detectorCycleProgress (p : Params) (s : State p) : ℕ :=
  s.cycleIndex + detectorStarted p s.phase

lemma startCycle_detectorCycleProgress (p : Params) (c : Config) (s : State p) :
    detectorCycleProgress p (startCycle p c s) = s.cycleIndex := by
  unfold startCycle
  split <;> simp [detectorCycleProgress, detectorStarted, resumeStarted]

lemma startCycle_detectorStart (p : Params) (c : Config) (s : State p) :
    detectorStart p (startCycle p c s).phase = 0 := by
  unfold startCycle
  split <;> rfl

lemma resume_detectorCycleProgress (p : Params) (c : Config) (s : State p) (r : Resume p) :
    detectorCycleProgress p (resume p c s r) = s.cycleIndex + resumeStarted p r +
      detectorStart p (resume p c s r).phase := by
  cases r with
  | startCycle => simp [resume, startCycle_detectorCycleProgress, startCycle_detectorStart, resumeStarted]
  | detect => rfl
  | ncRest n v =>
    simp only [resume]
    split
    · simp [startCycle_detectorCycleProgress, startCycle_detectorStart, resumeStarted]
    · simp [detectorCycleProgress, detectorStarted, detectorStart, resumeStarted]

lemma completeTransport_detectorCycleProgress (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    detectorCycleProgress p (completeTransport p c s v z r) = s.cycleIndex + resumeStarted p r +
      detectorStart p (completeTransport p c s v z r).phase := by
  unfold completeTransport
  dsimp only
  split
  · simp [detectorCycleProgress, detectorStarted, detectorStart]
  · exact resume_detectorCycleProgress p c _ r

lemma transportReply_detectorCycleProgress (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    detectorCycleProgress p (transportReply p c s v i z reply r) = s.cycleIndex + resumeStarted p r +
      detectorStart p (transportReply p c s v i z reply r).phase := by
  unfold transportReply
  split
  · simp [detectorCycleProgress, detectorStarted, detectorStart]
  · exact completeTransport_detectorCycleProgress p c s v (z + reply) r

lemma probeReply_detectorCycleProgress (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    detectorCycleProgress p (probeReply p c s trial accepted probe reply) = s.cycleIndex + 1 +
      detectorStart p (probeReply p c s trial accepted probe reply).phase := by
  unfold probeReply
  dsimp only
  split <;> simp [detectorCycleProgress, detectorStarted, detectorStart]

lemma update_detectorCycleProgress (p : Params) (c : Config) (s : State p)
    (a : Aux p c) (reply : Space p) :
    detectorCycleProgress p (update p c s a reply) = detectorCycleProgress p s +
      detectorStart p (update p c s a reply).phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split
    · simp [detectorCycleProgress, hp, detectorStarted, detectorStart]
    · rw [resume_detectorCycleProgress]
      simp [detectorCycleProgress, hp, detectorStarted]
  | transport v i z r =>
    simp only [update, hp, transportReply_detectorCycleProgress]
    simp [detectorCycleProgress, hp, detectorStarted]
  | probeInit trial accepted =>
    simp only [update, hp, probeReply_detectorCycleProgress]
    simp [detectorCycleProgress, hp, detectorStarted]
  | probe trial accepted probe =>
    simp only [update, hp, probeReply_detectorCycleProgress]
    simp [detectorCycleProgress, hp, detectorStarted]
  | validate trial accepted v values =>
    simp only [update, hp]
    split
    · simp [detectorCycleProgress, hp, detectorStarted, detectorStart]
    · split
      · simp [detectorCycleProgress, hp, detectorStarted, detectorStart]
      · split
        · rw [startCycle_detectorCycleProgress, startCycle_detectorStart]
          simp [detectorCycleProgress, hp, detectorStarted]
        · simp [detectorCycleProgress, hp, detectorStarted, detectorStart]
  | ncInit v =>
    simp only [update, hp, transportReply_detectorCycleProgress]
    simp [detectorCycleProgress, hp, detectorStarted, resumeStarted]
  | done => simp [update, hp, detectorStart]

lemma trajectory_detectorCycleProgress (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    detectorCycleProgress p (trajectory (sampleStep p c g H) N s ξ) =
      detectorCycleProgress p s + ∑ k ∈ Finset.range N, detectorStart p
        (trajectory (sampleStep p c g H) (k + 1) s ξ).phase := by
  induction N with
  | zero => simp [trajectory]
  | succ N ih =>
    conv_lhs => rw [trajectory_succ_last, sampleStep, update_detectorCycleProgress]
    rw [ih, Finset.sum_range_succ]
    rw [trajectory_succ_last, sampleStep]
    omega

lemma completed_detector_start_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range N, detectorStart p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) = c.cycles := by
  let a := fun k => detectorStart p (trajectory (sampleStep p c g H) k (initial p target) ξ).phase
  have hshift : (∑ k ∈ Finset.range N, a (k + 1)) + a 0 =
      (∑ k ∈ Finset.range N, a k) + a N := by
    clear hdone
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega
  have h0 : a 0 = 0 := by simp [a, trajectory, initial, detectorStart]
  have hn : a N = 0 := by simp [a, hdone, detectorStart]
  have hc := completed_cycleIndex p c g H target N ξ hdone
  have ht := trajectory_detectorCycleProgress p c g H (initial p target) N ξ
  rw [detectorCycleProgress, hdone, detectorStarted, hc] at ht
  simp only [detectorCycleProgress, initial, detectorStarted, resumeStarted, Nat.add_zero, Nat.zero_add] at ht
  change c.cycles = ∑ k ∈ Finset.range N, a (k + 1) at ht
  change (∑ k ∈ Finset.range N, a k) = c.cycles
  omega

def IsDetector (p : Params) : Phase p → Prop
  | .probeInit .. | .probe .. | .validate .. | .ncInit .. => True
  | _ => False

lemma startCycle_not_detector (p : Params) (c : Config) (s : State p) :
    ¬IsDetector p (startCycle p c s).phase := by
  unfold startCycle
  split <;> simp [IsDetector]

lemma resume_detector_start (p : Params) (c : Config) (s : State p) (r : Resume p)
    (hd : IsDetector p (resume p c s r).phase) :
    (resume p c s r).phase = .probeInit 0 none := by
  cases r with
  | startCycle => exact False.elim (startCycle_not_detector p c s hd)
  | detect => rfl
  | ncRest n v =>
    simp only [resume] at hd ⊢
    split at hd
    · exact False.elim (startCycle_not_detector p c _ hd)
    · exact False.elim hd

lemma completeTransport_detector_start (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p)
    (hd : IsDetector p (completeTransport p c s v z r).phase) :
    (completeTransport p c s v z r).phase = .probeInit 0 none := by
  unfold completeTransport at hd ⊢
  dsimp only at hd ⊢
  split at hd
  · exact False.elim hd
  · rename_i h
    simpa only [h, ↓reduceIte] using resume_detector_start p c _ r hd

lemma transportReply_detector_start (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hd : IsDetector p (transportReply p c s v i z reply r).phase) :
    (transportReply p c s v i z reply r).phase = .probeInit 0 none := by
  unfold transportReply at hd ⊢
  split at hd
  · exact False.elim hd
  · rename_i h
    simpa only [h, ↓reduceIte] using completeTransport_detector_start p c s v (z + reply) r hd

lemma probeReply_point_cycle (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    (probeReply p c s trial accepted probe reply).point = s.point ∧
      (probeReply p c s trial accepted probe reply).cycleIndex = s.cycleIndex := by
  unfold probeReply
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

lemma update_detector_shape (p : Params) (c : Config) (s : State p)
    (a : Aux p c) (reply : Space p) (hd : IsDetector p (update p c s a reply).phase) :
    (update p c s a reply).phase = .probeInit 0 none ∨
      (detectorCharge p s.phase = 1 ∧ (update p c s a reply).point = s.point ∧
        (update p c s a reply).cycleIndex = s.cycleIndex) := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp] at hd ⊢
    split at hd
    · exact False.elim hd
    · rename_i h
      exact Or.inl (by simpa only [h, ↓reduceIte] using resume_detector_start p c _ r hd)
  | transport v i z r =>
    simp only [update, hp] at hd ⊢
    exact Or.inl (transportReply_detector_start p c s v i z reply r hd)
  | probeInit trial accepted =>
    right
    simp only [update, hp, detectorCharge, true_and]
    exact probeReply_point_cycle p c s trial accepted _ reply
  | probe trial accepted probe =>
    right
    simp only [update, hp, detectorCharge, true_and]
    exact probeReply_point_cycle p c s trial accepted probe reply
  | validate trial accepted v values =>
    simp only [update, hp] at hd ⊢
    split
    · exact Or.inr ⟨rfl, rfl, rfl⟩
    · split
      · exact Or.inr ⟨rfl, rfl, rfl⟩
      · split
        · exfalso
          apply startCycle_not_detector p c _
          simpa only [*, ↓reduceIte] using hd
        · exact Or.inr ⟨rfl, rfl, rfl⟩
  | ncInit v =>
    simp only [update, hp] at hd ⊢
    exact Or.inl (transportReply_detector_start p c s _ 0 0 reply _ hd)
  | done => simp [update, hp, IsDetector] at hd

lemma detectorCharge_isDetector (p : Params) (phase : Phase p)
    (h : detectorCharge p phase = 1) : IsDetector p phase := by
  cases phase <;> simp_all [detectorCharge, IsDetector]

lemma trajectory_detector_origin (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hd : IsDetector p (trajectory (sampleStep p c g H) n (initial p target) ξ).phase) :
    ∃ k ≤ n, n = k + detectorPartial p c
        (trajectory (sampleStep p c g H) n (initial p target) ξ).phase ∧
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = .probeInit 0 none ∧
      (trajectory (sampleStep p c g H) k (initial p target) ξ).point =
        (trajectory (sampleStep p c g H) n (initial p target) ξ).point := by
  induction n with
  | zero => simp [trajectory, initial, IsDetector] at hd
  | succ n ih =>
    let X := fun k => trajectory (sampleStep p c g H) k (initial p target) ξ
    let reply := match (query p c (X n) (ξ n).1).2 with
      | none => g (query p c (X n) (ξ n).1).1 (ξ n).2
      | some v => H (query p c (X n) (ξ n).1).1 (ξ n).2 v
    have hstep : X (n + 1) = update p c (X n) (ξ n).1 reply := by
      change trajectory (sampleStep p c g H) (n + 1) (initial p target) ξ = _
      rw [trajectory_succ_last]
      rfl
    have hs := update_detector_shape p c (X n) (ξ n).1 reply (by rw [← hstep]; exact hd)
    rw [← hstep] at hs
    change ∃ k ≤ n + 1, n + 1 = k + detectorPartial p c (X (n + 1)).phase ∧
      (X k).phase = .probeInit 0 none ∧ (X k).point = (X (n + 1)).point
    rcases hs with hs | ⟨hcharge, hpoint, hcycle⟩
    · refine ⟨n + 1, le_refl _, ?_, hs, rfl⟩
      simp only [hs, detectorPartial, Nat.zero_mul, Nat.add_zero]
    · have hold : IsDetector p (X n).phase := detectorCharge_isDetector p _ hcharge
      obtain ⟨k, hk, hlen, hstart, hsame⟩ := ih hold
      have hv : PhaseValid p c (X n).phase := trajectory_valid p c g H (initial p target)
        (by simp [initial, PhaseValid, ResumeValid]) n ξ
      have hprog := update_detectorProgress p c (X n) (ξ n).1 reply hv
      rw [← hstep] at hprog
      dsimp only [detectorProgress] at hprog
      rw [hcycle, hcharge] at hprog
      have hpartial : detectorPartial p c (X (n + 1)).phase = detectorPartial p c (X n).phase + 1 := by omega
      refine ⟨k, by omega, ?_, hstart, ?_⟩
      · change n = k + detectorPartial p c (X n).phase at hlen
        omega
      · exact hsame.trans hpoint.symm

lemma ncInit_detector_origin (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω) (v : Space p)
    (hnc : (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = .ncInit v) :
    detectorCalls c ≤ n ∧
      (trajectory (sampleStep p c g H) (n - detectorCalls c) (initial p target) ξ).phase = .probeInit 0 none ∧
      (trajectory (sampleStep p c g H) (n - detectorCalls c) (initial p target) ξ).point =
        (trajectory (sampleStep p c g H) n (initial p target) ξ).point := by
  obtain ⟨k, hk, hlen, hstart, hpoint⟩ := trajectory_detector_origin p c g H target n ξ
    (by simp [hnc, IsDetector])
  simp only [hnc, detectorPartial] at hlen
  have heq : k = n - detectorCalls c := by omega
  subst k
  exact ⟨by omega, hstart, hpoint⟩

end LongTails.Proofs.HeavyTailedSospWork
