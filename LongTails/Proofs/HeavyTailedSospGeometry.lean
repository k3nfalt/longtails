import LongTails.Proofs.HeavyTailedSospInvariants
import LongTails.Proofs.HeavyTailedProbeGeometry

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp

namespace LongTails.Proofs.HeavyTailedSospGeometry

def AcceptedUnit (p : Params) (a : Option (Space p)) : Prop := ∀ v, a = some v → ‖v‖ = 1

def ProbeUnit (p : Params) (s : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) : Prop :=
  ‖s.fallback‖ = 1 ∧ ‖s.vector‖ = 1 ∧ ‖s.selected‖ = 1

def ResumeBound (p : Params) (h : ℝ) : Resume p → Prop
  | .ncRest _ v => ‖v‖ ≤ h
  | _ => True

def PhaseBound (p : Params) (h : ℝ) : Phase p → Prop
  | .reset _ _ r => ResumeBound p h r
  | .transport v _ _ r => ‖v‖ ≤ h ∧ ResumeBound p h r
  | .probeInit _ a => AcceptedUnit p a
  | .probe _ a s => AcceptedUnit p a ∧ ProbeUnit p s
  | .validate _ a v _ => AcceptedUnit p a ∧ ‖v‖ = 1
  | .ncInit v => ‖v‖ = 1
  | .done => True

lemma normalized_gradient_segment (p : Params) (h : ℝ) (hh : 0 ≤ h) (v : Space p) :
    ‖-(h • (‖v‖⁻¹ • v))‖ ≤ h := by
  by_cases hv : v = 0
  · simp [hv, hh]
  · simp [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma signedSegment_bound (p : Params) (c : Config) (a : Aux p c) (v : Space p)
    (hs : 0 ≤ c.s) (hv : ‖v‖ = 1) :
    ‖signedSegment p c a v‖ = c.s / (max 1 c.ncSegments : ℕ) := by
  unfold signedSegment
  rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_div, abs_mul]
  have hm : (0 : ℝ) ≤ (max 1 c.ncSegments : ℕ) := by positivity
  simp only [abs_of_nonneg hs, abs_of_nonneg hm]
  cases a.2.1 <;> simp

lemma initial_probe_unit (p : Params) (hd : 0 < p.d) (signs : Fin p.d → Bool) (target : ℕ) :
    ProbeUnit p (LongTails.Algorithms.HeavyTailedEnergyProbe.initialState signs target) := by
  have hn := LongTails.Proofs.HeavyTailedProbeGeometry.initialVector_norm hd signs
  exact ⟨hn, hn, hn⟩

lemma probe_step_unit (p : Params) (shift η : ℝ)
    (s : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) (hs : ProbeUnit p s) :
    ProbeUnit p (LongTails.Algorithms.HeavyTailedEnergyProbe.step shift η s reply) := by
  exact ⟨hs.1, LongTails.Proofs.HeavyTailedProbeGeometry.step_vector_norm shift η s hs.1 reply,
    LongTails.Proofs.HeavyTailedProbeGeometry.step_selected_norm shift η s hs.2.1 hs.2.2 reply⟩

lemma accepted_or_unit (p : Params) (a : Option (Space p)) (v : Space p)
    (ha : AcceptedUnit p a) (hv : ‖v‖ = 1) : AcceptedUnit p (a.or (some v)) := by
  cases a with
  | none => intro w hw; cases hw; exact hv
  | some u => intro w hw; exact ha w hw

lemma startCycle_bound (p : Params) (c : Config) (s : State p) (hh : 0 ≤ c.h) :
    PhaseBound p c.h (startCycle p c s).phase := by
  unfold startCycle
  split_ifs
  all_goals first | exact ⟨normalized_gradient_segment p c.h hh s.estimate, trivial⟩ | trivial

lemma resume_bound (p : Params) (c : Config) (s : State p) (r : Resume p)
    (hh : 0 ≤ c.h) (hr : ResumeBound p c.h r) : PhaseBound p c.h (resume p c s r).phase := by
  cases r with
  | startCycle => exact startCycle_bound p c s hh
  | detect => intro v hv; cases hv
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_bound p c _ hh
    · exact ⟨hr, hr⟩

lemma completeTransport_bound (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) (hh : 0 ≤ c.h) (hr : ResumeBound p c.h r) :
    PhaseBound p c.h (completeTransport p c s v z r).phase := by
  unfold completeTransport
  dsimp only
  split_ifs
  · exact hr
  · exact resume_bound p c _ r hh hr

lemma transportReply_bound (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hh : 0 ≤ c.h) (hv : ‖v‖ ≤ c.h) (hr : ResumeBound p c.h r) :
    PhaseBound p c.h (transportReply p c s v i z reply r).phase := by
  unfold transportReply
  split_ifs
  · exact ⟨hv, hr⟩
  · exact completeTransport_bound p c s v (z + reply) r hh hr

lemma probeReply_bound (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p)
    (ha : AcceptedUnit p accepted) (hv : ProbeUnit p probe) :
    PhaseBound p c.h (probeReply p c s trial accepted probe reply).phase := by
  have hn := probe_step_unit p c.shift c.η probe reply hv
  unfold probeReply
  dsimp only
  split_ifs
  · exact ⟨ha, hn⟩
  · exact ⟨ha, hn.2.2⟩

lemma update_bound (p : Params) (c : Config) (s : State p) (a : Aux p c) (reply : Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hv : PhaseBound p c.h s.phase) :
    PhaseBound p c.h (update p c s a reply).phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    split_ifs
    · exact hv
    · exact resume_bound p c _ r hh hv
  | transport v i z r =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    exact transportReply_bound p c s v i z reply r hh hv.1 hv.2
  | probeInit trial accepted =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    exact probeReply_bound p c s trial accepted _ reply hv (initial_probe_unit p hd _ _)
  | probe trial accepted probe =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    exact probeReply_bound p c s trial accepted probe reply hv.1 hv.2
  | validate trial accepted v values =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    split
    · exact hv
    · let accepted' := if LongTails.Algorithms.HeavyTailedRayleighMedian.output
          (max 1 c.meanBatch) (max 1 c.groups) (inner ℝ v reply :: values).reverse ≤ -2 * c.γ then
          accepted.or (some v) else accepted
      simp only [← hp]
      change PhaseBound p c.h (if trial + 1 < max 1 c.repeats then
        { s with phase := .probeInit (trial + 1) accepted' } else match accepted' with
          | none => startCycle p c { s with cycleIndex := s.cycleIndex + 1 }
          | some u => { s with phase := .ncInit u }).phase
      have ha : AcceptedUnit p accepted' := by
        dsimp only [accepted']
        split_ifs
        · exact accepted_or_unit p accepted v hv.1 hv.2
        · exact hv.1
      split
      · exact ha
      · cases hu : accepted' with
        | none => exact startCycle_bound p c _ hh
        | some u => exact ha u hu
  | ncInit v =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    have hn : ‖signedSegment p c a v‖ ≤ c.h := (signedSegment_bound p c a v hs hv).trans_le hseg
    exact transportReply_bound p c s _ 0 0 reply _ hh hn hn
  | done => simp [update, hp, PhaseBound]

lemma initial_bound (p : Params) (c : Config) (target : ℕ) :
    PhaseBound p c.h (initial p target).phase := trivial

lemma trajectory_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (s : State p) (hv : PhaseBound p c.h s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    PhaseBound p c.h (LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ).phase := by
  induction n generalizing s ξ with
  | zero => exact hv
  | succ n ih =>
    apply ih
    exact update_bound p c s (ξ 0).1 _ hd hh hs hseg hv

@[simp] lemma startCycle_point (p : Params) (c : Config) (s : State p) :
    (startCycle p c s).point = s.point := by
  unfold startCycle
  split_ifs <;> rfl

lemma resume_point (p : Params) (c : Config) (s : State p) (r : Resume p) :
    (resume p c s r).point = s.point := by
  cases r with
  | startCycle => exact startCycle_point p c s
  | detect => rfl
  | ncRest n v => simp only [resume]; split_ifs <;> simp

@[simp] lemma completeTransport_point (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    (completeTransport p c s v z r).point = s.point + v := by
  unfold completeTransport
  dsimp only
  split_ifs <;> simp [resume_point]

lemma transportReply_point (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    (transportReply p c s v i z reply r).point - s.point =
      if i + 1 < max 1 c.transportBatch then 0 else v := by
  unfold transportReply
  split_ifs <;> simp

@[simp] lemma probeReply_point (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    (probeReply p c s trial accepted probe reply).point = s.point := by
  unfold probeReply
  dsimp only
  split_ifs <;> rfl

lemma transportReply_displacement (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) (hh : 0 ≤ c.h) (hv : ‖v‖ ≤ c.h) :
    ‖(transportReply p c s v i z reply r).point - s.point‖ ≤ c.h := by
  rw [transportReply_point]
  split_ifs
  · simpa using hh
  · exact hv

lemma update_displacement (p : Params) (c : Config) (s : State p) (a : Aux p c) (reply : Space p)
    (hh : 0 ≤ c.h) (hs : 0 ≤ c.s) (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (hv : PhaseBound p c.h s.phase) : ‖(update p c s a reply).point - s.point‖ ≤ c.h := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split_ifs <;> simpa [resume_point] using hh
  | transport v i z r =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    exact transportReply_displacement p c s v i z reply r hh hv.1
  | probeInit trial accepted => simp [update, hp, hh]
  | probe trial accepted probe => simp [update, hp, hh]
  | validate trial accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals try simpa using hh
    all_goals split <;> simpa using hh
  | ncInit v =>
    simp only [hp, PhaseBound] at hv
    simp only [update, hp]
    exact transportReply_displacement p c s _ 0 0 reply _ hh
      ((signedSegment_bound p c a v hs hv).trans_le hseg)
  | done => simp [update, hp, hh]

lemma trajectory_displacement (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (s : State p) (hv : PhaseBound p c.h s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    ‖(LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ).point - s.point‖ ≤ n * c.h := by
  induction n with
  | zero => simp [LongTails.Proofs.HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    let sn := LongTails.Proofs.HeavyTailedProductProcess.trajectory
      (LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H) n s ξ
    have hn := trajectory_bound p c g H hd hh hs hseg s hv n ξ
    have hm : ‖(LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H sn (ξ n)).point - sn.point‖ ≤ c.h :=
      update_displacement p c sn (ξ n).1 _ hh hs hseg hn
    rw [LongTails.Proofs.HeavyTailedProductProcess.trajectory_succ_last]
    calc
      _ ≤ ‖(LongTails.Proofs.HeavyTailedSospExecution.sampleStep p c g H sn (ξ n)).point - sn.point‖ +
          ‖sn.point - s.point‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ c.h + n * c.h := add_le_add hm ih
      _ = (n + 1 : ℕ) * c.h := by push_cast; ring

end LongTails.Proofs.HeavyTailedSospGeometry
