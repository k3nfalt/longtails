import LongTails.Proofs.HeavyTailedSospEpoch
import LongTails.Proofs.HeavyTailedSospReset

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Proofs.HeavyTailedSospExecution
open LongTails.Proofs.HeavyTailedProductProcess

namespace LongTails.Proofs.HeavyTailedSospEstimator

noncomputable def partialError (p : Params) (c : Config) (G : Space p → Space p)
    (x : Space p) : Phase p → Space p
  | .transport v i z _ => ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ •
      (z - (i : ℝ) • (G (x + v) - G x))
  | _ => 0

noncomputable def error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) : Space p :=
  state.estimate - G state.point + partialError p c G state.point state.phase

noncomputable def noise (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (a : Aux p c) (reply : Space p) : Space p :=
  match state.phase with
  | .transport v .. => ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ •
      (reply - (G (state.point + v) - G state.point))
  | .ncInit v => ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ •
      (reply - (G (state.point + signedSegment p c a v) - G state.point))
  | _ => 0

lemma partialError_zero_index (p : Params) (c : Config) (G : Space p → Space p)
    (x v : Space p) (r : Resume p) :
    partialError p c G x (.transport v 0 0 r) = 0 := by
  simp [partialError]

lemma startCycle_partialError (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) :
    partialError p c G (startCycle p c state).point (startCycle p c state).phase = 0 := by
  unfold startCycle
  split_ifs <;> simp [partialError]

lemma resume_partialError (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (r : Resume p) :
    partialError p c G (resume p c state r).point (resume p c state r).phase = 0 := by
  cases r with
  | startCycle => exact startCycle_partialError p c G state
  | detect => simp [resume, partialError]
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_partialError p c G _
    · simp [partialError]

lemma resume_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (r : Resume p) :
    error p c G (resume p c state r) = state.estimate - G state.point := by
  rw [error, resume_partialError, add_zero,
    HeavyTailedSospReset.resume_estimate, HeavyTailedSospReset.resume_point]

lemma reset_error_identity (p : Params) (c : Config) (G : Space p → Space p)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (r : Resume p) (ξ : ℕ → Aux p c × p.Ω) :
    error p c G (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 r } ξ) =
      ((max 1 c.resetBatch : ℕ) : ℝ)⁻¹ •
        (∑ k ∈ Finset.range (max 1 c.resetBatch), g s.point (ξ k).2) - G s.point := by
  rw [HeavyTailedSospReset.reset_complete, resume_error]

lemma partial_increment (p : Params) (b : ℝ) (i : ℕ) (z reply δ : Space p) :
    b • (z + reply - ((i + 1 : ℕ) : ℝ) • δ) =
      b • (z - (i : ℝ) • δ) + b • (reply - δ) := by
  rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  rw [← smul_add]
  congr 1
  abel

lemma completeTransport_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (v z : Space p) (r : Resume p) :
    error p c G (completeTransport p c state v z r) =
      state.estimate + ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ • z - G (state.point + v) := by
  unfold completeTransport
  dsimp only
  split_ifs
  · simp [error, partialError]
  · rw [error, resume_partialError, add_zero,
      LongTails.Proofs.HeavyTailedSospReset.resume_estimate]
    have hpoint (s : State p) : (resume p c s r).point = s.point := by
      cases r <;> simp only [resume, startCycle]
      all_goals split_ifs <;> rfl
    rw [hpoint]

lemma startCycle_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) :
    error p c G (startCycle p c state) = state.estimate - G state.point := by
  unfold startCycle
  split_ifs <;> simp [error, partialError]

lemma probeReply_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    error p c G (probeReply p c state trial accepted probe reply) =
      state.estimate - G state.point := by
  unfold probeReply
  dsimp only
  split_ifs <;> simp [error, partialError]

lemma transportReply_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hi : i < max 1 c.transportBatch) :
    error p c G (transportReply p c state v i z reply r) =
      state.estimate - G state.point + partialError p c G state.point (.transport v i z r) +
        ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ • (reply - (G (state.point + v) - G state.point)) := by
  unfold transportReply
  split_ifs with h
  · simp only [error, partialError]
    rw [partial_increment]
    abel
  · rw [completeTransport_error]
    have he : i + 1 = max 1 c.transportBatch := by omega
    have hb : ((max 1 c.transportBatch : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [partialError]
    symm
    calc
      _ = state.estimate - G state.point + ((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ •
          (z + reply - ((i + 1 : ℕ) : ℝ) • (G (state.point + v) - G state.point)) := by
        rw [partial_increment]
        abel
      _ = _ := by
        rw [he, smul_sub, smul_smul, inv_mul_cancel₀ hb, one_smul]
        abel

lemma update_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (a : Aux p c) (reply : Space p)
    (hv : LongTails.Proofs.HeavyTailedSospInvariants.PhaseValid p c state.phase)
    (hr : ¬ LongTails.Proofs.HeavyTailedSospEpoch.IsReset p state.phase) :
    error p c G (update p c state a reply) =
      error p c G state + noise p c G state a reply := by
  cases hp : state.phase with
  | reset i z r => exact (hr (by simp [hp, HeavyTailedSospEpoch.IsReset])).elim
  | transport v i z r =>
    simp only [update, hp, noise]
    have hi : i < max 1 c.transportBatch := by
      simp only [hp, HeavyTailedSospInvariants.PhaseValid] at hv
      exact hv.1
    rw [transportReply_error p c G state v i z reply r hi]
    simp only [error, hp]
  | probeInit t accepted =>
    simp only [update, hp, noise]
    rw [probeReply_error]
    simp [error, hp, partialError]
  | probe t accepted probe =>
    simp only [update, hp, noise]
    rw [probeReply_error]
    simp [error, hp, partialError]
  | validate t accepted v values =>
    simp only [update, hp, noise]
    split_ifs
    all_goals solve
      | simp [error, hp, partialError]
      | (split
         · rw [startCycle_error]; simp [error, hp, partialError]
         · simp [error, hp, partialError])
  | ncInit v =>
    simp only [update, hp, noise]
    rw [transportReply_error p c G state _ 0 0 reply _ (by omega)]
    simp [error, hp, partialError]
  | done => simp [update, hp, noise]

def ZeroPartial (p : Params) : Phase p → Prop
  | .transport _ i z _ => i = 0 → z = 0
  | _ => True

lemma startCycle_zeroPartial (p : Params) (c : Config) (state : State p) :
    ZeroPartial p (startCycle p c state).phase := by
  unfold startCycle
  split_ifs <;> simp [ZeroPartial]

lemma resume_zeroPartial (p : Params) (c : Config) (state : State p) (r : Resume p) :
    ZeroPartial p (resume p c state r).phase := by
  cases r with
  | startCycle => exact startCycle_zeroPartial p c state
  | detect => trivial
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_zeroPartial p c _
    · simp [ZeroPartial]

lemma completeTransport_zeroPartial (p : Params) (c : Config) (state : State p)
    (v z : Space p) (r : Resume p) :
    ZeroPartial p (completeTransport p c state v z r).phase := by
  unfold completeTransport
  dsimp only
  split_ifs
  · trivial
  · exact resume_zeroPartial p c _ r

lemma transportReply_zeroPartial (p : Params) (c : Config) (state : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    ZeroPartial p (transportReply p c state v i z reply r).phase := by
  unfold transportReply
  split_ifs
  · simp [ZeroPartial]
  · exact completeTransport_zeroPartial p c state v (z + reply) r

lemma probeReply_zeroPartial (p : Params) (c : Config) (state : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    ZeroPartial p (probeReply p c state trial accepted probe reply).phase := by
  unfold probeReply
  dsimp only
  split_ifs <;> trivial

lemma update_zeroPartial (p : Params) (c : Config) (state : State p)
    (a : Aux p c) (reply : Space p) :
    ZeroPartial p (update p c state a reply).phase := by
  cases hp : state.phase <;> simp only [update, hp]
  · split_ifs
    · trivial
    · exact resume_zeroPartial p c _ _
  · exact transportReply_zeroPartial p c _ _ _ _ _ _
  · exact probeReply_zeroPartial p c _ _ _ _ _
  · exact probeReply_zeroPartial p c _ _ _ _ _
  · split_ifs
    all_goals first
      | trivial
      | (split
         · exact startCycle_zeroPartial p c _
         · trivial)
  · exact transportReply_zeroPartial p c _ _ _ _ _ _
  · trivial

lemma marked_error (p : Params) (c : Config) (G : Space p → Space p)
    (state : State p) (hz : ZeroPartial p state.phase)
    (hm : HeavyTailedSospInvariants.markCharge p state.phase = 1) :
    error p c G state = state.estimate - G state.point := by
  cases hp : state.phase with
  | transport v i z r =>
    cases r with
    | startCycle => simp [hp, HeavyTailedSospInvariants.markCharge] at hm
    | ncRest n w => simp [hp, HeavyTailedSospInvariants.markCharge] at hm
    | detect =>
      simp only [hp, HeavyTailedSospInvariants.markCharge] at hm
      split_ifs at hm with hi
      · have hzero : z = 0 := by
          simpa [hp, ZeroPartial, hi] using hz
        simp [error, hp, partialError, hi, hzero]
  | _ => simp [hp, HeavyTailedSospInvariants.markCharge] at hm

noncomputable def sampleNoise (p : Params) (c : Config) (G : Space p → Space p)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (state : State p) (z : Aux p c × p.Ω) : Space p :=
  let q := query p c state z.1
  noise p c G state z.1 (match q.2 with | none => g q.1 z.2 | some v => H q.1 z.2 v)

lemma trajectory_zeroPartial (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : ZeroPartial p s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    ZeroPartial p (trajectory (sampleStep p c g H) n s ξ).phase := by
  cases n with
  | zero => exact hs
  | succ n =>
    rw [trajectory_succ_last]
    exact update_zeroPartial p c _ _ _

lemma epoch_error_sum (p : Params) (c : Config) (G : Space p → Space p)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hv : HeavyTailedSospInvariants.PhaseValid p c s.phase)
    (ha : HeavyTailedSospEpoch.ResetAligned p c s)
    (hs : ¬ HeavyTailedSospEpoch.IsReset p s.phase)
    (hb : s.virtualIndex % max 1 c.epoch = 0)
    (n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hn : (trajectory (sampleStep p c g H) n s ξ).virtualIndex <
      s.virtualIndex + max 1 c.epoch) :
    error p c G (trajectory (sampleStep p c g H) n s ξ) = error p c G s +
      ∑ k ∈ Finset.range n, sampleNoise p c G g H
        (trajectory (sampleStep p c g H) k s ξ) (ξ k) := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory_succ_last] at hn ⊢
    have hm : (trajectory (sampleStep p c g H) n s ξ).virtualIndex ≤
        (sampleStep p c g H (trajectory (sampleStep p c g H) n s ξ) (ξ n)).virtualIndex :=
      (HeavyTailedSospInvariants.update_virtualIndex p c _ _ _).1
    have hp := lt_of_le_of_lt hm hn
    have hr := HeavyTailedSospEpoch.epoch_no_reset p c g H s ha hs hb n ξ hp
    have hvalid := HeavyTailedSospInvariants.trajectory_valid p c g H s hv n ξ
    change error p c G (update p c _ _ _) = _
    rw [update_error p c G _ _ _ hvalid hr, ih hp, Finset.sum_range_succ]
    exact add_assoc _ _ _

end LongTails.Proofs.HeavyTailedSospEstimator
