import LongTails.Algorithms.HeavyTailedSosp
import LongTails.Proofs.HeavyTailedTapeExecution

open MeasureTheory
open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp

namespace LongTails.Proofs.HeavyTailedSospExecution

noncomputable def sampleStep (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (state : State p) (z : Aux p c × p.Ω) : State p :=
  let q := query p c state z.1
  update p c state z.1 (match q.2 with | none => g q.1 z.2 | some v => H q.1 z.2 v)

lemma execute_sosp (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (P : ProbabilityMeasure (ℕ → p.Ω))
    (seed : Fin (max 1 c.cycles) × (ℕ → Aux p c)) (ξ : ℕ → p.Ω) (K : ℕ) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, x, v) ω => match v with | none => g x ω | some w => H x ω w }
    OracleTemplate.execute O (algorithm p c) (fun _ => K) seed ξ =
      (HeavyTailedProductProcess.trajectory (sampleStep p c g H) K
        (initial p seed.1.val) (fun k => (seed.2 k, ξ k))).selected := by
  intro O
  let : NeZero (max 1 c.cycles) := ⟨by omega⟩
  exact HeavyTailedTapeExecution.execute_fresh_tape
    ⟨(PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure, inferInstance⟩
    (auxLaw p c) P (fun target => initial p target.val) (query p c) (update p c)
    (fun state => state.selected)
    (fun q ω => match q.2 with | none => g q.1 ω | some v => H q.1 ω v) seed ξ K

lemma done_step (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (state : State p) (hdone : state.phase = .done) (z : Aux p c × p.Ω) :
    sampleStep p c g H state z = state := by
  simp [sampleStep, update, hdone]

lemma done_trajectory (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (state : State p) (hdone : state.phase = .done) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    HeavyTailedProductProcess.trajectory (sampleStep p c g H) n state ξ = state := by
  induction n generalizing ξ with
  | zero => rfl
  | succ n ih => rw [HeavyTailedProductProcess.trajectory, done_step p c g H state hdone, ih]

lemma completion_absorbing (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (state : State p) (ξ : ℕ → Aux p c × p.Ω) (k n : ℕ)
    (hdone : (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k state ξ).phase = .done) :
    HeavyTailedProductProcess.trajectory (sampleStep p c g H) (k + n) state ξ =
      HeavyTailedProductProcess.trajectory (sampleStep p c g H) k state ξ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, HeavyTailedProductProcess.trajectory_succ_last, ih]
    exact done_step p c g H _ hdone _

end LongTails.Proofs.HeavyTailedSospExecution
