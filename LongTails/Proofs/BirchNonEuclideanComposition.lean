import LongTails.Setups.BirchNonEuclideanComposition
import LongTails.Algorithms.BirchNonEuclideanComposition
import LongTails.Proofs.BirchCausalSuccess
import LongTails.Proofs.BirchMeasurableLmoAudit
import LongTails.Proofs.ExecutionHistory

namespace LongTails.Proofs.BirchNonEuclideanComposition

open MeasureTheory
open OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchNonEuclideanComposition
open LongTails.Algorithms.BirchNonEuclideanComposition

lemma execute_calls (p : Params) (O : Oracle (Point p.d) (Point p.d)) (Q : ℕ)
    (seed : (algorithm p).Seed) (samples : (k : ℕ) → O.Seed k) :
    (executeWithTrace O (algorithm p) (fun _ => Q) seed samples).2.length = Q := by
  erw [executeWithTrace_eq_executeIndexedState]
  exact executeIndexedState_length O (algorithm p) seed samples Q

lemma native_chosenLMO_valid (p : LongTails.Setups.BirchNonEuclidean.Params)
    (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N) :
    LongTails.Setups.UscgConstant.IsBallLMO p.N 1
      (LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO p) := by
  have hh := LongTails.Proofs.BirchLmoExistence.exists_measurable_lmo p.N hdef hcont
  unfold LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO
  rw [dite_eq_left hh]
  exact Classical.choose_spec hh

lemma chosenLMO_valid (p : Params) (hp : spec.valid p) :
    LongTails.Setups.UscgConstant.IsBallLMO p.N 1
      (LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO (native p)) :=
  native_chosenLMO_valid (native p) hp.1 hp.2.1

lemma execute_success (p : Params) (hp : spec.valid p)
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d)) (hI : spec.admissible p I O) :
    let Q := ⌈(5 + 528 * p.L * p.Δ / p.ε) * p.slots * p.credits + (32 + 1920 * p.L * p.Δ / p.ε) * p.κ * p.σ ^ 2 / p.ε⌉₊
    spec.successful p I (fun z : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm p) (fun _ => Q) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hI with ⟨hf, Ω, m, horacle⟩
  let := m
  rcases horacle with ⟨μ, P, g, hiid, hg, rfl⟩
  rcases hp with ⟨hdef, hcont, hL, hσ, hε, hΔ, hw, ⟨w⟩, hm, hH, hr⟩
  obtain ⟨R, hRpos, hRbound⟩ :=
    LongTails.Proofs.BirchLmoExistence.exists_norm_le_seminorm p.N hdef hcont
  have hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R := fun v hv =>
    (hRbound v).trans (by nlinarith)
  have hp : spec.valid p := ⟨hdef, hcont, hL, hσ, hε, hΔ, hw, ⟨w⟩, hm, hH, hr⟩
  have hQ : ⌈(5 + 528 * p.L * p.Δ / p.ε) * p.slots * p.credits + (32 + 1920 * p.L * p.Δ / p.ε) * p.κ * p.σ ^ 2 / p.ε⌉₊ =
      ⌈(5 + 528 * (p.L * p.Δ / p.ε)) * ((p.slots : ℝ) * p.credits) + (32 + 1920 * (p.L * p.Δ / p.ε)) * (p.κ * p.σ ^ 2 / p.ε)⌉₊ := by
    congr 1
    ring
  dsimp only
  rw [hQ]
  exact (LongTails.Proofs.BirchCausalSuccess.constructed_execute_success
    (native p) p.credits p.word (fun K B job => p.recipe K B job.worker job.source job.serial)
    hH hm hw hL hΔ hε
    (fun K B job => (hr K B job.worker job.source job.serial).1)
    (fun K B job => (hr K B job.worker job.source job.serial).2)
    I hf _ μ P hiid g hg w R hR hRpos.le hdef (chosenLMO_valid p hp)).2.2

end LongTails.Proofs.BirchNonEuclideanComposition
