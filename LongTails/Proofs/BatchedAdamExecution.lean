import LongTails.Algorithms.BatchedAdam
import LongTails.Proofs.AcceleratedMarkovExecution

namespace LongTails.Proofs.BatchedAdamExecution

open OracleTemplate LongTails.Setups.AffineHeavyTailedAdam
open LongTails.Algorithms.BatchedAdam StochasticGradient HeavyTailedMarkovGradient

lemma advance_prefix {d : ℕ} {Ω : Type} (cfg : Config)
    (g : Point d → Ω → Point d) (ξ : ℕ → Ω) (s : Adam.State d)
    (call j : ℕ) (hj : j < cfg.batchSize) :
    advance (fun k state => step cfg state (g state.core.point (ξ k))) j call
      (⟨0, 0, s⟩ : State d) =
      ⟨j, ∑ i : Fin j, g s.point (ξ (call + i.val)), s⟩ := by
  induction j with
  | zero => simp [advance]
  | succ j ih =>
    erw [advance_add (K := j) (J := 1), ih (by omega)]
    simp only [advance, step, hj, ite_true]
    congr 1
    rw [Fin.sum_univ_castSucc]
    rfl

lemma advance_block {d : ℕ} {Ω : Type} (cfg : Config) (hB : 0 < cfg.batchSize)
    (g : Point d → Ω → Point d) (ξ : ℕ → Ω) (s : Adam.State d) (call : ℕ) :
    advance (fun k state => step cfg state (g state.core.point (ξ k))) cfg.batchSize call
      (⟨0, 0, s⟩ : State d) =
      ⟨0, 0, coreStep cfg s (batchReply cfg g s.point (fun i => ξ (call + i.val)))⟩ := by
  unfold batchReply
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hB.ne'
  rw [hj]
  erw [advance_add (K := j) (J := 1), advance_prefix cfg g ξ s call j (by omega)]
  simp only [advance, step, hj, lt_self_iff_false, ite_false]
  congr 2
  rw [Fin.sum_univ_castSucc]
  rfl

lemma advance_process {d : ℕ} {Ω : Type} (cfg : Config) (hB : 0 < cfg.batchSize)
    (g : Point d → Ω → Point d) (ξ : ℕ → Ω) (x0 : Point d) (k T : ℕ) :
    advance (fun call state => step cfg state (g state.core.point (ξ call)))
      (T * cfg.batchSize) 0 (⟨0, 0, ⟨k, 0, x0, 0, 0, x0⟩⟩ : State d) =
      ⟨0, 0, process cfg x0 k g (fun t i => ξ (t * cfg.batchSize + i.val)) T⟩ := by
  induction T with
  | zero => simp [advance, process]
  | succ T ih =>
    rw [Nat.succ_mul]
    erw [advance_add, ih]
    simp only [Nat.zero_add]
    rw [advance_block cfg hB]
    rfl

lemma execute_process {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config) (hB : 0 < cfg.batchSize)
    (g : Point d → Ω → Point d) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (ξ : ℕ → Ω) (x0 : Point d) (k : Fin (cfg.lastIndex + 1)) (T : ℕ) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (method cfg x0) (fun _ => T * cfg.batchSize) k ξ =
      (process cfg x0 k.val g (fun t i => ξ (t * cfg.batchSize + i.val)) T).saved := by
  erw [execute_advance]
  change (advance (fun call state => step cfg state (g state.core.point (ξ call)))
    (T * cfg.batchSize) 0 (⟨0, 0, ⟨k.val, 0, x0, 0, 0, x0⟩⟩ : State d)).core.saved = _
  rw [advance_process cfg hB]

lemma process_time {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k : ℕ)
    (g : Point d → Ω → Point d) (ξ : ℕ → Fin cfg.batchSize → Ω) (t : ℕ) :
    (process cfg x0 k g ξ t).time = t ∧ (process cfg x0 k g ξ t).selected = k := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih => simp only [process, coreStep, ih.1, ih.2, and_self]

lemma process_core_independent {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k l : ℕ)
    (g : Point d → Ω → Point d) (ξ : ℕ → Fin cfg.batchSize → Ω) (t : ℕ) :
    (process cfg x0 k g ξ t).point = (process cfg x0 l g ξ t).point ∧
    (process cfg x0 k g ξ t).momentum = (process cfg x0 l g ξ t).momentum ∧
    (process cfg x0 k g ξ t).secondMoment = (process cfg x0 l g ξ t).secondMoment := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ t ih =>
    simp only [process, coreStep, ih.1, ih.2.1, ih.2.2, (process_time cfg x0 k g ξ t).1,
      (process_time cfg x0 l g ξ t).1]
    trivial

lemma process_saved {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k : ℕ)
    (g : Point d → Ω → Point d) (ξ : ℕ → Fin cfg.batchSize → Ω) (T : ℕ) :
    (process cfg x0 k g ξ T).saved =
      if k < T then (process cfg x0 0 g ξ k).point else x0 := by
  induction T with
  | zero => simp [process]
  | succ T ih =>
    simp only [process, coreStep, (process_time cfg x0 k g ξ T).1,
      (process_time cfg x0 k g ξ T).2]
    by_cases he : T = k
    · subst T
      simp only [ite_true, Nat.lt_succ_self]
      exact (process_core_independent cfg x0 k 0 g ξ k).1
    · rw [ite_eq_right he, ih]
      have hh : k < T + 1 ↔ k < T := by omega
      simp only [hh]

lemma process_eq_trajectory {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k : ℕ)
    (g : Point d → Ω → Point d) (ξ : ℕ → Fin cfg.batchSize → Ω) (t : ℕ) :
    process cfg x0 k g ξ t = trajectory cfg x0 k
      (fun j => batchReply cfg g (process cfg x0 k g ξ j).point (ξ j)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [process, trajectory, ← ih]

end LongTails.Proofs.BatchedAdamExecution
