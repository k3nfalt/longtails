import LongTails.Algorithms.StepDecaySgd
import LongTails.Proofs.Execution
import LongTails.Proofs.RiverValleyMaster

namespace OracleTemplate.RiverValley

open OracleTemplate.StepDecaySgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

lemma run_sd (g : E → Ω → E) (ηs ηc : ℝ) (T K : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ j, j ≤ τ + K →
      (fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method ηs ηc T K x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[j]
          ((τ, 0, x0), 0) = ((τ, j, schedSeq g (schedOf ηs ηc τ) x0 ξ j), j)
  | 0, _ => rfl
  | j + 1, h => by
      rw [Function.iterate_succ_apply', run_sd g ηs ηc T K x0 ξ τ j (by omega)]
      have hj : j < τ + K := by omega
      by_cases hτ : j < τ
      · simp [method, hτ, schedSeq, schedOf]
      · simp [method, hτ, hj, schedSeq, schedOf]

lemma run_sd_frozen (g : E → Ω → E) (ηs ηc : ℝ) (T K : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ m, ((fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method ηs ηc T K x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[τ + K + m]
          ((τ, 0, x0), 0)).1 = (τ, τ + K, schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + K))
  | 0 => by rw [Nat.add_zero, run_sd g ηs ηc T K x0 ξ τ (τ + K) le_rfl]
  | m + 1 => by
      rw [show τ + K + (m + 1) = (τ + K + m) + 1 by omega, Function.iterate_succ_apply']
      have ih := run_sd_frozen g ηs ηc T K x0 ξ τ m
      set sc := (fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method ηs ηc T K x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[τ + K + m]
          ((τ, 0, x0), 0)
      obtain ⟨s, c⟩ := sc
      simp only at ih
      subst ih
      simp [method]

noncomputable def sdOracle [MeasurableSpace Ω] (g : E → Ω → E) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) :
    Oracle E E where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, x) ω => g x ω

lemma execute_sd [MeasurableSpace Ω] (g : E → Ω → E) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (ηs ηc : ℝ) (T K : ℕ) (x0 : E) (B : ℕ) (τ : Fin (T + 1)) (ξ : ℕ → Ω) (hB : T + K ≤ B) :
    execute (sdOracle g P) (method ηs ηc T K x0) (fun _ => B) τ ξ =
      schedSeq g (schedOf ηs ηc τ.val) x0 ξ (τ.val + K) := by
  refine (execute_indexed (sdOracle g P) (method ηs ηc T K x0) B τ ξ).trans ?_
  obtain ⟨m, hm⟩ : ∃ m, B = (τ.val + K) + m := ⟨B - (τ.val + K), by have := τ.isLt; omega⟩
  subst hm
  have h := run_sd_frozen g ηs ηc T K x0 ξ τ.val m
  change ((((fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method ηs ηc T K x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[τ.val + K + m]
          ((τ.val, 0, x0), 0)).1).2.2) = _
  rw [h]

end OracleTemplate.RiverValley
