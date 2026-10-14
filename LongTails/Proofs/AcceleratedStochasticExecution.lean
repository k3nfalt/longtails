import LongTails.Algorithms.AcceleratedStochastic
import LongTails.Proofs.SgdExecution

namespace OracleTemplate.StochasticGradient

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_accelerated (g : E → Ω → E) (D : ℝ) (x0 : E) (ξ : ℕ → Ω)
    (K call k : ℕ) (x z : E) :
    advance (fun j state => (Gradient.accelerated (D, x0)).update state
      (g (((Gradient.accelerated (D, x0)).query state).2) (ξ j))) K call (k, x, z) =
      (k + K, acceleratedRun g D K k x z (fun i => ξ (call + i))) := by
  dsimp only [Gradient.accelerated]
  induction K generalizing call k x z with
  | zero => simp [advance, acceleratedRun]
  | succ K ih =>
    rw [advance]
    change advance _ K (call + 1) (k + 1,
      Gradient.acceleratedQuery (k, x, z) - (1 / D) • g (Gradient.acceleratedQuery (k, x, z)) (ξ call),
      z - (((k : ℝ) + 1) / 2 / D) • g (Gradient.acceleratedQuery (k, x, z)) (ξ call)) = _
    simpa only [acceleratedRun, div_div, Fin.val_zero, Nat.add_zero,
      Fin.val_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (call + 1) (k + 1)
        (Gradient.acceleratedQuery (k, x, z) - (1 / D) • g (Gradient.acceleratedQuery (k, x, z)) (ξ call))
        (z - (((k : ℝ) + 1) / (2 * D)) • g (Gradient.acceleratedQuery (k, x, z)) (ξ call))

lemma execute_accelerated_stochastic [MeasurableSpace Ω] (p : MeasureTheory.ProbabilityMeasure Ω)
    (g : E → Ω → E) (D : ℝ) (x0 : E) (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := ⟨MeasureTheory.Measure.infinitePi (fun _ : ℕ =>
                (p : MeasureTheory.Measure Ω)), inferInstance⟩
              answer := fun _ (_, x) seed => g x seed } (Gradient.accelerated (D, x0)) (fun _ => K) () ξ =
      (acceleratedRun g D K 0 x0 x0 (fun i => ξ i)).1 := by
  erw [execute_advance]
  change (Gradient.accelerated (D, x0)).output (advance _ K 0 (0, x0, x0)) = _
  erw [advance_accelerated]
  simp [Gradient.accelerated]

end OracleTemplate.StochasticGradient
