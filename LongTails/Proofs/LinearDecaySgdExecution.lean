import LongTails.Algorithms.LinearDecaySgd
import LongTails.Setups.SampledSmoothConvex
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace OracleTemplate.SampledConvex

open LongTails.Setups.SampledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ξ : Type} [MeasurableSpace Ξ]

omit [MeasurableSpace Ξ] in
lemma advance_linearDecaySgd (G : Ξ → E → E) (η : ℝ) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) :
    ∀ K j, StochasticGradient.advance
      (fun k state => (linearDecaySgd η T x0).update state
        (G (ξ k) (((linearDecaySgd η T x0).query state).2))) K j (j, path G η T x0 ξ j) =
      (j + K, path G η T x0 ξ (j + K)) := by
  intro K
  induction K with
  | zero => intro j; rfl
  | succ K ih =>
    intro j
    have h := ih (j + 1)
    rw [show j + 1 + K = j + (K + 1) by omega] at h
    exact h

noncomputable def sampleOracle (p : ProbabilityMeasure Ξ) (G : Ξ → E → E) : Oracle E E where
  Seed := fun _ => Ξ
  law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure Ξ)), inferInstance⟩
  answer := fun _ (_, x) ω => G ω x

lemma execute_linearDecaySgd (p : ProbabilityMeasure Ξ) (G : Ξ → E → E) (η : ℝ) (T : ℕ) (x0 : E)
    (K : ℕ) (ξ : ℕ → Ξ) :
    execute (sampleOracle p G) (linearDecaySgd η T x0) (fun _ => K) () ξ = path G η T x0 ξ K := by
  refine (StochasticGradient.execute_advance (sampleOracle p G) (linearDecaySgd η T x0) K () ξ).trans ?_
  have h := advance_linearDecaySgd G η T x0 ξ K 0
  rw [Nat.zero_add] at h
  change (linearDecaySgd η T x0).output (StochasticGradient.advance (fun k state =>
    (linearDecaySgd η T x0).update state (G (ξ k) (((linearDecaySgd η T x0).query state).2))) K 0
      (0, path G η T x0 ξ 0)) = _
  rw [h]
  rfl

omit [MeasurableSpace Ξ] in
lemma path_zero_scale (G : Ξ → E → E) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) :
    ∀ k, path G 0 T x0 ξ k = x0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [path, ih]

end OracleTemplate.SampledConvex
