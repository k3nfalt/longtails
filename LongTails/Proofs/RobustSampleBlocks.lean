import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.RobustGradient

open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

variable {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

lemma stream_groups_preserving (k r : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin k => fun j : Fin r => ξ (i*r+j))
      (Measure.infinitePi fun _ : ℕ => p)
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => p) := by
  have h := infinitePi_iid p
  exact (prefix_preserving (Measure.pi fun _ : Fin r => p) k).comp
    (FiniteVariance.infinite_block_law p _ h.independent h.marginal r)

lemma finite_groups_preserving (k r : ℕ) :
    MeasurePreserving (fun ξ : Fin (k*r) → Ω => fun i : Fin k => fun j : Fin r =>
      ξ ⟨i*r+j, by
        have hi := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
        simp only [Nat.succ_mul] at hi
        have hj := j.isLt
        omega⟩)
      (Measure.pi fun _ : Fin (k*r) => p)
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => p) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← (prefix_preserving p (k*r)).map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (stream_groups_preserving p k r).map_eq

lemma finite_split_preserving (n m : ℕ) :
    MeasurePreserving (fun ξ : Fin (n+m) → Ω =>
      ((fun i : Fin n => ξ ⟨i, by have hi := i.isLt; omega⟩),
       (fun j : Fin m => ξ ⟨n+j, by have hj := j.isLt; omega⟩)))
      (Measure.pi fun _ : Fin (n+m) => p)
      ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin m => p)) := by
  have h := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod
    (prefix_preserving p m)).comp (splitStream_preserving p n)
  refine ⟨by fun_prop, ?_⟩
  rw [← (prefix_preserving p (n+m)).map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  exact h.map_eq

lemma grouped_split_preserving (k r m : ℕ) :
    MeasurePreserving (fun ξ : Fin (k*r+m) → Ω =>
      ((fun (i : Fin k) (j : Fin r) => ξ ⟨i*r+j, by
        have hi := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
        simp only [Nat.succ_mul] at hi
        have hj := j.isLt
        omega⟩),
       (fun j : Fin m => ξ ⟨k*r+j, by have hj := j.isLt; omega⟩)))
      (Measure.pi fun _ : Fin (k*r+m) => p)
      ((Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => p).prod
        (Measure.pi fun _ : Fin m => p)) :=
  ((finite_groups_preserving p k r).prod (MeasurePreserving.id _)).comp
    (finite_split_preserving p (k*r) m)

end OracleTemplate.RobustGradient
