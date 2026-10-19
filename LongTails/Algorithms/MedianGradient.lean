import LongTails.Algorithms.RobustValue
import LongTails.Algorithms.DyadicVarianceReduction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OracleTemplate.MedianGradient

noncomputable def median {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => FiniteVariance.median3 (a i) (b i) (c i))

noncomputable def paired {d : ℕ} {U : Type}
    (A : Algorithm (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) U) :=
  batched (by decide : 0 < 3) A (fun s _ => (A.query s).2)
    (fun _ v => (median (v 0).1 (v 1).1 (v 2).1,
      median (v 0).2 (v 1).2 (v 2).2)) (0, 0)

noncomputable def oracle {d : ℕ} {Ω : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (ξ : Fin 3 → Ω) : EuclideanSpace ℝ (Fin d) :=
  median (g x (ξ 0)) (g x (ξ 1)) (g x (ξ 2))

noncomputable def method {d : ℕ} (cfg : DyadicHolder.DyadicConfig) (x0 : EuclideanSpace ℝ (Fin d)) :=
  paired (DyadicHolder.dyadicVR cfg x0)

end OracleTemplate.MedianGradient
