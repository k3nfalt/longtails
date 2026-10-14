import LongTails.Setups.CoordinateSmoothStronglyConvex
import LongTails.Algorithms.QueryPlan
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.AcceleratedCoordinate

open LongTails.Setups.CoordinateSmoothStronglyConvex

noncomputable def weight (p : Params) (i : Fin p.d) : ℕ :=
  max 1 ⌈Real.sqrt (p.L i / p.μ)⌉₊

noncomputable def totalWeight (p : Params) : ℕ := ∑ i, weight p i

def CoordinateChoice (p : Params) := Σ i : Fin p.d, Fin (weight p i)

noncomputable instance (p : Params) : Fintype (CoordinateChoice p) :=
  inferInstanceAs (Fintype (Σ i : Fin p.d, Fin (weight p i)))

instance (p : Params) : Nonempty (CoordinateChoice p) :=
  ⟨⟨0, ⟨0, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩⟩

noncomputable def tau (p : Params) : ℝ := 1 / (2 * (totalWeight p : ℝ))

noncomputable def eta (p : Params) : ℝ := 1 / (p.μ * (2 * (totalWeight p : ℝ) - 1))

noncomputable def extrapolate (p : Params)
    (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) :
    EuclideanSpace ℝ (Fin p.d) :=
  (tau p) • s.2 + (1 - tau p) • s.1

noncomputable def step (p : Params)
    (s : EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
    (i : Fin p.d) (reply : ℝ) :
    EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d) :=
  let x := extrapolate p s
  (x - EuclideanSpace.single i (reply / p.L i),
    (1 / (1 + eta p * p.μ)) •
      (s.2 + (eta p * p.μ) • x -
        EuclideanSpace.single i (eta p * (totalWeight p : ℝ) / (weight p i : ℝ) * reply)))

noncomputable def plan (p : Params) : (K : ℕ) →
    (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) →
    (Fin K → CoordinateChoice p) →
    QueryPlan (Fin p.d × EuclideanSpace ℝ (Fin p.d)) ℝ (EuclideanSpace ℝ (Fin p.d)) K
  | 0, s, _ => .done s.1
  | K + 1, s, choices =>
    .ask ((choices 0).1, extrapolate p s)
      (fun reply => plan p K (step p s (choices 0).1 reply) (fun j => choices j.succ))

noncomputable def run (p : Params)
    (g : Fin p.d × EuclideanSpace ℝ (Fin p.d) → ℝ) :
    (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)) →
    List (CoordinateChoice p) →
    EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d)
  | s, [] => s
  | s, i :: tail => run p g (step p s i.1 (g (i.1, extrapolate p s))) tail

def Seeds (p : Params) (K : ℕ) := Fin K → CoordinateChoice p

noncomputable instance (p : Params) (K : ℕ) : Fintype (Seeds p K) :=
  inferInstanceAs (Fintype (Fin K → CoordinateChoice p))

instance (p : Params) (K : ℕ) : Nonempty (Seeds p K) :=
  inferInstanceAs (Nonempty (Fin K → CoordinateChoice p))

instance (p : Params) (K : ℕ) : MeasurableSpace (Seeds p K) := ⊤
instance (p : Params) (K : ℕ) : MeasurableSingletonClass (Seeds p K) := ⟨fun _ => trivial⟩

noncomputable def acceleratedCoordinate (p : Params) (K : ℕ) :
    Algorithm (Fin p.d × EuclideanSpace ℝ (Fin p.d)) ℝ (EuclideanSpace ℝ (Fin p.d)) :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p K)).toMeasure, inferInstance⟩
    (0, p.x0) p.x0 K (plan p K (p.x0, p.x0))

end OracleTemplate.AcceleratedCoordinate
