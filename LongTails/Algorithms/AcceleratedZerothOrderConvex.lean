import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Uniform
import LongTails.Algorithms.Accelerated
import LongTails.Algorithms.AcceleratedBiasedStochastic
import LongTails.Algorithms.Batched
import LongTails.Algorithms.Clipping
import LongTails.Algorithms.Seeded
import LongTails.Setups.ZerothOrderSmoothAndConvex

section

open scoped BigOperators

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def direction {d : ℕ} (i : Fin d) : Point d :=
  EuclideanSpace.basisFun (Fin d) ℝ i

noncomputable def difference {d : ℕ} (h : ℝ) (x : Point d)
    (values : Point d → ℝ) : Point d :=
  ∑ i : Fin d, ((values (x + h • direction i) - values x) / h) • direction i

noncomputable def estimate {d : ℕ} {Ω : Type*} (g : Point d → Ω → ℝ)
    (h : ℝ) (x : Point d) (ξ : Fin d × Bool → Ω) : Point d :=
  ∑ i : Fin d, ((g (x + h • direction i) (ξ (i, true)) -
    g x (ξ (i, false))) / h) • direction i

noncomputable def valueQueries {d : ℕ} (h : ℝ) (s : ℕ × Point d × Point d)
    (i : Fin (Fintype.card (Fin d × Bool))) : Point d :=
  let j := (Fintype.equivFin (Fin d × Bool)).symm i
  if j.2 then Gradient.acceleratedQuery s + h • direction j.1
  else Gradient.acceleratedQuery s

noncomputable def decodeValues {d : ℕ} (h : ℝ)
    (values : Fin (Fintype.card (Fin d × Bool)) → ℝ) : Point d :=
  ∑ i : Fin d, ((values (Fintype.equivFin (Fin d × Bool) (i, true)) -
    values (Fintype.equivFin (Fin d × Bool) (i, false))) / h) • direction i

noncomputable def acceleratedFiniteDifference {d : ℕ} (hd : 0 < d)
    (D R h : ℝ) (x0 : Point d) : Algorithm (Point d) ℝ (Point d) :=
  batched (show 0 < Fintype.card (Fin d × Bool) by simp; omega)
    (BiasedStochasticGradient.projectedAccelerated D R x0)
    (valueQueries h) (fun _ => decodeValues h) 0

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def rescaled (A : Algorithm E ℝ E) (R B : ℝ) (x0 : E) : Algorithm E ℝ E :=
  let base := batched (by decide : 0 < 2) A
    (fun s i => if i = 0 then x0 + (2*R) • (A.query s).2 else x0)
    (fun _ v => (v 0 - v 1) / B + 1/2) 0
  { base with output := fun s => x0 + (2*R) • base.output s }

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

noncomputable def centeredOracle (g : Point d → Ω → ℝ) (R B : ℝ) (x0 y : Point d) (ω : Ω × Ω) : ℝ :=
  (g (x0 + (2*R) • y) ω.1 - g x0 ω.2) / B + 1/2

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def midpointCoordinate {m : ℕ} (h : ℝ) (j : Fin m) : ℝ :=
  -h+(2*(j:ℝ)+1)*h/m

noncomputable def midpointPoint {d m : ℕ} (h : ℝ) (v : Fin d → Fin m) : Point d :=
  WithLp.toLp 2 (fun i => midpointCoordinate h (v i))

noncomputable def boundaryDifference {d : ℕ} (h : ℝ) (x z : Point d) (f : Point d → ℝ) : Point d :=
  ∑ i : Fin d, ((f (x+z+(h-z i) • direction i)-f (x+z+(-h-z i) • direction i))/(2*h)) • direction i

noncomputable def coordinateSecant {d : ℕ} {Ω : Type*} (g : Point d → Ω → ℝ)
    (h : ℝ) (a b : Fin d → Point d) (ξ : Fin d × Bool → Ω) : Point d :=
  ∑ i : Fin d, ((g (a i) (ξ (i,true))-g (b i) (ξ (i,false)))/h) • direction i

noncomputable def coordinateDifference {d : ℕ} (h : ℝ) (a b : Fin d → Point d)
    (f : Point d → ℝ) : Point d :=
  ∑ i : Fin d, ((f (a i)-f (b i))/h) • direction i

noncomputable def gridUpper {d m : ℕ} (h : ℝ) (i : Fin d) (t : Point d × (Fin d → Fin m)) : Point d :=
  t.1+midpointPoint h t.2+(h-midpointPoint h t.2 i) • direction i

noncomputable def gridLower {d m : ℕ} (h : ℝ) (i : Fin d) (t : Point d × (Fin d → Fin m)) : Point d :=
  t.1+midpointPoint h t.2+(-h-midpointPoint h t.2 i) • direction i

noncomputable def gridOracle {d m : ℕ} {Ω : Type*} (g : Point d → Ω → ℝ)
    (h : ℝ) (x : Point d) (s : (Fin d → Fin m) × (Fin d × Bool → Ω)) : Point d :=
  coordinateSecant g (2*h) (fun i => gridUpper h i (x,s.1))
    (fun i => gridLower h i (x,s.1)) s.2

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def gridSeedLaw {d m : ℕ} (hm : 0 < m) (K : ℕ) :
    ProbabilityMeasure (Fin K → Fin d → Fin m) := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  exact ⟨Measure.pi (fun _ : Fin K => (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure),inferInstance⟩

def drawGrid {d m K : ℕ} (hm : 0 < m) (s : Fin K → Fin d → Fin m) (k : ℕ) : Fin d → Fin m :=
  if hk : k < K then s ⟨k,hk⟩ else fun _ => ⟨0,hm⟩

noncomputable def gridQueries {d m K : ℕ} (hm : 0 < m) (h : ℝ)
    (s : ℕ × (Fin K → Fin d → Fin m) × (ℕ × Point d × Point d))
    (i : Fin (Fintype.card (Fin d × Bool))) : Point d :=
  let j := (Fintype.equivFin (Fin d × Bool)).symm i
  let v := drawGrid hm s.2.1 s.1
  if j.2 then gridUpper h j.1 (Gradient.acceleratedQuery s.2.2,v)
  else gridLower h j.1 (Gradient.acceleratedQuery s.2.2,v)

noncomputable def acceleratedGrid {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (K : ℕ)
    (D R h : ℝ) (x0 : Point d) : Algorithm (Point d) ℝ (Point d) :=
  batched (show 0 < Fintype.card (Fin d × Bool) by simp; omega)
    (seeded (BiasedStochasticGradient.projectedAccelerated D R x0) (gridSeedLaw (d := d) hm K))
    (gridQueries hm h) (fun _ => decodeValues (2*h)) 0

end OracleTemplate.ZerothOrder

end

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def fromCoordinates {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (e : E ≃ₗᵢ[ℝ] Point d) (A : Algorithm (Point d) ℝ (Point d)) :
    Algorithm E ℝ E where
  Seed := A.Seed
  seedSpace := A.seedSpace
  law := A.law
  State := A.State
  initial := A.initial
  query :=  fun s => (0, e.symm (A.query s).2)
  update := A.update
  output := fun s => e.symm (A.output s)

end OracleTemplate.ZerothOrder
