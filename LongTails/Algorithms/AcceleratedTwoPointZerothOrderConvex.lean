import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LongTails.Algorithms.Accelerated
import LongTails.Algorithms.Batched
import LongTails.Algorithms.Seeded
import LongTails.Setups.ZerothOrderSmoothAndConvex

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def twoPointEstimate {d : ℕ} {Ω : Type*} (g : Point d → Ω → ℝ)
    (h : ℝ) (x u : Point d) (ω : Ω × Ω) : Point d :=
  ((d:ℝ)*(g (x+h • u) ω.1-g (x-h • u) ω.2)/(2*h)) • u

noncomputable def twoPointExact {d : ℕ} (f : Point d → ℝ)
    (h : ℝ) (x u : Point d) : Point d :=
  ((d:ℝ)*(f (x+h • u)-f (x-h • u))/(2*h)) • u

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

noncomputable def sphereLaw : ProbabilityMeasure (sphere (0:E) 1) := by
  let μ := (volume : Measure E).toSphere
  have hm : μ univ ≠ 0 := by
    intro hzero
    have hz : μ = 0 := Measure.measure_univ_eq_zero.mp hzero
    exact Measure.toSphere_ne_zero (volume : Measure E) hz
  refine ⟨(μ univ)⁻¹ • μ, ⟨?_⟩⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm (measure_ne_top μ univ)]


end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Metric

namespace OracleTemplate.StochasticGradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def coupledUpdate (M θ : ℝ) (k : ℕ) (s : E × E) (G : E) : E × E :=
  (Gradient.acceleratedQuery (k,s.1,s.2)-(2*θ/M) • G,s.2-(((k:ℝ)+1)/M) • G)

noncomputable def coupledRun (g : E → Ω → E) (M θ : ℝ) :
    (K : ℕ) → ℕ → E → E → (Fin K → Ω) → E × E
  | 0, _, x, z, _ => (x,z)
  | K+1, k, x, z, ξ =>
      let next := coupledUpdate M θ k (x,z) (g (Gradient.acceleratedQuery (k,x,z)) (ξ 0))
      coupledRun g M θ K (k+1) next.1 next.2 (fun i => ξ i.succ)

noncomputable def coupledAccelerated (M θ : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0,x0,x0)
  query := fun s => (0, (Gradient.acceleratedQuery) s)
  update s G := (s.1+1,coupledUpdate M θ s.1 s.2 G)
  output s := s.2.1

end OracleTemplate.StochasticGradient

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def twoPointSeedLaw {d : ℕ}
    (ρ : ProbabilityMeasure (sphere (0 : Point d) 1)) (K : ℕ) :
    ProbabilityMeasure (Fin K → sphere (0 : Point d) 1) :=
  ⟨Measure.pi (fun _ : Fin K => (ρ : Measure _)),inferInstance⟩

def drawTwoPointDirection {d K : ℕ} (hK : 0 < K)
    (s : Fin K → sphere (0 : Point d) 1) (k : ℕ) : sphere (0 : Point d) 1 :=
  if hk : k < K then s ⟨k,hk⟩ else s ⟨0,hK⟩

noncomputable def twoPointQueries {d K : ℕ} (hK : 0 < K) (h : ℝ)
    (s : ℕ × (Fin K → sphere (0 : Point d) 1) × (ℕ × Point d × Point d))
    (i : Fin 2) : Point d :=
  let x := Gradient.acceleratedQuery s.2.2
  let u := (drawTwoPointDirection hK s.2.1 s.1 : Point d)
  if i=0 then x+h • u else x-h • u

noncomputable def decodeTwoPoint {d K : ℕ} (hK : 0 < K) (h : ℝ)
    (s : ℕ × (Fin K → sphere (0 : Point d) 1) × (ℕ × Point d × Point d))
    (values : Fin 2 → ℝ) : Point d :=
  ((d:ℝ)*(values 0-values 1)/(2*h)) •
    (drawTwoPointDirection hK s.2.1 s.1 : Point d)

noncomputable def acceleratedTwoPoint {d K : ℕ} (hK : 0 < K)
    (ρ : ProbabilityMeasure (sphere (0 : Point d) 1)) (M θ h : ℝ) (x0 : Point d) :
    Algorithm (Point d) ℝ (Point d) :=
  batched (by decide : 0 < 2)
    (seeded (StochasticGradient.coupledAccelerated M θ x0) (twoPointSeedLaw ρ K))
    (twoPointQueries hK h) (decodeTwoPoint hK h) 0

end OracleTemplate.ZerothOrder

end
