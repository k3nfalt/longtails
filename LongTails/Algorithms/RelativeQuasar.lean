import LongTails.Setups.RelativeGradientStrongQuasar
import LongTails.Algorithms.ContinuizedQuasar

open MeasureTheory

namespace OracleTemplate.RelativeQuasar

open LongTails.Setups.RelativeGradientStrongQuasar

noncomputable def theta (p : Params) : ℝ :=
  1 / (8 * Real.sqrt (p.L / (p.μ * (1 - p.δ))) + 32 * p.δ ^ 2 * p.L / (p.γ * p.μ * (1 - p.δ)))

noncomputable def blockLength (p : Params) : ℕ :=
  max 1 ⌈32 * Real.sqrt (p.L / (p.μ * (1 - p.δ))) / p.γ + 128 * p.δ ^ 2 * p.L / (p.γ ^ 2 * p.μ * (1 - p.δ))⌉₊

noncomputable def blocks (p : Params) : ℕ :=
  max 1 (Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊)

noncomputable def calls (p : Params) : ℕ := blockLength p * blocks p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def jump (L μ θ : ℝ) (s : E × E) (v : E) : E × E :=
  (s.1 - (1 / L) • v, s.2 - (2 * θ / μ) • v)

noncomputable def advance (L μ γ θ : ℝ) (g : E → E) (s : E × E) (t : ℝ) : E × E :=
  let y := ContinuizedSimilarQuasar.flow γ θ (max 0 t) s
  jump L μ θ y (g y.1)

noncomputable def run (p : Params) (g : p.E → p.E) (k : ℕ)
    (s : p.E × p.E) (samples : Fin k → ℝ) : p.E × p.E :=
  ContinuizedSimilarQuasar.iterateSamples (advance p.L p.μ p.γ (theta p) g) k s samples

noncomputable def holdingLaw : ProbabilityMeasure ℝ := by
  letI := ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  exact ⟨ProbabilityTheory.expMeasure 1, inferInstance⟩

noncomputable def samplesLaw (k : ℕ) : ProbabilityMeasure (Fin k → ℝ) :=
  ⟨Measure.pi (fun _ => (holdingLaw : Measure ℝ)), inferInstance⟩

noncomputable def plan (p : Params) : (k : ℕ) → (p.E × p.E) → (Fin k → ℝ) →
    QueryPlan p.E p.E (p.E × p.E) k
  | 0, s, _ => .done s
  | k + 1, s, samples =>
      let y := ContinuizedSimilarQuasar.flow p.γ (theta p) (max 0 (samples 0)) s
      .ask y.1 (fun v => plan p k (jump p.L p.μ (theta p) y v) (fun i => samples i.succ))

noncomputable def accelerated (p : Params) : Algorithm p.E p.E p.E :=
  QueryPlan.algorithm (samplesLaw (calls p)) p.x0 p.x0 (calls p)
    (fun samples => QueryPlan.map Prod.fst (plan p (calls p) (p.x0, p.x0) samples))

noncomputable def output (p : Params) (O : Oracle p.E p.E)
    (seed : (accelerated p).Seed × ((k : ℕ) → O.Seed k)) : p.E :=
  execute O (accelerated p) (fun _ => calls p) seed.1 seed.2

end OracleTemplate.RelativeQuasar
