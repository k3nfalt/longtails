import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

namespace OracleTemplate.TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def acceleratedQuery (θ : ℝ) (s : E × E) : E :=
  (1 / (1 + θ)) • (s.1 + θ • s.2)

def acceleratedUpdate (θ μ : ℝ) (s : E × E) (g : E) : E × E :=
  let y := acceleratedQuery θ s
  (y - (θ ^ 2 / μ) • g, (1 - θ) • s.2 + θ • y - (θ / μ) • g)

def tailAverage (v : ℕ → E) (start count : ℕ) : E :=
  (count : ℝ)⁻¹ • ∑ k ∈ Finset.range count, v (start + k + 1)

def acceleratedRun (g : ℕ → E → E) (θ μ : ℝ) (x0 : E) : ℕ → E × E
  | 0 => (x0, x0)
  | k + 1 => acceleratedUpdate θ μ (acceleratedRun g θ μ x0 k)
      (g k (acceleratedQuery θ (acceleratedRun g θ μ x0 k)))

def tailAccelerated (θ μ : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × (ℕ → E × E)
  initial _ := (0, fun _ => (x0, x0))
  query s := (0, acceleratedQuery θ (s.2 s.1))
  update s g := (s.1 + 1,
    Function.update s.2 (s.1 + 1) (acceleratedUpdate θ μ (s.2 s.1) g))
  output s := tailAverage (fun k => (s.2 k).1) (s.1 / 2) (s.1 - s.1 / 2)

end OracleTemplate.TemporalDiscrepancy
