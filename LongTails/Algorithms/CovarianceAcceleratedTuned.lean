import LongTails.Algorithms.CovarianceAcceleratedGrid
import LongTails.Setups.CovarianceSmoothConvex

namespace LongTails.Algorithms.CovarianceAcceleratedTuned

noncomputable def confidence (δ : ℝ) : ℝ := Real.log (3 / δ)

noncomputable def horizonLog (N : ℕ) (δ : ℝ) : ℝ := Real.log (54 * (N : ℝ) / δ)

noncomputable def warmup (N : ℕ) (δ : ℝ) : ℕ := ⌈16 * horizonLog N δ⌉₊

noncomputable def steps (N : ℕ) (δ : ℝ) : ℕ := N - warmup N δ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def config (x0 : E) (L R σ s j ell : ℝ) (k T : ℕ) :
    CovarianceAccelerated.Config E
      (Fintype.card ↥(CovarianceAcceleratedGrid.grid (E := E) R (R / (T : ℝ) ^ 2)) + 1) :=
  let M := 100 * (σ * T + L * R * k)
  let ν := σ ^ 2 * T + j * M ^ 2 * ell / (T : ℝ) ^ 2
  let b := R / (32 * T * Real.sqrt ν)
  let η := 1 / (16 * R * s * T * Real.sqrt T / Real.sqrt ell + 64 * R * M + 64 * b * j * M ^ 2)
  let a := Real.sqrt (b / η)
  CovarianceAcceleratedGrid.config x0 R (R / (T : ℝ) ^ 2) a η (2 * η * L) (η * L * R ^ 2) (k - 1)

noncomputable def method (q : LongTails.Setups.CovarianceSmoothConvex.Params) (N : ℕ) :
    OracleTemplate.Algorithm q.E q.E q.E :=
  let c := config q.x0 q.L q.R q.σ q.s (horizonLog N q.δ) (confidence q.δ)
    (warmup N q.δ) (steps N q.δ)
  { CovarianceAccelerated.method c with output := fun state => if q.R = 0 then q.x0 else state.2.1 }

noncomputable def output (q : LongTails.Setups.CovarianceSmoothConvex.Params)
    (g : q.E → q.Ω → q.E) (ξ : ℕ → q.Ω) (N : ℕ) : q.E :=
  if q.R = 0 then q.x0 else
    CovarianceAccelerated.output
      (config q.x0 q.L q.R q.σ q.s (horizonLog N q.δ) (confidence q.δ)
        (warmup N q.δ) (steps N q.δ)) g ξ N

end LongTails.Algorithms.CovarianceAcceleratedTuned
