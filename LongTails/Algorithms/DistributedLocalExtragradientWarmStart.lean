import LongTails.Algorithms.DistributedLocalExtragradient
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort

namespace LongTails.Algorithms.DistributedLocalExtragradientWarmStart

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedQuantization

noncomputable def medianGrid {n d width : ℕ} (codes : Fin n → Grid d width) : Grid d width :=
  fun j => ((List.ofFn (fun i => codes i j)).mergeSort (· ≤ ·)).getD (n / 2) 0

noncomputable def warmPoint (p : Params) (s : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p) (i : Fin p.n) (samples : ℕ → p.Ω) : Point p :=
  projectBall p p.x0 p.R
    (LocalNonlinearExtragradient.warmRun (p.μ / (p.ρ * p.L ^ 2)) (g i) p.x0
      (fun k => samples (p.n * k + i.val)) s)

noncomputable def warmCodes (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) : Fin p.n → Grid p.d width :=
  fun i => quantize p.d width spacing (warmPoint p s g i samples - p.x0)

noncomputable def warmCenter (p : Params) (s width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) : Point p :=
  projectBall p p.x0 p.R
    (p.x0 + reconstruct spacing (medianGrid (warmCodes p s width spacing g samples)))

end LongTails.Algorithms.DistributedLocalExtragradientWarmStart
