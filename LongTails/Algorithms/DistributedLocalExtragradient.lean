import LongTails.Setups.DistributedJacobianStrongGrowth
import LongTails.Algorithms.LocalNonlinearExtragradient
import LongTails.Algorithms.LocalExtragradientQuantization
import LongTails.Proofs.Clipping

namespace LongTails.Algorithms.DistributedLocalExtragradient

open LongTails.Setups.DistributedJacobianStrongGrowth

noncomputable def blockOutput (p : Params) (T N : ℕ) (H : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω) : Point p :=
  (1 / (p.n : ℝ)) • ∑ i : Fin p.n, (x + OracleTemplate.clip H
    (LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
      (fun k => samples (N + (p.n * k + i.val))) T - x))

noncomputable def projectBall (p : Params) (center : Point p) (radius : ℝ) (x : Point p) : Point p :=
  center + OracleTemplate.clip radius (x - center)

noncomputable def localizedOutput (p : Params) (center : Point p) (r : ℝ) (x : Point p) : Point p :=
  projectBall p p.x0 p.R (projectBall p center (r / 2) x)

noncomputable def roundedBlockOutput (p : Params) (T N : ℕ) (H : ℝ)
    (width : ℕ) (spacing : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω) : Point p :=
  x + LocalExtragradientQuantization.quantizedAverage p.n p.d width spacing
    (fun i => OracleTemplate.clip H
      (LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) x
        (fun k => samples (N + (p.n * k + i.val))) T - x))

noncomputable def projectedBlockOutput (p : Params) (T N : ℕ) (H : ℝ)
    (width : ℕ) (spacing : ℝ) (center : Point p) (r : ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω) : Point p :=
  localizedOutput p center r (roundedBlockOutput p T N H width spacing g x samples)

end LongTails.Algorithms.DistributedLocalExtragradient
