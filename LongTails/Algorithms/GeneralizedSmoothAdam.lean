import LongTails.Setups.GeneralizedSmoothAdam

namespace LongTails.Algorithms.GeneralizedSmoothAdam

open OracleTemplate LongTails.Setups.GeneralizedSmoothAdam

noncomputable def stepScale (p : Params) : ℝ :=
  (1 - p.β) ^ 2 / (2 ^ 20 * (p.d + 1) * (1 + 4 * (1 + p.L0 + p.L1)) ^ 2)

noncomputable def algorithm (p : Params) (T : ℕ) :
    Algorithm (Adam.Point p.d) (Adam.Point p.d) (Adam.Point p.d) :=
  method p.β (1 / T) (stepScale p / Real.sqrt T) 1 (1 + p.σ ^ 2) (T - 1) p.x0

noncomputable def trajectory {d : ℕ} {Ω : Type*} (g : Adam.Point d → Ω → Adam.Point d)
    (β ρ η τ vinit : ℝ) (x0 : Adam.Point d) (ξ : ℕ → Ω) :
    ℕ → Adam.Point d × Adam.Point d × Adam.Point d
  | 0 => (x0, 0, WithLp.toLp 2 (fun _ => vinit))
  | t + 1 =>
      let s := trajectory g β ρ η τ vinit x0 ξ t
      let reply := g s.1 (ξ t)
      let m := β • s.2.1 + (1 - β) • reply
      let v := Adam.secondMomentStep ρ s.2.2 reply
      (s.1 - η • Adam.direction τ m v, m, v)

noncomputable def output (p : Params) (T : ℕ) (O : Oracle (Adam.Point p.d) (Adam.Point p.d))
    (selected : (algorithm p T).Seed) (ξ : (k : ℕ) → O.Seed k) : Adam.Point p.d :=
  execute O (algorithm p T) (fun _ => T) selected ξ

end LongTails.Algorithms.GeneralizedSmoothAdam
