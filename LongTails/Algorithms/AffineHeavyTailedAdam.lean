import LongTails.Setups.AffineHeavyTailedAdam

namespace LongTails.Algorithms.AffineHeavyTailedAdam

open OracleTemplate LongTails.Setups.AffineHeavyTailedAdam

noncomputable def config (q : Params) : Config where
  β₁ := 9 / 10
  β₂ := 999 / 1000
  η := q.ε / (2 ^ 29 * (q.L0 + q.L1 * q.ε))
  δ := q.ε / (8 * (q.d + 1))
  batchSize := 1 + ⌈(2 ^ 17 * (q.σ1 + (∑ i, q.σ0 i) / q.ε)) ^ (q.p / (q.p - 1))⌉₊
  lastIndex := ⌈2 ^ 32 * q.Δ * (q.L0 + q.L1 * q.ε) / q.ε ^ 2⌉₊

noncomputable def trajectory {d : ℕ} (cfg : Config) (x0 : Point d) (selected : ℕ)
    (samples : ℕ → Point d) : ℕ → Adam.State d
  | 0 => ⟨selected, 0, x0, 0, 0, x0⟩
  | t + 1 => coreStep cfg (trajectory cfg x0 selected samples t) (samples t)

noncomputable def batchReply {d : ℕ} {Ω : Type} (cfg : Config)
    (g : Point d → Ω → Point d) (x : Point d) (ξ : Fin cfg.batchSize → Ω) : Point d :=
  (cfg.batchSize : ℝ)⁻¹ • ∑ i, g x (ξ i)

noncomputable def process {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (selected : ℕ)
    (g : Point d → Ω → Point d) (ξ : ℕ → Fin cfg.batchSize → Ω) : ℕ → Adam.State d
  | 0 => ⟨selected, 0, x0, 0, 0, x0⟩
  | t + 1 => coreStep cfg (process cfg x0 selected g ξ t)
      (batchReply cfg g (process cfg x0 selected g ξ t).point (ξ t))

noncomputable def output (q : Params) (O : Oracle (Point q.d) (Point q.d))
    (selected : Fin ((config q).lastIndex + 1)) (ξ : (k : ℕ) → O.Seed k) : Point q.d :=
  execute O (method (config q) q.x0)
    (fun _ => (config q).batchSize * ((config q).lastIndex + 1)) selected ξ

end LongTails.Algorithms.AffineHeavyTailedAdam
