import LongTails.Proofs.RecursiveMomentumConvergence

namespace OracleTemplate.RecursiveMomentumGapBatch

open RecursiveMomentum LongTails.Setups.AffineVarianceMeanSquaredSmooth

noncomputable def batch (L Lbar Γ Λ Δ ε : ℝ) : ℕ :=
  ⌈8 * (Λ / ε) ^ 2 + 64 * Γ * ((L + Lbar) * Δ / ε ^ 2)⌉₊ + 1

noncomputable def horizon (L Lbar Γ Λ Δ ε : ℝ) : ℕ :=
  ⌈20 * (1 + 3 * Γ + 6 * (Λ / ε)) * ((L + Lbar) * Δ / ε ^ 2)⌉₊

noncomputable def algorithm (q : Params) :=
  recursiveMomentum (mGamma q.L q.Lbar q.Γ q.Λ q.ε) (1 / mInvA q.Γ q.Λ q.ε)
    (batch q.L q.Lbar q.Γ q.Λ q.Δ q.ε) (horizon q.L q.Lbar q.Γ q.Λ q.Δ q.ε) q.x0

end OracleTemplate.RecursiveMomentumGapBatch
