import LongTails.Setups.SelfConcordantBFGS
import LongTails.Algorithms.SelfConcordantBFGS
import LongTails.Proofs.SelfConcordantBFGSAccuracy

namespace LongTails.Theorems.SelfConcordantBFGS

open OracleTemplate LongTails.Setups.SelfConcordantBFGS LongTails.Algorithms.SelfConcordantBFGS
open LongTails.Proofs.SelfConcordantBFGSExecution LongTails.Proofs.SelfConcordantBFGSAccuracy

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 21 * (q.d + 1) * (q.Δ + 1) * ((q.Δ + 1) / (q.c1 ^ 3 * min q.c1 (1 - q.c2) ^ 2) + (q.d + 1) / (q.c1 * min q.c1 (1 - q.c2) ^ 4)) + 10 * q.Φ0 / min q.c1 (1 - q.c2) ^ 2 + 4 * Real.log (64 + 2 / q.ε) / min q.c1 (1 - q.c2)⌉₊ + 2

theorem result : Convergence LongTails.Setups.SelfConcordantBFGS.spec budget := by
  refine ⟨method, ?_, fun p _ => rfl⟩
  intro q hq I O hO
  obtain ⟨hc1, hc12, hc2, hB0, hΔ0, hΦ0, hε⟩ := hq
  obtain ⟨hD, hconv, hx0, Df, D2f, D3f, hSC, ⟨xs, hxs, hmin⟩, hlow, hmis, horc⟩ := hO
  refine ⟨xs, hxs, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  cases seed
  set K := ⌈2 ^ 21 * (q.d + 1) * (q.Δ + 1) * ((q.Δ + 1) / (q.c1 ^ 3 * min q.c1 (1 - q.c2) ^ 2) +
    (q.d + 1) / (q.c1 * min q.c1 (1 - q.c2) ^ 4)) + 10 * q.Φ0 / min q.c1 (1 - q.c2) ^ 2 +
    4 * Real.log (64 + 2 / q.ε) / min q.c1 (1 - q.c2)⌉₊ with hK
  change execute O (bfgs q.x0 q.B0) (fun _ => K + 1 + 1) () ξ ∈ I.D ∧
    I.f (execute O (bfgs q.x0 q.B0) (fun _ => K + 1 + 1) () ξ) - I.f xs ≤ q.ε
  rw [execute_eq_run]
  apply accuracy hc1 hc12 hc2 hB0 hΔ0 hΦ0 hε hD hconv hx0 hSC hlow hmis horc hxs (K + 1)
  have hc := Nat.le_ceil (2 ^ 21 * (q.d + 1) * (q.Δ + 1) * ((q.Δ + 1) /
    (q.c1 ^ 3 * min q.c1 (1 - q.c2) ^ 2) + (q.d + 1) / (q.c1 * min q.c1 (1 - q.c2) ^ 4)) +
    10 * q.Φ0 / min q.c1 (1 - q.c2) ^ 2 + 4 * Real.log (64 + 2 / q.ε) / min q.c1 (1 - q.c2))
  rw [← hK] at hc
  push_cast
  linarith

end LongTails.Theorems.SelfConcordantBFGS
