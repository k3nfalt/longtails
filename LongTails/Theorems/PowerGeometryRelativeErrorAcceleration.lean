import LongTails.Setups.PowerGeometryRelativeErrorConvex
import LongTails.Proofs.PowerDualAveragingRun

namespace LongTails.Theorems.PowerGeometryRelativeErrorAcceleration

open OracleTemplate LongTails.Setups.PowerGeometryRelativeErrorConvex
open LongTails.Algorithms.PowerDualAveraging LongTails.Proofs.PowerDualAveragingRun

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈(1536 * max 1 (32 ^ ((q.data.p - 2) / 2) / q.data.c) * q.data.L * q.R ^ 2 / q.ε) ^ (q.data.p / (q.data.p + 2)) + 4224 * q.data.L * q.data.α ^ 2 * q.R ^ 2 / q.ε⌉₊ + 1

theorem result : Convergence LongTails.Setups.PowerGeometryRelativeErrorConvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hd, hR, hε⟩ f O ⟨hf, hc, hlip, herr, u, hmin, hdist⟩
  refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  apply execute_accuracy q.data hd hf hc hlip O hε herr hmin hdist
    (T := budget q 0) (by dsimp [budget]; omega) ?_ seed ξ
  have heq : 12 * geometryConstant q.data * q.data.L * q.R ^ 2 / q.ε =
      1536 * max 1 (32 ^ ((q.data.p - 2) / 2) / q.data.c) * q.data.L * q.R ^ 2 / q.ε := by
    unfold geometryConstant
    ring
  rw [heq]
  have hh := Nat.le_ceil ((1536 * max 1 (32 ^ ((q.data.p - 2) / 2) / q.data.c) *
    q.data.L * q.R ^ 2 / q.ε) ^ (q.data.p / (q.data.p + 2)) +
    4224 * q.data.L * q.data.α ^ 2 * q.R ^ 2 / q.ε)
  dsimp [budget]
  push_cast
  linarith

end LongTails.Theorems.PowerGeometryRelativeErrorAcceleration
