import LongTails.Setups.SpectralTwoTapLogistic
import LongTails.Proofs.SpectralTwoTapExecution

open OracleTemplate
open LongTails.Setups.SpectralTwoTapLogistic

namespace LongTails.Theorems.SpectralTwoTapGd

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) :=
  fun p _ => p.K + 2*⌈2*p.d/p.W⌉₊

theorem result : Convergence LongTails.Setups.SpectralTwoTapLogistic.spec budget := by
  refine ⟨LongTails.Algorithms.SpectralTwoTapGd.algorithm,?_,
    LongTails.Proofs.SpectralTwoTapExecution.allowed⟩
  intro p hp D O h
  dsimp only
  intro seed
  exact LongTails.Proofs.SpectralTwoTapExecution.succeeds p hp D O h seed.1 seed.2

end LongTails.Theorems.SpectralTwoTapGd
