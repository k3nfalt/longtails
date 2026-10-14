import LongTails.Setups.DouglasRachfordSmoothConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.AcceleratedDouglasRachfordExecution

namespace OracleTemplate.DouglasRachford

open LongTails.Setups.DouglasRachfordSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * ⌈Real.sqrt (2 * q.R ^ 2 / (q.lam * q.γ * q.ε))⌉₊

theorem result : Convergence LongTails.Setups.DouglasRachfordSmoothConvex.spec budget := by
  apply convergence_of_block_budget (S := spec)
    (fun q => ⌈Real.sqrt (2 * q.R ^ 2 / (q.lam * q.γ * q.ε))⌉₊)
    (fun _ => 2)
  refine ⟨acceleratedDouglasRachford, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hγ, hlam0, hlam1, hstep, hR, hε⟩
  intro N hN
  rintro I O
    ⟨-, hlow, hup, hC, hg, hpf, hpg, xs, hxs, hmin, hdist⟩
  refine ⟨xs, hxs, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨seed, ξ⟩
    exact execute_accuracy q I O ⟨hL, hγ, hlam0, hlam1, hstep, hlow, hup, hC, hg, hxs, hmin⟩
      hR hε hpf hpg hdist seed ξ N hN

end OracleTemplate.DouglasRachford
