import LongTails.Setups.BroxGeneralNormConstrainedPL
import LongTails.Proofs.WarmHalvingBroxExecution

namespace OracleTemplate.WarmHalvingBrox

open LongTails.Setups.BroxGeneralNormConstrainedPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p i =>
  let K := ⌊Real.logb 4 (1 + 6 * p.Δ / (p.L * p.r ^ 2))⌋₊ +
    ⌈Real.logb (1 + p.μ / (25 * p.L)) (p.Δ / p.ε)⌉₊
  if i = 0 then K else 2 * K + ⌈Real.logb 4 (p.r ^ 2 * (8 * p.L ^ 2 / p.μ + 6 * p.L) / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.BroxGeneralNormConstrainedPL.spec budget := by
  refine ⟨fun q => algorithm q.L q.r q.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hμ, hε, hr⟩ I O ⟨hC, -, hx0, hd, hlip, hbdd, hpl, hΔ, hgradO, hlmoO⟩
  have H : Hyp I.f I.C p.L p.μ := ⟨hC, hd, hlip, hbdd, hpl, hL, hμ⟩
  refine Filter.Eventually.of_forall fun ω => ?_
  exact execute_success H hr hε hx0 hΔ O hgradO hlmoO (budget p) rfl rfl ω.1 ω.2

end OracleTemplate.WarmHalvingBrox
