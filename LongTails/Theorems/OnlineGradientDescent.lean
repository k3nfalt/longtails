import LongTails.Setups.OnlineConvexBoundedGradient
import LongTails.Proofs.OnlineGradientDescent

namespace OracleTemplate.OnlineGradientDescent

open LongTails.Setups.OnlineConvexBoundedGradient

noncomputable def bound (p : Params) (T : Horizon) : ℝ := p.D * p.G * Real.sqrt T

theorem result : OnlineConvergence LongTails.Setups.OnlineConvexBoundedGradient.spec bound := by
  refine ⟨algorithm, ?_, fun _ _ _ => trivial⟩
  intro p T hp losses O ho
  dsimp only
  have h := execution_success (spec.publicInput p T) hp losses O ho
  intro seed
  exact (h seed.1 seed.2).2

end OracleTemplate.OnlineGradientDescent
