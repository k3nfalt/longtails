import LongTailsOnline.Setups.StochasticBandit
import LongTailsOnline.Proofs.UcbRegret

namespace LongTailsOnline.Theorems.Ucb

open LongTailsOnline.Setups.StochasticBandit

noncomputable def method : (p : spec.Public) →
    OnlineTemplate.Algorithm (spec.Observation p) (spec.Action p) (spec.Feedback p) :=
  LongTailsOnline.Algorithms.Ucb.algorithm

noncomputable def bound : (p : spec.Params) → spec.Bound p := fun p => ((∑ i, if 0 < gap p i then 8 * Real.log (p.T + 1 : ℝ) / gap p i + 2 * gap p i else 0) + 5 * (p.k + 1 : ℝ)) / p.T

theorem result : OnlineTemplate.Guarantee LongTailsOnline.Setups.StochasticBandit.spec method bound := by
  refine ⟨fun _ _ => trivial, ?_⟩
  rintro p ⟨_, hμ, hbest⟩ P E ⟨hP, rfl⟩
  refine ⟨Filter.Eventually.of_forall (fun _ _ => trivial),
    LongTailsOnline.Proofs.Ucb.integrable_regret hμ hbest _, ?_⟩
  exact div_le_div_of_nonneg_right
    (LongTailsOnline.Proofs.Ucb.expected_regret_le hP hμ hbest) (Nat.cast_nonneg _)

end LongTailsOnline.Theorems.Ucb
