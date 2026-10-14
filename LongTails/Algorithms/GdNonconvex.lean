import LongTails.Setups.SmoothNonconvex

namespace OracleTemplate.NonconvexGradient

open LongTails.Setups.SmoothNonconvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def bestGradientStep (L : ℝ) (s : E × E × ℝ) (g : E) : E × E × ℝ :=
  (s.1 - (1 / L) • g, if ‖g‖ ^ 2 ≤ s.2.2 then (s.1, ‖g‖ ^ 2) else s.2)

noncomputable def gdBest : (ℝ × ℝ × ℝ × E) → Algorithm E E E
  | (L, Δ, _, x0) => {
      State := E × E × ℝ
      initial _ := (x0, x0, 2 * L * Δ)
      query := fun s => (0, (Prod.fst) s)
      update := bestGradientStep L
      output := fun s => s.2.1 }

end OracleTemplate.NonconvexGradient
