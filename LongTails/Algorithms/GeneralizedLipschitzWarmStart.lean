import LongTails.Template
import LongTails.Proofs.Clipping

namespace LongTails.Algorithms.GeneralizedLipschitzWarmStart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev State (E : Type) := ℕ × E × E × ℝ

noncomputable def weight (α : ℝ) (k : ℕ) : ℝ := α * ((1 - α)⁻¹) ^ (k + 1)

noncomputable def point (α : ℝ) (s : State E) : E :=
  (1 - α) • s.2.1 + α • s.2.2.1

noncomputable def initial (center : E) (G0 : ℝ) : State E :=
  (0, center, center, G0 ^ 2)

noncomputable def update (center : E) (D α : ℝ) (s : State E) (reply : E) : State E :=
  let h := weight α s.1 • reply
  let energy := s.2.2.2 + ‖h‖ ^ 2
  (s.1 + 1, point α s,
    center + OracleTemplate.clip D (s.2.2.1 - (2 * D / Real.sqrt energy) • h - center), energy)

noncomputable def algorithm (center : E) (D G0 α : ℝ) : OracleTemplate.Algorithm E E E where
  State := State E
  initial _ := initial center G0
  query s := (0, point α s)
  update := update center D α
  output s := s.2.1

noncomputable def output (center : E) (D G0 α : ℝ) (K : ℕ) (O : OracleTemplate.Oracle E E)
    (ξ : (k : ℕ) → O.Seed k) : E :=
  OracleTemplate.execute O (algorithm center D G0 α) (fun _ => K) () ξ

noncomputable def trajectory {Ω : Type} (center : E) (D G0 α : ℝ)
    (oracle : E → Ω → E) (ξ : ℕ → Ω) : ℕ → State E
  | 0 => initial center G0
  | n + 1 =>
    let s := trajectory center D G0 α oracle ξ n
    update center D α s (oracle (point α s) (ξ n))

end LongTails.Algorithms.GeneralizedLipschitzWarmStart
