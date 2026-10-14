import LongTails.Algorithms.Clipping

namespace OracleTemplate.ClippedExtragradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def stepSize (b S : ℝ) (g : E) : ℝ :=
  1 / (16 * max S (b * ‖g‖))

noncomputable def halfStep (b S : ℝ) (x g : E) : E :=
  x - stepSize b S g • g

noncomputable def finishStep (d γ : ℝ) (c x g : E) : E :=
  c + clip (2 * d) (x - γ • g - c)

noncomputable def regularizedReply (r : ℝ) (c x g : E) : E :=
  g + r • (x - c)

end OracleTemplate.ClippedExtragradient
