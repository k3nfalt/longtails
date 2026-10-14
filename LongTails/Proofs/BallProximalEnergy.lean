import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.BallProximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_progress {f : E → ℝ} {x y : E} {c t : ℝ}
    (hs : f y + ⟪c • (x - y), x - y⟫ ≤ f x)
    (hn : ‖x - y‖ = t) : c * t ^ 2 ≤ f x - f y := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hn] at hs
  linarith

lemma radial_distance {f : E → ℝ} {x y z : E} {c t : ℝ}
    (hs : f y + ⟪c • (x - y), z - y⟫ ≤ f z)
    (hn : ‖x - y‖ = t) :
    c * ‖y - z‖ ^ 2 + c * t ^ 2 + 2 * (f y - f z) ≤ c * ‖x - z‖ ^ 2 := by
  have he : ‖x - z‖ ^ 2 = t ^ 2 + 2 * ⟪x - y, y - z⟫ + ‖y - z‖ ^ 2 := by
    rw [show x - z = (x - y) + (y - z) by module, norm_add_sq_real, hn]
  rw [real_inner_smul_left, show z - y = -(y - z) by module, inner_neg_right] at hs
  rw [he]
  nlinarith

lemma radial_terminal {f : E → ℝ} {x y z : E} {c t : ℝ}
    (hc : 0 ≤ c) (hs : f y + ⟪c • (x - y), z - y⟫ ≤ f z)
    (hn : ‖x - y‖ = t) : f y - f z ≤ c * t * ‖y - z‖ := by
  have hi := real_inner_le_norm (x - y) (y - z)
  rw [hn] at hi
  rw [real_inner_smul_left, show z - y = -(y - z) by module, inner_neg_right] at hs
  have hm := mul_le_mul_of_nonneg_left hi hc
  nlinarith

lemma radial_norm_antitone {f : E → ℝ} {x y z : E} {c d t u : ℝ}
    (hc : 0 ≤ c) (hu : 0 < u)
    (hxy : ‖x - y‖ = t) (hyz : ‖y - z‖ = u)
    (hsy : f y + ⟪c • (x - y), z - y⟫ ≤ f z)
    (hsz : f z + ⟪d • (y - z), y - z⟫ ≤ f y) : d * u ≤ c * t := by
  have hi := real_inner_le_norm (x - y) (y - z)
  rw [hxy, hyz] at hi
  have hm := mul_le_mul_of_nonneg_left hi hc
  rw [real_inner_smul_left, show z - y = -(y - z) by module, inner_neg_right] at hsy
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hyz] at hsz
  have hh : d * u ^ 2 ≤ c * (t * u) := by linarith
  nlinarith

end OracleTemplate.BallProximal
