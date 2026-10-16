import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OracleTemplate.WeakMintyPicard

lemma power_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {K : ℕ}
    (hK : (4 / δ) * Real.log (1024 / δ ^ 2) ≤ K) :
    (1 - δ / 4) ^ K ≤ δ ^ 2 / 1024 := by
  have hq : 0 ≤ 1 - δ / 4 := by linarith
  have he : 1 - δ / 4 ≤ Real.exp (-δ / 4) := by
    have := Real.add_one_le_exp (-δ / 4)
    linarith
  have hp := pow_le_pow_left₀ hq he K
  rw [← Real.exp_nat_mul] at hp
  have hmul := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ δ / 4)
  have hid : δ / 4 * ((4 / δ) * Real.log (1024 / δ ^ 2)) =
      Real.log (1024 / δ ^ 2) := by field_simp
  rw [hid] at hmul
  have hlog : (K : ℝ) * (-δ / 4) ≤ -Real.log (1024 / δ ^ 2) := by linarith
  have hexp : Real.exp (-Real.log (1024 / δ ^ 2)) = δ ^ 2 / 1024 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  exact hp.trans ((Real.exp_le_exp.mpr hlog).trans_eq hexp)

lemma relative_factor {δ a q : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 ≤ a) (hcap : a ≤ δ ^ 2 / 1024) (hq : q ≤ 1) :
    (1 + q) * a ≤ (δ / 16) * (1 - a) := by
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hqa := mul_le_mul_of_nonneg_right hq ha
  have hδa := mul_le_mul_of_nonneg_right hδ1 ha
  nlinarith

variable {E : Type*} [NormedAddCommGroup E]

lemma relative_residual (T : E → E) (x y z : E) {q a θ : ℝ}
    (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hz : T z = z)
    (hT : ∀ u v, ‖T u - T v‖ ≤ q * ‖u - v‖)
    (hy : ‖y - z‖ ≤ a * ‖x - z‖)
    (hfactor : (1 + q) * a ≤ θ * (1 - a)) :
    ‖y - T y‖ ≤ θ * ‖y - x‖ := by
  have h1 : ‖y - T y‖ ≤ ‖y - z‖ + ‖z - T y‖ := by
    simpa [dist_eq_norm] using dist_triangle y z (T y)
  have h2 := hT y z
  rw [norm_sub_rev z (T y)] at h1
  rw [hz] at h2
  have h3 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    simpa [dist_eq_norm] using dist_triangle x y z
  rw [norm_sub_rev x y] at h3
  have h4 := mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ 1 + q)
  have h5 := mul_le_mul_of_nonneg_right hfactor (norm_nonneg (x - z))
  have h6 := mul_le_mul_of_nonneg_left
    (show (1 - a) * ‖x - z‖ ≤ ‖y - x‖ by nlinarith) hθ
  nlinarith

lemma iterate_residual [CompleteSpace E] (T : E → E) (x : E) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hT : ∀ u v, ‖T u - T v‖ ≤ (1 - δ / 4) * ‖u - v‖) {K : ℕ}
    (hK : (4 / δ) * Real.log (1024 / δ ^ 2) ≤ K) :
    ‖T^[K] x - T (T^[K] x)‖ ≤ (δ / 16) * ‖T^[K] x - x‖ := by
  let q : NNReal := NNReal.mk (1 - δ / 4) (by linarith)
  have hc : ContractingWith q T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul (fun u v => ?_)⟩
    · change 1 - δ / 4 < 1
      linarith
    · simpa only [dist_eq_norm, q, NNReal.coe_mk] using hT u v
  let z := hc.fixedPoint T
  have hz : T z = z := hc.fixedPoint_isFixedPt
  have hi : T^[K] z = z := by
    clear hK
    induction K with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hz]
  have hdist := (hc.2.iterate K).dist_le_mul x z
  rw [hi] at hdist
  have hy : ‖T^[K] x - z‖ ≤ (1 - δ / 4) ^ K * ‖x - z‖ := by
    simpa only [dist_eq_norm, NNReal.coe_pow, q, NNReal.coe_mk] using hdist
  exact relative_residual T x (T^[K] x) z (by linarith) (by positivity) hz hT hy
    (relative_factor hδ hδ1 (pow_nonneg (by linarith) K) (power_bound hδ hδ1 hK)
      (by linarith))

end OracleTemplate.WeakMintyPicard
