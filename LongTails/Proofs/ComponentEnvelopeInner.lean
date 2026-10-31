import LongTails.Proofs.ComponentEnvelopeGeometry
import LongTails.Proofs.CompositeGeneralizedLocal
import LongTails.Proofs.RecursiveEnvelopeGeometry

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.ComponentEnvelope

open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma regularized_support {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (μ : ℝ) (c x y : E) :
    regularized f μ c x + ⟪g x + μ • (x - c), y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤
      regularized f μ c y := by
  unfold regularized
  rw [squared_shift x y c, inner_add_left, real_inner_smul_left]
  linarith [Gradient.convex_support hc hg x y]

lemma regularized_trial_gap {f : E → ℝ} {g : E → E} {L0 L1 μ η : ℝ}
    (h0 : 0 ≤ L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hg : ∀ x, HasGradientAt f (g x) x) (hcont : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c x p : E)
    (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y)
    (hsmall : η * (L0 + μ + L1 * ‖g x‖) ≤ 1 / 16)
    (hr : L1 * (2 * η * ‖g x + μ • (x - c)‖) ≤ 1 / 2) :
    7 / 4 * η * ‖g x + μ • (x - c)‖ ^ 2 ≤
      regularized f μ c x - regularized f μ c p := by
  set r := g x + μ • (x - c)
  set y := x - (2 * η) • r
  have hy : y - x = -(2 * η) • r := by dsimp [y]; module
  have hn : ‖y - x‖ = 2 * η * ‖r‖ := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have hu := CompositeGeneralized.ball_upper h0 h1 hg hcont hs
    (x := x) (u := x) (v := y) hr (by simp; positivity) hn.le
  have hu' : regularized f μ c y ≤ regularized f μ c x +
      ⟪r, y - x⟫ + (L0 + L1 * ‖g x‖ + μ / 2) * ‖y - x‖ ^ 2 := by
    unfold regularized
    rw [squared_shift x y c]
    dsimp [r]
    rw [inner_add_left, real_inner_smul_left]
    linarith
  rw [hy, inner_smul_right, real_inner_self_eq_norm_sq] at hu'
  rw [show ‖-(2 * η) • r‖ = 2 * η * ‖r‖ by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]] at hu'
  have hb : (L0 + L1 * ‖g x‖ + μ / 2) * η ≤ 1 / 16 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 4 * η * ‖r‖ ^ 2 by positivity)
  have hp := hmin y
  nlinarith

lemma regularized_fejer {f : E → ℝ} {g : E → E} {μ η : ℝ}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hη : 0 ≤ η) (c x p : E)
    (hgap : 7 / 4 * η * ‖g x + μ • (x - c)‖ ^ 2 ≤
      regularized f μ c x - regularized f μ c p) :
    ‖x - η • (g x + μ • (x - c)) - p‖ ^ 2 ≤
      (1 - μ * η) * ‖x - p‖ ^ 2 -
        5 / 2 * η ^ 2 * ‖g x + μ • (x - c)‖ ^ 2 := by
  have hs := regularized_support hc hg μ c x p
  have he : x - η • (g x + μ • (x - c)) - p =
      (x - p) - η • (g x + μ • (x - c)) := by module
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right]
  have hi : ⟪x - p, g x + μ • (x - c)⟫ = -⟪g x + μ • (x - c), p - x⟫ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  rw [hi, norm_sub_rev p x] at *
  have hm := mul_le_mul_of_nonneg_left hs hη
  have hb := mul_le_mul_of_nonneg_left hgap hη
  nlinarith

lemma regularized_observable_fejer {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c x p : E) (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) :
    let r := g x + μ • (x - c)
    let η := 1 / (16 * (L0 + μ + L1 * ‖g x‖ + L1 * ‖r‖))
    ‖x - η • r - p‖ ^ 2 ≤
      (1 - μ * η) * ‖x - p‖ ^ 2 - 5 / 2 * η ^ 2 * ‖r‖ ^ 2 := by
  dsimp only
  set r := g x + μ • (x - c)
  set B := L0 + μ + L1 * ‖g x‖ + L1 * ‖r‖
  have hB : 0 < B := by dsimp [B]; positivity
  have hη : 0 ≤ 1 / (16 * B) := by positivity
  apply regularized_fejer hc hg hη c x p
  apply regularized_trial_gap h0.le h1 hμ hη hg hcont hs c x p hmin
  · have hb : L0 + μ + L1 * ‖g x‖ ≤ B := by
      dsimp [B]; nlinarith [mul_nonneg h1 (norm_nonneg r)]
    have hh : (L0 + μ + L1 * ‖g x‖) / (16 * B) ≤ 1 / 16 := by
      apply (div_le_iff₀ (by positivity : 0 < 16 * B)).mpr
      linarith
    convert hh using 1
    field_simp
  · change L1 * (2 * (1 / (16 * B)) * ‖r‖) ≤ 1 / 2
    have hb : L1 * ‖r‖ ≤ B := by
      dsimp [B]; nlinarith [mul_nonneg h1 (norm_nonneg (g x))]
    have hh : (L1 * ‖r‖) / (8 * B) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 8 * B)).mpr
      linarith
    convert hh using 1
    ring_nf


omit [CompleteSpace E] in
lemma regularized_denominator_bound {g : E → E} {L0 L1 μ : ℝ}
    (h1 : 0 ≤ L1) (hμ : 0 ≤ μ) (c x p : E)
    (hd : ‖x - p‖ ≤ ‖c - p‖) :
    L0 + μ + L1 * ‖g x‖ + L1 * ‖g x + μ • (x - c)‖ ≤
      L0 + μ + 2 * μ * L1 * ‖c - p‖ + 2 * L1 * ‖g x + μ • (x - c)‖ := by
  have hxc : ‖x - c‖ ≤ 2 * ‖c - p‖ := by
    have ht := norm_sub_le (x - p) (c - p)
    have he : (x - p) - (c - p) = x - c := by module
    rw [he] at ht
    linarith
  have he : g x = (g x + μ • (x - c)) - μ • (x - c) := by module
  have ht := norm_sub_le (g x + μ • (x - c)) (μ • (x - c))
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ] at ht
  have hb := mul_le_mul_of_nonneg_left hxc hμ
  have hg : ‖g x‖ ≤ ‖g x + μ • (x - c)‖ + 2 * μ * ‖c - p‖ := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hg h1
  nlinarith

lemma inner_cost_majorant {q ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    q ^ 2 + (1 + q) * ℓ ≤ 3 * ℓ * (1 + q ^ 2) := by
  have hq := sq_nonneg (q - 1)
  have ht := mul_nonneg (show 0 ≤ ℓ - 1 by linarith) (sq_nonneg q)
  have hm := mul_le_mul_of_nonneg_right (show 2 * q ≤ 1 + q ^ 2 by nlinarith)
    (show 0 ≤ ℓ by linarith)
  nlinarith [mul_nonneg (show 0 ≤ ℓ by linarith) (sq_nonneg q)]


end OracleTemplate.ComponentEnvelope
