import LongTails.Proofs.SlidingInner
import LongTails.Proofs.FrankWolfeDescent
import LongTails.Proofs.TwoSidedPLEnvelope

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_lower_support [CompleteSpace E] {Q : Set E} {f : E → ℝ}
    {g : E → E} {L : ℝ} (hQ : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) (c : E) :
    f x + L * ‖x - c‖ ^ 2 + ⟪g x + (2 * L) • (x - c), y - x⟫ +
      L / 2 * ‖y - x‖ ^ 2 ≤ f y + L * ‖y - c‖ ^ 2 := by
  have hn : ∀ z ∈ Q, ∀ w ∈ Q, ‖-g z - -g w‖ ≤ L * ‖z - w‖ := by
    intro z hz w hw
    rw [neg_sub_neg, norm_sub_rev]
    exact hlip z hz w hw
  have hs := FrankWolfe.smooth_upper_bound_on hQ
    (fun z hz => TwoSidedPL.hasGradientAt_neg' (hg z hz)) hn hx hy
  simp only [inner_neg_left] at hs
  have he : ‖y - c‖ ^ 2 = ‖x - c‖ ^ 2 + 2 * ⟪x - c, y - x⟫ + ‖y - x‖ ^ 2 := by
    rw [show y - c = (x - c) + (y - x) by abel, norm_add_sq_real]
  rw [inner_add_left, real_inner_smul_left, he]
  nlinarith

lemma envelope_quasar_transfer {f : E → ℝ} {x y u g : E} {L γ : ℝ}
    (hq : γ * (f y - f u) ≤ ⟪g, y - u⟫)
    (hn : 0 ≤ ⟪(2 * L) • (x - y) - g, y - u⟫) :
    γ * (f y + L * ‖x - y‖ ^ 2 - f u) ≤
      ⟪(2 * L) • (x - y), x - u⟫ - (2 - γ) * L * ‖x - y‖ ^ 2 := by
  rw [inner_sub_left] at hn
  have he : ⟪(2 * L) • (x - y), x - u⟫ =
      ⟪(2 * L) • (x - y), y - u⟫ + 2 * L * ‖x - y‖ ^ 2 := by
    rw [show x - u = (y - u) + (x - y) by abel, inner_add_right]
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [he]
  nlinarith

lemma envelope_gradient_lipschitz {x y u v : E} {L : ℝ} (hL : 0 ≤ L)
    (hp : ‖u - v‖ ^ 2 ≤ 2 * ⟪x - y, u - v⟫) :
    ‖(2 * L) • (x - u) - (2 * L) • (y - v)‖ ≤ 2 * L * ‖x - y‖ := by
  have hn : ‖(x - y) - (u - v)‖ ≤ ‖x - y‖ := by
    have he := norm_sub_sq_real (x - y) (u - v)
    nlinarith [norm_nonneg ((x - y) - (u - v)), norm_nonneg (x - y)]
  rw [← smul_sub, show (x - u) - (y - v) = (x - y) - (u - v) by abel,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * L)]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

lemma regularized_gradient_contraction {g : E → E} {u v x : E} {L : ℝ}
    (hL : 0 < L) (hg : ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ‖(u - (1 / (3 * L)) • (g u + (2 * L) • (u - x))) -
      (v - (1 / (3 * L)) • (g v + (2 * L) • (v - x)))‖ ≤
      (2 / 3 : ℝ) * ‖u - v‖ := by
  have hc : (1 / (3 * L)) * (2 * L) = (2 / 3 : ℝ) := by
    field_simp
  have he : (u - (1 / (3 * L)) • (g u + (2 * L) • (u - x))) -
      (v - (1 / (3 * L)) • (g v + (2 * L) • (v - x))) =
      (1 / 3 : ℝ) • (u - v) - (1 / (3 * L)) • (g u - g v) := by
    simp only [smul_add, smul_smul, hc]
    module
  rw [he]
  calc
    _ ≤ ‖(1 / 3 : ℝ) • (u - v)‖ + ‖(1 / (3 * L)) • (g u - g v)‖ :=
      norm_sub_le _ _
    _ = (1 / 3 : ℝ) * ‖u - v‖ + (1 / (3 * L)) * ‖g u - g v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3), abs_of_pos (by positivity)]
    _ ≤ (1 / 3 : ℝ) * ‖u - v‖ + (1 / (3 * L)) * (L * ‖u - v‖) := by
      gcongr
    _ = (2 / 3 : ℝ) * ‖u - v‖ := by
      field_simp
      ring

lemma projected_cleanup_gap {Q : Set E} {proj : E → E} {F : E → ℝ}
    {u v g e : E} {L : ℝ} (hQ : Convex ℝ Q)
    (hP : GeneralizedSliding.ProjectionOracle proj Q) (hv : v ∈ Q) (hL : 0 < L)
    (hlower : F u + ⟪g, v - u⟫ ≤ F v)
    (hupper : F (proj (u - (1 / L) • (g + e))) ≤ F u +
      ⟪g, proj (u - (1 / L) • (g + e)) - u⟫ +
      L / 2 * ‖proj (u - (1 / L) • (g + e)) - u‖ ^ 2) :
    F (proj (u - (1 / L) • (g + e))) - F v ≤
      L / 2 * (‖u - v‖ ^ 2 - ‖proj (u - (1 / L) • (g + e)) - v‖ ^ 2) +
      ⟪e, v - proj (u - (1 / L) • (g + e))⟫ := by
  have ht := GeneralizedSliding.inner_three_point hQ hP hL (le_refl (0 : ℝ))
    u u (g + e) hv
  simp only [GeneralizedSliding.innerTarget, add_zero, one_div_one, one_smul,
    zero_smul, mul_zero, zero_div, zero_mul, mul_one] at ht
  rw [inner_add_left] at ht
  have hg : ⟪g, proj (u - (1 / L) • (g + e)) - u⟫ - ⟪g, v - u⟫ =
      ⟪g, proj (u - (1 / L) • (g + e)) - v⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  have he : ⟪e, v - proj (u - (1 / L) • (g + e))⟫ =
      -⟪e, proj (u - (1 / L) • (g + e)) - v⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [norm_sub_rev v u] at ht
  rw [he]
  nlinarith

lemma projected_cleanup_diameter {Q : Set E} {proj : E → E} {F : E → ℝ}
    {u v g e : E} {L D : ℝ} (hQ : Convex ℝ Q)
    (hP : GeneralizedSliding.ProjectionOracle proj Q) (hv : v ∈ Q) (hL : 0 < L)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hlower : F u + ⟪g, v - u⟫ ≤ F v)
    (hupper : F (proj (u - (1 / L) • (g + e))) ≤ F u +
      ⟪g, proj (u - (1 / L) • (g + e)) - u⟫ +
      L / 2 * ‖proj (u - (1 / L) • (g + e)) - u‖ ^ 2) :
    F (proj (u - (1 / L) • (g + e))) - F v ≤ L / 2 * ‖u - v‖ ^ 2 + D * ‖e‖ := by
  have ht := projected_cleanup_gap hQ hP hv hL hlower hupper
  have hd := hdiam v hv _ (hP (u - (1 / L) • (g + e))).1
  have hi := real_inner_le_norm e (v - proj (u - (1 / L) • (g + e)))
  have hn := mul_le_mul_of_nonneg_left hd (norm_nonneg e)
  have hs := mul_nonneg hL.le (sq_nonneg ‖proj (u - (1 / L) • (g + e)) - v‖)
  nlinarith

end OracleTemplate.StochasticQuasar
