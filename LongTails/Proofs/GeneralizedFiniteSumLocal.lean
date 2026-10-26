import LongTails.Setups.GeneralizedSmoothFiniteSum
import LongTails.Proofs.CompositeGeneralizedLocal
import LongTails.Proofs.RelativeGeneralizedLocal
import LongTails.Proofs.SvrgConvex
import LongTails.Proofs.GeneralizedFiniteSumSampling

open Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.GeneralizedFiniteSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma snapshot_cocoercive {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1) (s y : E)
    (hr : L1 * ‖y - s‖ ≤ 1 / 8) :
    ‖g s - g y‖ ^ 2 ≤ 12 * (L0 + L1 * ‖g s‖) *
      (f s - f y - ⟪g y, s - y⟫) := by
  have ha : 0 ≤ L0 + L1 * ‖g s‖ := by positivity
  have hd := CompositeGeneralized.ball_lipschitz h0.le h1 hg hs
    (x := s) (u := s) (v := y) (r := ‖y - s‖) (by linarith)
    (by simp) le_rfl
  rw [norm_sub_rev s y] at hd
  have hd' := mul_le_mul_of_nonneg_left hd h1
  have ht := mul_le_mul_of_nonneg_left hr ha
  have hsmall : L1 * ‖g s - g y‖ ≤ (L0 + L1 * ‖g s‖) / 4 := by
    nlinarith
  have hb : 0 ≤ f s - f y - ⟪g y, s - y⟫ :=
    sub_nonneg.mpr (Gradient.convex_support hc hf y s)
  have hcoef : 8 * (L0 + L1 * ‖g s‖ + L1 * ‖g s - g y‖) ≤
      12 * (L0 + L1 * ‖g s‖) := by nlinarith
  exact (CompositeGeneralized.shifted_cocoercive h0 h1 hc hf hg hs y s).trans
    (mul_le_mul_of_nonneg_right hcoef hb)

lemma component_curvature {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1) (u s : E) :
    L0 + L1 * ‖g s‖ ≤ 3 * (L0 + L1 * ‖g u‖) +
      34 * L1 ^ 2 * (f s - f u - ⟪g u, s - u⟫) := by
  let D := f s - f u - ⟪g u, s - u⟫
  let a := L0 + L1 * ‖g u‖
  let d := ‖g s - g u‖
  have hD : 0 ≤ D := sub_nonneg.mpr (Gradient.convex_support hc hf u s)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have hn : ‖g s‖ ≤ ‖g u‖ + d := by
    have := norm_le_norm_sub_add (g s) (g u)
    dsimp [d]
    linarith
  have hb := CompositeGeneralized.shifted_cocoercive h0 h1 hc hf hg hs u s
  have hcoef : L0 + L1 * ‖g s‖ + L1 * d ≤ a + (2 * L1) * d := by
    dsimp [a]
    nlinarith [mul_le_mul_of_nonneg_left hn h1]
  have hsquare : d ^ 2 ≤ 8 * (a + (2 * L1) * d) * D := by
    exact hb.trans (by gcongr)
  have hbound := RelativeGeneralized.scalar_gradient_gap hd ha
    (show 0 ≤ 2 * L1 by positivity) hD hsquare
  have hyr : L1 * Real.sqrt (a * D) ≤ (a + L1 ^ 2 * D) / 2 := by
    rw [Real.sqrt_mul ha]
    have hsa := Real.sq_sqrt ha
    have hsD := Real.sq_sqrt hD
    nlinarith [sq_nonneg (Real.sqrt a - L1 * Real.sqrt D)]
  have hm := mul_le_mul_of_nonneg_left hbound h1
  dsimp [a, D] at *
  nlinarith [mul_le_mul_of_nonneg_left hn h1]

lemma average_curvature {n : ℕ} [NeZero n] {f : Fin n → E → ℝ}
    {g : Fin n × E → E} {L0 L1 G : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hf : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hg : ∀ i, Continuous (fun x => g (i, x)))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (fun x => g (i, x)) L0 L1)
    {u : E} (hu : IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) univ u)
    (hG : Finset.univ.expect (fun i : Fin n => ‖g (i, u)‖) ≤ G) (s : E) :
    Finset.univ.expect (fun i : Fin n => L0 + L1 * ‖g (i, s)‖) ≤ 3 * (L0 + L1 * G) +
      34 * L1 ^ 2 * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f s -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f u) := by
  have he := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => component_curvature h0 h1 (hc i) (hf i) (hg i) (hs i) u s)
  have hz := FiniteSum.fullGradient_minimizer hf hu
  unfold FiniteSum.fullGradient at hz
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const,
    Finset.expect_sub_distrib, FiniteSum.expect_inner_left, hz, inner_zero_left,
    sub_zero, ← FiniteSum.objective_eq_expect] at he
  have hm := mul_le_mul_of_nonneg_left hG h1
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  linarith

lemma local_direction_variance {n : ℕ} [NeZero n] {f : Fin n → E → ℝ}
    {g : Fin n → E → E} {L0 L1 : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hf : ∀ i x, HasGradientAt (f i) (g i x) x) (hg : ∀ i, Continuous (g i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (g i) L0 L1) (s y : E)
    (hr : L1 * ‖y - s‖ ≤ 1 / 8) :
    let w := snapshotWeights L0 L1 (fun i => g i s)
    ((2 * n).factorial : ℝ)⁻¹ *
      (∑ seed : Fin ((2 * n).factorial),
        ‖direction w (fun i => g i s) (drawIndex w seed) (g (drawIndex w seed) y) -
          (n : ℝ)⁻¹ • ∑ i, g i y‖ ^ 2) ≤
      24 * ((∑ i, w i) / n) *
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f s -
          LongTails.Setups.FiniteSumSmoothAndConvex.objective f y -
          ⟪(n : ℝ)⁻¹ • ∑ i, g i y, s - y⟫) := by
  classical
  let w := snapshotWeights L0 L1 (fun i => g i s)
  let H := fun i => f i s - f i y - ⟪g i y, s - y⟫
  have hw (i : Fin n) : 0 ≤ w i := by dsimp [w, snapshotWeights]; positivity
  have hH (i : Fin n) : 0 ≤ H i := sub_nonneg.mpr (Gradient.convex_support (hc i) (hf i) y s)
  have hd (i : Fin n) : ‖g i y - g i s‖ ^ 2 ≤ 12 * w i * H i := by
    rw [norm_sub_rev]
    exact snapshot_cocoercive h0 h1 (hc i) (hf i) (hg i) (hs i) s y hr
  have hv := direction_variance w (fun i => g i s) (fun i => g i y) H 12 hw hH (by norm_num) hd
  have he : (∑ i, H i) / n =
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f s -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f y -
        ⟪(n : ℝ)⁻¹ • ∑ i, g i y, s - y⟫ := by
    simp only [H, Finset.sum_sub_distrib, LongTails.Setups.FiniteSumSmoothAndConvex.objective,
      real_inner_smul_left, sum_inner, sub_div]
    ring
  rw [he] at hv
  simpa only [show (2 : ℝ) * 12 = 24 by norm_num, w] using hv

lemma aggregate_local_upper {n : ℕ} {f : Fin n → E → ℝ}
    {g : Fin n → E → E} {L0 L1 : ℝ}
    (h0 : 0 ≤ L0) (h1 : 0 ≤ L1)
    (hf : ∀ i x, HasGradientAt (f i) (g i x) x) (hg : ∀ i, Continuous (g i))
    (hs : ∀ i, CompositeGeneralized.SymmetricSmooth (g i) L0 L1)
    (s y out : E) (hy : L1 * ‖y - s‖ ≤ 1 / 2) (ho : L1 * ‖out - s‖ ≤ 1 / 2) :
    LongTails.Setups.FiniteSumSmoothAndConvex.objective f out ≤
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f y +
      ⟪(n : ℝ)⁻¹ • ∑ i, g i y, out - y⟫ +
      ((Finset.univ.sum (fun i : Fin n => L0 + L1 * ‖g i s‖)) / n) * ‖out - y‖ ^ 2 := by
  have hr : L1 * max ‖y - s‖ ‖out - s‖ ≤ 1 / 2 := by
    rcases le_total ‖y - s‖ ‖out - s‖ with h | h
    · simpa only [max_eq_right h] using ho
    · simpa only [max_eq_left h] using hy
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    CompositeGeneralized.ball_upper h0 h1 (hf i) (hg i) (hs i) hr
      (le_max_left _ _) (le_max_right _ _))
  simp only [Finset.expect_add_distrib, ← Finset.expect_mul, FiniteSum.expect_inner_left,
    ← FiniteSum.objective_eq_expect] at hh
  simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, Finset.sum_add_distrib, add_div] using hh

omit [CompleteSpace E] in
lemma weighted_full_gradient_norm {n : ℕ} [NeZero n] (g : Fin n → E)
    {L0 L1 : ℝ} (h0 : 0 ≤ L0) (h1 : 0 ≤ L1) :
    L1 * ‖(n : ℝ)⁻¹ • ∑ i, g i‖ ≤ (Finset.univ.sum (fun i : Fin n => L0 + L1 * ‖g i‖)) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  have hh := mul_le_mul_of_nonneg_left (norm_sum_le (s := Finset.univ) (f := g)) h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply (le_div_iff₀ hn).mpr
  have he : L1 * ((n : ℝ)⁻¹ * ‖∑ i, g i‖) * n = L1 * ‖∑ i, g i‖ := by field_simp
  rw [he]
  nlinarith

end OracleTemplate.GeneralizedFiniteSum
