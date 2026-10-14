import LongTails.Setups.NearZeroSumGames
import LongTails.Proofs.NearZeroSumCalculus
import LongTails.Proofs.NearZeroSumProjection
import LongTails.Proofs.NearZeroSumConjugate

open Set InnerProductSpace
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma slice_x_gradient {X : Set E} {Y : Set F} {f : WithLp 2 (E × F) → ℝ}
    {g : WithLp 2 (E × F)} {x : E} {y : F} (hy : y ∈ Y)
    (hf : HasGradientWithinAt f g {z | z.fst ∈ X ∧ z.snd ∈ Y} (WithLp.toLp 2 (x, y))) :
    HasGradientWithinAt (fun v => f (WithLp.toLp 2 (v, y))) g.fst X x := by
  let T : E →L[ℝ] WithLp 2 (E × F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E F)
  have heq : ∀ v, T v + WithLp.toLp 2 (0, y) = WithLp.toLp 2 (v, y) := by
    intro v
    apply WithLp.ofLp_injective 2
    simp [T]
  have h := gradient_comp_affine_within T (f := f) (g := g) (b := WithLp.toLp 2 (0, y))
    (x := x) (S := X) (C := {z | z.fst ∈ X ∧ z.snd ∈ Y})
    (by simpa only [heq] using hf)
    (fun v hv => by rw [heq]; exact ⟨hv, hy⟩)
    (q := g.fst) (by intro v; simp [T, WithLp.prod_inner_apply])
  simpa only [heq] using h

lemma slice_y_gradient {X : Set E} {Y : Set F} {f : WithLp 2 (E × F) → ℝ}
    {g : WithLp 2 (E × F)} {x : E} {y : F} (hx : x ∈ X)
    (hf : HasGradientWithinAt f g {z | z.fst ∈ X ∧ z.snd ∈ Y} (WithLp.toLp 2 (x, y))) :
    HasGradientWithinAt (fun v => f (WithLp.toLp 2 (x, v))) g.snd Y y := by
  let T : F →L[ℝ] WithLp 2 (E × F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ E F)
  have heq : ∀ v, T v + WithLp.toLp 2 (x, 0) = WithLp.toLp 2 (x, v) := by
    intro v
    apply WithLp.ofLp_injective 2
    simp [T]
  have h := gradient_comp_affine_within T (f := f) (g := g) (b := WithLp.toLp 2 (x, 0))
    (x := y) (S := Y) (C := {z | z.fst ∈ X ∧ z.snd ∈ Y})
    (by simpa only [heq] using hf)
    (fun v hv => by rw [heq]; exact ⟨hx, hv⟩)
    (q := g.snd) (by intro v; simp [T, WithLp.prod_inner_apply])
  simpa only [heq] using h

lemma strong_x_support {X : Set E} {Y : Set F} {f : WithLp 2 (E × F) → ℝ}
    {g : WithLp 2 (E × F)} {x v : E} {y : F} {μ : ℝ}
    (hc : StrongConvexOn X μ (fun u => f (WithLp.toLp 2 (u, y))))
    (hx : x ∈ X) (hv : v ∈ X) (hy : y ∈ Y)
    (hf : HasGradientWithinAt f g {z | z.fst ∈ X ∧ z.snd ∈ Y} (WithLp.toLp 2 (x, y))) :
    f (WithLp.toLp 2 (x, y)) + ⟪g.fst, v - x⟫ + μ / 2 * ‖v - x‖ ^ 2 ≤
      f (WithLp.toLp 2 (v, y)) :=
  strong_support_within hc hx hv (slice_x_gradient hy hf)

lemma strong_y_support {X : Set E} {Y : Set F} {f : WithLp 2 (E × F) → ℝ}
    {g : WithLp 2 (E × F)} {x : E} {y v : F} {ν : ℝ}
    (hc : StrongConvexOn Y ν (fun u => -f (WithLp.toLp 2 (x, u))))
    (hx : x ∈ X) (hy : y ∈ Y) (hv : v ∈ Y)
    (hf : HasGradientWithinAt f g {z | z.fst ∈ X ∧ z.snd ∈ Y} (WithLp.toLp 2 (x, y))) :
    f (WithLp.toLp 2 (x, v)) ≤
      f (WithLp.toLp 2 (x, y)) + ⟪g.snd, v - y⟫ - ν / 2 * ‖v - y‖ ^ 2 := by
  have h := strong_support_within hc hy hv (gradient_neg_within (slice_y_gradient hx hf))
  simp only [inner_neg_left] at h
  linarith

omit [CompleteSpace E] [CompleteSpace F] in

lemma saddle_monotonicity_of_support {h : E → F → ℝ} {μ ν : ℝ}
    {x₁ x₂ gx₁ gx₂ : E} {y₁ y₂ gy₁ gy₂ : F}
    (hx₁ : h x₁ y₁ + ⟪gx₁, x₂ - x₁⟫ + μ / 2 * ‖x₂ - x₁‖ ^ 2 ≤ h x₂ y₁)
    (hx₂ : h x₂ y₂ + ⟪gx₂, x₁ - x₂⟫ + μ / 2 * ‖x₁ - x₂‖ ^ 2 ≤ h x₁ y₂)
    (hy₁ : h x₁ y₂ ≤ h x₁ y₁ + ⟪gy₁, y₂ - y₁⟫ - ν / 2 * ‖y₂ - y₁‖ ^ 2)
    (hy₂ : h x₂ y₁ ≤ h x₂ y₂ + ⟪gy₂, y₁ - y₂⟫ - ν / 2 * ‖y₁ - y₂‖ ^ 2) :
    μ * ‖x₁ - x₂‖ ^ 2 + ν * ‖y₁ - y₂‖ ^ 2 ≤
      ⟪gx₁ - gx₂, x₁ - x₂⟫ - ⟪gy₁ - gy₂, y₁ - y₂⟫ := by
  rw [norm_sub_rev x₂ x₁] at hx₁
  rw [norm_sub_rev y₂ y₁] at hy₁
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

lemma game_monotonicity {p : Public} {I : Problem p} {H G : Space p → Space p}
    (hx : ∀ y ∈ p.Y, StrongConvexOn p.X p.μ (fun x => I.h (WithLp.toLp 2 (x, y))))
    (hy : ∀ x ∈ p.X, StrongConvexOn p.Y p.ν (fun y => -I.h (WithLp.toLp 2 (x, y))))
    (hgc : ConvexOn ℝ (domain p) I.g)
    (hh : ∀ z ∈ domain p, HasGradientWithinAt I.h (H z) (domain p) z)
    (hg : ∀ z ∈ domain p, HasGradientWithinAt I.g (G z) (domain p) z)
    {z w : Space p} (hz : z ∈ domain p) (hw : w ∈ domain p) :
    p.μ * ‖z.fst - w.fst‖ ^ 2 + p.ν * ‖z.snd - w.snd‖ ^ 2 ≤
      ⟪ownGradient H G z - ownGradient H G w, z - w⟫ := by
  have h₁ := strong_x_support (hx z.snd hz.2) hz.1 hw.1 hz.2 (hh z hz)
  have h₂ := strong_x_support (hx w.snd hw.2) hw.1 hz.1 hw.2 (hh w hw)
  have h₃ := strong_y_support (hy z.fst hz.1) hz.1 hz.2 hw.2 (hh z hz)
  have h₄ := strong_y_support (hy w.fst hw.1) hw.1 hw.2 hz.2 (hh w hw)
  have hs := saddle_monotonicity_of_support
    (h := fun x y => I.h (WithLp.toLp 2 (x, y))) (μ := p.μ) (ν := p.ν) h₁ h₂ h₃ h₄
  have hg₁ := convex_support_within hgc hz hw (hg z hz)
  have hg₂ := convex_support_within hgc hw hz (hg w hw)
  simp only [ownGradient, WithLp.prod_inner_apply,
    inner_sub_left, inner_sub_right, inner_add_left,
    inner_neg_left] at hg₁ hg₂ ⊢
  simp only [inner_sub_left, inner_sub_right] at hs
  simp only [WithLp.fst, WithLp.snd] at hg₁ hg₂ hs ⊢
  linarith

omit [CompleteSpace E] [CompleteSpace F] in
omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma pair_norm_le (x : E) (y : F) : ‖WithLp.toLp 2 (x, y)‖ ≤ ‖x‖ + ‖y‖ := by
  have h := norm_add_le (WithLp.toLp 2 (x, (0 : F))) (WithLp.toLp 2 ((0 : E), y))
  simpa only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add,
    WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using h

lemma own_gradient_lipschitz {p : Public} {H G : Space p → Space p} {z w : Space p} {L : ℝ}
    (hplus : ‖(H z + G z) - (H w + G w)‖ ≤ L * ‖z - w‖)
    (hminus : ‖(H z - G z) - (H w - G w)‖ ≤ L * ‖z - w‖) :
    ‖ownGradient H G z - ownGradient H G w‖ ≤ 2 * L * ‖z - w‖ := by
  have he : ownGradient H G z - ownGradient H G w =
      WithLp.toLp 2 (((H z + G z) - (H w + G w)).fst,
        -((H z - G z) - (H w - G w)).snd) := by
    apply WithLp.ofLp_injective 2
    ext <;> simp only [ownGradient, WithLp.ofLp_sub, Prod.fst_sub,
      Prod.snd_sub, WithLp.sub_fst, WithLp.sub_snd, WithLp.add_fst]
    module
  rw [he]
  have h := pair_norm_le (((H z + G z) - (H w + G w)).fst)
    (-((H z - G z) - (H w - G w)).snd)
  rw [norm_neg] at h
  have h₁ := (WithLp.norm_fst_le p.E ((H z + G z) - (H w + G w))).trans hplus
  have h₂ := (WithLp.norm_snd_le p.E ((H z - G z) - (H w - G w))).trans hminus
  linarith

lemma cross_gradient_error {p : Public} {G : Space p → Space p} {x xs : p.E} {y : p.F}
    {δ : ℝ} (hlip : ‖G (WithLp.toLp 2 (x, y)) - G (WithLp.toLp 2 (xs, y))‖ ≤
      δ * ‖WithLp.toLp 2 (x, y) - WithLp.toLp 2 (xs, y)‖) :
    ‖(2 : ℝ) • ((G (WithLp.toLp 2 (x, y))).snd - (G (WithLp.toLp 2 (xs, y))).snd)‖ ≤
      2 * δ * ‖x - xs‖ := by
  have h := (WithLp.norm_snd_le p.E (G (WithLp.toLp 2 (x, y)) -
    G (WithLp.toLp 2 (xs, y)))).trans hlip
  simp only [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_fst,
    WithLp.sub_snd] at h
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

lemma equilibrium_normal {p : Public} {I : Problem p} {H G : Space p → Space p}
    (hx : Convex ℝ p.X) (hy : Convex ℝ p.Y) {z : Space p} (hz : IsEquilibrium I z)
    (hh : HasGradientWithinAt I.h (H z) (domain p) z)
    (hg : HasGradientWithinAt I.g (G z) (domain p) z) :
    ConstrainedMonotone.Normal (domain p) z (-ownGradient H G z) := by
  have hdx := gradient_add_within (slice_x_gradient hz.1.2 hh) (slice_x_gradient hz.1.2 hg)
  have hdy := gradient_add_within (slice_y_gradient hz.1.1 hg)
    (gradient_neg_within (slice_y_gradient hz.1.1 hh))
  have hxg := minimizer_gradient_normal hx hz.1.1 hz.2.1 hdx
  have hyg := minimizer_gradient_normal hy hz.1.2
    (show ∀ y ∈ p.Y, I.g z + -I.h z ≤
      I.g (WithLp.toLp 2 (z.fst, y)) + -I.h (WithLp.toLp 2 (z.fst, y)) by
      simpa only [sub_eq_add_neg] using hz.2.2) hdy
  intro w hw
  have hxw := hxg w.fst hw.1
  have hyw := hyg w.snd hw.2
  simp only [inner_add_left, inner_neg_left] at hxw hyw
  simp only [ownGradient, inner_neg_left, WithLp.prod_inner_apply,
    inner_add_left, inner_neg_left]
  simp only [WithLp.fst, WithLp.snd, WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub] at hxw hyw ⊢
  linarith

lemma domain_convex {p : Public} (hx : Convex ℝ p.X) (hy : Convex ℝ p.Y) :
    Convex ℝ (domain p) := by
  intro u hu v hv a b ha hb hab
  exact ⟨hx hu.1 hv.1 ha hb hab, hy hu.2 hv.2 ha hb hab⟩

lemma domain_compact {p : Public} (hx : IsCompact p.X) (hy : IsCompact p.Y) :
    IsCompact (domain p) := by
  have he : domain p = WithLp.toLp 2 '' (p.X ×ˢ p.Y) := by
    ext z
    constructor
    · intro hz
      exact ⟨z.ofLp, hz, rfl⟩
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact hxy
  rw [he]
  exact (hx.prod hy).image (WithLp.prod_continuous_toLp 2 p.E p.F)

lemma product_normal {p : Public} {z n : Space p} (hz : z ∈ domain p)
    (hn : ConstrainedMonotone.Normal (domain p) z n) :
    ConstrainedMonotone.Normal p.X z.fst n.fst ∧
      ConstrainedMonotone.Normal p.Y z.snd n.snd := by
  constructor
  · intro x hx
    have h := hn (WithLp.toLp 2 (x, z.snd)) ⟨hx, hz.2⟩
    simpa [WithLp.prod_inner_apply] using h
  · intro y hy
    have h := hn (WithLp.toLp 2 (z.fst, y)) ⟨hz.1, hy⟩
    simpa [WithLp.prod_inner_apply] using h

noncomputable def shiftedGame {p : Public} (I : Problem p) (a b : ℝ) (x : p.E) (y : p.F) : ℝ :=
  I.h (WithLp.toLp 2 (x, y)) + I.g (WithLp.toLp 2 (x, y)) - a / 2 * ‖x‖ ^ 2 + b / 2 * ‖y‖ ^ 2

lemma shifted_game_x_support {p : Public} {I : Problem p} {H G : Space p → Space p}
    {x v : p.E} {y : p.F} {a b : ℝ}
    (hx : x ∈ p.X) (hv : v ∈ p.X) (hy : y ∈ p.Y)
    (hc : StrongConvexOn p.X p.μ (fun u => I.h (WithLp.toLp 2 (u, y))))
    (hgc : ConvexOn ℝ (domain p) I.g)
    (hh : HasGradientWithinAt I.h (H (WithLp.toLp 2 (x, y))) (domain p) (WithLp.toLp 2 (x, y)))
    (hg : HasGradientWithinAt I.g (G (WithLp.toLp 2 (x, y))) (domain p) (WithLp.toLp 2 (x, y))) :
    shiftedGame I a b x y +
      ⟪(H (WithLp.toLp 2 (x, y))).fst + (G (WithLp.toLp 2 (x, y))).fst - a • x, v - x⟫ +
      (p.μ - a) / 2 * ‖v - x‖ ^ 2 ≤ shiftedGame I a b v y := by
  have h₁ := strong_x_support hc hx hv hy hh
  have h₂ := convex_support_within hgc (show WithLp.toLp 2 (x, y) ∈ domain p from ⟨hx, hy⟩)
    (show WithLp.toLp 2 (v, y) ∈ domain p from ⟨hv, hy⟩) hg
  have hsum : (I.h (WithLp.toLp 2 (x, y)) + I.g (WithLp.toLp 2 (x, y))) +
      ⟪(H (WithLp.toLp 2 (x, y))).fst + (G (WithLp.toLp 2 (x, y))).fst, v - x⟫ +
      p.μ / 2 * ‖v - x‖ ^ 2 ≤ I.h (WithLp.toLp 2 (v, y)) + I.g (WithLp.toLp 2 (v, y)) := by
    simp [WithLp.prod_inner_apply, inner_sub_right] at h₂
    simp only [inner_add_left, inner_sub_right, WithLp.fst] at h₁ h₂ ⊢
    linarith
  have h := shifted_lower_support (f := fun u => I.h (WithLp.toLp 2 (u, y)) + I.g (WithLp.toLp 2 (u, y))) (a := a) hsum
  dsimp [shiftedGame]
  linarith

lemma shifted_game_y_support {p : Public} {I : Problem p} {H G : Space p → Space p}
    {x : p.E} {y v : p.F} {a b : ℝ}
    (hx : x ∈ p.X) (hy : y ∈ p.Y) (hv : v ∈ p.Y)
    (hX : Convex ℝ p.X) (hY : Convex ℝ p.Y)
    (hc : StrongConvexOn p.Y p.ν (fun u => -I.h (WithLp.toLp 2 (x, u))))
    (hh : HasGradientWithinAt I.h (H (WithLp.toLp 2 (x, y))) (domain p) (WithLp.toLp 2 (x, y)))
    (hg : ∀ z ∈ domain p, HasGradientWithinAt I.g (G z) (domain p) z)
    (hlip : ∀ z ∈ domain p, ∀ w ∈ domain p, ‖G z - G w‖ ≤ p.δ * ‖z - w‖) :
    shiftedGame I a b x v ≤ shiftedGame I a b x y +
      ⟪(H (WithLp.toLp 2 (x, y))).snd + (G (WithLp.toLp 2 (x, y))).snd + b • y, v - y⟫ -
      (p.ν - p.δ - b) / 2 * ‖v - y‖ ^ 2 := by
  have h₁ := strong_y_support hc hx hy hv hh
  have h₂ := smooth_upper_within (domain_convex hX hY) hg hlip
    (show WithLp.toLp 2 (x, y) ∈ domain p from ⟨hx, hy⟩)
    (show WithLp.toLp 2 (x, v) ∈ domain p from ⟨hx, hv⟩)
  have hsum : I.h (WithLp.toLp 2 (x, v)) + I.g (WithLp.toLp 2 (x, v)) ≤
      (I.h (WithLp.toLp 2 (x, y)) + I.g (WithLp.toLp 2 (x, y))) +
      ⟪(H (WithLp.toLp 2 (x, y))).snd + (G (WithLp.toLp 2 (x, y))).snd, v - y⟫ -
      (p.ν - p.δ) / 2 * ‖v - y‖ ^ 2 := by
    simp only [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_snd] at h₂
    simp only [WithLp.prod_inner_apply, inner_sub_right] at h₂
    simp only [inner_add_left, inner_sub_right, inner_zero_right, zero_add, WithLp.snd] at h₁ h₂ ⊢
    linarith
  have h := shifted_upper_support (f := fun u => I.h (WithLp.toLp 2 (x, u)) + I.g (WithLp.toLp 2 (x, u))) (b := b) hsum
  dsimp [shiftedGame]
  linarith


lemma game_fast_support {p : Public} {I : Problem p} {H G : Space p → Space p}
    {x₁ x₂ xs z₁ z₂ nx : p.E} {y₁ y₂ ny : p.F} {a b c : ℝ}
    (ha : 0 < a) (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    (hX : Convex ℝ p.X) (hY : Convex ℝ p.Y)
    (hx₁ : x₁ ∈ p.X) (hx₂ : x₂ ∈ p.X) (hxs : xs ∈ p.X)
    (hy₁ : y₁ ∈ p.Y) (hy₂ : y₂ ∈ p.Y)
    (hcx : ∀ y ∈ p.Y, StrongConvexOn p.X p.μ (fun x => I.h (WithLp.toLp 2 (x, y))))
    (hcy : ∀ x ∈ p.X, StrongConvexOn p.Y p.ν (fun y => -I.h (WithLp.toLp 2 (x, y))))
    (hgc : ConvexOn ℝ (domain p) I.g)
    (hh : ∀ u ∈ domain p, HasGradientWithinAt I.h (H u) (domain p) u)
    (hg : ∀ u ∈ domain p, HasGradientWithinAt I.g (G u) (domain p) u)
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖G u - G v‖ ≤ p.δ * ‖u - v‖)
    (hnx : ConstrainedMonotone.Normal p.X x₂ nx)
    (hny : ConstrainedMonotone.Normal p.Y y₁ ny)
    (hz : z₂ = (ownGradient H G (WithLp.toLp 2 (x₂, y₂))).fst - a • x₂ + nx) :
    fastValue (shiftedGame I a b) (fun y => I.g (WithLp.toLp 2 (xs, y))) a b x₁ z₁ y₁ +
      ⟪x₁ + (1 / a) • z₁, z₂ - z₁⟫ +
      ⟪(ownGradient H G (WithLp.toLp 2 (x₁, y₁))).snd + ny -
        (2 : ℝ) • ((G (WithLp.toLp 2 (x₁, y₁))).snd - (G (WithLp.toLp 2 (xs, y₁))).snd), y₂ - y₁⟫ +
      ‖z₂ - z₁‖ ^ 2 / (2 * a) + (b + c) / 2 * ‖y₂ - y₁‖ ^ 2 +
      a / 2 * ‖x₂ - x₁‖ ^ 2 ≤
        fastValue (shiftedGame I a b) (fun y => I.g (WithLp.toLp 2 (xs, y))) a b x₂ z₂ y₂ := by
  have hxx := shifted_game_x_support hx₂ hx₁ hy₂ (hcx y₂ hy₂) hgc
    (hh _ ⟨hx₂, hy₂⟩) (hg _ ⟨hx₂, hy₂⟩) (a := a) (b := b)
  have hyy := shifted_game_y_support hx₁ hy₁ hy₂ hX hY (hcy x₁ hx₁)
    (hh _ ⟨hx₁, hy₁⟩) hg hlip (a := a) (b := b)
  rw [hμ, show 2 * a - a = a by ring] at hxx
  rw [hν] at hyy
  have hq := convex_support_within hgc
    (show WithLp.toLp 2 (xs, y₁) ∈ domain p from ⟨hxs, hy₁⟩)
    (show WithLp.toLp 2 (xs, y₂) ∈ domain p from ⟨hxs, hy₂⟩) (hg _ ⟨hxs, hy₁⟩)
  have hqq : I.g (WithLp.toLp 2 (xs, y₁)) +
      ⟪(G (WithLp.toLp 2 (xs, y₁))).snd, y₂ - y₁⟫ ≤ I.g (WithLp.toLp 2 (xs, y₂)) := by
    simpa [WithLp.prod_inner_apply, add_comm] using (le_sub_iff_add_le.mp hq)
  have h := fast_value_support_of_normal (q := fun y => I.g (WithLp.toLp 2 (xs, y))) (z₁ := z₁) (b := b) ha hxx hyy (hnx x₁ hx₁) (hny y₂ hy₂) hz hqq
  have he : (ownGradient H G (WithLp.toLp 2 (x₁, y₁))).snd + ny -
      (2 : ℝ) • ((G (WithLp.toLp 2 (x₁, y₁))).snd - (G (WithLp.toLp 2 (xs, y₁))).snd) =
      -((H (WithLp.toLp 2 (x₁, y₁))).snd + (G (WithLp.toLp 2 (x₁, y₁))).snd + b • y₁) + ny + b • y₁ +
        (2 : ℝ) • (G (WithLp.toLp 2 (xs, y₁))).snd := by
    simp only [ownGradient, WithLp.snd, WithLp.ofLp_toLp]
    module
  rw [he]
  exact h


structure GameGeometry (p : Public) (I : Problem p) (H G : Space p → Space p) : Prop where
  convexX : Convex ℝ p.X
  convexY : Convex ℝ p.Y
  strongX : ∀ y ∈ p.Y, StrongConvexOn p.X p.μ (fun x => I.h (WithLp.toLp 2 (x, y)))
  strongY : ∀ x ∈ p.X, StrongConvexOn p.Y p.ν (fun y => -I.h (WithLp.toLp 2 (x, y)))
  convexG : ConvexOn ℝ (domain p) I.g
  gradientH : ∀ u ∈ domain p, HasGradientWithinAt I.h (H u) (domain p) u
  gradientG : ∀ u ∈ domain p, HasGradientWithinAt I.g (G u) (domain p) u
  lipschitzG : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖G u - G v‖ ≤ p.δ * ‖u - v‖

def FastValid {p : Public} (H G : Space p → Space p) (a : ℝ) (x z : p.E) (y : p.F) : Prop :=
  x ∈ p.X ∧ y ∈ p.Y ∧ ∃ nx, ConstrainedMonotone.Normal p.X x nx ∧
    z = (ownGradient H G (WithLp.toLp 2 (x, y))).fst - a • x + nx

noncomputable def gameGap {p : Public} (I : Problem p) (a b : ℝ) (xs : p.E) (ys : p.F)
    (x z : p.E) (y : p.F) : ℝ :=
  fastValue (shiftedGame I a b) (fun y => I.g (WithLp.toLp 2 (xs, y))) a b x z y -
    fastValue (shiftedGame I a b) (fun y => I.g (WithLp.toLp 2 (xs, y))) a b xs (-a • xs) ys

lemma game_gap_nonnegative {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    {x z : p.E} {y : p.F} (hv : FastValid H G a x z y) :
    0 ≤ gameGap I a b xs ys x z y := by
  obtain ⟨hx, hy, nx, hnx, hz⟩ := hv
  have hnormal := product_normal hs hns
  have h := game_fast_support ha hμ hν geom.convexX geom.convexY hs.1 hx hs.1 hs.2 hy
    geom.strongX geom.strongY geom.convexG geom.gradientH geom.gradientG geom.lipschitzG
    hnx hnormal.2 hz (z₁ := -a • xs)
  have he : xs + (1 / a) • (-a • xs) = 0 := by
    rw [smul_smul]
    have heq : (1 / a) * -a = -1 := by field_simp
    rw [heq]
    module
  simp only [WithLp.fst, WithLp.snd] at h
  simp only [he, inner_zero_left, sub_self, smul_zero,
    WithLp.ofLp_neg, Prod.snd_neg, add_neg_cancel] at h
  have h₁ : 0 ≤ ‖z - -a • xs‖ ^ 2 / (2 * a) := by positivity
  have h₂ : 0 ≤ (b + c) / 2 * ‖y - ys‖ ^ 2 := by positivity
  have h₃ : 0 ≤ a / 2 * ‖x - xs‖ ^ 2 := by positivity
  dsimp [gameGap]
  linarith

end OracleTemplate.NearZeroSum
