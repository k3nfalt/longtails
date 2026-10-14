import LongTails.Proofs.CompositeProx
import LongTails.Algorithms.Katyusha
import LongTails.Proofs.AcceleratedVariance
import LongTails.Proofs.AcceleratedFiniteSum

open Set
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadratic_young {L : ℝ} (hL : 0 < L) (a b : E) :
    ⟪a, b⟫ ≤ L * ‖b‖ ^ 2 + ‖a‖ ^ 2 / (4 * L) := by
  have h := sq_nonneg ‖a - (2 * L) • b‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at h
  have he : ‖a‖ ^ 2 / (4 * L) * (4 * L) = ‖a‖ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma model_descent {f ψ : E → ℝ} {L : ℝ} (hL : 0 < L)
    {x y G v : E}
    (hmodel : f y ≤ f x + ⟪G, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hprox : IsMinOn (Composite.proxObjective ψ (1 / (3 * L)) x v) univ y)
    (w : E) :
    f y + ψ y ≤ f x + ψ x + 3 * L / 2 * ‖w - x‖ ^ 2 + ⟪v, w - x⟫ +
      ψ w - ψ x + ‖G - v‖ ^ 2 / (4 * L) := by
  have hy : Composite.proxObjective ψ (1 / (3 * L)) x v y ≤
      Composite.proxObjective ψ (1 / (3 * L)) x v w := hprox (mem_univ w)
  have he (t : ℝ) : t / (2 * (1 / (3 * L))) = (3 * L / 2) * t := by
    field_simp
  simp only [Composite.proxObjective, he] at hy
  have hn := quadratic_young hL (G - v) (y - x)
  rw [inner_sub_left] at hn
  nlinarith

lemma convex_mix {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτh : τ ≤ 1 / 2) (snapshot y z : E) :
    ψ (mix τ snapshot (y, z)) ≤ τ * ψ z + (1 / 2) * ψ snapshot +
      (1 / 2 - τ) * ψ y := by
  have h₁ := hψ.2 (mem_univ z) (mem_univ y)
    (show 0 ≤ 2 * τ by positivity) (show 0 ≤ 1 - 2 * τ by linarith)
    (show 2 * τ + (1 - 2 * τ) = 1 by ring)
  have h₂ := hψ.2 (mem_univ ((2 * τ) • z + (1 - 2 * τ) • y))
    (mem_univ snapshot) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hx : (1 / 2 : ℝ) • ((2 * τ) • z + (1 - 2 * τ) • y) +
      (1 / 2 : ℝ) • snapshot = mix τ snapshot (y, z) := by dsimp [mix]; module
  rw [hx] at h₂
  simp only [smul_eq_mul] at h₁ h₂
  linarith

lemma coupling_raw {f ψ : E → ℝ} {τ α L μ : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hα : 0 < α) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2)
    (htune : 3 * α * L * τ ≤ 1) (hψ : StrongConvexOn univ μ ψ)
    (snapshot y z u G v ynext znext : E)
    (hmodel : f ynext ≤ f (mix τ snapshot (y, z)) +
      ⟪G, ynext - mix τ snapshot (y, z)⟫ + L / 2 * ‖ynext - mix τ snapshot (y, z)‖ ^ 2)
    (hy : IsMinOn (Composite.proxObjective ψ (1 / (3 * L)) (mix τ snapshot (y, z)) v)
      univ ynext)
    (hz : IsMinOn (Composite.proxObjective ψ α z v) univ znext)
    (hsy : ⟪G, y - mix τ snapshot (y, z)⟫ ≤ f y - f (mix τ snapshot (y, z)))
    (hsu : ⟪G, u - mix τ snapshot (y, z)⟫ ≤ f u - f (mix τ snapshot (y, z))) :
    f ynext + ψ ynext + τ / (2 * α) * (1 + α * μ) * ‖znext - u‖ ^ 2 ≤
      (1 / 2 - τ) * (f y + ψ y) + 1 / 2 * (f snapshot + ψ snapshot) +
      τ * (f u + ψ u) + τ / (2 * α) * ‖z - u‖ ^ 2 +
      τ * ⟪G - v, z - u⟫ + ‖G - v‖ ^ 2 / (4 * L) -
      1 / 2 * (f snapshot - f (mix τ snapshot (y, z)) -
        ⟪G, snapshot - mix τ snapshot (y, z)⟫) := by
  let x := mix τ snapshot (y, z)
  let w := mix τ snapshot (y, znext)
  have hwx : w - x = τ • (znext - z) := by dsimp [w, x, mix]; module
  have hcψ : ConvexOn ℝ univ ψ := (strongConvexOn_zero.mp (hψ.mono hμ))
  have hd := model_descent hL hmodel hy w
  change f ynext + ψ ynext ≤ f x + ψ x + 3 * L / 2 * ‖w - x‖ ^ 2 +
    ⟪v, w - x⟫ + ψ w - ψ x + ‖G - v‖ ^ 2 / (4 * L) at hd
  rw [hwx, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_pow, inner_smul_right] at hd
  have hc := convex_mix hcψ hτ.le hτh snapshot y znext
  change ψ w ≤ _ at hc
  have hm := Composite.prox_three_point hα hψ hz u
  have hm' : τ * (⟪v, znext - u⟫ + ψ znext - ψ u) ≤
      τ / (2 * α) * ‖z - u‖ ^ 2 - τ / (2 * α) * (1 + α * μ) * ‖znext - u‖ ^ 2 -
      τ / (2 * α) * ‖znext - z‖ ^ 2 := by
    calc
      _ = τ / α * (α * (⟪v, znext - u⟫ + ψ znext - ψ u)) := by field_simp
      _ ≤ τ / α * (‖z - u‖ ^ 2 / 2 - (1 + α * μ) / 2 * ‖znext - u‖ ^ 2 -
          ‖znext - z‖ ^ 2 / 2) := mul_le_mul_of_nonneg_left hm (div_nonneg hτ.le hα.le)
      _ = _ := by ring
  have hi : ⟪v, znext - u⟫ = ⟪v, znext - z⟫ + ⟪v, z - u⟫ := by
    rw [← inner_add_right]
    congr 1
    module
  rw [hi] at hm'
  have hid : τ * ⟪G, z - u⟫ =
      -(1 / 2 : ℝ) * ⟪G, snapshot - x⟫ - (1 / 2 - τ) * ⟪G, y - x⟫ -
      τ * ⟪G, u - x⟫ := by
    simp only [← inner_smul_right, ← inner_sub_right]
    congr 1
    dsimp [x, mix]
    module
  have hsy' := mul_le_mul_of_nonneg_left hsy (show 0 ≤ 1 / 2 - τ by linarith)
  have hsu' := mul_le_mul_of_nonneg_left hsu hτ.le
  have hcancel : 3 * L / 2 * τ ^ 2 * ‖znext - z‖ ^ 2 ≤
      τ / (2 * α) * ‖znext - z‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (le_div_iff₀ (by positivity : 0 < 2 * α)).mpr
    nlinarith [mul_le_mul_of_nonneg_left htune hτ.le]
  dsimp only [x] at hd hid hsy' hsu' ⊢
  rw [inner_sub_left]
  nlinarith only [hd, hc, hm', hid, hsy', hsu', hcancel]

variable [CompleteSpace E]

lemma expected_step {n : ℕ} [NeZero n] {f : Fin n → E → ℝ} {ψ : E → ℝ}
    {g : Fin n × E → E} {prox : ℝ → E → E → E} {τ α L μ : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hα : 0 < α) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2)
    (htune : 3 * α * L * τ ≤ 1)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (hψ : StrongConvexOn univ μ ψ)
    (hp : ∀ a, 0 < a → ∀ z v, IsMinOn (Composite.proxObjective ψ a z v) univ (prox a z v))
    (snapshot y z u : E) :
    let F := fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x + ψ x
    let next := fun i => advance τ α L prox snapshot (y, z) (FiniteSum.estimator g snapshot
      (mix τ snapshot (y, z)) i)
    (𝔼 i, (F (next i).1 - F u + τ / (2 * α) * (1 + α * μ) * ‖(next i).2 - u‖ ^ 2)) ≤
      (1 / 2 - τ) * (F y - F u) + 1 / 2 * (F snapshot - F u) +
        τ / (2 * α) * ‖z - u‖ ^ 2 := by
  dsimp only
  let x := mix τ snapshot (y, z)
  let G := FiniteSum.fullGradient g x
  let v := FiniteSum.estimator g snapshot x
  let ynext := fun i => prox (1 / (3 * L)) x (v i)
  let znext := fun i => prox α z (v i)
  have hpoint (i : Fin n) := coupling_raw hL hμ hα hτ hτh htune hψ
    snapshot y z u G (v i) (ynext i) (znext i)
    (Gradient.smooth_upper_bound (FiniteSum.objective_gradient hg)
      (FiniteSum.fullGradient_lipschitz hlip) x (ynext i))
    (hp _ (by positivity) x (v i)) (hp α hα z (v i))
    (Gradient.convex_support (FiniteSum.objective_convex hc)
      (FiniteSum.objective_gradient hg) x y)
    (Gradient.convex_support (FiniteSum.objective_convex hc)
      (FiniteSum.objective_gradient hg) x u)
  have hmean : (𝔼 i, ⟪G - v i, z - u⟫) = 0 := by
    simp only [inner_sub_left, Finset.expect_sub_distrib, Fintype.expect_const,
      FiniteSum.expect_inner_left, v, FiniteSum.estimator_unbiased, G, sub_self]
  have hvar : (𝔼 i, ‖G - v i‖ ^ 2) ≤
      2 * L * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f snapshot - LongTails.Setups.FiniteSumSmoothAndConvex.objective f x -
        ⟪G, snapshot - x⟫) := by
    simpa only [norm_sub_rev] using
      FiniteSum.estimator_variance_bound hL hc hg hlip snapshot x
  have hvar' := div_le_div_of_nonneg_right hvar (by positivity : 0 ≤ 4 * L)
  have hsimpl : 2 * L * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f snapshot - LongTails.Setups.FiniteSumSmoothAndConvex.objective f x -
      ⟪G, snapshot - x⟫) / (4 * L) =
      1 / 2 * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f snapshot - LongTails.Setups.FiniteSumSmoothAndConvex.objective f x -
        ⟪G, snapshot - x⟫) := by field_simp; ring
  rw [hsimpl] at hvar'
  have he := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    ← Finset.expect_div, Fintype.expect_const, hmean, mul_zero, add_zero] at he ⊢
  change (𝔼 i, LongTails.Setups.FiniteSumSmoothAndConvex.objective f (ynext i)) + (𝔼 i, ψ (ynext i)) -
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective f u + ψ u) +
      τ / (2 * α) * (1 + α * μ) * (𝔼 i, ‖znext i - u‖ ^ 2) ≤ _
  dsimp only [x] at hvar'
  nlinarith only [he, hvar']

end OracleTemplate.Katyusha
