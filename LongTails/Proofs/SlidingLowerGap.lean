import LongTails.Proofs.SlidingLowerOracle
import LongTails.Proofs.SlidingLowerMoreau
import LongTails.Proofs.GdConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SlidingLowerGap

open SlidingLowerChain SlidingLowerGeometry SlidingLowerInstance SlidingLowerOracle
open SoftRadialProjection SlidingLowerMoreau

variable {d T : ℕ}

lemma rescale_sub (s : ℝ) (x0 x y : Point d) :
    rescale s x0 y - rescale s x0 x = s⁻¹ • (y - x) := by
  unfold rescale; rw [← smul_sub]; congr 1; abel

lemma fS_lower {a s R ℓ : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hR : 5280 * (1 + Real.sqrt T) ≤ R)
    (hℓ : a / s ^ 2 * 2200 = ℓ) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x y : Point d) :
    fS a s R π x0 x + ⟪(a / s) • fgrad R π (rescale s x0 x), y - x⟫ - ℓ / 2 * ‖y - x‖ ^ 2 ≤
      fS a s R π x0 y := by
  have hR0 := (radius_facts hR).1
  have hg : ∀ z, HasGradientAt (fun z => -fS a s R π x0 z)
      (-((a / s) • fgrad R π (rescale s x0 z))) z := fun z => grad_neg (fS_gradient hR0 π x0 z)
  have hl : ∀ u v : Point d, ‖-((a / s) • fgrad R π (rescale s x0 u)) -
      -((a / s) • fgrad R π (rescale s x0 v))‖ ≤ ℓ * ‖u - v‖ := by
    intro u v
    rw [neg_sub_neg, norm_sub_rev, ← hℓ]
    exact scaled_lipschitz ha hs (fgrad_lipschitz hR π) x0 u v
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hl x y
  rw [inner_neg_left] at h
  linarith

lemma hS_support {a s R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d)
    (x0 x y : Point d) :
    hS a s R π x0 x + ⟪(a / s) • hgrad R π (rescale s x0 x), y - x⟫ ≤ hS a s R π x0 y := by
  have h := hbar_support hR π (rescale s x0 x) (rescale s x0 y)
  rw [rescale_sub] at h
  unfold hS
  rw [inner_smul_left, inner_smul_right] at *
  simp only [conj_trivial] at *
  have e : a / s * ⟪hgrad R π (rescale s x0 x), y - x⟫ =
      a * (s⁻¹ * ⟪hgrad R π (rescale s x0 x), y - x⟫) := by ring
  rw [e]
  nlinarith

lemma hS_convex {a s R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (π : Fin (2 * T + 1) ↪ Fin d)
    (x0 : Point d) : ConvexOn ℝ Set.univ (hS a s R π x0) :=
  LongTails.Proofs.SharpChainLowerBound.convexOn_of_subgradient _ _ (hS_support ha hR π x0)

lemma gap_lower {a s R ℓ : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hR : 5280 * (1 + Real.sqrt T) ≤ R)
    (hℓ : a / s ^ 2 * 2200 = ℓ) (hℓ0 : 0 < ℓ) (π : Fin (2 * T + 1) ↪ Fin d) (x0 x : Point d)
    (hx : |project R (rescale s x0 x) (π (xi (Fin.last T)))| ≤ 1 / 8) :
    min ((a / s) ^ 2 / (288 * ℓ)) (49 * ℓ * s ^ 2 / 512) ≤
      (fS a s R π x0 x + hS a s R π x0 x) -
        ⨅ v, ((fS a s R π x0 v + hS a s R π x0 v) + ℓ * ‖v - x‖ ^ 2) := by
  have hR0 := (radius_facts hR).1
  let g : Point d → Point d := fun z =>
    (a / s) • fgrad R π (rescale s x0 z) + (a / s) • hgrad R π (rescale s x0 z)
  have hF : ∀ z, HasGradientAt (fun z => fS a s R π x0 z + hS a s R π x0 z) (g z) z :=
    fun z => grad_add (fS_gradient hR0 π x0 z) (hS_gradient hR0 π x0 z)
  have hwc : ∀ u v, (fS a s R π x0 u + hS a s R π x0 u) + ⟪g u, v - u⟫ - ℓ / 2 * ‖v - u‖ ^ 2 ≤
      fS a s R π x0 v + hS a s R π x0 v := by
    intro u v
    have h1 := fS_lower ha hs hR hℓ π x0 u v
    have h2 := hS_support (s := s) ha hR0 π x0 u v
    simp only [g, inner_add_left]
    linarith
  obtain ⟨y, hgy, hΓ⟩ := moreau_lower hℓ0 hF hwc x
  have hgt : g y = (a / s) • totalField R (1 / 20) π (rescale s x0 y) := by
    simp only [g]; rw [← smul_add, total_gradient]
  have hRt : 80 * (2 * (1 + 33 * Real.sqrt T) + 1) ≤ R := by
    have := Real.sqrt_nonneg (T : ℝ); nlinarith
  refine le_trans ?_ hΓ
  by_cases hy : |project R (rescale s x0 y) (π (xi (Fin.last T)))| < 1
  · have hl := total_lower π hRt (rescale s x0 y) hy
    have hn : (a / s) * (1 / 6) ≤ (2 * ℓ) * ‖x - y‖ := by
      have h1 : ‖g y‖ = (a / s) * ‖totalField R (1 / 20) π (rescale s x0 y)‖ := by
        rw [hgt, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hs.le)]
      have h2 : ‖g y‖ = (2 * ℓ) * ‖x - y‖ := by
        rw [hgy, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hl (div_nonneg ha hs.le)
    have hxy : (a / s) / (12 * ℓ) ≤ ‖x - y‖ := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hq : ((a / s) / (12 * ℓ)) ^ 2 ≤ ‖x - y‖ ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (div_nonneg ha hs.le) (by linarith)) hxy 2
    calc min ((a / s) ^ 2 / (288 * ℓ)) (49 * ℓ * s ^ 2 / 512) ≤ (a / s) ^ 2 / (288 * ℓ) :=
          min_le_left _ _
      _ = ℓ / 2 * ((a / s) / (12 * ℓ)) ^ 2 := by field_simp; ring
      _ ≤ ℓ / 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_left hq (by linarith)
  · push Not at hy
    have hd : 7 / 8 ≤ ‖project R (rescale s x0 y) - project R (rescale s x0 x)‖ := by
      have h1 := coord_le (project R (rescale s x0 y) - project R (rescale s x0 x))
        (π (xi (Fin.last T)))
      simp only [PiLp.sub_apply] at h1
      have h2 := abs_sub_abs_le_abs_sub (project R (rescale s x0 y) (π (xi (Fin.last T))))
        (project R (rescale s x0 x) (π (xi (Fin.last T))))
      linarith
    have hl := project_lipschitz hR0 (rescale s x0 y) (rescale s x0 x)
    rw [rescale_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at hl
    have hxy : 7 * s / 16 ≤ ‖x - y‖ := by
      have h7 : 7 / 16 ≤ s⁻¹ * ‖y - x‖ := by linarith
      have h3 : s * (7 / 16) ≤ s * (s⁻¹ * ‖y - x‖) := mul_le_mul_of_nonneg_left h7 hs.le
      rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, norm_sub_rev] at h3
      linarith
    have hq : (7 * s / 16) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hxy 2
    calc min ((a / s) ^ 2 / (288 * ℓ)) (49 * ℓ * s ^ 2 / 512) ≤ 49 * ℓ * s ^ 2 / 512 :=
          min_le_right _ _
      _ = ℓ / 2 * (7 * s / 16) ^ 2 := by ring
      _ ≤ ℓ / 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_left hq (by linarith)

end LongTails.Proofs.SlidingLowerGap
