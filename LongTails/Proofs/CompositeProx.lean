import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.Composite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma strong_minimum_bound {F : E → ℝ} {μ : ℝ}
    (hF : StrongConvexOn univ μ F) {u : E} (hu : IsMinOn F univ u) (x : E) :
    μ / 2 * ‖x - u‖ ^ 2 ≤ F x - F u := by
  let c := μ / 2 * ‖x - u‖ ^ 2
  let d := F x - F u
  have hd : 0 ≤ d := sub_nonneg.mpr (hu (mem_univ x))
  by_contra hn
  have hdc : d < c := lt_of_not_ge hn
  have hc : 0 < c := lt_of_le_of_lt hd hdc
  let t := (c - d) / (2 * c)
  have ht : 0 < t := div_pos (sub_pos.mpr hdc) (by positivity)
  have ht1 : t < 1 := (div_lt_one (by positivity : 0 < 2 * c)).mpr (by linarith)
  have he : t * (2 * c) = c - d := div_mul_cancel₀ _ (by positivity)
  have h := hF.2 (mem_univ x) (mem_univ u) ht.le (sub_nonneg.mpr ht1.le)
    (show t + (1 - t) = 1 by ring)
  have hm : F u ≤ F (t • x + (1 - t) • u) := hu (mem_univ _)
  simp only [smul_eq_mul] at h
  change F (t • x + (1 - t) • u) ≤ t * F x + (1 - t) * F u - t * (1 - t) * c at h
  have hh : t * ((1 - t) * c - d) ≤ 0 := by dsimp [d]; nlinarith
  have hh' : (1 - t) * c - d ≤ 0 := (mul_le_mul_iff_right₀ ht).mp (by simpa using hh)
  nlinarith

lemma strong_add_convex {f ψ : E → ℝ} {μ : ℝ}
    (hf : ConvexOn ℝ univ f) (hψ : StrongConvexOn univ μ ψ) :
    StrongConvexOn univ μ (fun x => f x + ψ x) := by
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab => ?_⟩
  have h₁ := hf.2 hx hy ha hb hab
  have h₂ := hψ.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  linarith

noncomputable def proxObjective (ψ : E → ℝ) (a : ℝ) (z g v : E) : ℝ :=
  ‖v - z‖ ^ 2 / (2 * a) + ⟪g, v - z⟫ + ψ v

lemma prox_strong {ψ : E → ℝ} {μ a : ℝ}
    (hψ : StrongConvexOn univ μ ψ) (z g : E) :
    StrongConvexOn univ (1 / a + μ) (proxObjective ψ a z g) := by
  refine ⟨convex_univ, fun x hx y hy s t hs ht hst => ?_⟩
  have h := hψ.2 hx hy hs ht hst
  have hshift : s • x + t • y - z = s • (x - z) + t • (y - z) := by
    calc
      _ = s • (x - z) + t • (y - z) + (s + t - 1) • z := by module
      _ = _ := by rw [hst]; simp
  have hnorm : ‖s • (x - z) + t • (y - z)‖ ^ 2 =
      s * ‖x - z‖ ^ 2 + t * ‖y - z‖ ^ 2 - s * t * ‖x - y‖ ^ 2 := by
    have hxy : x - y = (x - z) - (y - z) := by module
    rw [hxy, norm_add_sq_real, norm_sub_sq_real (x - z) (y - z), norm_smul, norm_smul,
      real_inner_smul_left, inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hs, abs_of_nonneg ht]
    obtain rfl := eq_sub_of_add_eq hst
    ring
  simp only [proxObjective, hshift, hnorm, inner_add_right, inner_smul_right, smul_eq_mul] at h ⊢
  ring_nf at h ⊢
  linarith

lemma prox_three_point {ψ : E → ℝ} {μ a : ℝ} (ha : 0 < a)
    (hψ : StrongConvexOn univ μ ψ) {z g v : E}
    (hv : IsMinOn (proxObjective ψ a z g) univ v) (u : E) :
    a * (⟪g, v - u⟫ + ψ v - ψ u) ≤
      ‖z - u‖ ^ 2 / 2 - (1 + a * μ) / 2 * ‖v - u‖ ^ 2 - ‖v - z‖ ^ 2 / 2 := by
  have h := strong_minimum_bound
    (prox_strong hψ z g) hv u
  have hi : ⟪g, u - z⟫ = ⟪g, v - z⟫ - ⟪g, v - u⟫ := by
    rw [← inner_sub_right]
    congr 1
    module
  rw [proxObjective, proxObjective, hi, norm_sub_rev u v, norm_sub_rev u z] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  field_simp at hh
  nlinarith

end OracleTemplate.Composite
