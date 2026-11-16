import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManyConstraintCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def proxObj (ψ : E → ℝ) (a : ℝ) (z g v : E) : ℝ :=
  ‖v - z‖ ^ 2 / (2 * a) + ⟪g, v - z⟫ + ψ v

noncomputable def mix (τ : ℝ) (snapshot y z : E) : E :=
  τ • z + (1 / 2 : ℝ) • snapshot + (1 / 2 - τ) • y

lemma strong_min_on {K : Set E} {F : E → ℝ} {μ : ℝ}
    (hF : StrongConvexOn K μ F) {u : E} (huK : u ∈ K) (hu : IsMinOn F K u) {x : E}
    (hx : x ∈ K) : μ / 2 * ‖x - u‖ ^ 2 ≤ F x - F u := by
  let c := μ / 2 * ‖x - u‖ ^ 2
  let d := F x - F u
  have hd : 0 ≤ d := sub_nonneg.mpr (hu hx)
  by_contra hn
  have hdc : d < c := lt_of_not_ge hn
  have hc : 0 < c := lt_of_le_of_lt hd hdc
  let t := (c - d) / (2 * c)
  have ht : 0 < t := div_pos (sub_pos.mpr hdc) (by positivity)
  have ht1 : t < 1 := (div_lt_one (by positivity : 0 < 2 * c)).mpr (by linarith)
  have he : t * (2 * c) = c - d := div_mul_cancel₀ _ (by positivity)
  have h := hF.2 hx huK ht.le (sub_nonneg.mpr ht1.le) (show t + (1 - t) = 1 by ring)
  have hmem : t • x + (1 - t) • u ∈ K :=
    hF.1 hx huK ht.le (sub_nonneg.mpr ht1.le) (show t + (1 - t) = 1 by ring)
  have hm : F u ≤ F (t • x + (1 - t) • u) := hu hmem
  simp only [smul_eq_mul] at h
  change F (t • x + (1 - t) • u) ≤ t * F x + (1 - t) * F u - t * (1 - t) * c at h
  have hh : t * ((1 - t) * c - d) ≤ 0 := by dsimp [d]; nlinarith
  have hh' : (1 - t) * c - d ≤ 0 := (mul_le_mul_iff_right₀ ht).mp (by simpa using hh)
  nlinarith

lemma prox_strong_on {K : Set E} {ψ : E → ℝ} {μ a : ℝ}
    (hψ : StrongConvexOn K μ ψ) (z g : E) :
    StrongConvexOn K (1 / a + μ) (proxObj ψ a z g) := by
  refine ⟨hψ.1, fun x hx y hy s t hs ht hst => ?_⟩
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
  simp only [proxObj, hshift, hnorm, inner_add_right, inner_smul_right, smul_eq_mul] at h ⊢
  ring_nf at h ⊢
  linarith

lemma prox_three_point_on {K : Set E} {ψ : E → ℝ} {μ a : ℝ} (ha : 0 < a)
    (hψ : StrongConvexOn K μ ψ) {z g v : E} (hvK : v ∈ K)
    (hv : IsMinOn (proxObj ψ a z g) K v) {u : E} (hu : u ∈ K) :
    a * (⟪g, v - u⟫ + ψ v - ψ u) ≤
      ‖z - u‖ ^ 2 / 2 - (1 + a * μ) / 2 * ‖v - u‖ ^ 2 - ‖v - z‖ ^ 2 / 2 := by
  have h := strong_min_on (prox_strong_on hψ z g) hvK hv hu
  have hi : ⟪g, u - z⟫ = ⟪g, v - z⟫ - ⟪g, v - u⟫ := by
    rw [← inner_sub_right]; congr 1; module
  rw [proxObj, proxObj, hi, norm_sub_rev u v, norm_sub_rev u z] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  field_simp at hh
  nlinarith

lemma young (L : ℝ) (hL : 0 < L) (a b : E) :
    ⟪a, b⟫ ≤ L * ‖b‖ ^ 2 + ‖a‖ ^ 2 / (4 * L) := by
  have h := sq_nonneg ‖a - (2 * L) • b‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have he : ‖a‖ ^ 2 / (4 * L) * (4 * L) = ‖a‖ ^ 2 := div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma convex_mix_on {K : Set E} {ψ : E → ℝ} (hψ : ConvexOn ℝ K ψ)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτh : τ ≤ 1 / 2) {snapshot y z : E}
    (hs : snapshot ∈ K) (hy : y ∈ K) (hz : z ∈ K) :
    mix τ snapshot y z ∈ K ∧
    ψ (mix τ snapshot y z) ≤ τ * ψ z + (1 / 2) * ψ snapshot + (1 / 2 - τ) * ψ y := by
  have hzy := hψ.1 hz hy (show 0 ≤ 2 * τ by positivity) (show 0 ≤ 1 - 2 * τ by linarith)
    (show 2 * τ + (1 - 2 * τ) = 1 by ring)
  have h₁ := hψ.2 hz hy (show 0 ≤ 2 * τ by positivity) (show 0 ≤ 1 - 2 * τ by linarith)
    (show 2 * τ + (1 - 2 * τ) = 1 by ring)
  have hmem := hψ.1 hzy hs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have h₂ := hψ.2 hzy hs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hx : (1 / 2 : ℝ) • ((2 * τ) • z + (1 - 2 * τ) • y) + (1 / 2 : ℝ) • snapshot =
      mix τ snapshot y z := by dsimp [mix]; module
  rw [hx] at h₂ hmem
  refine ⟨hmem, ?_⟩
  simp only [smul_eq_mul] at h₁ h₂
  linarith

lemma coupling_on {K : Set E} {f ψ : E → ℝ} {τ α L μ Dg : ℝ}
    (hL : 0 < L) (hμ : 0 ≤ μ) (hα : 0 < α) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2)
    (htune : 3 * α * L * τ ≤ 1) (hψ : StrongConvexOn K μ ψ)
    {snapshot y z u G v ynext znext : E}
    (hs : snapshot ∈ K) (hyK : y ∈ K) (huK : u ∈ K) (hznK : znext ∈ K)
    (hmodel : f ynext ≤ f (mix τ snapshot y z) +
      ⟪G, ynext - mix τ snapshot y z⟫ + L / 2 * ‖ynext - mix τ snapshot y z‖ ^ 2)
    (hy : IsMinOn (proxObj ψ (1 / (3 * L)) (mix τ snapshot y z) v) K ynext)
    (hz : IsMinOn (proxObj ψ α z v) K znext)
    (hsy : ⟪G, y - mix τ snapshot y z⟫ ≤ f y - f (mix τ snapshot y z))
    (hsu : ⟪G, u - mix τ snapshot y z⟫ ≤ f u - f (mix τ snapshot y z) - Dg) :
    f ynext + ψ ynext + τ / (2 * α) * (1 + α * μ) * ‖znext - u‖ ^ 2 ≤
      (1 / 2 - τ) * (f y + ψ y) + 1 / 2 * (f snapshot + ψ snapshot) +
      τ * (f u + ψ u) + τ / (2 * α) * ‖z - u‖ ^ 2 +
      τ * ⟪G - v, z - u⟫ + ‖G - v‖ ^ 2 / (4 * L) - τ * Dg -
      1 / 2 * (f snapshot - f (mix τ snapshot y z) -
        ⟪G, snapshot - mix τ snapshot y z⟫) := by
  set x := mix τ snapshot y z with hxdef
  set w := mix τ snapshot y znext with hwdef
  have hwx : w - x = τ • (znext - z) := by simp only [hxdef, hwdef, mix]; module
  have hcψ : ConvexOn ℝ K ψ := (strongConvexOn_zero.mp (hψ.mono hμ))
  obtain ⟨hwK, hc⟩ := convex_mix_on hcψ hτ.le hτh hs hyK hznK
  rw [← hwdef] at hwK hc
  have hyw : proxObj ψ (1 / (3 * L)) x v ynext ≤ proxObj ψ (1 / (3 * L)) x v w := hy hwK
  have he (t : ℝ) : t / (2 * (1 / (3 * L))) = (3 * L / 2) * t := by field_simp
  simp only [proxObj, he] at hyw
  have hn := young L hL (G - v) (ynext - x)
  rw [inner_sub_left] at hn
  have hd : f ynext + ψ ynext ≤ f x + ψ x + 3 * L / 2 * ‖w - x‖ ^ 2 + ⟪v, w - x⟫ +
      ψ w - ψ x + ‖G - v‖ ^ 2 / (4 * L) := by nlinarith
  rw [hwx, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_pow, inner_smul_right] at hd
  have hm := prox_three_point_on hα hψ hznK hz huK
  have hm' : τ * (⟪v, znext - u⟫ + ψ znext - ψ u) ≤
      τ / (2 * α) * ‖z - u‖ ^ 2 - τ / (2 * α) * (1 + α * μ) * ‖znext - u‖ ^ 2 -
      τ / (2 * α) * ‖znext - z‖ ^ 2 := by
    calc
      _ = τ / α * (α * (⟪v, znext - u⟫ + ψ znext - ψ u)) := by field_simp
      _ ≤ τ / α * (‖z - u‖ ^ 2 / 2 - (1 + α * μ) / 2 * ‖znext - u‖ ^ 2 -
          ‖znext - z‖ ^ 2 / 2) := mul_le_mul_of_nonneg_left hm (div_nonneg hτ.le hα.le)
      _ = _ := by ring
  have hi : ⟪v, znext - u⟫ = ⟪v, znext - z⟫ + ⟪v, z - u⟫ := by
    rw [← inner_add_right]; congr 1; module
  rw [hi] at hm'
  have hid : τ * ⟪G, z - u⟫ =
      -(1 / 2 : ℝ) * ⟪G, snapshot - x⟫ - (1 / 2 - τ) * ⟪G, y - x⟫ - τ * ⟪G, u - x⟫ := by
    simp only [← inner_smul_right, ← inner_sub_right]
    congr 1
    simp only [hxdef, mix]
    module
  have hsy' := mul_le_mul_of_nonneg_left hsy (show 0 ≤ 1 / 2 - τ by linarith)
  have hsu' := mul_le_mul_of_nonneg_left hsu hτ.le
  have hcancel : 3 * L / 2 * τ ^ 2 * ‖znext - z‖ ^ 2 ≤ τ / (2 * α) * ‖znext - z‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (le_div_iff₀ (by positivity : 0 < 2 * α)).mpr
    nlinarith [mul_le_mul_of_nonneg_left htune hτ.le]
  rw [inner_sub_left]
  nlinarith only [hd, hc, hm', hid, hsy', hsu', hcancel]

end LongTails.Proofs.ManyConstraintCoupling
