import LongTails.Algorithms.AcceleratedMarkov
import LongTails.Proofs.Clipping
import LongTails.Proofs.AcceleratedStochastic

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedMarkovGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projected_gradient_inequality {D R a : ℝ} (hD : 0 < D) (hR : 0 ≤ R)
    (x0 z g u : E) (hu : ‖u - x0‖ ≤ R) :
    let next := x0 + clip R (z - (a / D) • g - x0)
    a * ⟪g, next - u⟫ ≤
      D / 2 * (‖z - u‖ ^ 2 - ‖next - u‖ ^ 2 - ‖next - z‖ ^ 2) := by
  dsimp
  let next := x0 + clip R (z - (a / D) • g - x0)
  have hi := inner_clip_residual_nonpos hR hu (z - (a / D) • g - x0)
  have hi' : ⟪z - next - (a / D) • g, -(next - u)⟫ ≤ 0 := by
    convert hi using 1; congr 1 <;> dsimp [next] <;> abel
  rw [inner_neg_right, inner_sub_left, real_inner_smul_left] at hi'
  have hp : a * ⟪g, next - u⟫ / D ≤ ⟪z - next, next - u⟫ := by
    have he : a * ⟪g, next - u⟫ / D = a / D * ⟪g, next - u⟫ := by ring
    rw [he]
    linarith
  have hp' := (div_le_iff₀ hD).mp hp
  have he : ‖z - u‖ ^ 2 = ‖z - next‖ ^ 2 + 2 * ⟪z - next, next - u⟫ + ‖next - u‖ ^ 2 := by
    rw [show z - u = (z - next) + (next - u) by abel, norm_add_sq_real]
  have hs : ‖next - z‖ = ‖z - next‖ := norm_sub_rev _ _
  change a * ⟪g, next - u⟫ ≤ _
  change a * ⟪g, next - u⟫ ≤ D / 2 * (‖z - u‖ ^ 2 - ‖next - u‖ ^ 2 - ‖next - z‖ ^ 2)
  rw [he, hs]
  nlinarith only [hp']

lemma bounded_young {b c d M p : ℝ} (hb : 0 ≤ b) (hc : 0 < c)
    (hd : 0 ≤ d) (hdM : d ≤ M) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    b * d - c * d ^ 2 ≤ b ^ p * M ^ (2 - p) / c ^ (p - 1) := by
  have hM : 0 ≤ M := hd.trans hdM
  by_cases hsmall : b ≤ c * d
  · have hh := mul_le_mul_of_nonneg_right hsmall hd
    have hn : 0 ≤ b ^ p * M ^ (2 - p) / c ^ (p - 1) := by positivity
    nlinarith
  have hbpos : 0 < b := lt_of_le_of_lt (mul_nonneg hc.le hd) (lt_of_not_ge hsmall)
  have hdc : d ≤ b / c := (le_div_iff₀ hc).mpr (by nlinarith [lt_of_not_ge hsmall])
  have h1 := Real.rpow_le_rpow hd hdc (sub_nonneg.mpr hp)
  have h2 := Real.rpow_le_rpow hd hdM (sub_nonneg.mpr hp2)
  have hd' : d ≤ (b / c) ^ (p - 1) * M ^ (2 - p) := by
    by_cases hz : d = 0
    · subst d
      positivity
    have he : d ^ (p - 1) * d ^ (2 - p) = d := by
      rw [← Real.rpow_add (lt_of_le_of_ne hd (Ne.symm hz)), show p - 1 + (2 - p) = 1 by ring,
        Real.rpow_one]
    rw [← he]
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hd _) (Real.rpow_nonneg (by positivity) _)
  have hh := mul_le_mul_of_nonneg_left hd' hb
  have he : b * ((b / c) ^ (p - 1) * M ^ (2 - p)) =
      b ^ p * M ^ (2 - p) / c ^ (p - 1) := by
    rw [Real.div_rpow hb hc.le]
    have hpow : b * b ^ (p - 1) = b ^ p := by
      nth_rw 1 [← Real.rpow_one b]
      rw [← Real.rpow_add hbpos, show 1 + (p - 1) = p by ring]
    calc
      _ = (b * b ^ (p - 1)) * M ^ (2 - p) / c ^ (p - 1) := by ring
      _ = _ := by rw [hpow]
  rw [he] at hh
  nlinarith [mul_nonneg hc.le (sq_nonneg d)]

lemma accelerated_projected_step [CompleteSpace E] {f : E → ℝ} {L D R p : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x0 x z u g : E) (hz : ‖z - x0‖ ≤ R) (hu : ‖u - x0‖ ≤ R)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a) (haB : a ^ 2 ≤ A + a) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    let next := x0 + clip R (z - (a / D) • g - x0)
    let out := (A / (A + a)) • x + (a / (A + a)) • next
    let e := gradient f y - g
    (A + a) * (f out - f u) + D / 2 * ‖next - u‖ ^ 2 ≤
      A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2 + a * ⟪e, z - u⟫ +
        min ((a * ‖e‖) ^ p * (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) (2 * R * a * ‖e‖) := by
  let B := A + a
  let y := (A / B) • x + (a / B) • z
  let next := x0 + clip R (z - (a / D) • g - x0)
  let out := (A / B) • x + (a / B) • next
  let e := gradient f y - g
  have hx := Gradient.convex_support hc hg y x
  have hum := Gradient.convex_support hc hg y u
  have hid : A • (x - y) + a • (u - y) = a • (u - z) := by
    dsimp [y, B]
    match_scalars
    all_goals field_simp [hB.ne'] <;> ring
  have hi := congrArg (fun v => ⟪gradient f y, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hw : B * (f y - f u) ≤ A * (f x - f u) + a * ⟪gradient f y, z - u⟫ := by
    have hx' := mul_le_mul_of_nonneg_left hx hA
    have hu' := mul_le_mul_of_nonneg_left hum ha
    rw [show u - z = -(z - u) by abel, inner_neg_right] at hi
    dsimp [B]
    nlinarith only [hx', hu', hi]
  have hout : out - y = (a / B) • (next - z) := by dsimp [out, y]; module
  have hd := Gradient.smooth_upper_bound hg hlip y out
  rw [hout, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hB.le)] at hd
  have hd' := mul_le_mul_of_nonneg_left hd hB.le
  have hcoef : L * a ^ 2 / (2 * B) ≤ D / 4 := by
    apply (div_le_iff₀ (by dsimp [B]; positivity : 0 < 2 * B)).mpr
    have h1 := mul_le_mul_of_nonneg_left haB hL
    have h2 := mul_le_mul_of_nonneg_right hLD hB.le
    dsimp [B]
    nlinarith only [h1, h2]
  have hdes : B * (f out - f u) ≤
      B * (f y - f u) + a * ⟪gradient f y, next - z⟫ + D / 4 * ‖next - z‖ ^ 2 := by
    have he : B * (f y + (a / B) * ⟪gradient f y, next - z⟫ +
        L / 2 * ((a / B) * ‖next - z‖) ^ 2) =
        B * f y + a * ⟪gradient f y, next - z⟫ + L * a ^ 2 / (2 * B) * ‖next - z‖ ^ 2 := by
      have hB0 : B ≠ 0 := hB.ne'
      field_simp

    rw [he] at hd'
    have hq := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖next - z‖)
    nlinarith only [hd', hq]
  have hproj := projected_gradient_inequality (a := a) hD hR x0 z g u hu
  have hn : ‖next - x0‖ ≤ R := by simpa [next] using norm_clip_le hR (z - (a / D) • g - x0)
  have hdR : ‖next - z‖ ≤ 2 * R := by
    have := norm_sub_le (next - x0) (z - x0)
    rw [show next - x0 - (z - x0) = next - z by abel] at this
    linarith
  have hyoung := bounded_young (mul_nonneg ha (norm_nonneg e))
    (show 0 < D / 4 by positivity) (norm_nonneg (next - z)) hdR hp hp2
  have hsmall : a * ‖e‖ * ‖next - z‖ - D / 4 * ‖next - z‖ ^ 2 ≤ 2 * R * a * ‖e‖ := by
    have hh := mul_le_mul_of_nonneg_left hdR (mul_nonneg ha (norm_nonneg e))
    nlinarith [mul_nonneg (show 0 ≤ D / 4 by positivity) (sq_nonneg ‖next - z‖)]
  have herr := le_min hyoung hsmall
  have he : ⟪gradient f y, z - u⟫ + ⟪gradient f y, next - z⟫ =
      ⟪g, next - u⟫ + ⟪e, z - u⟫ + ⟪e, next - z⟫ := by
    dsimp [e]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have heineq := mul_le_mul_of_nonneg_left (real_inner_le_norm e (next - z)) ha
  change B * (f out - f u) + D / 2 * ‖next - u‖ ^ 2 ≤ _
  have he' := congrArg (fun t : ℝ => a * t) he
  change a * ⟪g, next - u⟫ ≤ D / 2 * (‖z - u‖ ^ 2 - ‖next - u‖ ^ 2 - ‖next - z‖ ^ 2) at hproj
  nlinarith only [hw, hdes, hproj, herr, heineq, he']

end OracleTemplate.HeavyTailedMarkovGradient
