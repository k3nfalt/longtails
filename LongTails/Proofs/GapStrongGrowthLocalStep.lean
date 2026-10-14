import LongTails.Proofs.GapStrongGrowthGeometry
import LongTails.Proofs.GapStrongGrowthWeights
import LongTails.Proofs.GapStrongGrowthExponential

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

lemma query_local_bounds (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) {f : p.E → ℝ} {u : p.E}
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ u)
    (hm : GapUpperModel f u p.H0 p.H1)
    (n : ℕ) (x z : p.E) (hz : ‖z - u‖ ≤ 4 * p.R)
    (hgap : weight p n * (f x - f u) ≤ 8 * p.R ^ 2) :
    weight p n * (f (queryPoint p n (x, z)) - f u) ≤ 16 * p.R ^ 2 ∧
    weight p n * (p.H0 + p.H1 * (f (queryPoint p n (x, z)) - f u)) ≤
      16 * geometryScale p (weight p n) ^ 2 ∧
    512 * confidence p * increment p (weight p n) *
      ‖gradient f (queryPoint p n (x, z))‖ ≤ 3 * p.R := by
  let A := weight p n
  let a := increment p A
  let B := geometryScale p A
  let ybar := (A / (A + a)) • x + (a / (A + a)) • u
  have hA : 0 < A := weight_pos p hR hΔ n
  have ha : 0 < a := increment_pos p hR.le hA
  have hAp : 0 < A + a := by positivity
  have hB : 0 ≤ B := (show 0 ≤ (1 : ℝ) by norm_num).trans (denominator_ge_one p hR.le A)
  have hq := confidence_ge_one p
  have hq0 := confidence_pos p
  have hc : 32768 * confidence p * a * B = A := increment_scale p hR.le A
  have hc' : 32768 * a * B ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ 32768 * a * B by positivity)
    nlinarith only [hh, hc]
  have hratio : B * a / (A + a) ≤ 1 / 32768 := by
    apply (div_le_iff₀ hAp).mpr
    nlinarith only [hc', ha]
  have hybar : A * (f ybar - f u) ≤ 8 * p.R ^ 2 := by
    have hmix := hconv.2 (mem_univ x) (mem_univ u)
      (show 0 ≤ A / (A + a) by positivity) (show 0 ≤ a / (A + a) by positivity)
      (show A / (A + a) + a / (A + a) = 1 by field_simp)
    change A * (f x - f u) ≤ 8 * p.R ^ 2 at hgap
    change f ybar ≤ _ at hmix
    simp only [smul_eq_mul] at hmix
    have hmix' : f ybar * (A + a) ≤ A * f x + a * f u := by
      calc
        _ ≤ (A / (A + a) * f x + a / (A + a) * f u) * (A + a) :=
          mul_le_mul_of_nonneg_right hmix hAp.le
        _ = _ := by field_simp
    have hnonneg : 0 ≤ f ybar - f u := sub_nonneg.mpr (hmin (mem_univ _))
    nlinarith only [hmix', hgap, mul_nonneg ha.le hnonneg]
  have hd : B * ‖queryPoint p n (x, z) - ybar‖ ≤ p.R / 4096 := by
    have he : queryPoint p n (x, z) - ybar = (a / (A + a)) • (z - u) := by
      unfold queryPoint
      change (A / (A + a)) • x + (a / (A + a)) • z - ybar = _
      dsimp [ybar]
      module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ = (B * a / (A + a)) * ‖z - u‖ := by ring
      _ ≤ (1 / 32768) * (4 * p.R) := mul_le_mul hratio hz (norm_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  have hs : p.H0 * A + p.H1 * p.R ^ 2 ≤ B ^ 2 := geometry_scale_square p hR.le h0 h1 hA.le
  have hy := query_gap_bound h0 h1 hA hR hB hmin hm hs (geometry_scale_radius p A) hybar hd
  have hg := scaled_geometry h0 h1 hA hR.le hB (by norm_num : (1 : ℝ) ≤ 16)
    hmin hm hs (queryPoint p n (x, z)) hy
  refine ⟨hy, hg.1, ?_⟩
  have hb := mul_le_mul_of_nonneg_left hg.2 (show 0 ≤ 512 * confidence p * a by positivity)
  have hcR := congrArg (fun t : ℝ => t * (3 * p.R)) hc
  change 512 * confidence p * a * ‖gradient f (queryPoint p n (x, z))‖ ≤ 3 * p.R
  apply (mul_le_mul_iff_left₀ hA).mp
  nlinarith only [hb, hcR]

lemma primal_step_scaled (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (n : ℕ) (v : p.E) :
    geometryScale p (weight p n) *
      ‖(32 * confidence p * increment p (weight p n) ^ 2 /
        (weight p n + increment p (weight p n))) •
        clip (p.R / (confidence p * increment p (weight p n))) v‖ ≤ p.R / 1024 := by
  let A := weight p n
  let a := increment p A
  let B := geometryScale p A
  have hA : 0 < A := weight_pos p hR hΔ n
  have ha : 0 < a := increment_pos p hR.le hA
  have hAp : 0 < A + a := by positivity
  have hB : 0 ≤ B := (show 0 ≤ (1 : ℝ) by norm_num).trans (denominator_ge_one p hR.le A)
  have hq := confidence_pos p
  have hc : 32768 * confidence p * a * B = A := increment_scale p hR.le A
  have hc' : 32768 * a * B ≤ A := by
    have hh := mul_le_mul_of_nonneg_right (confidence_ge_one p)
      (show 0 ≤ 32768 * a * B by positivity)
    nlinarith only [hh, hc]
  have hh := mul_le_mul_of_nonneg_left (norm_clip_le
    (show 0 ≤ p.R / (confidence p * a) by positivity) v)
    (show 0 ≤ B * (32 * confidence p * a ^ 2 / (A + a)) by positivity)
  change B * ‖(32 * confidence p * a ^ 2 / (A + a)) • clip (p.R / (confidence p * a)) v‖ ≤ p.R / 1024
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb : B * (32 * confidence p * a ^ 2 / (A + a)) *
      (p.R / (confidence p * a)) ≤ p.R / 1024 := by
    field_simp
    nlinarith only [hc', ha]
  nlinarith only [hh, hb]

lemma step_quadratic_coefficient {A a B H q : ℝ} (hA : 0 < A) (ha : 0 < a)
    (hc : 32768 * q * a * B = A) (hH : A * H ≤ 16 * B ^ 2) :
    (A + a) * H * (32 * q * a ^ 2 / (A + a)) ^ 2 + a ^ 2 / 2 ≤ a ^ 2 := by
  have hAp : 0 < A + a := by positivity
  have hh := mul_le_mul_of_nonneg_right hH (show 0 ≤ a ^ 2 * q ^ 2 by positivity)
  have hs := congrArg (fun t : ℝ => t ^ 2) hc
  have hb : 2048 * q ^ 2 * a ^ 2 * H ≤ A + a := by
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith only [hh, hs, sq_nonneg A, mul_nonneg hA.le ha.le]
  apply (mul_le_mul_iff_right₀ hAp).mp
  field_simp
  nlinarith only [hb]

noncomputable def energy (p : Params) (f : p.E → ℝ) (u : p.E) (n : ℕ)
    (s : p.E × p.E) : ℝ :=
  weight p n * (f s.1 - f u) + ‖s.2 - u‖ ^ 2 / 2

lemma energy_nonneg (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    {f : p.E → ℝ} {u : p.E} (hmin : IsMinOn f univ u) (n : ℕ) (s : p.E × p.E) :
    0 ≤ energy p f u n s := by
  have hg : 0 ≤ f s.1 - f u := sub_nonneg.mpr (hmin (mem_univ _))
  have hA := weight_pos p hR hΔ n
  unfold energy
  positivity

lemma energy_small_bounds (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    {f : p.E → ℝ} {u : p.E} (hmin : IsMinOn f univ u) (n : ℕ) (s : p.E × p.E)
    (hV : energy p f u n s ≤ 8 * p.R ^ 2) :
    weight p n * (f s.1 - f u) ≤ 8 * p.R ^ 2 ∧ ‖s.2 - u‖ ≤ 4 * p.R := by
  have hg : 0 ≤ f s.1 - f u := sub_nonneg.mpr (hmin (mem_univ _))
  have hA := weight_pos p hR hΔ n
  unfold energy at hV
  constructor
  · nlinarith only [hV, sq_nonneg ‖s.2 - u‖]
  · nlinarith only [hV, mul_nonneg hA.le hg, norm_nonneg (s.2 - u), hR]

lemma step_energy_le (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) {f : p.E → ℝ} {u : p.E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hmin : IsMinOn f univ u) (hm : GapUpperModel f u p.H0 p.H1)
    (n : ℕ) (s : p.E × p.E) (v : p.E) (hV : energy p f u n s ≤ 8 * p.R ^ 2) :
    energy p f u (n + 1) (step p n s v) ≤ energy p f u n s +
      energyIncrement (confidence p) (increment p (weight p n))
        (gradient f (queryPoint p n s)) (s.2 - u)
        (clip (p.R / (confidence p * increment p (weight p n))) v) := by
  let A := weight p n
  let a := increment p A
  let y := queryPoint p n s
  let h := clip (p.R / (confidence p * a)) v
  let η := 32 * confidence p * a ^ 2 / (A + a)
  let H := p.H0 + p.H1 * (f y - f u)
  have hA : 0 < A := weight_pos p hR hΔ n
  have ha : 0 < a := increment_pos p hR.le hA
  have hAp : 0 < A + a := by positivity
  have hq := confidence_pos p
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hb := energy_small_bounds p hR hΔ hmin n s hV
  have hlocal := query_local_bounds p hR hΔ h0 h1 hconv hmin hm n s.1 s.2 hb.2 hb.1
  have hd : geometryScale p A * ‖(y - η • h) - y‖ ≤ p.R / 6 := by
    have hh := primal_step_scaled p hR hΔ n v
    change geometryScale p A * ‖η • h‖ ≤ p.R / 1024 at hh
    rw [show y - η • h - y = -(η • h) by module, norm_neg]
    linarith
  have hm' := model_safe_of_scaled_distance hR (geometry_scale_radius p A) hd hm
  have hs : f (y - η • h) ≤ f y - η * ⟪gradient f y, h⟫ + H * η ^ 2 * ‖h‖ ^ 2 := by
    rw [show y - η • h - y = -(η • h) by module] at hm'
    simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hη, mul_pow] at hm'
    dsimp [H]
    nlinarith only [hm']
  have hc := coupled_step hconv hgrad hA.le ha s.1 s.2 u h hs
  have hcoef := step_quadratic_coefficient hA ha (increment_scale p hR.le A) hlocal.2.1
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖h‖)
  have hηid : (A + a) * η = 32 * confidence p * a ^ 2 := by
    dsimp [η]
    field_simp
  change (A + a) * (f (y - η • h) - f u) + ‖s.2 - a • h - u‖ ^ 2 / 2 ≤
    A * (f s.1 - f u) + ‖s.2 - u‖ ^ 2 / 2 - (A + a) * η * ⟪gradient f y, h⟫ +
      ((A + a) * H * η ^ 2 + a ^ 2 / 2) * ‖h‖ ^ 2 + a * ⟪gradient f y - h, s.2 - u⟫ at hc
  change ((A + a) * H * η ^ 2 + a ^ 2 / 2) * ‖h‖ ^ 2 ≤ a ^ 2 * ‖h‖ ^ 2 at hcoef'
  change (A + a) * (f (y - η • h) - f u) + ‖s.2 - a • h - u‖ ^ 2 / 2 ≤
    A * (f s.1 - f u) + ‖s.2 - u‖ ^ 2 / 2 + energyIncrement (confidence p) a (gradient f y) (s.2 - u) h
  rw [hηid] at hc
  unfold energyIncrement
  nlinarith only [hc, hcoef']

end OracleTemplate.GapStrongGrowth
