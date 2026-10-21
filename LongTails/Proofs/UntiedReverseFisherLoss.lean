import LongTails.Setups.UntiedGaussianReverseFisher
import LongTails.Proofs.SymmetricReverseFisherLoss
import LongTails.Proofs.SymmetricReverseFisherScalar
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherLoss

open LongTails.Setups.UntiedGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherGaussian
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherHyperbolic

noncomputable def centre {p : Params} (θ : Means p) : Space p := (1 / 2 : ℝ) • (θ 0 + θ 1)

noncomputable def half {p : Params} (θ : Means p) : Space p := (1 / 2 : ℝ) • (θ 0 - θ 1)

lemma tanh_softmax (A B : ℝ) :
    (Real.exp A - Real.exp B) / (Real.exp A + Real.exp B) = Real.tanh ((A - B) / 2) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp A = Real.exp ((A + B) / 2) * Real.exp ((A - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp B = Real.exp ((A + B) / 2) * Real.exp (-((A - B) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]
  have hp := Real.exp_pos ((A + B) / 2)
  have hq : 0 < Real.exp ((A - B) / 2) + Real.exp (-((A - B) / 2)) := by positivity
  field_simp

lemma score_closed {p : Params} (θ : Means p) (x : Space p) :
    score θ x = centre θ + Real.tanh ⟪half θ, x - centre θ⟫ • half θ - x := by
  have hs : (Real.exp (-‖x - θ 0‖ ^ 2 / 2) - Real.exp (-‖x - θ 1‖ ^ 2 / 2)) /
      (Real.exp (-‖x - θ 0‖ ^ 2 / 2) + Real.exp (-‖x - θ 1‖ ^ 2 / 2)) =
      Real.tanh ⟪half θ, x - centre θ⟫ := by
    rw [tanh_softmax]
    congr 1
    unfold half centre
    rw [norm_sub_sq_real, norm_sub_sq_real]
    simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      inner_add_right, conj_trivial, real_inner_self_eq_norm_sq]
    rw [real_inner_comm (θ 0) x, real_inner_comm (θ 1) x, real_inner_comm (θ 1) (θ 0)]
    ring
  have hpos : 0 < Real.exp (-‖x - θ 0‖ ^ 2 / 2) + Real.exp (-‖x - θ 1‖ ^ 2 / 2) := by positivity
  unfold score weight
  rw [Fin.sum_univ_two, Fin.sum_univ_two, ← hs]
  set E0 := Real.exp (-‖x - θ 0‖ ^ 2 / 2)
  set E1 := Real.exp (-‖x - θ 1‖ ^ 2 / 2)
  have hsum : E0 / (E0 + E1) + E1 / (E0 + E1) = 1 := by field_simp
  have hdiff : E0 / (E0 + E1) - E1 / (E0 + E1) = (E0 - E1) / (E0 + E1) := by ring
  have hid : ∀ c d : ℝ, c • θ 0 + d • θ 1 =
      (c + d) • ((1 / 2 : ℝ) • (θ 0 + θ 1)) + (c - d) • ((1 / 2 : ℝ) • (θ 0 - θ 1)) := by
    intro c d
    module
  unfold centre half
  rw [hid, hsum, hdiff, one_smul]


section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianPDFReal_neg_mean (m x : ℝ) :
    gaussianPDFReal (-m) 1 x = gaussianPDFReal m 1 (-x) := by
  simp only [gaussianPDFReal]
  congr 2
  ring

lemma integrable_bounded_gaussian (m : ℝ) (v : NNReal) (h : ℝ → ℝ)
    (hm : AEStronglyMeasurable h (gaussianReal m v)) {C : ℝ} (hb : ∀ x, |h x| ≤ C) :
    Integrable h (gaussianReal m v) :=
  (integrable_const C).mono' hm (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hb x))

lemma gaussian_posterior_pair (m : ℝ) (h : ℝ → ℝ) (hm : Measurable h) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) :
    (∫ x, Real.tanh (m * x) * h x ∂gaussianReal m 1) +
      (∫ x, Real.tanh (m * x) * h x ∂gaussianReal (-m) 1) =
      (∫ x, h x ∂gaussianReal m 1) - ∫ x, h x ∂gaussianReal (-m) 1 := by
  have hth : ∀ x, |Real.tanh (m * x) * h x| ≤ C := fun x => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_tanh_lt_one _).le).trans (hb x)
  have hmt : Measurable (fun x => Real.tanh (m * x) * h x) := by fun_prop
  have i1 := (integrable_gaussian_iff m 1 one_ne_zero h).mp
    (integrable_bounded_gaussian m 1 h hm.aestronglyMeasurable hb)
  have i2 := (integrable_gaussian_iff m 1 one_ne_zero _).mp
    (integrable_bounded_gaussian m 1 _ hmt.aestronglyMeasurable hth)
  have i3 := (integrable_gaussian_iff (-m) 1 one_ne_zero h).mp
    (integrable_bounded_gaussian (-m) 1 h hm.aestronglyMeasurable hb)
  have i4 := (integrable_gaussian_iff (-m) 1 one_ne_zero _).mp
    (integrable_bounded_gaussian (-m) 1 _ hmt.aestronglyMeasurable hth)
  have hpt (x : ℝ) : gaussianPDFReal m 1 x * h x - gaussianPDFReal m 1 x * (Real.tanh (m * x) * h x) =
      gaussianPDFReal (-m) 1 x * h x + gaussianPDFReal (-m) 1 x * (Real.tanh (m * x) * h x) := by
    have hbal := gaussian_posterior_balance m x
    rw [gaussianPDFReal_neg_mean]
    linear_combination h x * hbal
  have he : (∫ x, gaussianPDFReal m 1 x * h x) - (∫ x, gaussianPDFReal m 1 x * (Real.tanh (m * x) * h x)) =
      (∫ x, gaussianPDFReal (-m) 1 x * h x) + ∫ x, gaussianPDFReal (-m) 1 x * (Real.tanh (m * x) * h x) := by
    rw [← integral_sub i1 i2, ← integral_add i3 i4]
    congr 1
    ext x
    exact hpt x
  simp_rw [integral_gaussianReal_eq_integral_smul (show (1 : NNReal) ≠ 0 by norm_num), smul_eq_mul]
  linarith

end General

section Vector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_of_bound (f : E → ℝ) (hf : Continuous f) {C : ℝ} (hb : ∀ z, |f z| ≤ C) :
    Integrable f (stdGaussian E) :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun z => by simpa [Real.norm_eq_abs] using hb z))

lemma abs_tanh_le_one' (x : ℝ) : |Real.tanh x| ≤ 1 := (Real.abs_tanh_lt_one x).le

lemma abs_tanh_sq_le_one (x : ℝ) : |Real.tanh x ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (abs_tanh_le_one' x)

lemma abs_tanh_mul_le_one (x y : ℝ) : |Real.tanh x * Real.tanh y| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_tanh_le_one' x)).trans (abs_tanh_le_one' y)

lemma integral_inner_shift (u v : E) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ z, f ⟪u, v + z⟫ ∂stdGaussian E) = ∫ x, f x ∂gaussianReal ⟪u, v⟫ (‖u‖ ^ 2).toNNReal := by
  rw [← gaussian_projection_shift u v]
  exact (integral_map (by fun_prop) hf.aestronglyMeasurable).symm

lemma cross_pair (v b w : E) :
    (∫ z, Real.tanh ⟪v, v + z⟫ * Real.tanh ⟪b, w + (v + z)⟫ ∂stdGaussian E) +
      (∫ z, Real.tanh ⟪v, -v + z⟫ * Real.tanh ⟪b, w + (-v + z)⟫ ∂stdGaussian E) =
      (∫ z, Real.tanh ⟪b, w + (v + z)⟫ ∂stdGaussian E) -
        ∫ z, Real.tanh ⟪b, w + (-v + z)⟫ ∂stdGaussian E := by
  by_cases hv0 : v = 0
  · subst v
    simp
  let R := ‖v‖
  have hR : 0 < R := norm_pos_iff.mpr hv0
  let u := R⁻¹ • v
  let β := ⟪u, b⟫
  let bp := b - β • u
  let c0 := ⟪b, w⟫
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact inv_mul_cancel₀ hR.ne'
  have hvu : v = R • u := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hubp : ⟪u, bp⟫ = 0 := by
    dsimp only [bp, β]
    rw [inner_sub_right, inner_smul_right, huu]
    ring
  have hbu : ⟪b, u⟫ = β := real_inner_comm _ _
  have hb : b = β • u + bp := by dsimp only [bp]; abel
  have hs (m : ℝ) (z : E) : ⟪v, m • u + z⟫ = R * (m + ⟪u, z⟫) := by
    rw [hvu]
    simp only [inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, huu]
    ring
  have ht (m : ℝ) (z : E) :
      ⟪b, w + (m • u + z)⟫ = c0 + β * (m + ⟪u, z⟫) + ⟪bp, z⟫ := by
    have h1 : ⟪b, m • u⟫ = β * m := by rw [inner_smul_right, hbu]; ring
    have h2 : ⟪b, z⟫ = β * ⟪u, z⟫ + ⟪bp, z⟫ := by
      conv_lhs => rw [hb]
      rw [inner_add_left, inner_smul_left]
      simp
    rw [inner_add_right, inner_add_right, h1, h2]
    ring
  have hpos : v = R • u := hvu
  have hneg : -v = (-R) • u := by rw [hvu, neg_smul]
  have k1 : (∫ z, Real.tanh ⟪v, v + z⟫ * Real.tanh ⟪b, w + (v + z)⟫ ∂stdGaussian E) =
      ∫ z, Real.tanh (R * (R + ⟪u, z⟫)) * Real.tanh (c0 + β * (R + ⟪u, z⟫) + ⟪bp, z⟫)
        ∂stdGaussian E := by
    congr 1; ext z
    rw [show ⟪v, v + z⟫ = ⟪v, R • u + z⟫ by rw [← hpos], hs,
      show ⟪b, w + (v + z)⟫ = ⟪b, w + (R • u + z)⟫ by rw [← hpos], ht]
  have k2 : (∫ z, Real.tanh ⟪v, -v + z⟫ * Real.tanh ⟪b, w + (-v + z)⟫ ∂stdGaussian E) =
      ∫ z, Real.tanh (R * (-R + ⟪u, z⟫)) * Real.tanh (c0 + β * (-R + ⟪u, z⟫) + ⟪bp, z⟫)
        ∂stdGaussian E := by
    congr 1; ext z
    rw [show ⟪v, -v + z⟫ = ⟪v, (-R) • u + z⟫ by rw [← hneg], hs,
      show ⟪b, w + (-v + z)⟫ = ⟪b, w + ((-R) • u + z)⟫ by rw [← hneg], ht]
  have k3 : (∫ z, Real.tanh ⟪b, w + (v + z)⟫ ∂stdGaussian E) =
      ∫ z, Real.tanh (c0 + β * (R + ⟪u, z⟫) + ⟪bp, z⟫) ∂stdGaussian E := by
    congr 1; ext z
    rw [show ⟪b, w + (v + z)⟫ = ⟪b, w + (R • u + z)⟫ by rw [← hpos], ht]
  have k4 : (∫ z, Real.tanh ⟪b, w + (-v + z)⟫ ∂stdGaussian E) =
      ∫ z, Real.tanh (c0 + β * (-R + ⟪u, z⟫) + ⟪bp, z⟫) ∂stdGaussian E := by
    congr 1; ext z
    rw [show ⟪b, w + (-v + z)⟫ = ⟪b, w + ((-R) • u + z)⟫ by rw [← hneg], ht]
  rw [k1, k2, k3, k4]
  have hF1 : Continuous (fun q : ℝ × ℝ => Real.tanh (R * q.1) * Real.tanh (c0 + β * q.1 + q.2)) := by
    fun_prop
  have hF2 : Continuous (fun q : ℝ × ℝ => Real.tanh (c0 + β * q.1 + q.2)) := by fun_prop
  have hb1 (q : ℝ × ℝ) : |Real.tanh (R * q.1) * Real.tanh (c0 + β * q.1 + q.2)| ≤ 1 :=
    abs_tanh_mul_le_one _ _
  have hb2 (q : ℝ × ℝ) : |Real.tanh (c0 + β * q.1 + q.2)| ≤ 1 := abs_tanh_le_one' _
  have e1 := integral_orthogonal_shift u bp hu hubp R _ hF1 hb1
  have e2 := integral_orthogonal_shift u bp hu hubp (-R) _ hF1 hb1
  have e3 := integral_orthogonal_shift u bp hu hubp R _ hF2 hb2
  have e4 := integral_orthogonal_shift u bp hu hubp (-R) _ hF2 hb2
  rw [e1, e2, e3, e4]
  let h := fun s : ℝ => ∫ t, Real.tanh (c0 + β * s + t) ∂gaussianReal 0 (‖bp‖ ^ 2).toNNReal
  have hm : Measurable h := by
    have hf : StronglyMeasurable (fun q : ℝ × ℝ => Real.tanh (c0 + β * q.1 + q.2)) :=
      hF2.stronglyMeasurable
    exact hf.integral_prod_right'.measurable
  have hbh (s : ℝ) : |h s| ≤ 1 := by
    have hn := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 (‖bp‖ ^ 2).toNNReal)
      (ae_of_all _ (fun t => (show ‖Real.tanh (c0 + β * s + t)‖ ≤ 1 by
        simpa only [Real.norm_eq_abs] using abs_tanh_le_one' (c0 + β * s + t))))
    simpa [h, Real.norm_eq_abs] using hn
  simp_rw [integral_const_mul]
  exact gaussian_posterior_pair R h hm hbh

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_sq_combo (w v b : E) (T1 T2 : ℝ) :
    ‖w + T1 • v - T2 • b‖ ^ 2 = ‖w‖ ^ 2 + T1 ^ 2 * ‖v‖ ^ 2 + T2 ^ 2 * ‖b‖ ^ 2 +
      2 * T1 * ⟪w, v⟫ - 2 * T2 * ⟪w, b⟫ - 2 * (T1 * T2) * ⟪v, b⟫ := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq w,
    ← real_inner_self_eq_norm_sq v, ← real_inner_self_eq_norm_sq b]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, conj_trivial]
  rw [real_inner_comm v w, real_inner_comm b w, real_inner_comm b v]
  ring

lemma integral_expansion (w v b s : E) :
    (∫ z, ‖w + Real.tanh ⟪v, s + z⟫ • v - Real.tanh ⟪b, w + (s + z)⟫ • b‖ ^ 2
        ∂stdGaussian E) =
      ‖w‖ ^ 2 + ‖v‖ ^ 2 * (∫ z, Real.tanh ⟪v, s + z⟫ ^ 2 ∂stdGaussian E) +
        ‖b‖ ^ 2 * (∫ z, Real.tanh ⟪b, w + (s + z)⟫ ^ 2 ∂stdGaussian E) +
        2 * ⟪w, v⟫ * (∫ z, Real.tanh ⟪v, s + z⟫ ∂stdGaussian E) -
        2 * ⟪w, b⟫ * (∫ z, Real.tanh ⟪b, w + (s + z)⟫ ∂stdGaussian E) -
        2 * ⟪v, b⟫ * (∫ z, Real.tanh ⟪v, s + z⟫ * Real.tanh ⟪b, w + (s + z)⟫
          ∂stdGaussian E) := by
  have i1 := integrable_of_bound (fun z : E => Real.tanh ⟪v, s + z⟫ ^ 2) (by fun_prop)
    (fun z => abs_tanh_sq_le_one _)
  have i2 := integrable_of_bound (fun z : E => Real.tanh ⟪b, w + (s + z)⟫ ^ 2) (by fun_prop)
    (fun z => abs_tanh_sq_le_one _)
  have i3 := integrable_of_bound (fun z : E => Real.tanh ⟪v, s + z⟫) (by fun_prop)
    (fun z => abs_tanh_le_one' _)
  have i4 := integrable_of_bound (fun z : E => Real.tanh ⟪b, w + (s + z)⟫) (by fun_prop)
    (fun z => abs_tanh_le_one' _)
  have i5 := integrable_of_bound
    (fun z : E => Real.tanh ⟪v, s + z⟫ * Real.tanh ⟪b, w + (s + z)⟫) (by fun_prop)
    (fun z => abs_tanh_mul_le_one _ _)
  have hpt : ∀ z, ‖w + Real.tanh ⟪v, s + z⟫ • v - Real.tanh ⟪b, w + (s + z)⟫ • b‖ ^ 2 =
      ‖w‖ ^ 2 + ‖v‖ ^ 2 * Real.tanh ⟪v, s + z⟫ ^ 2 + ‖b‖ ^ 2 * Real.tanh ⟪b, w + (s + z)⟫ ^ 2 +
        (2 * ⟪w, v⟫) * Real.tanh ⟪v, s + z⟫ - (2 * ⟪w, b⟫) * Real.tanh ⟪b, w + (s + z)⟫ -
        (2 * ⟪v, b⟫) * (Real.tanh ⟪v, s + z⟫ * Real.tanh ⟪b, w + (s + z)⟫) := by
    intro z
    rw [norm_sq_combo]
    ring
  have hA2 : Integrable (fun z : E => ‖w‖ ^ 2 + ‖v‖ ^ 2 * Real.tanh ⟪v, s + z⟫ ^ 2)
      (stdGaussian E) := (integrable_const _).add (i1.const_mul _)
  have hA3 : Integrable (fun z : E => ‖w‖ ^ 2 + ‖v‖ ^ 2 * Real.tanh ⟪v, s + z⟫ ^ 2 +
      ‖b‖ ^ 2 * Real.tanh ⟪b, w + (s + z)⟫ ^ 2) (stdGaussian E) := hA2.add (i2.const_mul _)
  have hA4 : Integrable (fun z : E => ‖w‖ ^ 2 + ‖v‖ ^ 2 * Real.tanh ⟪v, s + z⟫ ^ 2 +
      ‖b‖ ^ 2 * Real.tanh ⟪b, w + (s + z)⟫ ^ 2 + (2 * ⟪w, v⟫) * Real.tanh ⟪v, s + z⟫)
      (stdGaussian E) := hA3.add (i3.const_mul _)
  have hA5 : Integrable (fun z : E => ‖w‖ ^ 2 + ‖v‖ ^ 2 * Real.tanh ⟪v, s + z⟫ ^ 2 +
      ‖b‖ ^ 2 * Real.tanh ⟪b, w + (s + z)⟫ ^ 2 + (2 * ⟪w, v⟫) * Real.tanh ⟪v, s + z⟫ -
      (2 * ⟪w, b⟫) * Real.tanh ⟪b, w + (s + z)⟫) (stdGaussian E) := hA4.sub (i4.const_mul _)
  rw [integral_congr_ae (ae_of_all _ hpt)]
  rw [integral_sub hA5 (i5.const_mul _), integral_sub hA4 (i4.const_mul _),
    integral_add hA3 (i3.const_mul _), integral_add hA2 (i2.const_mul _),
    integral_add (integrable_const _) (i1.const_mul _)]
  simp only [integral_const, integral_const_mul, smul_eq_mul, probReal_univ, one_mul]

lemma integral_tanh_sq_neg (v : E) :
    (∫ z, Real.tanh ⟪v, -v + z⟫ ^ 2 ∂stdGaussian E) =
      ∫ z, Real.tanh ⟪v, v + z⟫ ^ 2 ∂stdGaussian E := by
  rw [← integral_stdGaussian_neg (fun z : E => Real.tanh ⟪v, -v + z⟫ ^ 2) (by fun_prop)]
  congr 1; ext z
  rw [show -v + -z = -(v + z) by abel, inner_neg_right, Real.tanh_neg, neg_sq]

lemma integral_tanh_neg (v : E) :
    (∫ z, Real.tanh ⟪v, -v + z⟫ ∂stdGaussian E) =
      -∫ z, Real.tanh ⟪v, v + z⟫ ∂stdGaussian E := by
  rw [← integral_stdGaussian_neg (fun z : E => Real.tanh ⟪v, -v + z⟫) (by fun_prop),
    ← integral_neg]
  congr 1; ext z
  rw [show -v + -z = -(v + z) by abel, inner_neg_right, Real.tanh_neg]

lemma radial_integral (v : E) :
    ‖v‖ ^ 2 * (∫ z, Real.tanh ⟪v, v + z⟫ ^ 2 ∂stdGaussian E) = radialSelf ‖v‖ := by
  rw [integral_inner_shift v v (fun y => Real.tanh y ^ 2) (by fun_prop),
    real_inner_self_eq_norm_sq]
  have hs := gaussian_integral_scale ‖v‖ ‖v‖ (fun y => Real.tanh y ^ 2) (by fun_prop)
  rw [← pow_two ‖v‖] at hs
  rw [hs]
  rfl

lemma teacher_tanh_sq (b c : E) :
    (∫ z, Real.tanh ⟪b, c + z⟫ ^ 2 ∂stdGaussian E) =
      1 - ∫ y, sech y ^ 2 ∂gaussianReal ⟪b, c⟫ (‖b‖ ^ 2).toNNReal := by
  rw [integral_inner_shift b c (fun y => Real.tanh y ^ 2) (by fun_prop), gaussian_tanh_sq]

lemma teacher_tanh (b c : E) :
    (∫ z, Real.tanh ⟪b, c + z⟫ ∂stdGaussian E) =
      ∫ y, Real.tanh y ∂gaussianReal ⟪b, c⟫ (‖b‖ ^ 2).toNNReal :=
  integral_inner_shift b c Real.tanh (by fun_prop)

lemma pair_decomposition (w v b : E) :
    ((∫ z, ‖w + Real.tanh ⟪v, v + z⟫ • v - Real.tanh ⟪b, w + (v + z)⟫ • b‖ ^ 2
        ∂stdGaussian E) +
      ∫ z, ‖w + Real.tanh ⟪v, -v + z⟫ • v - Real.tanh ⟪b, w + (-v + z)⟫ • b‖ ^ 2
        ∂stdGaussian E) / 2 =
      ‖w‖ ^ 2 + radialSelf ‖v‖ +
        (scalarPotential ‖b‖ ⟪w + v, b⟫ + scalarPotential ‖b‖ ⟪w + -v, b⟫) / 2 := by
  rw [integral_expansion, integral_expansion, integral_tanh_sq_neg, integral_tanh_neg]
  have hc := cross_pair v b w
  simp_rw [← add_assoc] at hc ⊢
  rw [teacher_tanh_sq b (w + v), teacher_tanh_sq b (w + -v), teacher_tanh b (w + v),
    teacher_tanh b (w + -v)] at *
  have hr := radial_integral v
  unfold scalarPotential
  rw [real_inner_comm b (w + v), real_inner_comm b (w + -v)]
  have hw : ⟪w, b⟫ = (⟪b, w + v⟫ + ⟪b, w + -v⟫) / 2 := by
    rw [inner_add_right, inner_add_right, inner_neg_right, real_inner_comm w b]; ring
  have hv : ⟪v, b⟫ = (⟪b, w + v⟫ - ⟪b, w + -v⟫) / 2 := by
    rw [inner_add_right, inner_add_right, inner_neg_right, real_inner_comm v b]; ring
  rw [hw, hv]
  linear_combination hr - (⟪b, w + v⟫ - ⟪b, w + -v⟫) / 2 * hc

end Vector

lemma point_zero {p : Params} (θ : Means p) : θ 0 = centre θ + half θ := by
  unfold centre half; module

lemma point_one {p : Params} (θ : Means p) : θ 1 = centre θ + -half θ := by
  unfold centre half; module

lemma score_sub_at {p : Params} (μ θ : Means p) (s z : Space p) :
    score θ (centre θ + s + z) - score μ (centre θ + s + z) =
      (centre θ - centre μ) + Real.tanh ⟪half θ, s + z⟫ • half θ -
        Real.tanh ⟪half μ, (centre θ - centre μ) + (s + z)⟫ • half μ := by
  rw [score_closed, score_closed]
  have h1 : centre θ + s + z - centre θ = s + z := by abel
  have h2 : centre θ + s + z - centre μ = (centre θ - centre μ) + (s + z) := by abel
  rw [h1, h2]
  abel

theorem loss_decomposition {p : Params} (μ θ : Means p) :
    loss μ θ = ‖centre θ - centre μ‖ ^ 2 + radialSelf ‖half θ‖ +
      (scalarPotential ‖half μ‖ ⟪θ 0 - centre μ, half μ⟫ +
        scalarPotential ‖half μ‖ ⟪θ 1 - centre μ, half μ⟫) / 2 := by
  have h0 : θ 0 - centre μ = (centre θ - centre μ) + half θ := by rw [point_zero]; abel
  have h1 : θ 1 - centre μ = (centre θ - centre μ) + -half θ := by rw [point_one]; abel
  rw [h0, h1, ← pair_decomposition]
  unfold loss
  rw [Fin.sum_univ_two]
  congr 2
  · congr 1; ext z
    rw [point_zero, score_sub_at]
  · congr 1; ext z
    rw [point_one, score_sub_at]

end LongTails.Proofs.UntiedReverseFisherLoss
