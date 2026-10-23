import LongTails.Proofs.GaussianBlocks
import LongTails.Proofs.SymmetricReverseFisherHermite

namespace LongTails.Proofs.GaussianLinear

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.GaussianBlocks
open scoped NNReal

lemma linear_law (w : ℕ → ℝ) (K : ℕ) :
    stdStream.map (fun τ : ℕ → ℝ => ∑ k ∈ Finset.range K, w k * τ k) =
      gaussianReal 0 (∑ k ∈ Finset.range K, w k ^ 2).toNNReal := by
  induction K with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Real.toNNReal_zero, gaussianReal_zero_var]
      rw [Measure.map_const]
      simp
  | succ K ih =>
      have hii : iIndepFun (fun k (τ : ℕ → ℝ) => w k * τ k) stdStream :=
        (iIndepFun_infinitePi (X := fun _ (ω : ℝ) => ω) (fun _ => measurable_id)).comp
          (fun k (x : ℝ) => w k * x) (fun k => measurable_const.mul measurable_id)
      have hind : IndepFun (∑ k ∈ Finset.range K, fun τ : ℕ → ℝ => w k * τ k)
          (fun τ => w K * τ K) stdStream :=
        hii.indepFun_finsetSum_of_notMem
          (fun k => (by fun_prop : Measurable fun τ : ℕ → ℝ => w k * τ k))
          (by simp)
      have hX : HasLaw (∑ k ∈ Finset.range K, fun τ : ℕ → ℝ => w k * τ k)
          (gaussianReal 0 (∑ k ∈ Finset.range K, w k ^ 2).toNNReal) stdStream := by
        refine ⟨by fun_prop, ?_⟩
        rw [← ih]
        congr 1
        funext τ
        simp
      have hY : HasLaw (fun τ : ℕ → ℝ => w K * τ K) (gaussianReal 0 (w K ^ 2).toNNReal)
          stdStream := by
        refine ⟨(by fun_prop : Measurable fun τ : ℕ → ℝ => w K * τ K).aemeasurable, ?_⟩
        have hc : (fun τ : ℕ → ℝ => w K * τ K) = (fun x => w K * x) ∘ (fun τ => τ K) := rfl
        rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop), Measure.infinitePi_map_eval,
          gaussianReal_map_const_mul]
        congr 1
        · simp
        · ext
          simp [Real.coe_toNNReal', max_eq_left (sq_nonneg (w K))]
      have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hX hY
      have he : (∑ k ∈ Finset.range K, fun τ : ℕ → ℝ => w k * τ k) + (fun τ => w K * τ K) =
          fun τ : ℕ → ℝ => ∑ k ∈ Finset.range (K + 1), w k * τ k := by
        funext τ
        simp [Finset.sum_range_succ]
      rw [he] at hsum
      rw [hsum]
      congr 1
      · simp
      · ext
        have h1 : 0 ≤ ∑ k ∈ Finset.range K, w k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
        simp [Real.coe_toNNReal', max_eq_left h1, max_eq_left (sq_nonneg (w K)),
          Finset.sum_range_succ, max_eq_left (add_nonneg h1 (sq_nonneg (w K)))]

lemma gaussian_moments (V : ℝ) (hV : 0 ≤ V) :
    (∫ x, x ^ 2 ∂gaussianReal 0 V.toNNReal) = V ∧
      (∫ x, x ^ 4 ∂gaussianReal 0 V.toNNReal) = 3 * V ^ 2 := by
  have hmap : gaussianReal 0 V.toNNReal = (gaussianReal 0 1).map (fun z => Real.sqrt V * z) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.coe_toNNReal', max_eq_left hV, Real.sq_sqrt hV]
  rw [hmap]
  constructor
  · rw [integral_map (by fun_prop) (by fun_prop)]
    have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [variance_eq_integral (measurable_id.aemeasurable)] at hv
    simp only [integral_id_gaussianReal, sub_zero, id_eq, NNReal.coe_one] at hv
    simp_rw [mul_pow, Real.sq_sqrt hV]
    rw [integral_const_mul, hv, mul_one]
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [mul_pow]
    rw [integral_const_mul, LongTails.Proofs.SymmetricReverseFisherHermite.gaussian_fourth_moment]
    have h4 : Real.sqrt V ^ 4 = V ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hV]
    rw [h4]
    ring

lemma abs_lower (a x : ℝ) (ha : 0 < a) : x ^ 2 / a - x ^ 4 / (4 * a ^ 3) ≤ |x| := by
  have hu : |x| / a - (|x| / a) ^ 2 + (|x| / a) ^ 4 / 4 ≥ 0 := by
    set u := |x| / a
    have hu0 : 0 ≤ u := div_nonneg (abs_nonneg x) ha.le
    nlinarith [sq_nonneg (u - 1), sq_nonneg u, sq_nonneg (u ^ 2 - 2), mul_nonneg hu0 (sq_nonneg (u - 1)),
      mul_nonneg hu0 (sq_nonneg (u ^ 2 / 2 - 1))]
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hx4 : x ^ 4 = |x| ^ 4 := (Even.pow_abs (by decide) x).symm
  rw [hx2, hx4]
  have : |x| ^ 2 / a - |x| ^ 4 / (4 * a ^ 3) = a * ((|x| / a) ^ 2 - (|x| / a) ^ 4 / 4) := by
    field_simp
  rw [this]
  have hx : |x| = a * (|x| / a) := by field_simp
  nlinarith [hu, ha]

lemma gaussian_abs_lower (V : ℝ) (hV : 0 ≤ V) :
    (4 / 9) * Real.sqrt V ≤ ∫ x, |x| ∂gaussianReal 0 V.toNNReal := by
  rcases hV.eq_or_lt with h0 | hpos
  · subst h0
    simp only [Real.sqrt_zero, mul_zero]
    exact integral_nonneg fun _ => abs_nonneg _
  have ha : 0 < 3 / 2 * Real.sqrt V := by positivity
  obtain ⟨h2, h4⟩ := gaussian_moments V hV
  have hi2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 V.toNNReal) :=
    (memLp_id_gaussianReal 2).integrable_norm_pow' |>.congr (by
      filter_upwards with x; simp [Real.norm_eq_abs, sq_abs])
  have hi4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 V.toNNReal) :=
    (memLp_id_gaussianReal 4).integrable_norm_pow' |>.congr (by
      filter_upwards with x; simp [Real.norm_eq_abs]; exact Even.pow_abs (by decide) x)
  have hia : Integrable (fun x : ℝ => |x|) (gaussianReal 0 V.toNNReal) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hm := integral_mono ((hi2.div_const _).sub (hi4.div_const _)) hia
    (fun x => abs_lower (3 / 2 * Real.sqrt V) x ha)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub (hi2.div_const _) (hi4.div_const _), integral_div, integral_div, h2, h4] at hm
  have hs : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV
  have hspos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hpos
  have heq : V / (3 / 2 * Real.sqrt V) - 3 * V ^ 2 / (4 * (3 / 2 * Real.sqrt V) ^ 3) =
      (4 / 9) * Real.sqrt V := by
    have hV2 : V = Real.sqrt V ^ 2 := hs.symm
    set q := Real.sqrt V with hq
    rw [hV2]
    field_simp
    ring
  linarith

end LongTails.Proofs.GaussianLinear
