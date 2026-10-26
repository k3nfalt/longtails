import LongTails.Proofs.HilbertSmallMoments
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory

namespace LongTails.Proofs.AffineAdamBatchMoments

lemma batch_power_scale {p S : ℝ} (hp : 1 < p) (hS : 0 ≤ S) (n : ℕ) (hn : 0 < n) :
    4 * (n : ℝ) ^ (1 - p) * S ^ p ≤
      (4 * (n : ℝ) ^ ((1 - p) / p) * S) ^ p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.mul_rpow (by positivity) hS, Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_mul hn0.le, div_mul_cancel₀ _ (by linarith : p ≠ 0)]
  have h4 : (4 : ℝ) ≤ (4 : ℝ) ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) hp.le
  gcongr

lemma scalar_batch_first_moment {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {p g a b : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : Measurable X) (hi : Integrable X P)
    (hpi : Integrable (fun ω => |X ω - g| ^ p) P)
    (hm : ∫ ω, X ω ∂P = g)
    (hbound : (∫ ω, |X ω - g| ^ p ∂P) ≤ a ^ p + b ^ p * |g| ^ p)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => |(n : ℝ)⁻¹ * ∑ i, X (ξ i) - g|)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin n → Ω, |(n : ℝ)⁻¹ * ∑ i, X (ξ i) - g|
      ∂Measure.pi (fun _ => P)) ≤ 4 * (n : ℝ) ^ ((1 - p) / p) * (a + b * |g|) := by
  have hs (i : Fin n) : Integrable (fun ξ : Fin n → Ω => X (ξ i)) (Measure.pi fun _ => P) :=
    integrable_comp_eval hi
  have hei : Integrable (fun ξ : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i, X (ξ i) - g)
      (Measure.pi fun _ => P) :=
    ((integrable_finsetSum _ (fun i _ => hs i)).const_mul _).sub (integrable_const g)
  have hp' := HilbertSmallMoments.iid_centered_mean_power_bound hX hp.le hp2 hi g
    (by simpa only [Real.norm_eq_abs] using hpi) hm n hn
  simp only [smul_eq_mul, Real.norm_eq_abs] at hp'
  refine ⟨hei.abs, ?_⟩
  change (∫ ξ : Fin n → Ω, ‖(n : ℝ)⁻¹ * ∑ i, X (ξ i) - g‖ ∂Measure.pi (fun _ => P)) ≤ _
  apply HilbertSmallMoments.first_power_from_moment hp.le (by positivity)
    (by simpa only [Real.norm_eq_abs] using hei.abs)
    (by simpa only [Real.norm_eq_abs] using hp'.1)
  have hsum : a ^ p + b ^ p * |g| ^ p ≤ (a + b * |g|) ^ p := by
    rw [← Real.mul_rpow hb (abs_nonneg g)]
    exact Real.add_rpow_le_rpow_add ha (mul_nonneg hb (abs_nonneg g)) hp.le
  exact hp'.2.trans ((mul_le_mul_of_nonneg_left (hbound.trans hsum)
    (by positivity : 0 ≤ 4 * (n : ℝ) ^ (1 - p))).trans
      (batch_power_scale hp (by positivity) n hn))

end LongTails.Proofs.AffineAdamBatchMoments
