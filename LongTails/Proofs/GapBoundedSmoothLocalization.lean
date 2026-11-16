import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapBoundedSmoothLocalization

open AdaptivePolynomialLocalization AdaptiveGeneralizedSmoothLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma localized_curvature (s : Seed (E := E)) (L a B : ℝ)
    (hL : 0 ≤ L) (ha : 0 < a) (hB : 0 < B) (hrB : 2 * s.r ≤ B)
    (hGa : s.G ≤ a * B) (hcurv : ∀ x, ‖fderiv ℝ s.g x‖ ≤ L) (x : E) :
    ‖fderiv ℝ (field s.f s.g 2 a B (a * B ^ 2)) x‖ ≤ L + 376 * a := by
  have hp := AdaptivePolynomialHinge.mixing_bounds 2 ((wall a B x - s.f x) / (a * B ^ 2))
  change 0 ≤ mixing s.f 2 a B (a * B ^ 2) x ∧
    mixing s.f 2 a B (a * B ^ 2) x ≤ 1 at hp
  have hd := field_derivative_norm_bound s.f s.g 2 (by norm_num) a B (a * B ^ 2)
    ha.le (by positivity) x (fderiv ℝ s.g x) (s.gradient x) (s.differentiable x).hasFDerivAt
  have ht := transition_term s 2 (by norm_num) a B ha hB hrB hGa x
  norm_num at ht
  have hfirst := mul_le_mul_of_nonneg_left (hcurv x) (sub_nonneg.mpr hp.2)
  have hfirst' : (1 - mixing s.f 2 a B (a * B ^ 2) x) * L ≤ L := by
    nlinarith [mul_nonneg hp.1 hL]
  have hsecond := mul_le_mul_of_nonneg_right hp.2 ha.le
  have htrans : mixingDerivative s.f 2 a B (a * B ^ 2) x * ‖a • x - s.g x‖ ^ 2 ≤
      375 * a := by nlinarith [mul_le_mul_of_nonneg_right hp.2 ha.le]
  linarith

end LongTails.Proofs.GapBoundedSmoothLocalization
