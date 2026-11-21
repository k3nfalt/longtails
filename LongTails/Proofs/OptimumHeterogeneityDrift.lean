import LongTails.Proofs.OptimumHeterogeneityGrowth
import LongTails.Proofs.OptimumHeterogeneityAllocation
import LongTails.Proofs.WeakInterpolationGeometry

namespace LongTails.Proofs.OptimumHeterogeneityDrift

open Metric LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneityDesign LongTails.Algorithms.OptimumHeterogeneitySgd
open OptimumHeterogeneityAllocation OptimumHeterogeneityGrowth OptimumHeterogeneityGeometry
open scoped RealInnerProductSpace

variable {p : Params} {f : Functions p} {z : Point p}

noncomputable def direction (p : Params) (f : Functions p) (x : Point p) :=
  ∑ i, weights p i • gradient (f i) x

noncomputable def gap (p : Params) (f : Functions p) (y x : Point p) :=
  ∑ i, weights p i * remainder (f i) (gradient (f i) y) y x

lemma gradient_difference (D : Geometry p f z) (y x : Point p) :
    ‖direction p f x - direction p f y‖ ^ 2 ≤
      2 * capacity p p.L * gap p f y x := by
  let w := weights p
  let a i := remainder (f i) (gradient (f i) y) y x
  have hw (i) : 0 ≤ w i := weight_nn D.valid i
  have ha i : 0 ≤ a i := (remainder_bounds (D.convex i) (D.grad i) (D.lip i) y x).1
  have hL := D.valid.1.2.1
  have hc (i) : ‖gradient (f i) x - gradient (f i) y‖ ^ 2 ≤ 2 * p.L i * a i := by
    rcases (hL i).eq_or_lt with h | h
    · have h0 : gradient (f i) x - gradient (f i) y = 0 :=
        norm_le_zero_iff.mp (by simpa [← h] using D.lip i x y)
      simp [h0, ← h]
    · exact OracleTemplate.SampledConvex.cocoercive h (D.convex i) (D.grad i) (D.lip i) x y
  have hterm (i) : w i * ‖gradient (f i) x - gradient (f i) y‖ ≤
      Real.sqrt (2 * w i * p.L i) * Real.sqrt (w i * a i) := by
    have h₁ := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hw i)) (hL i))
    have h₂ := Real.sq_sqrt (mul_nonneg (hw i) (ha i))
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [mul_pow, mul_pow, h₁, h₂]
    linarith [mul_le_mul_of_nonneg_left (hc i) (sq_nonneg (w i))]
  have h₁ : ‖direction p f x - direction p f y‖ ≤
      ∑ i, Real.sqrt (2 * w i * p.L i) * Real.sqrt (w i * a i) := by
    unfold direction
    rw [← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    calc
      _ ≤ ∑ i, ‖w i • (gradient (f i) x - gradient (f i) y)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => by simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)] using hterm i
  have h₂ := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i => mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hw i)) (hL i))
    (fun i => mul_nonneg (hw i) (ha i))
  have h := pow_le_pow_left₀ (norm_nonneg _) (h₁.trans h₂) 2
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hw i)) (hL i)),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (ha i))] at h
  simp_rw [mul_assoc, ← Finset.mul_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (curvature_bound D.valid) (by norm_num))
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (ha i)))

lemma corrected_step (D : Geometry p f z) (k : ℕ) (y x : Point p) :
    ‖x - stepSize p k • (direction p f x - direction p f y) - y‖ ^ 2 ≤
      ‖x-y‖ ^ 2 - stepSize p k * gap p f y x := by
  have hcap := curvature_bound D.valid
  have hw := (OptimumHeterogeneityDesign.weights_optimal D.valid).1
  have hone := hw.2.1 p.L ⟨fun i => ⟨D.valid.1.2.1 i, le_rfl⟩, D.valid.1.2.2.2.1⟩
  apply WeakInterpolationGeometry.deterministic_step (p := p.toParams)
    (lt_of_lt_of_le zero_lt_one (hone.trans hcap)) (step_bounds D.valid k).1
    ((step_bounds D.valid k).2.2.trans (by norm_num : (1:ℝ)/4 ≤ 1/2))
  · unfold direction
    rw [← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    exact weighted_radial f _ _ hw.1 D.convex D.grad y x
  · exact gradient_difference D y x

end LongTails.Proofs.OptimumHeterogeneityDrift
