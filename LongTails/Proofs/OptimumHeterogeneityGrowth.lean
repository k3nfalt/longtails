import LongTails.Proofs.OptimumHeterogeneityDesign
import LongTails.Proofs.OptimumHeterogeneityGeometry
import LongTails.Proofs.LinearDecaySgdStep
import LongTails.Proofs.SvrgConvex

namespace LongTails.Proofs.OptimumHeterogeneityGrowth

open Set Metric LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneityDesign OptimumHeterogeneityGeometry
open scoped RealInnerProductSpace

variable {p : Params} {f : Functions p}

structure Geometry (p : Params) (f : Functions p) (z : Point p) : Prop where
  valid : spec.valid p
  convex : ∀ i, ConvexOn ℝ univ (f i)
  grad : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x
  lip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖
  optimal : z ∈ solutions p f
  initial : ‖p.x0 - z‖ ≤ p.R
  offsets : ∑ i, ‖gradient (f i) z‖ ^ 2 ≤ p.n * p.ζ ^ 2
  growth : ∀ x, p.μ / 2 * infDist x (solutions p f) ^ 2 ≤ objective p f x - objective p f z

variable {z : Point p} (D : Geometry p f z)
include D

lemma objective_grad (x : Point p) :
    HasGradientAt (objective p f) ((p.n : ℝ)⁻¹ • ∑ i, gradient (f i) x) x := by
  have h := OracleTemplate.FiniteSum.objective_gradient (f := f)
    (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) D.grad x
  have he : objective p f = LongTails.Setups.FiniteSumSmoothAndConvex.objective f := by
    funext y
    change (∑ i, f i y) / (p.n : ℝ) = (p.n : ℝ)⁻¹ * ∑ i, f i y
    rw [div_eq_inv_mul]
  rw [he]
  exact h

lemma offset_sum {y : Point p} (hy : y ∈ solutions p f) : ∑ i, gradient (f i) y = 0 := by
  have hmin := (hy.isLocalMin Filter.univ_mem).fderiv_eq_zero
  have hzero : gradient (objective p f) y = 0 := by simp [gradient, hmin]
  rw [(objective_grad D y).gradient] at hzero
  exact (smul_eq_zero.mp hzero).resolve_left (inv_ne_zero (by exact_mod_cast p.n.ne_zero))

lemma solution_closed : IsClosed (solutions p f) := by
  change IsClosed {y | IsMinOn (objective p f) univ y}
  have he : {y | IsMinOn (objective p f) univ y} =
      ⋂ x, {y | objective p f y ≤ objective p f x} := by
    ext y
    simp [IsMinOn, IsMinFilter]
  rw [he]
  exact isClosed_iInter fun x => isClosed_le
    (continuous_iff_continuousAt.mpr fun y => (objective_grad D y).continuousAt) continuous_const

lemma offset_eq {y : Point p} (hy : y ∈ solutions p f) (i : Fin p.n) :
    gradient (f i) y = gradient (f i) z := by
  let a j := remainder (f j) (gradient (f j) z) z y
  have ha j : 0 ≤ a j := (remainder_bounds (D.convex j) (D.grad j) (D.lip j) z y).1
  have he : objective p f y = objective p f z := le_antisymm (hy (mem_univ z)) (D.optimal (mem_univ y))
  change (∑ j, f j y) / (p.n : ℝ) = (∑ j, f j z) / (p.n : ℝ) at he
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  have hsum : ∑ j, a j = 0 := by
    rw [show ∑ j, a j = _ from remainder_sum f _ (offset_sum D D.optimal) z y,
      Finset.sum_sub_distrib, (div_left_inj' hn).mp he, sub_self]
  have hzi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hsum i (Finset.mem_univ i)
  have H := OracleTemplate.SampledConvex.cocoercive
    (show 0 < p.L i + 1 by linarith [D.valid.1.2.1 i]) (D.convex i) (D.grad i)
    (fun x v => (D.lip i x v).trans (by nlinarith [norm_nonneg (x-v)])) y z
  change ‖_‖ ^ 2 ≤ 2 * _ * a i at H
  rw [hzi, mul_zero] at H
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient (f i) y - gradient (f i) z)]))

lemma small_bias {y : Point p} (hy : y ∈ solutions p f) :
    ‖∑ i, weights p i • gradient (f i) y‖ ≤ p.ε / 64 := by
  let w := weights p
  have hw := (OptimumHeterogeneityDesign.weights_optimal D.valid).1.2.2
  have hb := balanced_offset w (fun i => gradient (f i) y) ((∑ i, w i) / p.n) (offset_sum D hy)
  simp_rw [offset_eq D hy] at hb ⊢
  change _ ≤ Real.sqrt (centeredEnergy p w) * _ at hb
  apply hb.trans
  have hE : 0 ≤ centeredEnergy p w := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hg : 0 ≤ ∑ i, ‖gradient (f i) z‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod := mul_le_mul_of_nonneg_left D.offsets hE
  have hh := Real.sq_sqrt hE
  have hj := Real.sq_sqrt hg
  have hpos := D.valid.1.2.2.2.2.2.2
  change 4096 * _ * _ * centeredEnergy p w ≤ _ at hw
  nlinarith only [sq_nonneg (Real.sqrt (centeredEnergy p w) * Real.sqrt (∑ i, ‖gradient (f i) z‖ ^ 2) -
    p.ε / 64), show 0 ≤ p.ε from hpos.le, hw, hprod,
    calc (Real.sqrt (centeredEnergy p w) * Real.sqrt (∑ i, ‖gradient (f i) z‖ ^ 2)) ^ 2
        = centeredEnergy p w * (∑ i, ‖gradient (f i) z‖ ^ 2) := by rw [mul_pow, hh, hj]]

lemma weighted_growth {y : Point p} (hy : y ∈ solutions p f) (x : Point p)
    (hd : infDist x (solutions p f) = ‖x-y‖) :
    ‖x-y‖ ^ 2 / 2 ≤ ∑ i, weights p i * remainder (f i) (gradient (f i) y) y x := by
  let s := ‖x-y‖ ^ 2 / 2
  let a i := remainder (f i) (gradient (f i) y) y x
  have ha i := remainder_bounds (D.convex i) (D.grad i) (D.lip i) y x
  have hw := (OptimumHeterogeneityDesign.weights_optimal D.valid).1
  by_cases hs : 0 < s
  · have hsum := remainder_sum f _ (offset_sum D hy) y x
    have he : objective p f y = objective p f z := le_antisymm (hy (mem_univ z)) (D.optimal (mem_univ y))
    have hg := D.growth x
    rw [← he, hd] at hg
    change _ ≤ (∑ i, f i x) / (p.n : ℝ) - (∑ i, f i y) / (p.n : ℝ) at hg
    rw [← sub_div] at hg
    have hh := (le_div_iff₀ (by exact_mod_cast p.n.pos : (0 : ℝ) < p.n)).mp hg
    have had : (fun i => a i / s) ∈ admissibleCurvatures p := by
      refine ⟨fun i => ⟨div_nonneg (ha i).1 hs.le, (div_le_iff₀ hs).mpr (ha i).2⟩, ?_⟩
      rw [← Finset.sum_div]
      apply (le_div_iff₀ hs).mpr
      dsimp only [a]
      rw [hsum, Finset.sum_sub_distrib]
      dsimp only [s]
      linarith
    have h := hw.2.1 _ had
    simp only [← mul_div_assoc, ← Finset.sum_div] at h
    simpa only [one_mul] using (le_div_iff₀ hs).mp h
  · exact le_trans (le_of_not_gt hs) (Finset.sum_nonneg fun i _ => mul_nonneg (hw.1 i) (ha i).1)

end LongTails.Proofs.OptimumHeterogeneityGrowth
