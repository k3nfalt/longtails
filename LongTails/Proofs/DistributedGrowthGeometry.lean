import LongTails.Proofs.DistributedGrowthComparison
import LongTails.Proofs.StrongGrowthWeights
import LongTails.Proofs.SampleLossCalculus
import LongTails.Proofs.SvrgConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedGrowthGeometry

open Set
open scoped RealInnerProductSpace
open LongTails.Setups.DistributedMeanStrongGrowth
open LongTails.Algorithms.StrongGrowthWeights StrongGrowthWeights
open OracleTemplate.Gradient

variable {p : Params} {f : Functions p}

structure Geometry (p : Params) (f : Functions p) : Prop where
  valid : spec.valid p
  convex : ∀ i, ConvexOn ℝ univ (f i)
  grad : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x
  lip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x-y‖
  growth : ∀ x, ∑ i, ‖gradient (f i) x‖^2 ≤ p.n * p.ρ * ‖gradient (objective p f) x‖^2

lemma avg_grad (D : Geometry p f) (x : Point p) :
    HasGradientAt (objective p f) ((p.n : ℝ)⁻¹ • ∑ i, gradient (f i) x) x := by
  have H := OracleTemplate.FiniteSum.objective_gradient (f := f)
    (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) D.grad x
  have he : objective p f = LongTails.Setups.FiniteSumSmoothAndConvex.objective f := by
    funext y
    exact div_eq_inv_mul ..
  rw [he]
  exact H

lemma sum_grad (D : Geometry p f) (x : Point p) :
    ∑ i, gradient (f i) x = (p.n : ℝ) • gradient (objective p f) x := by
  rw [(avg_grad D x).gradient, smul_smul]
  simp [show (p.n:ℝ) ≠ 0 by exact_mod_cast p.n.ne_zero]

lemma local_min (D : Geometry p f) {z : Point p} :
    z ∈ solutions p f ↔ ∀ i, IsMinOn (f i) univ z := by
  constructor
  · intro hz i y _
    have hzero : gradient (objective p f) z = 0 := by
      change IsMinOn (objective p f) univ z at hz
      simp [gradient, (hz.isLocalMin Filter.univ_mem).fderiv_eq_zero]
    have hg := D.growth z
    rw [hzero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] at hg
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => sq_nonneg ‖gradient (f j) z‖) (Finset.mem_univ i)
    have hn : ‖gradient (f i) z‖ = 0 := by nlinarith
    have hs := convex_support (D.convex i) (D.grad i) z y
    simpa [norm_eq_zero.mp hn] using hs
  · intro hz y _
    change (∑ i, f i z) / (p.n:ℝ) ≤ (∑ i, f i y) / p.n
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hz i (mem_univ y))) (by positivity)

lemma avg_convex (D : Geometry p f) : ConvexOn ℝ univ (objective p f) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (D.convex i).2 (mem_univ x) (mem_univ y) ha hb hab)
  simp only [smul_eq_mul,Finset.sum_add_distrib, ← Finset.mul_sum] at h
  change (∑ i, f i _) / _ ≤ a*((∑ i, f i x)/_) + b*((∑ i, f i y)/_)
  simpa only [add_div, mul_div_assoc] using (div_le_div_of_nonneg_right h
    (show 0 ≤ (p.n:ℝ) by positivity))

lemma component_lip (D : Geometry p f) (i : Fin p.n) (x y : Point p) :
    ‖gradient (f i) x - gradient (f i) y‖ ≤ 3 * p.n * p.L * ‖x-y‖ := by
  have hL := D.valid.2.1.trans_le D.valid.2.2.1
  have h := SampleLossCalculus.grad_lipschitz_of_model
    (F := f i) (C := (p.n:ℝ)*p.L/2) (by positivity)
    (fun z => (D.grad i z).differentiableAt) ?_ x y
  · linarith only [h]
  intro z v
  let r (j : Fin p.n) := f j (z+v) - f j z - ⟪gradient (f j) z,v⟫
  have hr (j : Fin p.n) : 0 ≤ r j := by
    have h := convex_support (D.convex j) (D.grad j) z (z+v)
    exact sub_nonneg.mpr (by simpa only [add_sub_cancel_left] using h)
  have hu := smooth_upper_bound (fun t => (avg_grad D t).gradient ▸ avg_grad D t)
    D.lip z (z+v)
  simp only [add_sub_cancel_left] at hu
  have hs : (∑ j, r j) = (p.n : ℝ) *
      (objective p f (z+v)-objective p f z-⟪gradient (objective p f) z,v⟫) := by
    simp only [r, Finset.sum_sub_distrib, ← sum_inner, sum_grad D, real_inner_smul_left, objective]
    field_simp [show (p.n : ℝ) ≠ 0 by exact_mod_cast p.n.ne_zero]
  have hi := Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i)
  rw [hs] at hi
  rw [(D.grad i z).hasFDerivAt.fderiv, InnerProductSpace.toDual_apply_apply,
    abs_of_nonneg (hr i)]
  change r i ≤ _
  linarith only [hi, mul_le_mul_of_nonneg_left hu (show 0 ≤ (p.n:ℝ) by positivity)]

noncomputable def surrogate (p : Params) (f : Functions p) (x : Point p) :=
  ∑ i, weight p i * f i x

noncomputable def direction (p : Params) (f : Functions p) (x : Point p) :=
  ∑ i, weight p i • gradient (f i) x

lemma weighted_grad (D : Geometry p f) (x : Point p) :
    HasGradientAt (surrogate p f) (direction p f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (D.grad i x).hasFDerivAt.const_mul (weight p i))
  unfold surrogate direction
  simpa only [map_sum,map_smul] using h

lemma weighted_lip (D : Geometry p f) (x y : Point p) :
    ‖direction p f x-direction p f y‖ ≤ (∑ i, weight p i)*(3*p.n*p.L)*‖x-y‖ := by
  unfold direction
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show 0 < weight p i from div_pos (signal_pos D.valid i) (speed D.valid i))]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (component_lip D i x y)
    (div_pos (signal_pos D.valid i) (speed D.valid i)).le

lemma aligned (D : Geometry p f) (x : Point p) :
    information p * ‖gradient (objective p f) x‖^2 ≤
      ⟪direction p f x,gradient (objective p f) x⟫ := by
  let g := gradient (objective p f) x
  by_cases h : g = 0
  · change information p * ‖g‖^2 ≤ ⟪_,g⟫
    simp [h]
  have hn : 0 < ‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr h)
  let a (i : Fin p.n) := ⟪gradient (f i) x, g⟫ / ‖g‖^2
  have hsum : ∑ i, a i = p.n := by
    simp only [a, ← Finset.sum_div, ← sum_inner, sum_grad D, real_inner_smul_left]
    change (p.n : ℝ) * ⟪g,g⟫ / ‖g‖^2 = _
    rw [real_inner_self_eq_norm_sq, mul_div_cancel_right₀ _ hn.ne']
  have he : ∑ i, a i^2 ≤ p.n*p.ρ := by
    calc
      _ ≤ ∑ i, ‖gradient (f i) x‖^2 / ‖g‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [show a i^2 = ⟪gradient (f i) x,g⟫^2 / (‖g‖^2)^2 by simp [a,div_pow]]
        apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
        have hi := abs_real_inner_le_norm (gradient (f i) x) g
        have hs := mul_self_le_mul_self (abs_nonneg _) hi
        rw [← sq_abs, sq] at *
        field_simp [hn.ne']
        nlinarith [sq_abs ⟪gradient (f i) x,g⟫]
      _ ≤ _ := by rw [← Finset.sum_div]; exact (div_le_iff₀ hn).mpr (D.growth x)
  have hh := support D.valid a hsum he
  simp only [a, ← mul_div_assoc, ← Finset.sum_div] at hh
  change _ ≤ ⟪_,g⟫
  simpa only [direction,sum_inner,real_inner_smul_left] using (le_div_iff₀ hn).mp hh

lemma weighted_gap (D : Geometry p f) {z : Point p} (hz : z ∈ solutions p f) (x : Point p) :
    information p * (objective p f x - objective p f z) ≤ surrogate p f x - surrogate p f z := by
  apply DistributedGrowthComparison.gap_of_alignment (avg_convex D) _ (weighted_grad D)
    D.lip (weighted_lip D) _ (information_pos D.valid) (aligned D)
  · intro y
    rw [(avg_grad D y).gradient]
    exact avg_grad D y
  · intro y
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left ((local_min D).mp hz i (mem_univ y))
        (div_pos (signal_pos D.valid i) (speed D.valid i)).le)

end LongTails.Proofs.DistributedGrowthGeometry
