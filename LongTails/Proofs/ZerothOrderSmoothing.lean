import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import LongTails.Algorithms.AcceleratedZerothOrderConvex
import LongTails.Proofs.AcceleratedMarkovRun
import LongTails.Proofs.GdConvex
import LongTails.Proofs.ZerothOrderEstimator

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma finite_average_distance {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ι → E) (c : E) {B : ℝ}
    (hb : ∀ i, ‖g i-c‖ ≤ B) :
    ‖(Fintype.card ι : ℝ)⁻¹ • (∑ i, g i)-c‖ ≤ B := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card ι : ℝ)⁻¹ • (∑ i, g i)-c =
      (Fintype.card ι : ℝ)⁻¹ • (∑ i, (g i-c)) := by
    rw [Finset.sum_sub_distrib,smul_sub,Finset.sum_const,Finset.card_univ]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hn.ne',one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * (∑ i, ‖g i-c‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * (∑ _i : ι, B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) (inv_nonneg.mpr hn.le)
    _ = B := by simp [hn.ne']

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma sum_coordinate_resampling {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (i : ι) (F : (ι → α) → ℝ) :
    (∑ v : ι → α, ∑ j : α, F (Function.update v i j)) =
      (Fintype.card α : ℝ)*(∑ v : ι → α, F v) := by
  classical
  let T : ((ι → α) × α) → ((ι → α) × α) := fun p => (Function.update p.1 i p.2,p.1 i)
  have hT : Function.Involutive T := by
    intro ⟨v,j⟩
    apply Prod.ext
    · funext k
      by_cases hk : k=i
      · subst k
        simp [T]
      · simp [T,Function.update_of_ne hk]
    · simp [T]
  have hs := Equiv.sum_comp (hT.toPerm T) (fun p : (ι → α) × α => F p.1)
  simp only [Function.Involutive.coe_toPerm, T, Fintype.sum_prod_type] at hs
  calc
    _ = ∑ v : ι → α, ∑ _j : α, F v := hs
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rw [Finset.mul_sum]

lemma coordinate_average_error {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Nonempty α] (i : ι) (B G : (ι → α) → ℝ) {b : ℝ}
    (herr : ∀ v, |B v-(∑ j : α, G (Function.update v i j))/(Fintype.card α : ℝ)| ≤ b) :
    |(∑ v : ι → α, B v)/(Fintype.card (ι → α) : ℝ)-
      (∑ v : ι → α, G v)/(Fintype.card (ι → α) : ℝ)| ≤ b := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card (ι → α) := by exact_mod_cast Fintype.card_pos
  have heq : (∑ v : ι → α, B v)-(∑ v : ι → α, G v) =
      ∑ v : ι → α, (B v-(∑ j : α, G (Function.update v i j))/(Fintype.card α : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_coordinate_resampling i G]
    field_simp
  rw [← sub_div, heq, abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ ∑ v : ι → α, |B v-(∑ j : α, G (Function.update v i j))/(Fintype.card α : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : ι → α, b := Finset.sum_le_sum (fun v _ => herr v)
    _ = _ := by simp; ring

end OracleTemplate.ZerothOrder

end

section

open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smoothed_cut {G : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ G) (hg : ∀ x, HasGradientAt G (g x) x)
    {x u : E} {H b : ℝ}
    (hmid : G ((1 / 2 : ℝ) • (x + u)) ≤ (H + b) / 2)
    (hgap : H - G x ≤ (G x - b) / 4) :
    3 / 4 * (G x - b) ≤ ⟪g x, x - u⟫ := by
  have hs := Gradient.convex_support hc hg x ((1 / 2 : ℝ) • (x + u))
  have he : (1 / 2 : ℝ) • (x + u) - x = (-1 / 2 : ℝ) • (x - u) := by module
  rw [he, inner_smul_right] at hs
  linarith

lemma noisy_smoothed_cut {G : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ G) (hg : ∀ x, HasGradientAt G (g x) x)
    {x u v : E} {H b : ℝ}
    (hmid : G ((1 / 2 : ℝ) • (x + u)) ≤ (H + b) / 2)
    (hgap : H - G x ≤ (G x - b) / 4)
    (herr : |⟪v - g x, x - u⟫| ≤ (G x - b) / 4) :
    ⟪v, u - x⟫ ≤ -(G x - b) / 2 := by
  have hs := smoothed_cut hc hg hmid hgap
  have he := (abs_le.mp herr).1
  rw [inner_sub_left] at he
  have hd : u - x = -(x - u) := by module
  rw [hd, inner_neg_right]
  linarith

omit [CompleteSpace E] in
lemma weighted_midpoint_bound {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    {f : E → ℝ} (hc : ConvexOn ℝ Set.univ f) (z : ι → E) (x u : E) :
    (∑ i ∈ s, w i * f ((1 / 2 : ℝ) • (x + u) + z i)) ≤
      ((∑ i ∈ s, w i * f (x + (2 : ℝ) • z i)) + f u) / 2 := by
  have hi (i : ι) : f ((1 / 2 : ℝ) • (x + u) + z i) ≤
      (f (x + (2 : ℝ) • z i) + f u) / 2 := by
    have h := hc.2 (Set.mem_univ (x + (2 : ℝ) • z i)) (Set.mem_univ u)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have he : (1 / 2 : ℝ) • (x + (2 : ℝ) • z i) + (1 / 2 : ℝ) • u =
        (1 / 2 : ℝ) • (x + u) + z i := by module
    rw [he] at h
    simp only [smul_eq_mul] at h
    linarith
  calc
    _ ≤ ∑ i ∈ s, w i * ((f (x + (2 : ℝ) • z i) + f u) / 2) :=
      Finset.sum_le_sum (fun i hi' => mul_le_mul_of_nonneg_left (hi i) (hw i hi'))
    _ = ((∑ i ∈ s, w i * f (x + (2 : ℝ) • z i)) + f u) / 2 := by
      simp_rw [add_div, mul_add, ← mul_div_assoc]
      rw [Finset.sum_add_distrib]
      simp only [← Finset.sum_div, ← Finset.sum_mul, hs]
      ring

lemma weighted_support {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (z : ι → E) (x y : E) :
    ⟪∑ i ∈ s, w i • g (x + z i), y - x⟫ ≤
      (∑ i ∈ s, w i * f (y + z i)) - (∑ i ∈ s, w i * f (x + z i)) := by
  simp only [sum_inner, real_inner_smul_left]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := Gradient.convex_support hc hg (x+z i) (y+z i)
  rw [add_sub_add_right_eq_sub] at h
  simpa only [mul_sub] using mul_le_mul_of_nonneg_left h (hw i hi)

lemma weighted_smoothed_cut {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    {f : E → ℝ} {g : E → E} (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (z : ι → E) (x u : E)
    (hgap : (∑ i ∈ s, w i * f (x + (2 : ℝ) • z i)) -
      (∑ i ∈ s, w i * f (x + z i)) ≤
        ((∑ i ∈ s, w i * f (x + z i)) - f u) / 4) :
    3 / 4 * ((∑ i ∈ s, w i * f (x + z i)) - f u) ≤
      ⟪∑ i ∈ s, w i • g (x + z i), x - u⟫ := by
  have hm := weighted_midpoint_bound s w hw hs hc z x u
  have hb := weighted_support s w hw hc hg z x ((1/2 : ℝ) • (x+u))
  have he : (1/2 : ℝ) • (x+u) - x = (-1/2 : ℝ) • (x-u) := by module
  rw [he, inner_smul_right] at hb
  linarith

end OracleTemplate.ZerothOrder

end

section

open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma finite_smoothing_gap {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (z : ι → E) (hz : ∑ i ∈ s, w i • z i = 0) (x : E) :
    0 ≤ (∑ i ∈ s, w i*f (x+z i))-f x ∧
      (∑ i ∈ s, w i*f (x+z i))-f x ≤ L/2*(∑ i ∈ s, w i*‖z i‖^2) := by
  have hlin : (∑ i ∈ s, w i*⟪g x,z i⟫) = 0 := by
    simp only [← inner_smul_right, ← inner_sum, hz, inner_zero_right]
  have hbase : (∑ i ∈ s, w i*f x) = f x := by rw [← Finset.sum_mul, hs, one_mul]
  have hlo := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (Gradient.convex_support hc hg x (x+z i)) (hw i hi))
  simp only [add_sub_cancel_left, mul_sub, Finset.sum_sub_distrib, hlin, hbase] at hlo
  have hup := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (Gradient.smooth_upper_bound hg hlip x (x+z i)) (hw i hi))
  simp only [add_sub_cancel_left, mul_add, Finset.sum_add_distrib, hlin, hbase, add_zero] at hup
  have hquad : (∑ i ∈ s, w i*(L/2*‖z i‖^2)) = L/2*(∑ i ∈ s, w i*‖z i‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hquad] at hup
  exact ⟨hlo, by linarith⟩

lemma finite_smoothing_gradient {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {f : E → ℝ} {g : E → E} (hg : ∀ x, HasGradientAt f (g x) x)
    (z : ι → E) (x : E) :
    HasGradientAt (fun y => ∑ i ∈ s, w i*f (y+z i))
      (∑ i ∈ s, w i • g (x+z i)) x := by
  have hi (i : ι) : HasFDerivAt (fun y => w i*f (y+z i))
      (w i • (InnerProductSpace.toDual ℝ E) (g (x+z i))) x := by
    simpa using (((hg (x+z i)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const (z i))).const_mul (w i))
  have hsum := HasFDerivAt.sum (u := s) (fun i _ => hi i)
  change HasFDerivAt _ ((InnerProductSpace.toDual ℝ E) (∑ i ∈ s, w i • g (x+z i))) x
  convert hsum using 1
  · ext y
    simp only [Finset.sum_apply]
  · simp

omit [CompleteSpace E] in
lemma finite_smoothing_lipschitz {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    {g : E → E} {L : ℝ} (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (z : ι → E) (x y : E) :
    ‖(∑ i ∈ s, w i • g (x+z i))-(∑ i ∈ s, w i • g (y+z i))‖ ≤ L*‖x-y‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖w i • g (x+z i)-w i • g (y+z i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, w i*(L*‖x-y‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      have h := hlip (x+z i) (y+z i)
      rw [add_sub_add_right_eq_sub] at h
      exact mul_le_mul_of_nonneg_left h (hw i hi)
    _ = L*‖x-y‖ := by rw [← Finset.sum_mul, hs, one_mul]

omit [CompleteSpace E] in
lemma finite_smoothing_convex {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (z : ι → E) :
    ConvexOn ℝ Set.univ (fun x => ∑ i ∈ s, w i*f (x+z i)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh := hc.2 (Set.mem_univ (x+z i)) (Set.mem_univ (y+z i)) ha hb hab
  have he : a • (x+z i)+b • (y+z i) = a • x+b • y+z i := by
    rw [smul_add, smul_add]
    have hz : a • z i+b • z i = z i := by rw [← add_smul, hab, one_smul]
    calc
      _ = a • x+b • y+(a • z i+b • z i) := by abel
      _ = _ := by rw [hz]
  rw [he] at hh
  simp only [smul_eq_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (hw i hi)
  nlinarith only [hh']

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma midpointCoordinate_abs {m : ℕ} {h : ℝ} (hh : 0 ≤ h) (j : Fin m) :
    |midpointCoordinate h j| ≤ h := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j:ℝ)+1 ≤ m := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j := by positivity
  apply abs_le.mpr
  unfold midpointCoordinate
  have hl : 0 ≤ (2*(j:ℝ)+1)*h/m := by positivity
  have hu : (2*(j:ℝ)+1)*h/m ≤ 2*h := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_right hj hh]
  constructor <;> linarith

lemma midpointPoint_apply {d m : ℕ} (h : ℝ) (v : Fin d → Fin m) (i : Fin d) :
    midpointPoint h v i = midpointCoordinate h (v i) := rfl

lemma midpointPoint_update {d m : ℕ} (h : ℝ) (v : Fin d → Fin m) (i : Fin d) (j : Fin m) :
    midpointPoint h (Function.update v i j) = midpointPoint h v+
      (midpointCoordinate h j-midpointCoordinate h (v i)) • direction i := by
  ext k
  by_cases hk : k=i
  · subst k
    simp [midpointPoint_apply,PiLp.add_apply,PiLp.smul_apply,direction,EuclideanSpace.basisFun_apply]
  · simp [midpointPoint_apply,PiLp.add_apply,PiLp.smul_apply,direction,EuclideanSpace.basisFun_apply,
      hk]

lemma midpointCoordinate_rev {m : ℕ} (h : ℝ) (j : Fin m) :
    midpointCoordinate h j.rev = -midpointCoordinate h j := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j:ℝ)+(j.rev:ℝ)+1 = m := by
    have hjn : j.val+j.rev.val+1 = m := by simp only [Fin.val_rev]; omega
    exact_mod_cast hjn
  unfold midpointCoordinate
  apply (mul_right_cancel₀ (ne_of_gt hm))
  field_simp
  linear_combination 2*h*hj

lemma midpointCoordinate_sum {m : ℕ} (h : ℝ) : ∑ j : Fin m, midpointCoordinate h j = 0 := by
  have he := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin m)) (midpointCoordinate h)
  change (∑ j : Fin m, midpointCoordinate h j.rev) = ∑ j : Fin m, midpointCoordinate h j at he
  simp_rw [midpointCoordinate_rev,Finset.sum_neg_distrib] at he
  linarith

lemma midpointPoint_sum {d m : ℕ} (h : ℝ) (hm : 0 < m) :
    ∑ v : Fin d → Fin m, midpointPoint h v = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  ext i
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.zero_apply,midpointPoint_apply]
  have hs := sum_coordinate_resampling i (fun v : Fin d → Fin m => midpointCoordinate h (v i))
  simp only [Function.update_self,midpointCoordinate_sum,Finset.sum_const_zero,Fintype.card_fin] at hs
  nlinarith

end OracleTemplate.ZerothOrder

end

section

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def gridSmooth {d : ℕ} (f : Point d → ℝ) (h : ℝ) (m : ℕ) (x : Point d) : ℝ :=
  (Fintype.card (Fin d → Fin m) : ℝ)⁻¹ * ∑ v : Fin d → Fin m, f (x+midpointPoint h v)

noncomputable def gridGradient {d : ℕ} (f : Point d → ℝ) (h : ℝ) (m : ℕ) (x : Point d) : Point d :=
  (Fintype.card (Fin d → Fin m) : ℝ)⁻¹ • ∑ v : Fin d → Fin m, gradient f (x+midpointPoint h v)

lemma midpointPoint_norm_sq {d m : ℕ} {h : ℝ} (hh : 0 ≤ h) (v : Fin d → Fin m) :
    ‖midpointPoint h v‖^2 ≤ (d:ℝ)*h^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin d, h^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have he := midpointCoordinate_abs hh (v i)
      change (midpointCoordinate h (v i))^2 ≤ h^2
      nlinarith [sq_abs (midpointCoordinate h (v i)),mul_self_le_mul_self (abs_nonneg _) he]
    _ = _ := by simp

lemma grid_smoothing_gap {d m : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L) (hh : 0 ≤ h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    0 ≤ gridSmooth f h m x-f x ∧ gridSmooth f h m x-f x ≤ L*(d:ℝ)*h^2/2 := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let N : ℝ := Fintype.card (Fin d → Fin m)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hw : (∑ _v : Fin d → Fin m, N⁻¹) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have hz : (∑ v : Fin d → Fin m, N⁻¹ • midpointPoint h v) = 0 := by
    rw [← Finset.smul_sum,midpointPoint_sum h hm,smul_zero]
  have hs := finite_smoothing_gap Finset.univ (fun _ : Fin d → Fin m => N⁻¹)
    (fun _ _ => inv_nonneg.mpr hN.le) hw hc hg hlip (midpointPoint h) hz x
  simp only [← Finset.mul_sum] at hs
  change 0 ≤ gridSmooth f h m x-f x ∧ gridSmooth f h m x-f x ≤ _ at hs
  have hnorm : N⁻¹*(∑ v : Fin d → Fin m, ‖midpointPoint h v‖^2) ≤ (d:ℝ)*h^2 := by
    calc
      _ ≤ N⁻¹*(∑ _v : Fin d → Fin m, (d:ℝ)*h^2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => midpointPoint_norm_sq hh v)) (inv_nonneg.mpr hN.le)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        change N⁻¹*(N*((d:ℝ)*h^2)) = _
        rw [← mul_assoc,inv_mul_cancel₀ hN.ne',one_mul]
  refine ⟨hs.1, hs.2.trans ?_⟩
  have he := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ L/2 by positivity)
  nlinarith only [he]

lemma grid_smoothing_hasGradient {d m : ℕ} {f : Point d → ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x) (h : ℝ) (x : Point d) :
    HasGradientAt (gridSmooth f h m) (gridGradient f h m x) x := by
  have hs := finite_smoothing_gradient Finset.univ
    (fun _ : Fin d → Fin m => (Fintype.card (Fin d → Fin m) : ℝ)⁻¹) hg (midpointPoint h) x
  simp only [← Finset.mul_sum,← Finset.smul_sum] at hs
  exact hs

lemma grid_smoothing_gradient {d m : ℕ} {f : Point d → ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x) (h : ℝ) (x : Point d) :
    gradient (gridSmooth f h m) x = gridGradient f h m x :=
  (grid_smoothing_hasGradient hg h x).gradient

lemma grid_smoothing_gradient_distance {d m : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    ‖gridGradient f h m x-gradient f x‖^2 ≤ (d:ℝ)*L^2*h^2 := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have hs (v : Fin d → Fin m) : ‖gradient f (x+midpointPoint h v)-gradient f x‖ ≤ L*(Real.sqrt d*h) := by
    have hz : ‖midpointPoint h v‖ ≤ Real.sqrt d*h := by
      have hsq := midpointPoint_norm_sq hh v
      nlinarith [norm_nonneg (midpointPoint h v),mul_nonneg (Real.sqrt_nonneg (d:ℝ)) hh]
    have hi := hlip (x+midpointPoint h v) x
    rw [add_sub_cancel_left] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hz hL)
  have hb := finite_average_distance (fun v : Fin d → Fin m => gradient f (x+midpointPoint h v)) (gradient f x) hs
  change ‖gridGradient f h m x-gradient f x‖ ≤ L*(Real.sqrt d*h) at hb
  have hsq := mul_self_le_mul_self (norm_nonneg _) hb
  calc
    _ ≤ (L*(Real.sqrt d*h))^2 := by nlinarith only [hsq]
    _ = _ := by rw [mul_pow,mul_pow,hsqrt]; ring

lemma grid_smoothing_convex {d m : ℕ} {f : Point d → ℝ}
    (hc : ConvexOn ℝ univ f) (h : ℝ) : ConvexOn ℝ univ (gridSmooth f h m) := by
  have hs := finite_smoothing_convex Finset.univ
    (fun _ : Fin d → Fin m => (Fintype.card (Fin d → Fin m) : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hc (midpointPoint h)
  simp only [← Finset.mul_sum] at hs
  exact hs

lemma grid_smoothing_lipschitz {d m : ℕ} {f : Point d → ℝ} {L : ℝ}
    (hm : 0 < m) (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (h : ℝ) (x y : Point d) : ‖gridGradient f h m x-gridGradient f h m y‖ ≤ L*‖x-y‖ := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hN : (0:ℝ) < Fintype.card (Fin d → Fin m) := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _v : Fin d → Fin m, (Fintype.card (Fin d → Fin m) : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have hs := finite_smoothing_lipschitz Finset.univ
    (fun _ : Fin d → Fin m => (Fintype.card (Fin d → Fin m) : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr hN.le) hw hlip (midpointPoint h) x y
  simp only [← Finset.smul_sum] at hs
  exact hs

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma measurable_midpointPoint {d m : ℕ} (h : ℝ) : Measurable (midpointPoint (d := d) (m := m) h) := by
  have hc : Measurable (midpointCoordinate (m := m) h) := measurable_of_countable _
  unfold midpointPoint
  exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    (Measurable.of_eval (fun i => hc.comp (measurable_pi_apply i)))

lemma measurable_midpointPoint_apply {d m : ℕ} (h : ℝ) (i : Fin d) :
    Measurable (fun v : Fin d → Fin m => midpointPoint h v i) := by
  have hc : Measurable (midpointCoordinate (m := m) h) := measurable_of_countable _
  exact hc.comp (measurable_pi_apply i)

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma measurable_gridUpper {d m : ℕ} (h : ℝ) (i : Fin d) : Measurable (gridUpper (m := m) h i) := by
  have hz : Measurable (midpointPoint (d := d) (m := m) h) := measurable_midpointPoint h
  have hzi : Measurable (fun v : Fin d → Fin m => midpointPoint h v i) := measurable_midpointPoint_apply h i
  exact (measurable_fst.add (hz.comp measurable_snd)).add
    ((measurable_const.sub (hzi.comp measurable_snd)).smul_const _)

lemma measurable_gridLower {d m : ℕ} (h : ℝ) (i : Fin d) : Measurable (gridLower (m := m) h i) := by
  have hz : Measurable (midpointPoint (d := d) (m := m) h) := measurable_midpointPoint h
  have hzi : Measurable (fun v : Fin d → Fin m => midpointPoint h v i) := measurable_midpointPoint_apply h i
  exact (measurable_fst.add (hz.comp measurable_snd)).add
    ((measurable_const.sub (hzi.comp measurable_snd)).smul_const _)

end OracleTemplate.ZerothOrder

end

section

open Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma grid_smoothing_comparator_gap {d m : ℕ} {f : Point d → ℝ} {L R h : ℝ}
    (hm : 0 < m) (hL : 0 < L) (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    {x0 u x : Point d} (hmin : IsMinOn f univ u) (hu : ‖u-x0‖ ≤ R) (hx : ‖x-x0‖ ≤ R) :
    |gridSmooth f h m x-gridSmooth f h m u| ≤ 2*L*R^2+L*(d:ℝ)*h^2/2 := by
  have hsx := grid_smoothing_gap hm hL.le hh hc hg hlip x
  have hsu := grid_smoothing_gap hm hL.le hh hc hg hlip u
  have hxgap := HeavyTailedMarkovGradient.smooth_gap_ball hL hR hg hlip hmin hu hx
  apply abs_le.mpr
  have hn : 0 ≤ 2*L*R^2 := by positivity
  constructor <;> linarith [hsx.1,hsx.2,hsu.1,hsu.2,hxgap.1,hxgap.2]

end OracleTemplate.ZerothOrder

end

section

section

open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma affine_scaled_gradient {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (z : E) (c : ℝ) (x : E) :
    HasGradientAt (fun y => f (z+c • y)) (c • g (z+c • x)) x := by
  have h := (hg (z+c • x)).hasFDerivAt.comp x (((hasFDerivAt_id x).const_smul c).const_add z)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1 <;> ext y <;> simp []

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma integrable_continuous_bounded_offset {E F Ω : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] {p : Measure Ω} [IsFiniteMeasure p]
    {f : E → F} (hf : Continuous f) {z : Ω → E} (hz : Measurable z)
    {r : ℝ} (hb : ∀ ω, ‖z ω‖ ≤ r) (x : E) :
    Integrable (fun ω => f (x+z ω)) p := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hf.continuousOn
  have hm : Measurable (fun ω => f (x+z ω)) := hf.measurable.comp (measurable_const.add hz)
  apply Integrable.of_bound hm.aestronglyMeasurable C
  filter_upwards [] with ω
  apply hC
  rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left]
  exact hb ω

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma compact_integral_hasDerivAt {U : Type*} [TopologicalSpace U] [CompactSpace U]
    [MeasurableSpace U] [BorelSpace U] {p : Measure U} [IsFiniteMeasure p]
    {F D : ℝ × U → ℝ} (hF : Continuous F) (hD : Continuous D)
    (hd : ∀ t u, HasDerivAt (fun s => F (s,u)) (D (t,u)) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ u, F (s,u) ∂p) (∫ u, D (t,u) ∂p) t := by
  have hFc (s : ℝ) : Continuous (fun u => F (s,u)) := hF.comp (continuous_const.prodMk continuous_id)
  have hDc (s : ℝ) : Continuous (fun u => D (s,u)) := hD.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set U)).exists_bound_of_continuousOn (hFc t).continuousOn
  have hi : Integrable (fun u => F (t,u)) p := by
    apply Integrable.of_bound (hFc t).measurable.aestronglyMeasurable C
    exact Eventually.of_forall (fun u => hC u (mem_univ u))
  obtain ⟨B,hB⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ : IsCompact (univ : Set U))).exists_bound_of_continuousOn hD.continuousOn
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball t 1) (bound := fun _ : U => B) (ball_mem_nhds t (by norm_num))
    (Eventually.of_forall (fun s => (hFc s).measurable.aestronglyMeasurable)) hi
    (hDc t).measurable.aestronglyMeasurable
    (Eventually.of_forall (fun u s hs => hB (s,u) ⟨mem_closedBall.mpr (le_of_lt hs),mem_univ u⟩))
    (integrable_const B) (Eventually.of_forall (fun u s _ => hd s u))).2

end OracleTemplate.ZerothOrder

end

section

open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma coordinate_product_gradient {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (j : Fin d) (x : E) :
    HasGradientAt (fun y => y j*f y)
      ((x j) • g x+f x • EuclideanSpace.single j (1:ℝ)) x := by
  have hscalar (a b : ℝ) : inner ℝ a b=a*b := by change b*a=a*b; ring
  have he (y : E) : ⟪EuclideanSpace.single j (1:ℝ),y⟫=y j := by
    simp [PiLp.inner_apply]
  have hcoord : HasFDerivAt (fun y : E => y j) (innerSL ℝ (EuclideanSpace.single j (1:ℝ))) x := by
    convert (innerSL ℝ (EuclideanSpace.single j (1:ℝ))).hasFDerivAt (x := x) using 1
    funext y
    exact (he y).symm
  have h := hcoord.mul (hg x).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext y
  simp [he]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

omit [CompleteSpace E] in
lemma integral_smoothing_midpoint {f : E → ℝ} (hc : ConvexOn ℝ univ f)
    (z : Ω → E) (x u : E)
    (hi : Integrable (fun ω => f ((1/2:ℝ) • (x+u)+z ω)) p)
    (h2 : Integrable (fun ω => f (x+(2:ℝ) • z ω)) p) :
    (∫ ω, f ((1/2:ℝ) • (x+u)+z ω) ∂p) ≤
      ((∫ ω, f (x+(2:ℝ) • z ω) ∂p)+f u)/2 := by
  have hp (ω : Ω) : f ((1/2:ℝ) • (x+u)+z ω) ≤ (f (x+(2:ℝ) • z ω)+f u)/2 := by
    have h := hc.2 (mem_univ (x+(2:ℝ) • z ω)) (mem_univ u)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)+1/2=1)
    have he : (1/2:ℝ) • (x+(2:ℝ) • z ω)+(1/2:ℝ) • u = (1/2:ℝ) • (x+u)+z ω := by module
    rw [he] at h
    simp only [smul_eq_mul] at h
    linarith
  have h := integral_mono hi ((h2.add (integrable_const _)).div_const 2) hp
  rw [integral_div] at h
  simp only [Pi.add_apply] at h
  rw [integral_add h2 (integrable_const _)] at h
  simpa only [integral_const,probReal_univ,one_smul] using h

omit [IsProbabilityMeasure p] in
lemma integral_smoothing_support {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (z : Ω → E) (x y : E)
    (hix : Integrable (fun ω => f (x+z ω)) p)
    (hiy : Integrable (fun ω => f (y+z ω)) p)
    (hig : Integrable (fun ω => g (x+z ω)) p) :
    ⟪∫ ω, g (x+z ω) ∂p,y-x⟫ ≤
      (∫ ω, f (y+z ω) ∂p)-(∫ ω, f (x+z ω) ∂p) := by
  have hp (ω : Ω) : ⟪g (x+z ω),y-x⟫ ≤ f (y+z ω)-f (x+z ω) := by
    have h := Gradient.convex_support hc hg (x+z ω) (y+z ω)
    rw [add_sub_add_right_eq_sub] at h
    linarith
  have h := integral_mono (hig.inner_const (y-x)) (hiy.sub hix) hp
  simp only [Pi.sub_apply] at h
  rw [integral_sub hiy hix] at h
  have he := integral_inner (𝕜 := ℝ) hig (y-x)
  have hex : (fun ω => ⟪y-x,g (x+z ω)⟫) = (fun ω => ⟪g (x+z ω),y-x⟫) := by
    funext ω
    exact real_inner_comm _ _
  rw [hex,real_inner_comm (∫ ω, g (x+z ω) ∂p) (y-x)] at he
  rw [he] at h
  exact h

lemma integral_smoothed_cut {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (z : Ω → E) (x u : E)
    (hix : Integrable (fun ω => f (x+z ω)) p)
    (him : Integrable (fun ω => f ((1/2:ℝ) • (x+u)+z ω)) p)
    (hi2 : Integrable (fun ω => f (x+(2:ℝ) • z ω)) p)
    (hig : Integrable (fun ω => g (x+z ω)) p)
    (hgap : (∫ ω, f (x+(2:ℝ) • z ω) ∂p)-(∫ ω, f (x+z ω) ∂p) ≤
      ((∫ ω, f (x+z ω) ∂p)-f u)/4) :
    3/4*((∫ ω, f (x+z ω) ∂p)-f u) ≤ ⟪∫ ω, g (x+z ω) ∂p,x-u⟫ := by
  have hm := integral_smoothing_midpoint hc z x u him hi2
  have hs := integral_smoothing_support hc hg z x ((1/2:ℝ) • (x+u)) hix him hig
  have he : (1/2:ℝ) • (x+u)-x = (-1/2:ℝ) • (x-u) := by module
  rw [he,inner_smul_right] at hs
  linarith

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma radial_density_integral {d : ℕ} (hd : 0 < d) :
    (∫ r in Ioc (0:ℝ) 1, (d:ℝ)*r^(d-1))=1 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),intervalIntegral.integral_const_mul,integral_pow]
  have hn : d-1+1=d := Nat.sub_add_cancel hd
  have hn' : ((d-1:ℕ):ℝ)+1=(d:ℝ) := by exact_mod_cast hn
  rw [hn]
  simp [hn',Nat.ne_of_gt hd]

lemma radial_density_integrable (d : ℕ) :
    Integrable (fun r : ℝ => (d:ℝ)*r^(d-1)) (volume.restrict (Ioc (0:ℝ) 1)) :=
  (((continuous_const.mul (continuous_id.pow (d-1))).intervalIntegrable 0 1).1)

lemma radial_density_nonneg (d : ℕ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioc (0:ℝ) 1), 0 ≤ (d:ℝ)*r^(d-1) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact mul_nonneg (by positivity) (pow_nonneg hr.1.le _)

noncomputable def radialLaw (d : ℕ) (hd : 0 < d) : ProbabilityMeasure ℝ := by
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let w := fun r : ℝ => ENNReal.ofReal ((d:ℝ)*r^(d-1))
  refine ⟨μ.withDensity w,⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have h := ofReal_integral_eq_lintegral_ofReal (radial_density_integrable d) (radial_density_nonneg d)
  rw [radial_density_integral hd] at h
  simpa only [ENNReal.ofReal_one] using h.symm

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped Pointwise

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def sphereRotate (e : E ≃ₗᵢ[ℝ] E) (u : sphere (0:E) 1) : sphere (0:E) 1 :=
  ⟨e u, by simpa only [mem_sphere_zero_iff_norm, e.norm_map] using u.property⟩

omit [FiniteDimensional ℝ E] in
lemma measurable_sphereRotate (e : E ≃ₗᵢ[ℝ] E) : Measurable (sphereRotate e) :=
  (e.continuous.measurable.comp measurable_subtype_coe).subtype_mk

omit [BorelSpace E] [FiniteDimensional ℝ E] in
omit [MeasurableSpace E] in
lemma sphereRotate_cone_preimage (e : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0:E) 1)) :
    Ioo (0:ℝ) 1 • ((↑) '' (sphereRotate e ⁻¹' s)) =
      e ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨a,ha,y,hy,hax⟩
    rcases hy with ⟨u,hu,rfl⟩
    subst x
    refine ⟨a,ha,e u,⟨sphereRotate e u,hu,rfl⟩,?_⟩
    exact (e.map_smul a (u:E)).symm
  · rintro ⟨a,ha,y,hy,hax⟩
    rcases hy with ⟨u,hu,rfl⟩
    let v := sphereRotate e.symm u
    have hv : sphereRotate e v ∈ s := by
      have he : sphereRotate e v = u := by ext; simp [sphereRotate,v]
      simpa only [he] using hu
    refine ⟨a,ha,(v:E),⟨v,hv,rfl⟩,?_⟩
    apply e.injective
    simpa only [map_smul, v, sphereRotate, e.apply_symm_apply] using hax

lemma sphereRotate_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereRotate e) (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨measurable_sphereRotate e, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_sphereRotate e) hs,
    Measure.toSphere_apply' _ ((measurable_sphereRotate e) hs), Measure.toSphere_apply' _ hs,
    sphereRotate_cone_preimage]
  congr 1
  have he : MeasurableEmbedding (e : E → E) := e.toHomeomorph.measurableEmbedding
  have h := congrArg (fun μ : Measure E => μ (Ioo (0:ℝ) 1 • ((↑) '' s))) e.measurePreserving.map_eq
  rw [he.map_apply] at h
  exact h

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma radialLaw_measure (d : ℕ) (hd : 0 < d) : (radialLaw d hd : Measure ℝ) =
    (volume.restrict (Ioc (0:ℝ) 1)).withDensity (fun r : ℝ => ENNReal.ofReal ((d:ℝ)*r^(d-1))) := rfl

lemma radialLaw_integral (d : ℕ) (hd : 0 < d) (f : ℝ → ℝ) :
    (∫ r, f r ∂(radialLaw d hd : Measure ℝ)) = ∫ r in (0:ℝ)..1, (d:ℝ)*r^(d-1)*f r := by
  rw [radialLaw_measure]
  have hm : Measurable (fun r : ℝ => ENNReal.ofReal ((d:ℝ)*r^(d-1))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [radial_density_nonneg d] with r hr
  rw [ENNReal.toReal_ofReal hr,smul_eq_mul]

lemma radialLaw_mem_interval (d : ℕ) (hd : 0 < d) :
    ∀ᵐ r : ℝ ∂(radialLaw d hd : Measure ℝ), r ∈ Ioc (0:ℝ) 1 := by
  rw [radialLaw_measure]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]


lemma sphereLaw_measure : (sphereLaw E : Measure (sphere (0:E) 1)) =
    ((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere := rfl

lemma sphereLaw_rotate (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereRotate e) (sphereLaw E : Measure _) (sphereLaw E : Measure _) := by
  refine ⟨measurable_sphereRotate e, ?_⟩
  rw [sphereLaw_measure, Measure.map_smul, (sphereRotate_preserving e).map_eq]
  exact (measurable_sphereRotate e).aemeasurable

lemma sphereLaw_integral_rotate (e : E ≃ₗᵢ[ℝ] E) (f : sphere (0:E) 1 → ℝ) :
    (∫ u, f (sphereRotate e u) ∂(sphereLaw E : Measure _)) = ∫ u, f u ∂(sphereLaw E : Measure _) := by
  have hi : Isometry (sphereRotate e) := by
    intro u v
    change edist (e (u:E)) (e (v:E)) = edist (u:E) (v:E)
    exact e.isometry _ _
  exact (sphereLaw_rotate E e).integral_comp hi.isClosedEmbedding.measurableEmbedding f

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1

noncomputable def ballOffset (v : ℝ × S) : E := max 0 (min 1 v.1) • (v.2:E)

omit [NeZero d] in
lemma ballOffset_continuous : Continuous (ballOffset (d := d)) := by
  unfold ballOffset
  fun_prop

omit [NeZero d] in
lemma ballOffset_norm (v : ℝ × S) : ‖ballOffset v‖ ≤ 1 := by
  have hn : ‖(v.2:E)‖=1 := mem_sphere_zero_iff_norm.mp v.2.property
  dsimp [ballOffset]
  rw [norm_smul,Real.norm_eq_abs,hn,mul_one,abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_left _ _)

omit [NeZero d] in
lemma ballOffset_of_mem_interval (r : ℝ) (u : S) (hr : r ∈ Ioc (0:ℝ) 1) :
    ballOffset (r,u)=r • (u:E) := by
  simp only [ballOffset,min_eq_right hr.2,max_eq_right hr.1.le]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

omit [NeZero d] in
lemma sphere_coordinate_abs (u : S) (i : Fin d) : |(u:E) i| ≤ 1 := by
  have hn : ‖(u:E)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
  simpa only [Real.norm_eq_abs,hn] using PiLp.norm_apply_le (u:E) i

omit [NeZero d] in
lemma sphere_coordinate_measurable (i : Fin d) : Measurable (fun u : S => (u:E) i) :=
  ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).comp continuous_subtype_val).measurable

lemma sphere_coordinate_power_integrable (i : Fin d) (k : ℕ) :
    Integrable (fun u : S => (u:E) i ^ k) Q := by
  apply Integrable.of_bound ((sphere_coordinate_measurable i).pow_const k).aestronglyMeasurable 1
  filter_upwards [] with u
  rw [Real.norm_eq_abs,abs_pow]
  simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (sphere_coordinate_abs u i) k

lemma sphere_coordinate_moments_equal (i j : Fin d) (k : ℕ) :
    (∫ u : S, (u:E) i ^ k ∂Q) = ∫ u : S, (u:E) j ^ k ∂Q := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have he (u : S) : (sphereRotate e u : E) i = (u:E) j := by
    simp [sphereRotate,e,LinearIsometryEquiv.piLpCongrLeft_apply]
  have h := sphereLaw_integral_rotate E e (fun u : S => (u:E) i ^ k)
  simpa only [he] using h.symm

lemma sphere_coordinate_second_moment (i : Fin d) :
    (∫ u : S, (u:E) i ^ 2 ∂Q) = 1/(d:ℝ) := by
  have hs (u : S) : ∑ j : Fin d, (u:E) j ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    have hn : ‖(u:E)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
    rw [hn,one_pow]
  have he : (∫ u : S, ∑ j : Fin d, (u:E) j ^ 2 ∂Q) = 1 := by
    simp only [hs,integral_const,probReal_univ,one_smul]
  rw [integral_finsetSum _ (fun j _ => sphere_coordinate_power_integrable j 2)] at he
  have hj (j : Fin d) : (∫ u : S, (u:E) j ^ 2 ∂Q) = ∫ u : S, (u:E) i ^ 2 ∂Q :=
    sphere_coordinate_moments_equal j i 2
  simp only [hj, Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  have hd : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  apply (eq_div_iff hd).mpr
  nlinarith only [he]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_coordinate_product_integrable (i j : Fin d) :
    Integrable (fun u : S => (u:E) i * (u:E) j) Q := by
  apply Integrable.of_bound ((sphere_coordinate_measurable i).mul (sphere_coordinate_measurable j)).aestronglyMeasurable 1
  filter_upwards [] with u
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul]
  simpa only [one_mul] using mul_le_mul (sphere_coordinate_abs u i) (sphere_coordinate_abs u j) (abs_nonneg _) zero_le_one

lemma sphere_coordinate_cross_moment (i j : Fin d) (hij : i ≠ j) :
    (∫ u : S, (u:E) i * (u:E) j ∂Q) = 0 := by
  let e := LinearIsometryEquiv.piLpCongrRight 2 (fun k : Fin d =>
    if k=i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else LinearIsometryEquiv.refl ℝ ℝ)
  have hi (u : S) : (sphereRotate e u : E) i = -(u:E) i := by
    simp [sphereRotate,e]
  have hj (u : S) : (sphereRotate e u : E) j = (u:E) j := by
    simp [sphereRotate,e,Ne.symm hij]
  have h := sphereLaw_integral_rotate E e (fun u : S => (u:E) i * (u:E) j)
  simp only [hi,hj,neg_mul,integral_neg] at h
  linarith

lemma sphere_coordinate_covariance (i j : Fin d) :
    (∫ u : S, (u:E) i * (u:E) j ∂Q) = if i=j then 1/(d:ℝ) else 0 := by
  by_cases h : i=j
  · subst j
    simpa only [ite_true,←pow_two] using sphere_coordinate_second_moment i
  · rw [ite_eq_right h]
    exact sphere_coordinate_cross_moment i j h

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

omit [NeZero d] in
lemma plane_reflection_coordinate (i j : Fin d) (hij : i ≠ j) (t : ℝ) (x : E) :
    let w := EuclideanSpace.single i (1:ℝ) + t • EuclideanSpace.single j (1:ℝ)
    ((Submodule.span ℝ {w}).reflection x) i = ((1-t^2)*x i+2*t*x j)/(1+t^2) := by
  intro w
  have hwi : w i = 1 := by simp [w,hij]
  have hwj : w j = t := by simp [w,Ne.symm hij]
  have hscalar (a b : ℝ) : inner ℝ a b = a*b := by change b*a=a*b; ring
  have hsingle (k : Fin d) (y : E) : ⟪EuclideanSpace.single k (1:ℝ),y⟫ = y k := by
    simp [PiLp.inner_apply]
  have hin (y : E) : ⟪w,y⟫ = y i+t*y j := by
    simp [w,inner_add_left,real_inner_smul_left,hsingle]
  have hn : ‖w‖^2 = 1+t^2 := by
    rw [← real_inner_self_eq_norm_sq,hin,hwi,hwj]
    ring
  have hden : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
  rw [Submodule.reflection_singleton_apply]
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,nsmul_eq_mul,RCLike.ofReal_real_eq_id, id_eq]
  rw [hin,hn,hwi]
  field_simp; ring

lemma sphere_reflection_moment_identity (i j : Fin d) (hij : i ≠ j) (t : ℝ) (k : ℕ) :
    (∫ u : S, ((1-t^2)*(u:E) i+2*t*(u:E) j)^k ∂Q) =
      (1+t^2)^k * (∫ u : S, (u:E) i ^ k ∂Q) := by
  let w := EuclideanSpace.single i (1:ℝ) + t • EuclideanSpace.single j (1:ℝ)
  let e := (Submodule.span ℝ {w}).reflection
  have hc (u : S) : (sphereRotate e u : E) i = ((1-t^2)*(u:E) i+2*t*(u:E) j)/(1+t^2) :=
    plane_reflection_coordinate i j hij t (u:E)
  have h := sphereLaw_integral_rotate E e (fun u : S => (u:E) i ^ k)
  simp_rw [hc,div_pow] at h
  rw [integral_div] at h
  have hden : (1+t^2)^k ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
  exact ((div_eq_iff hden).mp h).trans (mul_comm _ _)

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def planeReflection (i j : Fin d) (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {EuclideanSpace.single i (1:ℝ)+t • EuclideanSpace.single j (1:ℝ)}).reflection

omit [NeZero d] in
lemma planeReflection_apply (i j : Fin d) (hij : i ≠ j) (t : ℝ) (x : E) :
    planeReflection i j t x =
      (2*((x i+t*x j)/(1+t^2))) • (EuclideanSpace.single i (1:ℝ)+t • EuclideanSpace.single j (1:ℝ))-x := by
  let w := EuclideanSpace.single i (1:ℝ)+t • EuclideanSpace.single j (1:ℝ)
  have hscalar (a b : ℝ) : inner ℝ a b=a*b := by change b*a=a*b; ring
  have hsingle (k : Fin d) (y : E) : ⟪EuclideanSpace.single k (1:ℝ),y⟫=y k := by
    simp [PiLp.inner_apply]
  have hin (y : E) : ⟪w,y⟫=y i+t*y j := by simp [w,inner_add_left,real_inner_smul_left,hsingle]
  have hwi : w i=1 := by simp [w,hij]
  have hwj : w j=t := by simp [w,Ne.symm hij]
  have hn : ‖w‖^2=1+t^2 := by
    rw [← real_inner_self_eq_norm_sq,hin,hwi,hwj]
    ring
  change (Submodule.span ℝ {w}).reflection x = _
  rw [Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [hin,hn]
  simp only [two_smul ℕ,two_mul,add_smul]
  rfl

omit [NeZero d] in
lemma planeReflection_hasDerivAt (i j : Fin d) (hij : i ≠ j) (x : E) (t : ℝ) :
    HasDerivAt (fun s => planeReflection i j s x)
      ((2*((x i+t*x j)/(1+t^2))) • EuclideanSpace.single j (1:ℝ)+
        (2*((x j*(1+t^2)-(x i+t*x j)*(2*t))/(1+t^2)^2)) •
          (EuclideanSpace.single i (1:ℝ)+t • EuclideanSpace.single j (1:ℝ))) t := by
  have hnum := (hasDerivAt_const t (x i)).add ((hasDerivAt_id t).mul_const (x j))
  have hden := (hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).pow 2)
  have hdiv := hnum.div hden (by positivity : (1:ℝ)+t^2 ≠ 0)
  have hw := (hasDerivAt_const t (EuclideanSpace.single i (1:ℝ))).add
    ((hasDerivAt_id t).smul_const (EuclideanSpace.single j (1:ℝ)))
  have h := ((hdiv.const_mul 2).smul hw).sub_const x
  simp only [zero_add,one_mul,mul_one,Nat.cast_ofNat,one_smul] at h
  simpa [planeReflection_apply i j hij,mul_div_assoc,Pi.add_apply,Pi.div_apply,Pi.smul_apply,Pi.pow_apply] using h

omit [NeZero d] in
lemma planeReflection_hasDerivAt_zero (i j : Fin d) (hij : i ≠ j) (x : E) :
    HasDerivAt (fun s => planeReflection i j s x)
      ((2*x i) • EuclideanSpace.single j (1:ℝ)+(2*x j) • EuclideanSpace.single i (1:ℝ)) 0 := by
  simpa using planeReflection_hasDerivAt i j hij x 0

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_linear_second_moment (a : Fin d → ℝ) :
    (∫ u : S, (∑ i, a i * (u:E) i)^2 ∂Q) = (∑ i, (a i)^2)/(d:ℝ) := by
  have hp (u : S) : (∑ i, a i * (u:E) i)^2 =
      ∑ i, ∑ j, (a i*a j)*((u:E) i*(u:E) j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hI (i j : Fin d) : Integrable (fun u : S => (a i*a j)*((u:E) i*(u:E) j)) Q :=
    (sphere_coordinate_product_integrable i j).const_mul _
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  calc
    _ = ∑ i, (a i)^2/(d:ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ => hI i j)]
      simp_rw [integral_const_mul, sphere_coordinate_covariance]
      simp [mul_ite,pow_two]; ring
    _ = (∑ i, (a i)^2)/(d:ℝ) := (Finset.sum_div _ _ _).symm

lemma sphere_projection_second_moment (x : E) :
    (∫ u : S, ⟪x,(u:E)⟫^2 ∂Q) = ‖x‖^2/(d:ℝ) := by
  have hscalar (a b : ℝ) : inner ℝ a b = a*b := by
    change b*a = a*b
    ring
  simpa only [PiLp.inner_apply,hscalar,EuclideanSpace.real_norm_sq_eq]
    using sphere_linear_second_moment (fun i => x i)

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def planeRotation (i j : Fin d) (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  (planeReflection i j 0).trans (planeReflection i j t)

noncomputable def planeRotationVelocity (i j : Fin d) (t : ℝ) (x : E) : E :=
  let y := planeReflection i j 0 x
  (2*((y i+t*y j)/(1+t^2))) • EuclideanSpace.single j (1:ℝ)+
    (2*((y j*(1+t^2)-(y i+t*y j)*(2*t))/(1+t^2)^2)) •
      (EuclideanSpace.single i (1:ℝ)+t • EuclideanSpace.single j (1:ℝ))

omit [NeZero d] in
lemma planeRotation_zero (i j : Fin d) (x : E) : planeRotation i j 0 x=x := by
  simp [planeRotation,planeReflection]

omit [NeZero d] in
lemma planeRotation_hasDerivAt (i j : Fin d) (hij : i ≠ j) (x : E) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j s x) (planeRotationVelocity i j t x) t :=
  planeReflection_hasDerivAt i j hij (planeReflection i j 0 x) t

omit [NeZero d] in
lemma planeRotationVelocity_zero (i j : Fin d) (hij : i ≠ j) (x : E) :
    planeRotationVelocity i j 0 x =
      (2*x i) • EuclideanSpace.single j (1:ℝ)-(2*x j) • EuclideanSpace.single i (1:ℝ) := by
  have hi : (planeReflection i j 0 x) i=x i := by
    simpa [planeReflection] using plane_reflection_coordinate i j hij 0 x
  have hj : (planeReflection i j 0 x) j= -x j := by
    rw [planeReflection_apply i j hij]
    simp [PiLp.sub_apply,PiLp.smul_apply,Ne.symm hij]
  simp [planeRotationVelocity,hi,hj]
  module

omit [NeZero d] in
lemma planeRotation_continuous (i j : Fin d) (hij : i ≠ j) :
    Continuous (fun z : ℝ × E => planeRotation i j z.1 z.2) := by
  simp only [planeRotation,LinearIsometryEquiv.trans_apply,planeReflection_apply i j hij]
  fun_prop (disch := intros; positivity)

omit [NeZero d] in
lemma planeRotationVelocity_continuous (i j : Fin d) :
    Continuous (fun z : ℝ × E => planeRotationVelocity i j z.1 z.2) := by
  unfold planeRotationVelocity
  fun_prop (disch := intros; positivity)

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_rotation_derivative_integral {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (i j : Fin d) (hij : i ≠ j) :
    (∫ u : S, ⟪g (u:E),(2*(u:E) i) • EuclideanSpace.single j (1:ℝ)-
      (2*(u:E) j) • EuclideanSpace.single i (1:ℝ)⟫ ∂Q)=0 := by
  let F := fun z : ℝ × S => f (planeRotation i j z.1 (z.2:E))
  let D := fun z : ℝ × S => ⟪g (planeRotation i j z.1 (z.2:E)),planeRotationVelocity i j z.1 (z.2:E)⟫
  have hm : Continuous (fun z : ℝ × S => (z.1,(z.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hR := (planeRotation_continuous i j hij).comp hm
  have hV := (planeRotationVelocity_continuous i j).comp hm
  have hF : Continuous F := hf.comp hR
  have hD : Continuous D := (hg.comp hR).inner hV
  have hder (t : ℝ) (u : S) : HasDerivAt (fun s => F (s,u)) (D (t,u)) t := by
    have h := (hd _).hasFDerivAt.comp_hasDerivAt t (planeRotation_hasDerivAt i j hij (u:E) t)
    simp only [InnerProductSpace.toDual_apply_apply] at h
    exact h
  have h := compact_integral_hasDerivAt (p := Q) hF hD hder 0
  have he (t : ℝ) : (∫ u : S, F (t,u) ∂Q) = ∫ u : S, f (u:E) ∂Q :=
    sphereLaw_integral_rotate E (planeRotation i j t) (fun u : S => f (u:E))
  simp_rw [he] at h
  have hz := h.unique (hasDerivAt_const 0 (∫ u : S, f (u:E) ∂Q))
  simpa only [D,planeRotation_zero,planeRotationVelocity_zero i j hij] using hz

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_integrable_continuous {f : E → ℝ} (hf : Continuous f) :
    Integrable (fun u : S => f (u:E)) Q := by
  have hb (u : S) : ‖(u:E)‖ ≤ (1:ℝ) := by
    exact le_of_eq (mem_sphere_zero_iff_norm.mp u.property)
  simpa only [zero_add] using integrable_continuous_bounded_offset (p := Q) hf measurable_subtype_coe hb (0:E)

lemma sphere_pair_integration_by_parts {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (i j : Fin d) (hij : i ≠ j) :
    (∫ u : S, (u:E) i*f (u:E)+(u:E) i*(u:E) j*(g (u:E)) j-
      (u:E) j^2*(g (u:E)) i ∂Q)=0 := by
  have hfc : Continuous (fun x : E => x j*f x) := by fun_prop
  have hgc : Continuous (fun x : E => (x j) • g x+f x • EuclideanSpace.single j (1:ℝ)) := by fun_prop
  have h := sphere_rotation_derivative_integral hfc hgc (coordinate_product_gradient hd j) i j hij
  have hscalar (a b : ℝ) : inner ℝ a b=a*b := by change b*a=a*b; ring
  have hi (y : E) (k : Fin d) : ⟪y,EuclideanSpace.single k (1:ℝ)⟫=y k := by
    simp [PiLp.inner_apply]
  have he (u : S) :
      ⟪((u:E) j) • g (u:E)+f (u:E) • EuclideanSpace.single j (1:ℝ),
        (2*(u:E) i) • EuclideanSpace.single j (1:ℝ)-(2*(u:E) j) • EuclideanSpace.single i (1:ℝ)⟫ =
      2*((u:E) i*f (u:E)+(u:E) i*(u:E) j*(g (u:E)) j-(u:E) j^2*(g (u:E)) i) := by
    simp [inner_sub_right,inner_smul_right,hi,hij]
    ring
  simp_rw [he] at h
  rw [integral_const_mul] at h
  linarith

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_coordinate_mean_zero (i : Fin d) : (∫ u : S, (u:E) i ∂Q)=0 := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have he (u : S) : (sphereRotate e u:E) i= -(u:E) i := by simp [sphereRotate,e]
  have h := sphereLaw_integral_rotate E e (fun u : S => (u:E) i)
  simp only [he,integral_neg] at h
  linarith

lemma sphere_radial_boundary_hasDerivAt {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (i : Fin d) (r : ℝ) :
    HasDerivAt (fun t => ∫ u : S, f (t • (u:E))*(u:E) i ∂Q)
      (∫ u : S, ⟪g (r • (u:E)),(u:E)⟫*(u:E) i ∂Q) r := by
  let F := fun z : ℝ × S => f (z.1 • (z.2:E))*(z.2:E) i
  let D := fun z : ℝ × S => ⟪g (z.1 • (z.2:E)),(z.2:E)⟫*(z.2:E) i
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hder (t : ℝ) (u : S) : HasDerivAt (fun s => F (s,u)) (D (t,u)) t := by
    have h := (hd (t • (u:E))).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (u:E))
    simpa [F,D] using h.mul_const ((u:E) i)
  exact compact_integral_hasDerivAt (p := Q) hF hD hder r

lemma sphere_radial_boundary_zero (f : E → ℝ) (i : Fin d) :
    (∫ u : S, f ((0:ℝ) • (u:E))*(u:E) i ∂Q)=0 := by
  simp only [zero_smul,integral_const_mul,sphere_coordinate_mean_zero,mul_zero]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_radial_integral_continuous {f : E → ℝ} (hf : Continuous f) :
    Continuous (fun r : ℝ => ∫ u : S, f (r • (u:E)) ∂Q) := by
  have hF : Continuous (Function.uncurry (fun r : ℝ => fun u : S => f (r • (u:E)))) := by
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := Q) hF (isCompact_univ : IsCompact (univ : Set S))
  simpa only [Measure.restrict_univ] using h

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_tangential_integration_by_parts {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x) (i : Fin d) :
    (∫ u : S, (g (u:E)) i-(u:E) i*⟪g (u:E),(u:E)⟫ ∂Q) =
      ((d:ℝ)-1)*(∫ u : S, (u:E) i*f (u:E) ∂Q) := by
  let H := fun j : Fin d => fun u : S => (u:E) i*f (u:E)+
    (u:E) i*(u:E) j*(g (u:E)) j-(u:E) j^2*(g (u:E)) i
  have hH (j : Fin d) : Integrable (H j) Q := by
    apply sphere_integrable_continuous (f := fun x : E => x i*f x+x i*x j*(g x) j-x j^2*(g x) i)
    fun_prop
  have hA : Integrable (fun u : S => (u:E) i*f (u:E)) Q := sphere_integrable_continuous (f := fun x : E => x i*f x) (by fun_prop)
  have hB : Integrable (fun u : S => (g (u:E)) i-(u:E) i*⟪g (u:E),(u:E)⟫) Q := sphere_integrable_continuous (f := fun x : E => (g x) i-x i*⟪g x,x⟫) (by fun_prop)
  have hp (j : Fin d) : (∫ u : S, H j u ∂Q) = if j=i then (∫ u : S, (u:E) i*f (u:E) ∂Q) else 0 := by
    by_cases hji : j=i
    · subst j
      rw [ite_eq_left rfl]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [H]
      ring
    · rw [ite_eq_right hji]
      exact sphere_pair_integration_by_parts hf hg hd i j (Ne.symm hji)
  have hs := congrArg (fun h : Fin d → ℝ => ∑ j, h j) (funext hp)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  rw [← integral_finsetSum _ (fun j _ => hH j)] at hs
  have he (u : S) : (∑ j : Fin d, H j u) =
      (d:ℝ)*((u:E) i*f (u:E))-((g (u:E)) i-(u:E) i*⟪g (u:E),(u:E)⟫) := by
    have hn : ∑ j : Fin d, (u:E) j^2=1 := by
      rw [← EuclideanSpace.real_norm_sq_eq,mem_sphere_zero_iff_norm.mp u.property,one_pow]
    have hscalar (a b : ℝ) : inner ℝ a b=a*b := by change b*a=a*b; ring
    have hin : ∑ j : Fin d, (u:E) j*(g (u:E)) j=⟪g (u:E),(u:E)⟫ := by
      simp only [PiLp.inner_apply,hscalar]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    dsimp only [H]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp_rw [mul_assoc ((u:E) i)]
    rw [← Finset.mul_sum,← Finset.sum_mul,hin,hn]
    ring
  simp_rw [he] at hs
  rw [integral_sub (hA.const_mul _) hB,integral_const_mul] at hs
  linarith

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_integrable_continuous_map {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {f : E → F} (hf : Continuous f) : Integrable (fun u : S => f (u:E)) Q := by
  have hb (u : S) : ‖(u:E)‖ ≤ (1:ℝ) := le_of_eq (mem_sphere_zero_iff_norm.mp u.property)
  simpa only [zero_add] using integrable_continuous_bounded_offset (p := Q) hf measurable_subtype_coe hb (0:E)

omit [NeZero d] in
lemma integral_euclidean_apply {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    {f : Ω → E} (hi : Integrable f p) (i : Fin d) :
    (∫ ω, f ω ∂p) i = ∫ ω, (f ω) i ∂p := by
  have hscalar (a b : ℝ) : inner ℝ a b=a*b := by change b*a=a*b; ring
  have he (x : E) : ⟪EuclideanSpace.single i (1:ℝ),x⟫=x i := by
    simp [PiLp.inner_apply]
  have h := integral_inner (𝕜 := ℝ) hi (EuclideanSpace.single i (1:ℝ))
  simp only [he] at h
  exact h.symm

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_radial_balance {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (i : Fin d) (r : ℝ) :
    r*((∫ u : S, (g (r • (u:E))) i ∂Q)-
      (∫ u : S, ⟪g (r • (u:E)),(u:E)⟫*(u:E) i ∂Q)) =
      ((d:ℝ)-1)*(∫ u : S, f (r • (u:E))*(u:E) i ∂Q) := by
  have hF : Continuous (fun x : E => f (r • x)) := by fun_prop
  have hG : Continuous (fun x : E => r • g (r • x)) := by fun_prop
  have hD (x : E) : HasGradientAt (fun y => f (r • y)) (r • g (r • x)) x := by
    simpa only [zero_add] using affine_scaled_gradient hd (0:E) r x
  have h := sphere_tangential_integration_by_parts hF hG hD i
  have hi : Integrable (fun u : S => (g (r • (u:E))) i) Q :=
    sphere_integrable_continuous (f := fun x : E => (g (r • x)) i) (by fun_prop)
  have hj : Integrable (fun u : S => ⟪g (r • (u:E)),(u:E)⟫*(u:E) i) Q :=
    sphere_integrable_continuous (f := fun x : E => ⟪g (r • x),x⟫*x i) (by fun_prop)
  have he (u : S) : (r • g (r • (u:E))) i-(u:E) i*⟪r • g (r • (u:E)),(u:E)⟫ =
      r*((g (r • (u:E))) i-⟪g (r • (u:E)),(u:E)⟫*(u:E) i) := by
    simp only [PiLp.smul_apply,smul_eq_mul,real_inner_smul_left]
    ring
  simp_rw [he] at h
  rw [integral_const_mul,integral_sub hi hj] at h
  convert h using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  ring

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_weighted_radial_hasDerivAt {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (i : Fin d) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => t^(d-1)*(∫ u : S, f (t • (u:E))*(u:E) i ∂Q))
      (r^(d-1)*(∫ u : S, (g (r • (u:E))) i ∂Q)) r := by
  let A := ∫ u : S, f (r • (u:E))*(u:E) i ∂Q
  let D := ∫ u : S, ⟪g (r • (u:E)),(u:E)⟫*(u:E) i ∂Q
  let G := ∫ u : S, (g (r • (u:E))) i ∂Q
  have hb := sphere_radial_balance hf hg hd i r
  have hd1 : 1 ≤ d := NeZero.pos d
  have hn : ((d-1:ℕ):ℝ)=(d:ℝ)-1 := by simp only [Nat.cast_sub hd1,Nat.cast_one]
  change r*(G-D)=((d:ℝ)-1)*A at hb
  rw [← hn] at hb
  have he : ((d-1:ℕ):ℝ)*r^((d-1)-1)*A+r^(d-1)*D=r^(d-1)*G := by
    by_cases hz : d-1=0
    · simp only [hz,Nat.cast_zero,zero_mul] at hb
      simp only [hz,Nat.cast_zero,zero_mul,pow_zero,one_mul,zero_add]
      nlinarith only [hb,hr]
    · have hnpos : 1 ≤ d-1 := by omega
      have hp : r^(d-1)=r^((d-1)-1)*r := by
        rw [← pow_succ,Nat.sub_add_cancel hnpos]
      rw [hp]
      nlinarith only [congrArg (fun v : ℝ => r^((d-1)-1)*v) hb]
  have h := ((hasDerivAt_id r).pow (d-1)).mul (sphere_radial_boundary_hasDerivAt hf hg hd i r)
  convert h using 1
  · rfl
  · simpa only [mul_one, id_eq, Pi.pow_apply, A, G, D] using he.symm

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma sphere_boundary_ball_identity {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x) (i : Fin d) :
    (∫ r in (0:ℝ)..1, r^(d-1)*(∫ u : S, (g (r • (u:E))) i ∂Q)) =
      ∫ u : S, f (u:E)*(u:E) i ∂Q := by
  have hA : Continuous (fun r : ℝ => ∫ u : S, f (r • (u:E))*(u:E) i ∂Q) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (sphere_radial_boundary_hasDerivAt hf hg hd i r).continuousAt
  have hG : Continuous (fun r : ℝ => ∫ u : S, (g (r • (u:E))) i ∂Q) :=
    sphere_radial_integral_continuous (f := fun x : E => (g x) i) (by fun_prop)
  have hw : Continuous (fun r : ℝ => r^(d-1)*(∫ u : S, f (r • (u:E))*(u:E) i ∂Q)) :=
    (continuous_id.pow _).mul hA
  have hi : IntervalIntegrable (fun r : ℝ => r^(d-1)*(∫ u : S, (g (r • (u:E))) i ∂Q)) volume 0 1 :=
    ((continuous_id.pow _).mul hG).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hw.continuousOn (fun r hr => sphere_weighted_radial_hasDerivAt hf hg hd i hr.1) hi
  simpa only [one_pow,one_mul,sphere_radial_boundary_zero,mul_zero,sub_zero,one_smul] using h

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)
local notation "P" => (radialLaw d (NeZero.pos d) : Measure ℝ)

lemma radial_average_gradient_identity {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x) (i : Fin d) :
    (∫ r, (∫ u : S, (g (r • (u:E))) i ∂Q) ∂P) =
      (d:ℝ)*(∫ u : S, f (u:E)*(u:E) i ∂Q) := by
  rw [radialLaw_integral]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul,sphere_boundary_ball_identity hf hg hd]

lemma sphere_estimator_mean {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (z : E) {c : ℝ} (hc : c ≠ 0) (i : Fin d) :
    (∫ r, (∫ u : S, (g (z+c • (r • (u:E)))) i ∂Q) ∂P) =
      ((d:ℝ)/c)*(∫ u : S, f (z+c • (u:E))*(u:E) i ∂Q) := by
  have hF : Continuous (fun x : E => f (z+c • x)) := by fun_prop
  have hG : Continuous (fun x : E => c • g (z+c • x)) := by fun_prop
  have h := radial_average_gradient_identity hF hG (affine_scaled_gradient hd z c) i
  simp only [PiLp.smul_apply,smul_eq_mul] at h
  simp_rw [integral_const_mul] at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hc).mpr
  convert h using 1; ring

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)
local notation "P" => (radialLaw d (NeZero.pos d) : Measure ℝ)

lemma ball_offset_continuous_integrable {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {f : E → F} (hf : Continuous f) (z : E) (c : ℝ) :
    Integrable (fun v : ℝ × S => f (z+c • ballOffset v)) ((P).prod Q) := by
  have hb (v : ℝ × S) : ‖c • ballOffset v‖ ≤ |c| := by
    rw [norm_smul,Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ballOffset_norm v) (abs_nonneg c)
  exact integrable_continuous_bounded_offset hf
    (ballOffset_continuous.measurable.const_smul c) hb z

lemma ball_estimator_coordinate_mean {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (z : E) {c : ℝ} (hc : c ≠ 0) (i : Fin d) :
    (∫ v : ℝ × S, (g (z+c • ballOffset v)) i ∂(P).prod Q) =
      ((d:ℝ)/c)*(∫ u : S, f (z+c • (u:E))*(u:E) i ∂Q) := by
  have hi := ball_offset_continuous_integrable (f := fun x : E => (g x) i) (by fun_prop) z c
  rw [integral_prod _ hi]
  trans ∫ r, (∫ u : S, (g (z+c • (r • (u:E)))) i ∂Q) ∂P
  · apply integral_congr_ae
    filter_upwards [radialLaw_mem_interval d (NeZero.pos d)] with r hr
    apply integral_congr_ae
    filter_upwards [] with u
    rw [ballOffset_of_mem_interval r u hr]
  · exact sphere_estimator_mean hf hg hd z hc i

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)
local notation "P" => (radialLaw d (NeZero.pos d) : Measure ℝ)

lemma ball_boundary_gradient {f : E → ℝ} {g : E → E}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (z : E) {c : ℝ} (hc : c ≠ 0) :
    (∫ v : ℝ × S, g (z+c • ballOffset v) ∂(P).prod Q) =
      ∫ u : S, (((d:ℝ)/c)*f (z+c • (u:E))) • (u:E) ∂Q := by
  have hi := ball_offset_continuous_integrable hg z c
  have hj : Integrable (fun u : S => (((d:ℝ)/c)*f (z+c • (u:E))) • (u:E)) Q :=
    sphere_integrable_continuous_map (f := fun y : E => (((d:ℝ)/c)*f (z+c • y)) • y) (by fun_prop)
  ext i
  rw [integral_euclidean_apply hi,integral_euclidean_apply hj]
  rw [ball_estimator_coordinate_mean hf hg hd z hc i]
  simp only [PiLp.smul_apply,smul_eq_mul,mul_assoc]
  rw [integral_const_mul]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)
local notation "P" => (radialLaw d (NeZero.pos d) : Measure ℝ)

lemma ball_offset_mean_zero : (∫ w : ℝ × S, ballOffset w ∂(P).prod Q) = (0:E) := by
  have hi : Integrable (ballOffset (d := d)) ((P).prod Q) := by
    simpa using ball_offset_continuous_integrable (f := id) continuous_id (0:E) 1
  ext i
  rw [integral_euclidean_apply hi]
  have hii := ball_offset_continuous_integrable (f := fun x : E => x i) (by fun_prop) (0:E) 1
  simp only [one_smul,zero_add] at hii
  rw [integral_prod _ hii]
  simp only [ballOffset,PiLp.smul_apply,smul_eq_mul,integral_const_mul,
    sphere_coordinate_mean_zero,mul_zero,integral_zero,PiLp.zero_apply]

lemma ball_smoothing_lower {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (z : E) (c : ℝ) :
    f z ≤ ∫ w : ℝ × S, f (z+c • ballOffset w) ∂(P).prod Q := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).differentiableAt.continuousAt)
  have hi := ball_offset_continuous_integrable hf z c
  have hz : Integrable (fun w : ℝ × S => c • ballOffset w) ((P).prod Q) := by
    simpa using ball_offset_continuous_integrable (f := id) continuous_id (0:E) c
  have hs (w : ℝ × S) : ⟪g z,c • ballOffset w⟫ ≤ f (z+c • ballOffset w)-f z := by
    have h := Gradient.convex_support hc hg z (z+c • ballOffset w)
    rw [add_sub_cancel_left] at h
    linarith
  have hh := integral_mono (hz.const_inner (g z)) (hi.sub (integrable_const _)) hs
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi (integrable_const _)] at hh
  rw [integral_inner (𝕜 := ℝ) hz (g z)] at hh
  simp only [integral_smul,ball_offset_mean_zero,smul_zero,inner_zero_right,
    integral_const,probReal_univ,one_smul] at hh
  linarith

lemma search_gain_implies_smoothing_gap {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (z u : E) (c : ℝ) {b : ℝ} (hb : 0 < b) (hgap : b ≤ f z-f u)
    (hgain : (∫ w : ℝ × S, f (z+(2*c) • ballOffset w)-f z ∂(P).prod Q) ≤ (f z-f u)/8) :
    b ≤ (∫ w : ℝ × S, f (z+c • ballOffset w) ∂(P).prod Q)-f u ∧
    (∫ w : ℝ × S, f (z+(2*c) • ballOffset w) ∂(P).prod Q)-
      (∫ w : ℝ × S, f (z+c • ballOffset w) ∂(P).prod Q) ≤
      ((∫ w : ℝ × S, f (z+c • ballOffset w) ∂(P).prod Q)-f u)/4 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).differentiableAt.continuousAt)
  rw [integral_sub (ball_offset_continuous_integrable hf z (2*c)) (integrable_const _)] at hgain
  simp only [integral_const,probReal_univ,one_smul] at hgain
  have hl := ball_smoothing_lower hc hg z c
  constructor <;> linarith

end OracleTemplate.ZerothOrder

end

end

section

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p]

lemma bounded_offset_gradient {f : E → ℝ} {g : E → E}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    {z : Ω → E} (hz : Measurable z) {r : ℝ} (hb : ∀ ω, ‖z ω‖ ≤ r) (x0 : E) :
    HasGradientAt (fun x => ∫ ω, f (x+z ω) ∂p) (∫ ω, g (x0+z ω) ∂p) x0 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  obtain ⟨C,hC⟩ := (isCompact_closedBall x0 (1+r)).exists_bound_of_continuousOn hg.continuousOn
  have hder := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x ω => f (x+z ω))
    (F' := fun x ω => toDual ℝ E (g (x+z ω)))
    (μ := p) (bound := fun _ => C) (ball_mem_nhds x0 (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun x => (integrable_continuous_bounded_offset hf hz hb x).aestronglyMeasurable))
    (integrable_continuous_bounded_offset hf hz hb x0)
    ((toDual ℝ E).continuous.comp_aestronglyMeasurable (integrable_continuous_bounded_offset (p := p) hg hz hb x0).aestronglyMeasurable)
    (Eventually.of_forall (fun ω x hx => by
      rw [(toDual ℝ E).norm_map]
      apply hC
      rw [mem_closedBall,dist_eq_norm]
      calc
        ‖x+z ω-x0‖ = ‖(x-x0)+z ω‖ := by congr 1; abel
        _ ≤ ‖x-x0‖+‖z ω‖ := norm_add_le _ _
        _ ≤ 1+r := add_le_add (le_of_lt (by simpa [mem_ball,dist_eq_norm] using hx)) (hb ω)))
    (integrable_const C)
    (Eventually.of_forall (fun ω x _ => by
      convert (hd (x+z ω)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (z ω)) using 1 <;> simp [Function.comp_def]))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hder using 1
  exact ((toDual ℝ E).toLinearIsometry.integral_comp_comm _).symm

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma bounded_offset_convex {f : E → ℝ} (hf : Continuous f) (hc : ConvexOn ℝ univ f)
    {z : Ω → E} (hz : Measurable z) {r : ℝ} (hb : ∀ ω, ‖z ω‖ ≤ r) :
    ConvexOn ℝ univ (fun x => ∫ ω, f (x+z ω) ∂p) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb' hab
  have hi x := integrable_continuous_bounded_offset (p := p) hf hz hb x
  calc
    (∫ ω, f (a • x+b • y+z ω) ∂p) ≤ ∫ ω, a*f (x+z ω)+b*f (y+z ω) ∂p := by
      apply integral_mono (hi _) (((hi x).const_mul a).add ((hi y).const_mul b))
      intro ω
      have he : a • x+b • y+z ω = a • (x+z ω)+b • (y+z ω) := by
        rw [smul_add,smul_add]
        have hh : a • z ω+b • z ω=z ω := by rw [← add_smul,hab,one_smul]
        calc
          _ = a • x+b • y+(a • z ω+b • z ω) := by rw [hh]
          _ = _ := by abel
      change f (a • x+b • y+z ω) ≤ a*f (x+z ω)+b*f (y+z ω)
      rw [he]
      exact hc.2 (mem_univ _) (mem_univ _) ha hb' hab
    _ = a • (∫ ω, f (x+z ω) ∂p)+b • (∫ ω, f (y+z ω) ∂p) := by
      rw [integral_add ((hi x).const_mul a) ((hi y).const_mul b),integral_const_mul,integral_const_mul]
      rfl

omit [CompleteSpace E] in
lemma bounded_offset_gradient_lipschitz {g : E → E} (hg : Continuous g) {L : ℝ}
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    {z : Ω → E} (hz : Measurable z) {r : ℝ} (hb : ∀ ω, ‖z ω‖ ≤ r) (x y : E) :
    ‖(∫ ω, g (x+z ω) ∂p)-(∫ ω, g (y+z ω) ∂p)‖ ≤ L*‖x-y‖ := by
  rw [← integral_sub (integrable_continuous_bounded_offset hg hz hb x)
    (integrable_continuous_bounded_offset hg hz hb y)]
  have hbound : ∀ᵐ ω ∂p, ‖g (x+z ω)-g (y+z ω)‖ ≤ L*‖x-y‖ := by
    filter_upwards [] with ω
    simpa only [add_sub_add_right_eq_sub] using hlip (x+z ω) (y+z ω)
  simpa using norm_integral_le_of_norm_le_const hbound

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => Point d
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)
local notation "P" => (radialLaw d (NeZero.pos d) : Measure ℝ)

noncomputable def ballSmooth (f : E → ℝ) (h : ℝ) (x : E) : ℝ :=
  ∫ w : ℝ × S, f (x+h • ballOffset w) ∂(P).prod Q

lemma ballSmooth_gradient {f : E → ℝ} {g : E → E}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x) (h : ℝ) (x : E) :
    HasGradientAt (ballSmooth f h)
      (∫ w : ℝ × S, g (x+h • ballOffset w) ∂(P).prod Q) x := by
  apply bounded_offset_gradient (r := |h|) hg hd (ballOffset_continuous.measurable.const_smul h)
  intro w
  change ‖h • ballOffset w‖ ≤ |h|
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (ballOffset_norm w) (abs_nonneg h)).trans_eq (mul_one _)

lemma ballSmooth_convex {f : E → ℝ} (hf : Continuous f) (hc : ConvexOn ℝ univ f) (h : ℝ) :
    ConvexOn ℝ univ (ballSmooth f h) := by
  apply bounded_offset_convex (r := |h|) hf hc (ballOffset_continuous.measurable.const_smul h)
  intro w
  change ‖h • ballOffset w‖ ≤ |h|
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (ballOffset_norm w) (abs_nonneg h)).trans_eq (mul_one _)

lemma ballSmooth_gradient_lipschitz {f : E → ℝ} {g : E → E} {L : ℝ}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (h : ℝ) (x y : E) :
    ‖gradient (ballSmooth f h) x-gradient (ballSmooth f h) y‖ ≤ L*‖x-y‖ := by
  rw [(ballSmooth_gradient hg hd h x).gradient,(ballSmooth_gradient hg hd h y).gradient]
  apply bounded_offset_gradient_lipschitz (r := |h|) hg hlip (ballOffset_continuous.measurable.const_smul h)
  intro w
  change ‖h • ballOffset w‖ ≤ |h|
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (ballOffset_norm w) (abs_nonneg h)).trans_eq (mul_one _)

lemma ballSmooth_upper {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 ≤ L) (hd : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (h : ℝ) (x : E) :
    ballSmooth f h x ≤ f x+L*h^2/2 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hi := ball_offset_continuous_integrable hf x h
  have hz : Integrable (fun w : ℝ × S => h • ballOffset w) ((P).prod Q) := by
    simpa using ball_offset_continuous_integrable (f := id) continuous_id (0:E) h
  have hu (w : ℝ × S) : f (x+h • ballOffset w) ≤ f x+⟪g x,h • ballOffset w⟫+L*h^2/2 := by
    have hs := Gradient.smooth_upper_bound hd hlip x (x+h • ballOffset w)
    rw [add_sub_cancel_left] at hs
    have hn : ‖h • ballOffset w‖ ≤ |h| := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (ballOffset_norm w) (abs_nonneg h)).trans_eq (mul_one _)
    have hsq : ‖h • ballOffset w‖^2 ≤ h^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (norm_nonneg _) (abs_nonneg h)).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hsq hL]
  have hh := integral_mono hi (((integrable_const _).add (hz.const_inner (g x))).add (integrable_const _)) hu
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_const _).add (hz.const_inner (g x))) (integrable_const _),
    integral_add (integrable_const _) (hz.const_inner (g x)),integral_inner (𝕜 := ℝ) hz (g x)] at hh
  simpa [ballSmooth,integral_smul,ball_offset_mean_zero] using hh

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} [NeZero d]
local notation "E" => Point d
local notation "S" => sphere (0:E) 1
local notation "Q" => (sphereLaw E : Measure S)

lemma twoPointExact_sphere_mean {f : E → ℝ} {g : E → E}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x)
    (x : E) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun u : S => twoPointExact f h x u) Q ∧
      (∫ u : S, twoPointExact f h x u ∂Q)=gradient (ballSmooth f h) x := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hc : Continuous (fun u : E => twoPointExact f h x u) := by unfold twoPointExact; fun_prop
  have hi := sphere_integrable_continuous_map hc
  refine ⟨hi,?_⟩
  rw [(ballSmooth_gradient hg hd h x).gradient,ball_boundary_gradient hf hg hd x hh]
  have hb : Integrable (fun u : S => (((d:ℝ)/h)*f (x+h • (u:E))) • (u:E)) Q :=
    sphere_integrable_continuous_map (f := fun u : E => (((d:ℝ)/h)*f (x+h • u)) • u) (by fun_prop)
  ext i
  rw [integral_euclidean_apply hi,integral_euclidean_apply hb]
  have hplus : Integrable (fun u : S => f (x+h • (u:E))*(u:E) i) Q :=
    sphere_integrable_continuous_map (f := fun u : E => f (x+h • u)*u i) (by fun_prop)
  have hminus : Integrable (fun u : S => f (x-h • (u:E))*(u:E) i) Q :=
    sphere_integrable_continuous_map (f := fun u : E => f (x-h • u)*u i) (by fun_prop)
  have hr := sphereLaw_integral_rotate E (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)
    (fun u : S => f (x+h • (u:E))*(u:E) i)
  have hre : (∫ u : S, f (x-h • (u:E))*(u:E) i ∂Q) =
      -(∫ u : S, f (x+h • (u:E))*(u:E) i ∂Q) := by
    have hn (u : S) : (sphereRotate (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) u : E) = -(u:E) := rfl
    simp only [hn,smul_neg,← sub_eq_add_neg,
      PiLp.neg_apply,mul_neg,integral_neg] at hr
    linarith
  simp only [twoPointExact,PiLp.smul_apply,smul_eq_mul]
  have he (u : S) : (d:ℝ)*(f (x+h • (u:E))-f (x-h • (u:E)))/(2*h)*(u:E) i =
      (d:ℝ)/(2*h)*(f (x+h • (u:E))*(u:E) i-f (x-h • (u:E))*(u:E) i) := by ring
  simp_rw [he,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_sub hplus hminus,hre]
  ring

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma twoPointExact_sphere_second_moment {d : ℕ} [NeZero d]
    {f : Point d → ℝ} {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    Integrable (fun u : sphere (0 : Point d) 1 => ‖twoPointExact f h x u‖^2) (sphereLaw (Point d)) ∧
      (∫ u : sphere (0 : Point d) 1, ‖twoPointExact f h x u‖^2 ∂sphereLaw (Point d)) ≤
        2*(d:ℝ)*‖gradient f x‖^2+((d:ℝ)*L*h)^2/8 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hF : Continuous (fun u : Point d => ‖twoPointExact f h x u‖^2) := by
    unfold twoPointExact
    fun_prop
  have hi := sphere_integrable_continuous_map hF
  refine ⟨hi,?_⟩
  have hp : Integrable (fun u : sphere (0 : Point d) 1 => ⟪gradient f x,(u:Point d)⟫^2)
      (sphereLaw (Point d)) := sphere_integrable_continuous_map ((innerSL ℝ (gradient f x)).continuous.pow 2)
  have hb : ∀ u : sphere (0 : Point d) 1, ‖twoPointExact f h x u‖^2 ≤
      2*(d:ℝ)^2*⟪gradient f x,(u:Point d)⟫^2+((d:ℝ)*L*h)^2/8 := by
    intro u
    have hu : ‖(u:Point d)‖=1 := mem_sphere_zero_iff_norm.mp u.property
    have he := twoPointExact_directional_error hh hc hg hlip x u hu
    have hn := norm_sub_le_norm_sub_add_norm_sub (twoPointExact f h x u)
      (((d:ℝ)*⟪gradient f x,(u:Point d)⟫) • (u:Point d)) 0
    simp only [sub_zero] at hn
    have hn2 := mul_self_le_mul_self (norm_nonneg _) hn
    have hs : ‖((d:ℝ)*⟪gradient f x,(u:Point d)⟫) • (u:Point d)‖^2=
        (d:ℝ)^2*⟪gradient f x,(u:Point d)⟫^2 := by
      rw [norm_smul,hu,mul_one,Real.norm_eq_abs,sq_abs,mul_pow]
    have he2 := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (d:ℝ)*L*h/4) |>.mpr he
    nlinarith [sq_nonneg (‖twoPointExact f h x u-((d:ℝ)*⟪gradient f x,(u:Point d)⟫) • (u:Point d)‖-
      ‖((d:ℝ)*⟪gradient f x,(u:Point d)⟫) • (u:Point d)‖),
      norm_nonneg (twoPointExact f h x u),sq_nonneg (‖twoPointExact f h x u‖)]
  have hr := integral_mono hi ((hp.const_mul _).add (integrable_const _)) hb
  simp only [Pi.add_apply] at hr
  rw [integral_add (hp.const_mul _) (integrable_const _),integral_const_mul,
    sphere_projection_second_moment,integral_const] at hr
  simp only [probReal_univ,one_smul] at hr
  have hd : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  convert hr using 1; field_simp

end OracleTemplate.ZerothOrder

end

section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma measurable_twoPointEstimate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun w : Point d × (Point d × (Ω × Ω)) =>
      twoPointEstimate g h w.1 w.2.1 w.2.2) := by
  unfold twoPointEstimate
  have hp : Measurable (fun w : Point d × (Point d × (Ω × Ω)) => g (w.1+h • w.2.1) w.2.2.1) :=
    hg.comp ((measurable_fst.add (measurable_fst.comp measurable_snd |>.const_smul h)).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hm : Measurable (fun w : Point d × (Point d × (Ω × Ω)) => g (w.1-h • w.2.1) w.2.2.2) :=
    hg.comp ((measurable_fst.sub (measurable_fst.comp measurable_snd |>.const_smul h)).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (((hp.sub hm).const_mul _).div_const _).smul (measurable_fst.comp measurable_snd)

lemma twoPoint_sphere_noise {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} (p : Measure Ω) [IsProbabilityMeasure p]
    (hg : Measurable (Function.uncurry g)) (hf : Continuous f)
    (hi : ∀ x, Integrable (g x) p) (hm : ∀ x, (∫ ω, g x ω ∂p)=f x)
    {σ : ℝ} (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (h : ℝ) (x : Point d) :
    let q := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1)).prod (p.prod p)
    let e := fun w : sphere (0 : Point d) 1 × (Ω × Ω) =>
      twoPointEstimate g h x w.1 w.2-twoPointExact f h x w.1
    Integrable (fun w => ‖e w‖^2) q ∧
      (∫ w, ‖e w‖^2 ∂q) ≤ (d:ℝ)^2*σ^2/(2*h^2) := by
  intro q e
  have harg : Measurable (fun w : sphere (0 : Point d) 1 × (Ω × Ω) => (x,((w.1:Point d),w.2))) :=
    measurable_const.prodMk ((continuous_subtype_val.measurable.comp measurable_fst).prodMk measurable_snd)
  have hG := (measurable_twoPointEstimate hg h).comp harg
  have hE : Continuous (fun u : Point d => twoPointExact f h x u) := by unfold twoPointExact; fun_prop
  have hu : Measurable (fun w : sphere (0 : Point d) 1 × (Ω × Ω) => (w.1:Point d)) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hdet := hE.measurable.comp hu
  have he : Measurable e := hG.sub hdet
  have hs (u : sphere (0 : Point d) 1) := twoPointEstimate_noise p hg hi hm hvi hv h x u
    (mem_sphere_zero_iff_norm.mp u.property)
  have hinner : Integrable (fun u : sphere (0 : Point d) 1 => ∫ ω, ‖‖e (u,ω)‖^2‖ ∂p.prod p) (sphereLaw (Point d)) := by
    apply (integrable_const (μ := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1))) ((d:ℝ)^2*σ^2/(2*h^2))).mono_nonneg
      (he.norm.pow_const 2).norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    · apply Filter.Eventually.of_forall
      intro u
      simpa only [Real.norm_eq_abs,abs_sq] using (hs u).2
  have hint : Integrable (fun w => ‖e w‖^2) q :=
    (integrable_prod_iff (he.norm.pow_const 2).aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall (fun u => (hs u).1),hinner⟩
  refine ⟨hint,?_⟩
  rw [show q=(sphereLaw (Point d) : Measure _).prod (p.prod p) from rfl,integral_prod _ hint]
  have hh := integral_mono hint.integral_prod_left (integrable_const (μ := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1))) ((d:ℝ)^2*σ^2/(2*h^2)))
    (fun u => (hs u).2)
  simpa using hh

end OracleTemplate.ZerothOrder

end

section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma twoPoint_sphere_oracle {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} (p : Measure Ω) [IsProbabilityMeasure p]
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) p) (hm : ∀ x, (∫ ω, g x ω ∂p)=f x)
    {σ L h : ℝ} (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    let q := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1)).prod (p.prod p)
    let T := fun w : sphere (0 : Point d) 1 × (Ω × Ω) => twoPointEstimate g h x w.1 w.2
    Integrable T q ∧ (∫ w, T w ∂q)=gradient (ballSmooth f h) x ∧
      Integrable (fun w => ‖T w‖^2) q ∧
      (∫ w, ‖T w‖^2 ∂q) ≤ 4*(d:ℝ)*‖gradient f x‖^2+((d:ℝ)*L*h)^2/4+(d:ℝ)^2*σ^2/h^2 := by
  intro q T
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hgc : Continuous (gradient f) := (show LipschitzWith ⟨L,hL⟩ (gradient f) from
    LipschitzWith.of_dist_le_mul (fun x y => by
      change dist (gradient f x) (gradient f y) ≤ L * dist x y
      simpa only [dist_eq_norm] using hlip x y)).continuous
  have harg : Measurable (fun w : sphere (0 : Point d) 1 × (Ω × Ω) => (x,((w.1:Point d),w.2))) :=
    measurable_const.prodMk ((continuous_subtype_val.measurable.comp measurable_fst).prodMk measurable_snd)
  have hTm' := (measurable_twoPointEstimate hg h).comp harg
  have hTm : Measurable T := hTm'
  have hN := twoPoint_sphere_noise p hg hf hi hm hvi hv h x
  have hH := twoPointExact_sphere_second_moment hL hh hc hd hlip x
  have hfst := measurePreserving_fst (μ := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1))) (ν := p.prod p)
  have hH2 := hfst.integrable_comp_of_integrable hH.1
  let H := fun w : sphere (0 : Point d) 1 × (Ω × Ω) => twoPointExact f h x w.1
  have hNi : Integrable (fun w => ‖T w-H w‖^2) q := hN.1
  have hHi : Integrable (fun w => ‖H w‖^2) q := hH2
  have hbound (w : sphere (0 : Point d) 1 × (Ω × Ω)) : ‖T w‖^2 ≤ 2*‖T w-H w‖^2+2*‖H w‖^2 := by
    have hn := norm_sub_le_norm_sub_add_norm_sub (T w) (H w) 0
    simp only [sub_zero] at hn
    have hs := mul_self_le_mul_self (norm_nonneg _) hn
    nlinarith [sq_nonneg (‖T w-H w‖-‖H w‖)]
  have hB : Integrable (fun w => 2*‖T w-H w‖^2+2*‖H w‖^2) q := (hNi.const_mul 2).add (hHi.const_mul 2)
  have hT2 : Integrable (fun w => ‖T w‖^2) q := hB.mono_nonneg
    (hTm.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Filter.Eventually.of_forall hbound)
  have hTi : Integrable T q := ((memLp_two_iff_integrable_sq_norm hTm.aestronglyMeasurable).mpr hT2).integrable (by norm_num)
  refine ⟨hTi,?_,hT2,?_⟩
  · rw [show q=(sphereLaw (Point d) : Measure _).prod (p.prod p) from rfl,integral_prod _ hTi]
    have he (u : sphere (0 : Point d) 1) : (∫ ω, T (u,ω) ∂p.prod p)=twoPointExact f h x u :=
      (twoPointEstimate_mean p hi hm h x u).2
    simp_rw [he]
    exact (twoPointExact_sphere_mean hgc hd x hh.ne').2
  · have hb := integral_mono hT2 hB hbound
    rw [integral_add (hNi.const_mul 2) (hHi.const_mul 2),integral_const_mul,integral_const_mul] at hb
    have he : (∫ w, ‖H w‖^2 ∂q)=(∫ u : sphere (0 : Point d) 1, ‖twoPointExact f h x u‖^2 ∂sphereLaw (Point d)) := by
      simpa only [probReal_univ,one_smul] using
        integral_fun_fst (μ := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1))) (ν := p.prod p)
          (fun u : sphere (0 : Point d) 1 => ‖twoPointExact f h x u‖^2)
    rw [he] at hb
    have hNb : (∫ w, ‖T w-H w‖^2 ∂q) ≤ (d:ℝ)^2*σ^2/(2*h^2) := hN.2
    have hsum := add_le_add (mul_le_mul_of_nonneg_left hNb (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hH.2 (by norm_num : (0:ℝ) ≤ 2))
    exact hb.trans (hsum.trans_eq (by ring))

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma ballSmooth_gradient_bias {d : ℕ} [NeZero d] {f : Point d → ℝ} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    ‖gradient (ballSmooth f h) x-gradient f x‖ ≤ L*h := by
  have hgc : Continuous (gradient f) := (show LipschitzWith ⟨L,hL⟩ (gradient f) from
    LipschitzWith.of_dist_le_mul (fun x y => by
      change dist (gradient f x) (gradient f y) ≤ L * dist x y
      simpa only [dist_eq_norm] using hlip x y)).continuous
  let q := (radialLaw d (NeZero.pos d) : Measure ℝ).prod (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1))
  have hi := ball_offset_continuous_integrable hgc x h
  have he : (∫ w : ℝ × sphere (0 : Point d) 1, gradient f (x+h • ballOffset w)-gradient f x ∂q) =
      gradient (ballSmooth f h) x-gradient f x := by
    rw [integral_sub hi (integrable_const _),(ballSmooth_gradient hgc hd h x).gradient]
    simp
  rw [← he]
  have hb : ∀ᵐ w : ℝ × sphere (0 : Point d) 1 ∂q,
      ‖gradient f (x+h • ballOffset w)-gradient f x‖ ≤ L*h := by
    filter_upwards [] with w
    have hn : ‖h • ballOffset w‖ ≤ h := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ballOffset_norm w) hh
    have ht := hlip (x+h • ballOffset w) x
    rw [add_sub_cancel_left] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hn hL)
  simpa [q] using norm_integral_le_of_norm_le_const hb

lemma twoPoint_sphere_relative_moment {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} (p : Measure Ω) [IsProbabilityMeasure p]
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) p) (hm : ∀ x, (∫ ω, g x ω ∂p)=f x)
    {σ L h : ℝ} (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hd : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    let q := (sphereLaw (Point d) : Measure (sphere (0 : Point d) 1)).prod (p.prod p)
    (∫ w, ‖twoPointEstimate g h x w.1 w.2‖^2 ∂q) ≤
      8*(d:ℝ)*‖gradient (ballSmooth f h) x‖^2+10*(d:ℝ)^2*L^2*h^2+(d:ℝ)^2*σ^2/h^2 := by
  intro q
  have hb := (twoPoint_sphere_oracle p hg hi hm hvi hv hL hh hc hd hlip x).2.2.2
  have he := ballSmooth_gradient_bias hL hh.le hd hlip x
  have hn := norm_sub_le_norm_sub_add_norm_sub (gradient f x) (gradient (ballSmooth f h) x) 0
  simp only [sub_zero,norm_sub_rev (gradient f x)] at hn
  have ht : ‖gradient f x‖ ≤ L*h+‖gradient (ballSmooth f h) x‖ := by linarith
  have ht2 := mul_self_le_mul_self (norm_nonneg _) ht
  have hs : ‖gradient f x‖^2 ≤ 2*‖gradient (ballSmooth f h) x‖^2+2*L^2*h^2 := by
    nlinarith [sq_nonneg (L*h-‖gradient (ballSmooth f h) x‖)]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hd2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hcoef := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ L^2*h^2 by positivity)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*(d:ℝ) by positivity)
  nlinarith [sq_nonneg ((d:ℝ)*L*h)]

end OracleTemplate.ZerothOrder

end
