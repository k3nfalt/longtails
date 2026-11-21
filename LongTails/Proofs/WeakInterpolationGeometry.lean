import LongTails.Setups.DistributedWeakInterpolation
import LongTails.Proofs.InterpolationWeights
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeakInterpolationGeometry

open LongTails.Setups.DistributedWeakInterpolation LongTails.Algorithms.WeakInterpolationDesign
open InterpolationWeights

variable {p : Params} {f : Functions p}

lemma solutions_closed (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) :
    IsClosed (solutions p f) := by
  have he : solutions p f = ⋂ i, ⋂ y, {x | f i x ≤ f i y} := by
    ext x
    simp only [solutions, Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_congr' fun i => by simp [IsMinOn, IsMinFilter]
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun y =>
    isClosed_le (continuous_iff_continuousAt.mpr fun x => (hg i x).continuousAt) continuous_const

lemma gap_at_nearest (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖)
    {z : Point p} (hz : z ∈ solutions p f) (x : Point p) (i : Fin p.n) :
    f i x - f i z ≤ p.L i * (infDist x (solutions p f) ^ 2 / 2) := by
  obtain ⟨y, hy, hd⟩ := (solutions_closed hg).exists_infDist_eq_dist ⟨z, hz⟩ x
  have he : f i y = f i z := le_antisymm (hy i (mem_univ z)) (hz i (mem_univ y))
  have hh := ((hy i).isLocalMin Filter.univ_mem).fderiv_eq_zero
  have hzero : gradient (f i) y = 0 := by simp [gradient, hh]
  have hu := OracleTemplate.Gradient.smooth_upper_bound (hg i) (hlip i) y x
  rw [hzero, inner_zero_left, add_zero, he] at hu
  rw [hd, dist_eq_norm]
  linarith

lemma weighted_growth (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖)
    {z : Point p} (hz : z ∈ solutions p f) (x : Point p)
    (hqg : p.μ / 2 * infDist x (solutions p f) ^ 2 ≤ objective p f x - objective p f z)
    {c : ℝ} (hc : 0 ≤ c) (hh : ∀ i, 0 < (p.h i : ℝ))
    (hs : ∑ i, curvature p.L (fun j => p.h j) c i = (p.n : ℝ) * p.μ) :
    (∑ i, weight p.L (fun j => p.h j) c i * curvature p.L (fun j => p.h j) c i) *
      (infDist x (solutions p f) ^ 2 / 2) ≤
      ∑ i, weight p.L (fun j => p.h j) c i * (f i x - f i z) := by
  apply scaled_curvature _ _ _ hc hh (gap_at_nearest hg hlip hz x)
  rw [hs, Finset.sum_sub_distrib]
  unfold objective at hqg
  rw [← sub_div] at hqg
  have h := (le_div_iff₀ (show 0 < (p.n : ℝ) by exact_mod_cast p.n.pos)).mp hqg
  linarith

noncomputable def surrogate (p : Params) (f : Functions p) (x : Point p) : ℝ :=
  ∑ i, weights p i * f i x

noncomputable def direction (p : Params) (f : Functions p) (x : Point p) : Point p :=
  ∑ i, weights p i • gradient (f i) x

lemma surrogate_support (hw : ∀ i, 0 ≤ weights p i)
    (hc : ∀ i, ConvexOn ℝ univ (f i)) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (x z : Point p) : surrogate p f x - surrogate p f z ≤ ⟪direction p f x, x - z⟫ := by
  have h (i : Fin p.n) := OracleTemplate.Gradient.convex_support (hc i) (hg i) x z
  have hi (i : Fin p.n) : f i x - f i z ≤ ⟪gradient (f i) x, x - z⟫ := by
    have h' := h i
    rw [← neg_sub x z, inner_neg_right] at h'
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hw i))
  simpa only [surrogate, direction, sum_inner, real_inner_smul_left, mul_sub,
    Finset.sum_sub_distrib] using hs

lemma surrogate_upper_of_bounds {L : Fin p.n → ℝ} (hw : ∀ i, 0 ≤ weights p i)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ L i * ‖x - y‖)
    {C : ℝ} (hC : ∑ i, weights p i * L i ≤ C) (x y : Point p) :
    surrogate p f y ≤ surrogate p f x + ⟪direction p f x, y - x⟫ + C * (‖y - x‖ ^ 2 / 2) := by
  have hi (i : Fin p.n) : f i y ≤ f i x + ⟪gradient (f i) x, y - x⟫ +
      L i * (‖y - x‖ ^ 2 / 2) := by
    linarith [OracleTemplate.Gradient.smooth_upper_bound (hg i) (hlip i) x y]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hi i) (hw i))
  simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  unfold surrogate direction
  rw [sum_inner]
  simp only [real_inner_smul_left]
  linarith [mul_le_mul_of_nonneg_right hC (show 0 ≤ ‖y - x‖ ^ 2 / 2 by positivity)]

lemma surrogate_upper (hw : ∀ i, 0 ≤ weights p i)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖)
    {C : ℝ} (hC : ∑ i, weights p i * p.L i ≤ C) (x y : Point p) :
    surrogate p f y ≤ surrogate p f x + ⟪direction p f x, y - x⟫ + C * (‖y - x‖ ^ 2 / 2) :=
  surrogate_upper_of_bounds hw hg hlip hC x y

lemma surrogate_min (hw : ∀ i, 0 ≤ weights p i) {z : Point p} (hz : z ∈ solutions p f)
    (y : Point p) : surrogate p f z ≤ surrogate p f y :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hz i (mem_univ y)) (hw i))

lemma deterministic_step {x z g : Point p} {gap C η : ℝ} (hC : 0 < C)
    (hη : 0 ≤ η) (hηC : η * C ≤ 1 / 2)
    (hs : gap ≤ ⟪g, x - z⟫) (hgrad : ‖g‖ ^ 2 ≤ 2 * C * gap) :
    ‖x - η • g - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 - η * gap := by
  have he : x - η • g - z = (x - z) - η • g := by abel
  rw [he, norm_sub_sq_real, real_inner_smul_right, real_inner_comm g (x-z), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hη]
  have hgap : 0 ≤ gap := by
    exact nonneg_of_mul_nonneg_right ((sq_nonneg _).trans hgrad) (by positivity : 0 < 2 * C)
  have h1 := mul_le_mul_of_nonneg_left hgrad (sq_nonneg η)
  have h2 := mul_le_mul_of_nonneg_right hηC (mul_nonneg hη hgap)
  nlinarith [mul_le_mul_of_nonneg_left hs hη]

lemma direction_sq_of_bounds {L : Fin p.n → ℝ} (hw : ∀ i, 0 ≤ weights p i)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ L i * ‖x - y‖)
    {C : ℝ} (hC : 0 < C) (hL : ∑ i, weights p i * L i ≤ C)
    {z : Point p} (hz : z ∈ solutions p f) (x : Point p) :
    ‖direction p f x‖^2 ≤ 2*C*(surrogate p f x-surrogate p f z) := by
  let g := direction p f x
  let y := x - C⁻¹ • g
  have he : y-x = -C⁻¹ • g := by dsimp [y]; module
  have hh := (surrogate_min hw hz y).trans (surrogate_upper_of_bounds hw hg hlip hL x y)
  rw [he, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (inv_pos.mpr hC)] at hh
  change surrogate p f z ≤ surrogate p f x + -C⁻¹ * ⟪g,g⟫ + C * ((C⁻¹ * ‖g‖)^2 / 2) at hh
  rw [real_inner_self_eq_norm_sq] at hh
  field_simp [hC.ne', hC] at hh
  change ‖g‖^2 ≤ _
  nlinarith

lemma direction_sq (hw : ∀ i, 0 ≤ weights p i)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖)
    {C : ℝ} (hC : 0 < C) (hL : ∑ i, weights p i * p.L i ≤ C)
    {z : Point p} (hz : z ∈ solutions p f) (x : Point p) :
    ‖direction p f x‖^2 ≤ 2*C*(surrogate p f x-surrogate p f z) :=
  direction_sq_of_bounds hw hg hlip hC hL hz x

end LongTails.Proofs.WeakInterpolationGeometry
