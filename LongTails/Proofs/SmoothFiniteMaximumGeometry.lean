import LongTails.Proofs.SlidingStep
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LongTails.Setups.SmoothFiniteMaximum
import LongTails.Proofs.FrankWolfeDescent
import LongTails.Proofs.AffineSoftmaxResidual

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SmoothFiniteMaximumGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma affine_residual_bounds {C : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {z x : E} (hz : z ∈ C) (hx : x ∈ C) :
    0 ≤ f x - (f z + ⟪g z, x - z⟫) ∧
      f x - (f z + ⟪g z, x - z⟫) ≤ L / 2 * ‖x - z‖ ^ 2 := by
  have hlo := OracleTemplate.FrankWolfe.convex_support_on hc hz hx (hg z hz)
  have hhi := OracleTemplate.FrankWolfe.smooth_upper_bound_on hc.1 hg hlip hz hx
  constructor <;> linarith

lemma residual_exponent_bounds {C : Set E} {f : E → ℝ} {g : E → E} {L r τ : ℝ}
    (hc : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hτ : 0 < τ) (hcap : L * r ^ 2 ≤ τ)
    {z x : E} (hz : z ∈ C) (hx : x ∈ C) (hd : ‖x - z‖ ≤ r) :
    0 ≤ (f x - (f z + ⟪g z, x - z⟫)) / τ ∧
      (f x - (f z + ⟪g z, x - z⟫)) / τ ≤ 1 / 2 := by
  have hb := affine_residual_bounds hc hg hlip hz hx
  have hs : ‖x - z‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - z)]
  have hm := mul_le_mul_of_nonneg_left hs hL
  constructor
  · exact div_nonneg hb.1 hτ.le
  · apply (div_le_iff₀ hτ).2
    nlinarith


open LongTails.Algorithms.AffineSoftmaxEstimator in
lemma smoothValue_lower {ι : Type*} [Fintype ι] (v : ι → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (i : ι) : v i ≤ smoothValue τ v := by
  have hs : Real.exp (v i / τ) ≤ ∑ j, Real.exp (v j / τ) :=
    Finset.single_le_sum (fun j _ => (Real.exp_pos (v j / τ)).le) (Finset.mem_univ i)
  have hh := Real.log_le_log (Real.exp_pos (v i / τ)) hs
  rw [Real.log_exp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hτ.le
  have he : τ * (v i / τ) = v i := by field_simp
  rw [he] at hm
  exact hm

open LongTails.Algorithms.AffineSoftmaxEstimator in
lemma smoothValue_upper {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) {τ M : ℝ} (hτ : 0 < τ) (hM : ∀ i, v i ≤ M) :
    smoothValue τ v ≤ M + τ * Real.log (Fintype.card ι) := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (∑ i, Real.exp (v i / τ)) ≤
      (Fintype.card ι : ℝ) * Real.exp (M / τ) := by
    calc
      _ ≤ ∑ _ : ι, Real.exp (M / τ) := Finset.sum_le_sum (fun i _ =>
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hM i) hτ.le))
      _ = _ := by simp
  have hp : 0 < ∑ i, Real.exp (v i / τ) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hh := Real.log_le_log hp hs
  rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hτ.le
  unfold smoothValue
  convert hm using 1
  field_simp [hτ.ne']
  ring


open LongTails.Algorithms.AffineSoftmaxEstimator in
lemma smoothValue_gradient {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) (g : ι → E) {τ : ℝ} (hτ : τ ≠ 0) {x : E}
    (hg : ∀ i, HasGradientAt (f i) (g i) x) :
    HasGradientAt (fun y => smoothValue τ (fun i => f i y))
      (∑ i, (Real.exp (f i x / τ) / ∑ j, Real.exp (f j x / τ)) • g i) x := by
  have hp : 0 < ∑ i, Real.exp (f i x / τ) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hi (i : ι) : HasFDerivAt (fun y => Real.exp (f i y / τ))
      (Real.exp (f i x / τ) • (τ⁻¹ • (InnerProductSpace.toDual ℝ E (g i)))) x := by
    simpa only [div_eq_mul_inv, mul_comm] using ((hg i).hasFDerivAt.const_mul τ⁻¹).exp
  have hh := ((HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hi i)).log hp.ne').const_mul τ
  unfold smoothValue
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hh using 1
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  field_simp [hτ, hp.ne']


lemma bounded_gradient_value_difference {C : Set E} {f : E → ℝ} {g : E → E} {G : ℝ}
    (hc : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hbound : ∀ x ∈ C, ‖g x‖ ≤ G) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    |f x - f y| ≤ G * ‖x - y‖ := by
  have h1 := OracleTemplate.FrankWolfe.convex_support_on hc hx hy (hg x hx)
  have h2 := OracleTemplate.FrankWolfe.convex_support_on hc hy hx (hg y hy)
  have hi1 : |⟪g x, y - x⟫| ≤ G * ‖x - y‖ := by
    calc
      _ ≤ ‖g x‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
      _ ≤ G * ‖y - x‖ := mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev]
  have hi2 : |⟪g y, x - y⟫| ≤ G * ‖x - y‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hbound y hy) (norm_nonneg _))
  obtain ⟨ha, hb⟩ := abs_le.mp hi1
  obtain ⟨hc', hd⟩ := abs_le.mp hi2
  apply abs_le.mpr
  constructor <;> linarith


open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Proofs.AffineSoftmaxResidual

lemma smoothValue_gradient_lipschitz {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set E} (f : ι → E → ℝ) {τ L G : ℝ} (hτ : 0 < τ) (hG : 0 ≤ G)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G)
    (hlip : ∀ i x y, x ∈ C → y ∈ C →
      ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ‖gradient (fun z => smoothValue τ (fun i => f i z)) x -
      gradient (fun z => smoothValue τ (fun i => f i z)) y‖ ≤
      (L + 2 * G ^ 2 / τ) * ‖x - y‖ := by
  have hxg := smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)
  have hyg := smoothValue_gradient f (fun i => gradient (f i) y) hτ.ne' (fun i => hg i y hy)
  rw [hxg.gradient, hyg.gradient]
  change ‖(∑ i, gibbsWeight τ (fun j => f j x) i • gradient (f i) x) -
      ∑ i, gibbsWeight τ (fun j => f j y) i • gradient (f i) y‖ ≤ _
  have hvw (i : ι) : |f i x - f i y| ≤ G * ‖x - y‖ :=
    bounded_gradient_value_difference (hc i) (hg i) (hbound i) hx hy
  have hpq := gibbsWeight_difference (fun i => f i x) (fun i => f i y)
    hτ (mul_nonneg hG (norm_nonneg _)) hvw
  calc
    _ ≤ L * ‖x - y‖ + G * (2 * (G * ‖x - y‖) / τ) :=
      probability_mixture_difference _ _ _ _
        (fun i => (gibbsWeight_pos τ (fun j => f j x) i).le)
        (gibbsWeight_sum τ (fun j => f j x)) hG
        (fun i => hlip i x y hx hy) (fun i => hbound i y hy) hpq
    _ = _ := by ring


lemma smoothValue_support {ι : Type*} [Fintype ι] [Nonempty ι]
    (v w : ι → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    smoothValue τ v + (∑ i, gibbsWeight τ v i * (w i - v i)) ≤ smoothValue τ w := by
  let p := gibbsWeight τ v
  let q := gibbsWeight τ w
  have hk := OracleTemplate.SimplexEntropy.relative_entropy_lower
    (fun i => (gibbsWeight_pos τ v i).le) (gibbsWeight_pos τ w)
    (gibbsWeight_sum τ v) (gibbsWeight_sum τ w)
  have hk0 : 0 ≤ ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) :=
    (div_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).trans hk
  have hh := mul_nonneg hτ.le hk0
  have hi (i : ι) : τ * (p i * Real.log (p i) - p i * Real.log (q i)) =
      p i * (v i - w i) + p i * (smoothValue τ w - smoothValue τ v) := by
    change τ * (p i * Real.log (gibbsWeight τ v i) - p i * Real.log (gibbsWeight τ w i)) = _
    rw [gibbsWeight_log, gibbsWeight_log]
    unfold smoothValue
    field_simp
    ring
  rw [Finset.mul_sum] at hh
  simp_rw [hi] at hh
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, gibbsWeight_sum, one_mul] at hh
  have he : (∑ i, p i * (w i - v i)) = -(∑ i, p i * (v i - w i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change smoothValue τ v + (∑ i, p i * (w i - v i)) ≤ smoothValue τ w
  rw [he]
  linarith


lemma smoothValue_gradient_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) {τ G : ℝ} (hτ : τ ≠ 0) {x : E}
    (hg : ∀ i, HasGradientAt (f i) (gradient (f i) x) x)
    (hbound : ∀ i, ‖gradient (f i) x‖ ≤ G) :
    ‖gradient (fun z => smoothValue τ (fun i => f i z)) x‖ ≤ G := by
  rw [(smoothValue_gradient f (fun i => gradient (f i) x) hτ hg).gradient]
  exact norm_sum_smul_le (fun i _ => (gibbsWeight_pos τ (fun j => f j x) i).le)
    (gibbsWeight_sum τ (fun j => f j x)) (fun i _ => hbound i)

lemma smoothValue_convex {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set E} (f : ι → E → ℝ) {τ G : ℝ} (hτ : 0 < τ) (hC : Convex ℝ C)
    (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hbound : ∀ i x, x ∈ C → ‖gradient (f i) x‖ ≤ G) :
    ConvexOn ℝ C (fun z => smoothValue τ (fun i => f i z)) := by
  apply OracleTemplate.GeneralizedSliding.convexOn_of_subgradient (M := G) hC
    (sub := gradient (fun z => smoothValue τ (fun i => f i z)))
  intro x hx
  refine ⟨smoothValue_gradient_bound f hτ.ne' (fun i => hg i x hx) (fun i => hbound i x hx), ?_⟩
  intro y hy
  have hs := smoothValue_support (fun i => f i x) (fun i => f i y) hτ
  have hi : ⟪gradient (fun z => smoothValue τ (fun i => f i z)) x, y - x⟫ ≤
      ∑ i, gibbsWeight τ (fun j => f j x) i * (f i y - f i x) := by
    rw [(smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)).gradient]
    simp only [sum_inner, real_inner_smul_left]
    apply Finset.sum_le_sum
    intro i _
    have hh := OracleTemplate.FrankWolfe.convex_support_on (hc i) hx hy (hg i x hx)
    exact mul_le_mul_of_nonneg_left (by linarith : ⟪gradient (f i) x, y - x⟫ ≤ f i y - f i x)
      (gibbsWeight_pos τ (fun j => f j x) i).le
  linarith

end LongTails.Proofs.SmoothFiniteMaximumGeometry
