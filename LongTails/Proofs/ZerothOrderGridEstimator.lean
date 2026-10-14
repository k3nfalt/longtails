import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic
import LongTails.Algorithms.AcceleratedZerothOrderConvex
import LongTails.Proofs.ZerothOrderEstimator
import LongTails.Proofs.ZerothOrderSmoothing

section

open MeasureTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma uniform_integral_explicit {ι E : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ι → E) :
    (∫ i, f i ∂(PMF.uniformOfFintype ι).toMeasure) = (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i := by
  simp [PMF.integral_eq_sum,PMF.uniformOfFintype_apply,Finset.smul_sum]

lemma finite_prod_integrable {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    {μ : Measure ι} [IsFiniteMeasure μ] {ν : Measure Ω} [SFinite ν]
    {f : ι × Ω → E} (hf : AEStronglyMeasurable f (μ.prod ν))
    (hi : ∀ i, Integrable (fun ω => f (i,ω)) ν) : Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff hf).mpr
  exact ⟨Filter.Eventually.of_forall hi, Integrable.of_finite⟩

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma secant_average_error (m : ℕ) (hm : 0 < m) (a v : ℕ → ℝ) {h b : ℝ}
    (hh : 0 < h)
    (herr : ∀ j < m, |(a (j+1)-a j)/(2*h/m)-v j| ≤ b) :
    |(a m-a 0)/(2*h)-(∑ j ∈ Finset.range m, v j)/m| ≤ b := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have heq : (a m-a 0)/(2*h)-(∑ j ∈ Finset.range m, v j)/m =
      (∑ j ∈ Finset.range m, ((a (j+1)-a j)/(2*h/m)-v j))/m := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_range_sub]
    field_simp
  rw [heq, abs_div, abs_of_pos hm']
  apply (div_le_iff₀ hm').mpr
  calc
    _ ≤ ∑ j ∈ Finset.range m, |(a (j+1)-a j)/(2*h/m)-v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, b := Finset.sum_le_sum (fun j hj => herr j (Finset.mem_range.mp hj))
    _ = b*m := by simp; ring

end OracleTemplate.ZerothOrder

end

section

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma boundary_secant_error {f : E → ℝ} {g : E → E} {L h t : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (ht : |t| ≤ h)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (q e : E) (he : ‖e‖ = 1) :
    |(f (q+(h-t) • e)-f (q+(-h-t) • e))/(2*h)-⟪g q,e⟫| ≤ 2*L*h := by
  let a := q+(-h-t) • e
  let b := q+(h-t) • e
  have hba : b-a = (2*h) • e := by dsimp [a,b]; module
  have hab : a-b = -(2*h) • e := by dsimp [a,b]; module
  have hlo := Gradient.convex_support hc hg a b
  have hup := Gradient.convex_support hc hg b a
  rw [hba, inner_smul_right] at hlo
  rw [hab, inner_smul_right] at hup
  have hlow : ⟪g a,e⟫ ≤ (f b-f a)/(2*h) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hlo])
  have hupp : (f b-f a)/(2*h) ≤ ⟪g b,e⟫ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hup])
  have ha : ‖a-q‖ ≤ 2*h := by
    simp only [a, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, he, mul_one]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp ht).2], by linarith [(abs_le.mp ht).1]⟩
  have hb : ‖b-q‖ ≤ 2*h := by
    simp only [b, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, he, mul_one]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp ht).2], by linarith [(abs_le.mp ht).1]⟩
  have hga : |⟪g a,e⟫-⟪g q,e⟫| ≤ 2*L*h := by
    rw [← inner_sub_left]
    have hi := abs_real_inner_le_norm (g a-g q) e
    rw [he, mul_one] at hi
    exact hi.trans ((hlip a q).trans (by nlinarith [mul_le_mul_of_nonneg_left ha hL]))
  have hgb : |⟪g b,e⟫-⟪g q,e⟫| ≤ 2*L*h := by
    rw [← inner_sub_left]
    have hi := abs_real_inner_le_norm (g b-g q) e
    rw [he, mul_one] at hi
    exact hi.trans ((hlip b q).trans (by nlinarith [mul_le_mul_of_nonneg_left hb hL]))
  change |(f b-f a)/(2*h)-⟪g q,e⟫| ≤ _
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hga).1], by linarith [(abs_le.mp hgb).2]⟩

lemma midpoint_secant_bias {f : E → ℝ} {g : E → E} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (m : ℕ) (hm : 0 < m) (q e : E) (he : ‖e‖ = 1) :
    |(f (q+h • e)-f (q-h • e))/(2*h)-
      (∑ j ∈ Finset.range m, ⟪g (q+(-h+(2*(j:ℝ)+1)*h/m) • e),e⟫)/m| ≤ 2*L*h/m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let a := fun j : ℕ => f (q+(-h+2*(j:ℝ)*h/m) • e)
  let v := fun j : ℕ => ⟪g (q+(-h+(2*(j:ℝ)+1)*h/m) • e),e⟫
  have herr (j : ℕ) (_hj : j < m) : |(a (j+1)-a j)/(2*h/m)-v j| ≤ 2*L*h/m := by
    have ht := boundary_secant_error hL (div_pos hh hm')
      (show |(0:ℝ)| ≤ h/m by simp; positivity) hc hg hlip
      (q+(-h+(2*(j:ℝ)+1)*h/m) • e) e he
    have hplus : q+(-h+(2*(j:ℝ)+1)*h/m) • e+(h/m-0) • e =
        q+(-h+2*((j+1:ℕ):ℝ)*h/m) • e := by push_cast; module
    have hminus : q+(-h+(2*(j:ℝ)+1)*h/m) • e+(- (h/m)-0) • e =
        q+(-h+2*(j:ℝ)*h/m) • e := by module
    rw [hplus,hminus] at ht
    simpa only [a,v,mul_div_assoc] using ht
  have hb : 0 ≤ 2*L*h/m := by positivity
  have ht := secant_average_error m hm a v hh herr
  have ha0 : a 0 = f (q-h • e) := by simp [a,sub_eq_add_neg]
  have ham : a m = f (q+h • e) := by
    have heq : -h+2*(m:ℝ)*h/m = h := by field_simp; ring
    simp only [a,heq]
  rw [ha0,ham] at ht
  exact ht

lemma boundaryDifference_apply {d : ℕ} (h : ℝ) (x z : Point d) (f : Point d → ℝ) (i : Fin d) :
    boundaryDifference h x z f i =
      (f (x+z+(h-z i) • direction i)-f (x+z+(-h-z i) • direction i))/(2*h) := by
  simp [boundaryDifference, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma boundary_difference_local_error {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z : Point d) (hz : ∀ i, |z i| ≤ h) :
    ‖boundaryDifference h x z f-gradient f (x+z)‖^2 ≤ 4*(d : ℝ)*L^2*h^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin d, (2*L*h)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have herr := boundary_secant_error hL hh (hz i) hc hg hlip (x+z) (direction i) (direction_norm i)
      have heq : ⟪gradient f (x+z),direction i⟫ = gradient f (x+z) i := EuclideanSpace.inner_basisFun_real _ _ _
      rw [heq] at herr
      simp only [PiLp.sub_apply, boundaryDifference_apply]
      nlinarith [sq_abs ((f (x+z+(h-z i) • direction i)-f (x+z+(-h-z i) • direction i))/(2*h)-gradient f (x+z) i),
        mul_self_le_mul_self (abs_nonneg _) herr]
    _ = _ := by simp; ring

lemma boundary_difference_spatial_error {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z : Point d) (hz : ∀ i, |z i| ≤ h) :
    ‖boundaryDifference h x z f-gradient f x‖^2 ≤ 10*(d : ℝ)*L^2*h^2 := by
  have hb := boundary_difference_local_error hL hh hc hg hlip x z hz
  have hzsq : ‖z‖^2 ≤ (d : ℝ)*h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, h^2 := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [sq_abs (z i), mul_self_le_mul_self (abs_nonneg (z i)) (hz i)]
      _ = _ := by simp
  have hgdiff := hlip (x+z) x
  rw [add_sub_cancel_left] at hgdiff
  have hgsq : ‖gradient f (x+z)-gradient f x‖^2 ≤ (d : ℝ)*L^2*h^2 := by
    have h1 := mul_self_le_mul_self (norm_nonneg _) hgdiff
    have h2 := mul_le_mul_of_nonneg_left hzsq (sq_nonneg L)
    nlinarith only [h1,h2]
  have ht := norm_sub_le_norm_sub_add_norm_sub (boundaryDifference h x z f) (gradient f (x+z)) (gradient f x)
  have ht2 := mul_self_le_mul_self (norm_nonneg _) ht
  nlinarith [sq_nonneg (‖boundaryDifference h x z f-gradient f (x+z)‖-‖gradient f (x+z)-gradient f x‖)]

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma boundary_error_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {σ L h : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z : Point d) (hz : ∀ i, |z i| ≤ h) :
    let est := coordinateSecant g (2*h) (fun i => x+z+(h-z i) • direction i)
      (fun i => x+z+(-h-z i) • direction i)
    Integrable (fun ξ => ‖est ξ-gradient f x‖^2) Q ∧
      (∫ ξ, ‖est ξ-gradient f x‖^2 ∂Q) ≤ 2*(d:ℝ)*σ^2/h^2+20*(d:ℝ)*L^2*h^2 := by
  have hb := boundary_difference_spatial_error hL hh hc hg hlip x z hz
  have hn := coordinateSecant_error_moment (h := 2*h) hmap hgm hgi hvi hv
    (fun i => x+z+(h-z i) • direction i) (fun i => x+z+(-h-z i) • direction i)
    (gradient f x) hb
  refine ⟨hn.1, ?_⟩
  convert hn.2 using 1; ring

lemma boundary_smoothed_error_moment {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {σ L h : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (hm : 0 < m) (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x z : Point d) (hz : ∀ i, |z i| ≤ h) :
    let est := coordinateSecant g (2*h) (fun i => x+z+(h-z i) • direction i)
      (fun i => x+z+(-h-z i) • direction i)
    Integrable (fun ξ => ‖est ξ-gridGradient f h m x‖^2) Q ∧
      (∫ ξ, ‖est ξ-gridGradient f h m x‖^2 ∂Q) ≤ 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2 := by
  have hb := boundary_difference_spatial_error hL hh hc hg hlip x z hz
  have hgdist := grid_smoothing_gradient_distance hm hL hh.le hlip x
  rw [norm_sub_rev] at hgdist
  have hdet : ‖boundaryDifference h x z f-gridGradient f h m x‖^2 ≤ 22*(d:ℝ)*L^2*h^2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (boundaryDifference h x z f) (gradient f x) (gridGradient f h m x)
    have ht2 := mul_self_le_mul_self (norm_nonneg _) ht
    nlinarith [sq_nonneg (‖boundaryDifference h x z f-gradient f x‖-‖gradient f x-gridGradient f h m x‖)]
  have hn := coordinateSecant_error_moment (h := 2*h) hmap hgm hgi hvi hv
    (fun i => x+z+(h-z i) • direction i) (fun i => x+z+(-h-z i) • direction i)
    (gridGradient f h m x) hdet
  refine ⟨hn.1, ?_⟩
  convert hn.2 using 1; ring

end OracleTemplate.ZerothOrder

end

section

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma grid_estimator_coordinate_bias {d m : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hm : 0 < m) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x : Point d) (i : Fin d) :
    |(∑ v : Fin d → Fin m, boundaryDifference h x (midpointPoint h v) f i)/(Fintype.card (Fin d → Fin m) : ℝ)-
      (∑ v : Fin d → Fin m, gradient f (x+midpointPoint h v) i)/(Fintype.card (Fin d → Fin m) : ℝ)| ≤ 2*L*h/m := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  apply coordinate_average_error i
  intro v
  let z := midpointPoint h v
  let q := x+z-(z i) • direction i
  have hs := midpoint_secant_bias hL hh hc hg hlip m hm q (direction i) (direction_norm i)
  have hplus : q+h • direction i = x+z+(h-z i) • direction i := by dsimp [q]; module
  have hminus : q-h • direction i = x+z+(-h-z i) • direction i := by dsimp [q]; module
  have hup (j : Fin m) : x+midpointPoint h (Function.update v i j) =
      q+(-h+(2*(j:ℝ)+1)*h/m) • direction i := by
    rw [midpointPoint_update]
    dsimp [q,z,midpointPoint_apply,midpointCoordinate]
    module
  have hsum : (∑ j : Fin m, gradient f (x+midpointPoint h (Function.update v i j)) i) =
      ∑ j ∈ Finset.range m, ⟪gradient f (q+(-h+(2*(j:ℝ)+1)*h/m) • direction i),direction i⟫ := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hup]
    exact (EuclideanSpace.inner_basisFun_real _ _ _).symm
  simp only [Fintype.card_fin]
  change |boundaryDifference h x z f i-(∑ j : Fin m, gradient f (x+midpointPoint h (Function.update v i j)) i)/m| ≤ _
  rw [boundaryDifference_apply,hsum,← hplus,← hminus]
  exact hs

lemma grid_estimator_bias_sq {d m : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hm : 0 < m) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x : Point d) :
    ‖(Fintype.card (Fin d → Fin m) : ℝ)⁻¹ • (∑ v : Fin d → Fin m, boundaryDifference h x (midpointPoint h v) f)-
      (Fintype.card (Fin d → Fin m) : ℝ)⁻¹ • (∑ v : Fin d → Fin m, gradient f (x+midpointPoint h v))‖^2 ≤
      (d : ℝ)*(2*L*h/m)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin d, (2*L*h/m)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := grid_estimator_coordinate_bias hL hh hm hc hg hlip x i
      have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
      simp only [PiLp.sub_apply,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul]
      simp only [← div_eq_inv_mul] at *
      nlinarith [sq_abs ((∑ v : Fin d → Fin m, boundaryDifference h x (midpointPoint h v) f i)/(Fintype.card (Fin d → Fin m) : ℝ)-
        (∑ v : Fin d → Fin m, gradient f (x+midpointPoint h v) i)/(Fintype.card (Fin d → Fin m) : ℝ))]
    _ = _ := by simp

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

attribute [local irreducible] coordinateSecant midpointPoint midpointCoordinate direction

lemma measurable_gridOracle {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (Function.uncurry (gridOracle (m := m) g h)) := by
  unfold Function.uncurry gridOracle coordinateSecant
  apply Finset.measurable_sum
  intro i hi
  have hu : Measurable (fun z : Point d × ((Fin d → Fin m) × (Fin d × Bool → Ω)) => gridUpper h i (z.1,z.2.1)) :=
    (measurable_gridUpper h i).comp (measurable_fst.prodMk measurable_snd.fst)
  have hl : Measurable (fun z : Point d × ((Fin d → Fin m) × (Fin d × Bool → Ω)) => gridLower h i (z.1,z.2.1)) :=
    (measurable_gridLower h i).comp (measurable_fst.prodMk measurable_snd.fst)
  exact (((hg.comp (hu.prodMk ((measurable_pi_apply (i,true)).comp measurable_snd.snd))).sub
    (hg.comp (hl.prodMk ((measurable_pi_apply (i,false)).comp measurable_snd.snd)))).div_const (2*h)).smul_const _

set_option maxHeartbeats 400000 in
lemma gridOracle_integral {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Nonempty (Fin m)]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q]
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (h : ℝ) (x : Point d) :
    Integrable (gridOracle (m := m) g h x) ((PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q) ∧
      (∫ s, gridOracle g h x s ∂(PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q) =
        (Fintype.card (Fin d → Fin m) : ℝ)⁻¹ • ∑ v : Fin d → Fin m, boundaryDifference h x (midpointPoint h v) f := by
  have hm : Measurable (gridOracle (m := m) g h x) :=
    (measurable_gridOracle (d := d) (m := m) (g := g) hgm h).of_uncurry_left
  have hsection (v : Fin d → Fin m) := coordinateSecant_integral hmap hgi hmean (2*h)
    (fun i => x+midpointPoint h v+(h-midpointPoint h v i) • direction i)
    (fun i => x+midpointPoint h v+(-h-midpointPoint h v i) • direction i)
  have hi : Integrable (gridOracle (m := m) g h x) ((PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q) :=
    finite_prod_integrable hm.aestronglyMeasurable (fun v => (hsection v).1)
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  change (∫ v, ∫ ξ, coordinateSecant g (2*h)
    (fun i => x+midpointPoint h v+(h-midpointPoint h v i) • direction i)
    (fun i => x+midpointPoint h v+(-h-midpointPoint h v i) • direction i) ξ ∂Q
    ∂(PMF.uniformOfFintype (Fin d → Fin m)).toMeasure) = _
  simp_rw [(hsection _).2]
  exact uniform_integral_explicit _

lemma gridOracle_error_moment {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {σ L h : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (hm : 0 < m) (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    Integrable (fun s => ‖gridOracle (m := m) g h x s-gridGradient f h m x‖^2)
      ((PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q) ∧
      (∫ s, ‖gridOracle g h x s-gridGradient f h m x‖^2
        ∂(PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q) ≤ 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2 := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hmeas : Measurable (fun s => ‖gridOracle (m := m) g h x s-gridGradient f h m x‖^2) :=
    (((measurable_gridOracle (d := d) (m := m) (g := g) hgm h).of_uncurry_left).sub_const _).norm.pow_const 2
  have hsec (v : Fin d → Fin m) := boundary_smoothed_error_moment hmap hgm hgi hvi hv hm hL hh hc hg hlip
    x (midpointPoint h v) (fun i => by rw [midpointPoint_apply]; exact midpointCoordinate_abs hh.le (v i))
  have hi : Integrable (fun s => ‖gridOracle (m := m) g h x s-gridGradient f h m x‖^2)
      ((PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q) :=
    finite_prod_integrable hmeas.aestronglyMeasurable (fun v => (hsec v).1)
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have hb := integral_mono hi.integral_prod_left
    (integrable_const (2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2)) (fun v => (hsec v).2)
  simpa only [integral_const,probReal_univ,one_smul] using hb

lemma gridOracle_bias {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {L h : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hm : 0 < m) (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x : Point d) :
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    ‖gradient (gridSmooth f h m) x-∫ s, gridOracle (m := m) g h x s
      ∂(PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod Q‖ ≤ 2*L*h*Real.sqrt d/m := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  rw [(gridOracle_integral (m := m) hmap hgm hgi hmean h x).2,grid_smoothing_gradient hg h x,norm_sub_rev]
  have hb := grid_estimator_bias_sq hL hh hm hc hg hlip x
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  have he : (2*L*h*Real.sqrt d/m)^2 = (d:ℝ)*(2*L*h/m)^2 := by
    calc
      _ = (2*L*h/m)^2*(Real.sqrt d)^2 := by ring
      _ = _ := by rw [hsqrt]; ring
  have hn : 0 ≤ 2*L*h*Real.sqrt d/m := by positivity
  change ‖_ - gridGradient f h m x‖^2 ≤ _ at hb
  nlinarith [norm_nonneg ((Fintype.card (Fin d → Fin m):ℝ)⁻¹ • (∑ v : Fin d → Fin m, boundaryDifference h x (midpointPoint h v) f)-gridGradient f h m x)]

end OracleTemplate.ZerothOrder

end
