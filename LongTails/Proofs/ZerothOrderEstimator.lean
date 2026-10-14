import LongTails.Algorithms.AcceleratedTwoPointZerothOrderConvex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import LongTails.Algorithms.AcceleratedZerothOrderConvex
import LongTails.Proofs.GdConvex
import LongTails.Setups.ZerothOrderSmoothAndConvex

section

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.FiniteVariance

lemma independent_difference_moment {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {X Y : Ω → ℝ}
    (hX : MemLp X 2 p) (hY : MemLp Y 2 p) (hind : IndepFun X Y p)
    (hmeanX : (∫ ω, X ω ∂p) = 0) (hmeanY : (∫ ω, Y ω ∂p) = 0)
    (c : ℝ) :
    Integrable (fun ω => ((X ω - Y ω) / c)^2) p ∧
      (∫ ω, ((X ω - Y ω) / c)^2 ∂p) =
        ((∫ ω, X ω ^ 2 ∂p) + (∫ ω, Y ω ^ 2 ∂p)) / c^2 := by
  have hsub : MemLp (fun ω => X ω - Y ω) 2 p := hX.sub hY
  have hmean : (∫ ω, X ω - Y ω ∂p) = 0 := by
    rw [integral_sub (hX.integrable (by norm_num)) (hY.integrable (by norm_num)), hmeanX, hmeanY]
    simp
  have hv := variance_fun_sub hX hY
  rw [hind.covariance_eq_zero hX hY] at hv
  simp only [mul_zero, sub_zero] at hv
  rw [variance_eq_integral hsub.aemeasurable, variance_eq_integral hX.aemeasurable,
    variance_eq_integral hY.aemeasurable, hmean, hmeanX, hmeanY] at hv
  simp only [sub_zero] at hv
  refine ⟨?_, ?_⟩
  · simpa only [div_pow] using hsub.integrable_sq.div_const (c^2)
  · simp only [div_pow]
    rw [integral_div, hv]

end OracleTemplate.FiniteVariance

end

section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma direction_norm {d : ℕ} (i : Fin d) : ‖direction i‖ = 1 :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one i

lemma difference_apply {d : ℕ} (h : ℝ) (x : Point d) (f : Point d → ℝ) (i : Fin d) :
    difference h x f i = (f (x + h • direction i) - f x) / h := by
  simp [difference, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma finite_difference_error {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : Point d) (i : Fin d) :
    0 ≤ difference h x f i - gradient f x i ∧
      difference h x f i - gradient f x i ≤ L * h / 2 := by
  have hl := Gradient.convex_support hc hg x (x + h • direction i)
  have hu := Gradient.smooth_upper_bound hg hlip x (x + h • direction i)
  have he : x + h • direction i - x = h • direction i := by abel
  rw [he, inner_smul_right] at hl hu
  rw [norm_smul, direction_norm, Real.norm_eq_abs, abs_of_pos hh, mul_one] at hu
  have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
    EuclideanSpace.inner_basisFun_real _ _ _
  rw [hi] at hl hu
  rw [difference_apply]
  constructor
  · apply sub_nonneg.mpr
    exact (le_div_iff₀ hh).mpr (by nlinarith only [hl])
  · apply (sub_le_iff_le_add).mpr
    exact (div_le_iff₀ hh).mpr (by nlinarith only [hu])

lemma difference_bias_sq {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : Point d) : ‖difference h x f - gradient f x‖ ^ 2 ≤ (d : ℝ) * (L * h / 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin d, (L * h / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have he := finite_difference_error hh hc hg hlip x i
      exact sq_le_sq₀ he.1 (he.1.trans he.2) |>.mpr he.2
    _ = _ := by simp

lemma estimate_apply {d : ℕ} {Ω : Type*} (g : Point d → Ω → ℝ)
    (h : ℝ) (x : Point d) (ξ : Fin d × Bool → Ω) (i : Fin d) :
    estimate g h x ξ i = (g (x + h • direction i) (ξ (i, true)) -
      g x (ξ (i, false))) / h := by
  simp [estimate, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma measurable_estimate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun z : Point d × (Fin d × Bool → Ω) => estimate g h z.1 z.2) := by
  unfold estimate
  apply Finset.measurable_sum
  intro i _
  exact (((hg.comp ((measurable_fst.add_const _).prodMk
    ((measurable_pi_apply _).comp measurable_snd))).sub
    (hg.comp (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)))).div_const h).smul_const _

lemma integral_comp_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {q : α → β} (hq : MeasurePreserving q μ ν)
    {φ : β → ℝ} (hφ : Integrable φ ν) : (∫ x, φ (q x) ∂μ) = ∫ y, φ y ∂ν := by
  have hm : AEStronglyMeasurable φ (μ.map q) := by rw [hq.map_eq]; exact hφ.aestronglyMeasurable
  have he := integral_map hq.measurable.aemeasurable hm
  rw [hq.map_eq] at he
  exact he.symm

lemma estimate_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (h : ℝ) (x : Point d) :
    Integrable (estimate g h x) Q ∧ (∫ ξ, estimate g h x ξ ∂Q) = difference h x f := by
  have hi (i : Fin d) : Integrable (fun ξ : Fin d × Bool → Ω =>
      (g (x + h • direction i) (ξ (i, true)) - g x (ξ (i, false))) / h) Q :=
    ((hmap _).integrable_comp_of_integrable (hgi _)).sub
      ((hmap _).integrable_comp_of_integrable (hgi _)) |>.div_const h
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hi i).smul_const _)
  · unfold estimate difference
    rw [integral_finsetSum _ (fun i _ => (hi i).smul_const _)]
    apply Finset.sum_congr rfl
    intro i _
    have hip : Integrable (fun ξ : Fin d × Bool → Ω =>
        g (x + h • direction i) (ξ (i, true))) Q :=
      (hmap _).integrable_comp_of_integrable (hgi _)
    have him : Integrable (fun ξ : Fin d × Bool → Ω => g x (ξ (i, false))) Q :=
      (hmap _).integrable_comp_of_integrable (hgi _)
    rw [integral_smul_const, integral_div, integral_sub hip him]
    rw [integral_comp_preserving (hmap (i, true)) (hgi _),
      integral_comp_preserving (hmap (i, false)) (hgi _), hmean, hmean]


lemma difference_noise_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} {σ h : ℝ}
    (ha : Integrable (fun ω => a ω ^ 2) μ) (hb : Integrable (fun ω => b ω ^ 2) μ)
    (ham : AEStronglyMeasurable a μ) (hbm : AEStronglyMeasurable b μ)
    (hav : (∫ ω, a ω ^ 2 ∂μ) ≤ σ ^ 2) (hbv : (∫ ω, b ω ^ 2 ∂μ) ≤ σ ^ 2) :
    Integrable (fun ω => ((a ω - b ω) / h) ^ 2) μ ∧
      (∫ ω, ((a ω - b ω) / h) ^ 2 ∂μ) ≤ 4 * σ ^ 2 / h ^ 2 := by
  have hai : MemLp a 2 μ := (memLp_two_iff_integrable_sq ham).mpr ha
  have hbi : MemLp b 2 μ := (memLp_two_iff_integrable_sq hbm).mpr hb
  have hi := (hai.sub hbi).integrable_sq.div_const (h ^ 2)
  simp only [div_pow] at *
  refine ⟨hi, ?_⟩
  have hpoint : ∀ ω, (a ω - b ω) ^ 2 / h ^ 2 ≤
      (2 * a ω ^ 2 + 2 * b ω ^ 2) / h ^ 2 := by
    intro ω
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (a ω + b ω)]) (sq_nonneg h)
  have hm := integral_mono hi (((ha.const_mul 2).add (hb.const_mul 2)).div_const (h ^ 2)) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hi hm
  rw [integral_div, integral_div, integral_add (ha.const_mul 2) (hb.const_mul 2),
    integral_const_mul, integral_const_mul] at hm
  rw [integral_div]
  exact hm.trans (div_le_div_of_nonneg_right (show 2 * (∫ ω, a ω ^ 2 ∂μ) + 2 * (∫ ω, b ω ^ 2 ∂μ) ≤ 4 * σ ^ 2 by linarith) (sq_nonneg h))

lemma estimate_variance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} {σ : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (h : ℝ) (x : Point d) :
    Integrable (fun ξ => ‖estimate g h x ξ - difference h x f‖ ^ 2) Q ∧
      (∫ ξ, ‖estimate g h x ξ - difference h x f‖ ^ 2 ∂Q) ≤
        4 * (d : ℝ) * σ ^ 2 / h ^ 2 := by
  have hcoord (i : Fin d) :
      Integrable (fun ξ => (estimate g h x ξ i - difference h x f i) ^ 2) Q ∧
      (∫ ξ, (estimate g h x ξ i - difference h x f i) ^ 2 ∂Q) ≤
        4 * σ ^ 2 / h ^ 2 := by
    let a := fun ξ : Fin d × Bool → Ω =>
      g (x + h • direction i) (ξ (i, true)) - f (x + h • direction i)
    let b := fun ξ : Fin d × Bool → Ω => g x (ξ (i, false)) - f x
    have ha : Integrable (fun ξ => a ξ ^ 2) Q :=
      (hmap _).integrable_comp_of_integrable (hvi _)
    have hb : Integrable (fun ξ => b ξ ^ 2) Q :=
      (hmap _).integrable_comp_of_integrable (hvi _)
    have ham : AEStronglyMeasurable a Q :=
      ((hmap _).integrable_comp_of_integrable (hgi _)).aestronglyMeasurable.sub aestronglyMeasurable_const
    have hbm : AEStronglyMeasurable b Q :=
      ((hmap _).integrable_comp_of_integrable (hgi _)).aestronglyMeasurable.sub aestronglyMeasurable_const
    have hav : (∫ ξ, a ξ ^ 2 ∂Q) ≤ σ ^ 2 := by
      change (∫ ξ, (g (x + h • direction i) (ξ (i, true)) - f (x + h • direction i)) ^ 2 ∂Q) ≤ _
      exact (integral_comp_preserving (hmap (i, true)) (hvi _)).trans_le (hv _)
    have hbv : (∫ ξ, b ξ ^ 2 ∂Q) ≤ σ ^ 2 := by
      change (∫ ξ, (g x (ξ (i, false)) - f x) ^ 2 ∂Q) ≤ _
      exact (integral_comp_preserving (hmap (i, false)) (hvi _)).trans_le (hv _)
    have he : (fun ξ => (estimate g h x ξ i - difference h x f i) ^ 2) =
        fun ξ => ((a ξ - b ξ) / h) ^ 2 := by
      funext ξ
      rw [estimate_apply, difference_apply]
      dsimp [a, b]
      congr 1
      ring
    rw [he]
    exact difference_noise_sq ha hb ham hbm hav hbv
  have he : (fun ξ => ‖estimate g h x ξ - difference h x f‖ ^ 2) =
      fun ξ => ∑ i : Fin d, (estimate g h x ξ i - difference h x f i) ^ 2 := by
    funext ξ
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => (hcoord i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hcoord i).1)]
  calc
    _ ≤ ∑ _i : Fin d, 4 * σ ^ 2 / h ^ 2 :=
      Finset.sum_le_sum (fun i _ => (hcoord i).2)
    _ = _ := by simp; ring

lemma difference_bias {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : Point d) : ‖difference h x f - gradient f x‖ ≤ L * h * Real.sqrt d / 2 := by
  have hs := difference_bias_sq hh hc hg hlip x
  have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hn : 0 ≤ L * h * Real.sqrt d / 2 := by positivity
  have he : (L * h * Real.sqrt d / 2) ^ 2 = (d : ℝ) * (L * h / 2) ^ 2 := by
    simp only [div_pow, mul_pow, hd]
    ring
  rw [← he] at hs
  exact (sq_le_sq₀ (norm_nonneg _) hn).mp hs

lemma integrable_sq_perturbation {E Ξ : Type*} [NormedAddCommGroup E] [MeasurableSpace Ξ]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {X : Ξ → E} {a c : E}
    (hm : AEStronglyMeasurable X Q)
    (hv : Integrable (fun ξ => ‖X ξ - a‖ ^ 2) Q) :
    Integrable (fun ξ => ‖X ξ - c‖ ^ 2) Q ∧
      (∫ ξ, ‖X ξ - c‖ ^ 2 ∂Q) ≤
        2 * (∫ ξ, ‖X ξ - a‖ ^ 2 ∂Q) + 2 * ‖a - c‖ ^ 2 := by
  have hu (ξ : Ξ) : ‖X ξ - c‖ ^ 2 ≤ 2 * ‖X ξ - a‖ ^ 2 + 2 * ‖a - c‖ ^ 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (X ξ) a c
    have hn := sq_nonneg (‖X ξ - a‖ - ‖a - c‖)
    have hs := mul_self_le_mul_self (norm_nonneg _) ht
    nlinarith only [hn, hs]
  have hmi : Integrable (fun ξ => 2 * ‖X ξ - a‖ ^ 2 + 2 * ‖a - c‖ ^ 2) Q :=
    (hv.const_mul 2).add (integrable_const _)
  have hi : Integrable (fun ξ => ‖X ξ - c‖ ^ 2) Q :=
    hmi.mono' (((hm.sub aestronglyMeasurable_const).norm.pow 2))
      (Filter.Eventually.of_forall (fun ξ => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖X ξ - c‖))] using hu ξ))
  refine ⟨hi, ?_⟩
  have he := integral_mono hi hmi hu
  rw [integral_add (hv.const_mul 2) (integrable_const _), integral_const_mul] at he
  simpa only [integral_const, probReal_univ, one_smul] using he

attribute [local irreducible] direction difference estimate

lemma estimate_error_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {σ L h : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : Point d) :
    Integrable (fun ξ => ‖estimate g h x ξ - gradient f x‖ ^ 2) Q ∧
      (∫ ξ, ‖estimate g h x ξ - gradient f x‖ ^ 2 ∂Q) ≤
        8 * (d : ℝ) * σ ^ 2 / h ^ 2 + (d : ℝ) * L ^ 2 * h ^ 2 / 2 := by
  have hv' := estimate_variance (d := d) (Ω := Ω) (σ := σ) (Q := Q) (f := f) (p := p) (g := g) hmap hgi hvi hv h x
  have hb := difference_bias_sq (d := d) (f := f) (L := L) (h := h) hh hc hg hlip x
  have hm : Measurable (fun ξ : Fin d × Bool → Ω => estimate g h x ξ) :=
    (measurable_estimate (d := d) (g := g) hgm h).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin d × Bool → Ω => (x, ξ)))
  have result := integrable_sq_perturbation (Q := Q) (X := estimate g h x) (a := difference h x f) (c := gradient f x) hm.aestronglyMeasurable hv'.1
  refine ⟨result.1, ?_⟩
  calc
    _ ≤ 2 * (∫ ξ, ‖estimate g h x ξ - difference h x f‖ ^ 2 ∂Q) +
        2 * ‖difference h x f - gradient f x‖ ^ 2 := result.2
    _ ≤ 2 * (4 * (d : ℝ) * σ ^ 2 / h ^ 2) + 2 * ((d : ℝ) * (L * h / 2) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hv'.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by ring

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma coordinateSecant_apply {d : ℕ} {Ω : Type*} (g : Point d → Ω → ℝ)
    (h : ℝ) (a b : Fin d → Point d) (ξ : Fin d × Bool → Ω) (i : Fin d) :
    coordinateSecant g h a b ξ i = (g (a i) (ξ (i,true))-g (b i) (ξ (i,false)))/h := by
  simp [coordinateSecant, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma coordinateDifference_apply {d : ℕ} (h : ℝ) (a b : Fin d → Point d)
    (f : Point d → ℝ) (i : Fin d) : coordinateDifference h a b f i = (f (a i)-f (b i))/h := by
  simp [coordinateDifference, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma coordinateSecant_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (h : ℝ) (a b : Fin d → Point d) :
    Integrable (coordinateSecant g h a b) Q ∧ (∫ ξ, coordinateSecant g h a b ξ ∂Q) = coordinateDifference h a b f := by
  have hi (i : Fin d) : Integrable (fun ξ : Fin d × Bool → Ω =>
      (g (a i) (ξ (i, true)) - g (b i) (ξ (i, false))) / h) Q :=
    ((hmap _).integrable_comp_of_integrable (hgi _)).sub
      ((hmap _).integrable_comp_of_integrable (hgi _)) |>.div_const h
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hi i).smul_const _)
  · unfold coordinateSecant coordinateDifference
    rw [integral_finsetSum _ (fun i _ => (hi i).smul_const _)]
    apply Finset.sum_congr rfl
    intro i _
    have hip : Integrable (fun ξ : Fin d × Bool → Ω =>
        g (a i) (ξ (i, true))) Q :=
      (hmap _).integrable_comp_of_integrable (hgi _)
    have him : Integrable (fun ξ : Fin d × Bool → Ω => g (b i) (ξ (i, false))) Q :=
      (hmap _).integrable_comp_of_integrable (hgi _)
    rw [integral_smul_const, integral_div, integral_sub hip him]
    rw [integral_comp_preserving (hmap (i, true)) (hgi _),
      integral_comp_preserving (hmap (i, false)) (hgi _), hmean, hmean]

lemma coordinateSecant_variance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} {σ : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (h : ℝ) (a b : Fin d → Point d) :
    Integrable (fun ξ => ‖coordinateSecant g h a b ξ - coordinateDifference h a b f‖ ^ 2) Q ∧
      (∫ ξ, ‖coordinateSecant g h a b ξ - coordinateDifference h a b f‖ ^ 2 ∂Q) ≤
        4 * (d : ℝ) * σ ^ 2 / h ^ 2 := by
  have hcoord (i : Fin d) :
      Integrable (fun ξ => (coordinateSecant g h a b ξ i - coordinateDifference h a b f i) ^ 2) Q ∧
      (∫ ξ, (coordinateSecant g h a b ξ i - coordinateDifference h a b f i) ^ 2 ∂Q) ≤
        4 * σ ^ 2 / h ^ 2 := by
    let noiseA := fun ξ : Fin d × Bool → Ω =>
      g (a i) (ξ (i, true)) - f (a i)
    let noiseB := fun ξ : Fin d × Bool → Ω => g (b i) (ξ (i, false)) - f (b i)
    have ha : Integrable (fun ξ => noiseA ξ ^ 2) Q :=
      (hmap _).integrable_comp_of_integrable (hvi _)
    have hb : Integrable (fun ξ => noiseB ξ ^ 2) Q :=
      (hmap _).integrable_comp_of_integrable (hvi _)
    have ham : AEStronglyMeasurable noiseA Q :=
      ((hmap _).integrable_comp_of_integrable (hgi _)).aestronglyMeasurable.sub aestronglyMeasurable_const
    have hbm : AEStronglyMeasurable noiseB Q :=
      ((hmap _).integrable_comp_of_integrable (hgi _)).aestronglyMeasurable.sub aestronglyMeasurable_const
    have hav : (∫ ξ, noiseA ξ ^ 2 ∂Q) ≤ σ ^ 2 := by
      change (∫ ξ, (g (a i) (ξ (i, true)) - f (a i)) ^ 2 ∂Q) ≤ _
      exact (integral_comp_preserving (hmap (i, true)) (hvi _)).trans_le (hv _)
    have hbv : (∫ ξ, noiseB ξ ^ 2 ∂Q) ≤ σ ^ 2 := by
      change (∫ ξ, (g (b i) (ξ (i, false)) - f (b i)) ^ 2 ∂Q) ≤ _
      exact (integral_comp_preserving (hmap (i, false)) (hvi _)).trans_le (hv _)
    have he : (fun ξ => (coordinateSecant g h a b ξ i - coordinateDifference h a b f i) ^ 2) =
        fun ξ => ((noiseA ξ - noiseB ξ) / h) ^ 2 := by
      funext ξ
      rw [coordinateSecant_apply, coordinateDifference_apply]
      dsimp [noiseA, noiseB]
      congr 1
      ring
    rw [he]
    exact difference_noise_sq ha hb ham hbm hav hbv
  have he : (fun ξ => ‖coordinateSecant g h a b ξ - coordinateDifference h a b f‖ ^ 2) =
      fun ξ => ∑ i : Fin d, (coordinateSecant g h a b ξ i - coordinateDifference h a b f i) ^ 2 := by
    funext ξ
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => (hcoord i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hcoord i).1)]
  calc
    _ ≤ ∑ _i : Fin d, 4 * σ ^ 2 / h ^ 2 :=
      Finset.sum_le_sum (fun i _ => (hcoord i).2)
    _ = _ := by simp; ring


lemma measurable_coordinateSecant {d : ℕ} {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g))
    (h : ℝ) (a b : Fin d → T → Point d) (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) :
    Measurable (fun z : T × (Fin d × Bool → Ω) => coordinateSecant g h (fun i => a i z.1) (fun i => b i z.1) z.2) := by
  unfold coordinateSecant
  apply Finset.measurable_sum
  intro i hi
  exact (((hg.comp (((ha i).comp measurable_fst).prodMk ((measurable_pi_apply (i,true)).comp measurable_snd))).sub
    (hg.comp (((hb i).comp measurable_fst).prodMk ((measurable_pi_apply (i,false)).comp measurable_snd)))).div_const h).smul_const _

lemma coordinateSecant_error_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {p : Measure Ω}
    {Q : Measure (Fin d × Bool → Ω)} [IsProbabilityMeasure Q] {σ h B : ℝ}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (a b : Fin d → Point d) (c : Point d) (hB : ‖coordinateDifference h a b f-c‖^2 ≤ B) :
    Integrable (fun ξ => ‖coordinateSecant g h a b ξ-c‖^2) Q ∧
      (∫ ξ, ‖coordinateSecant g h a b ξ-c‖^2 ∂Q) ≤ 8*(d:ℝ)*σ^2/h^2+2*B := by
  have hn := coordinateSecant_variance hmap hgi hvi hv h a b
  have hm : Measurable (coordinateSecant g h a b) := by
    unfold coordinateSecant
    apply Finset.measurable_sum
    intro i hi
    exact (((hgm.comp (measurable_const.prodMk (measurable_pi_apply (i,true)))).sub
      (hgm.comp (measurable_const.prodMk (measurable_pi_apply (i,false))))).div_const h).smul_const _
  have he := integrable_sq_perturbation (a := coordinateDifference h a b f) (c := c) hm.aestronglyMeasurable hn.1
  refine ⟨he.1, ?_⟩
  calc
    _ ≤ 2*(4*(d:ℝ)*σ^2/h^2)+2*B := he.2.trans
      (add_le_add (mul_le_mul_of_nonneg_left hn.2 (by norm_num)) (mul_le_mul_of_nonneg_left hB (by norm_num)))
    _ = _ := by ring

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma centeredOracle_measurable {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (R B : ℝ) (x0 : Point d) :
    Measurable (Function.uncurry (centeredOracle g R B x0)) := by
  have h1 : Measurable (fun v : Point d × (Ω × Ω) => g (x0 + (2*R) • v.1) v.2.1) :=
    hg.comp (((measurable_fst.const_smul (2*R)).const_add x0).prodMk
      (measurable_fst.comp measurable_snd))
  have h2 : Measurable (fun v : Point d × (Ω × Ω) => g x0 v.2.2) :=
    hg.comp (measurable_const.prodMk (measurable_snd.comp measurable_snd))
  exact ((h1.sub h2).div_const B).add_const _

lemma centeredOracle_mean {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    (p : Measure Ω) [IsProbabilityMeasure p] (hi : ∀ x, Integrable (g x) p)
    (hm : ∀ x, (∫ ω, g x ω ∂p) = f x) (R B : ℝ) (x0 y : Point d) :
    Integrable (centeredOracle g R B x0 y) (p.prod p) ∧
      (∫ ω, centeredOracle g R B x0 y ω ∂p.prod p) =
        (f (x0 + (2*R) • y) - f x0) / B + 1/2 := by
  have hX := (measurePreserving_fst (μ := p) (ν := p)).integrable_comp_of_integrable (hi (x0 + (2*R) • y))
  have hY := (measurePreserving_snd (μ := p) (ν := p)).integrable_comp_of_integrable (hi x0)
  simp only [Function.comp_def] at hX hY
  have hd : Integrable (fun ω : Ω × Ω => (g (x0 + (2*R) • y) ω.1 - g x0 ω.2) / B) (p.prod p) :=
    (hX.sub hY).div_const B
  refine ⟨hd.add (integrable_const _), ?_⟩
  unfold centeredOracle
  rw [integral_add hd (integrable_const _), integral_div,
    integral_sub hX hY, integral_fun_fst, integral_fun_snd]
  simp [hm]

lemma centeredOracle_variance {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    (p : Measure Ω) [IsProbabilityMeasure p] (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hm : ∀ x, (∫ ω, g x ω ∂p) = f x)
    {σ : ℝ} (hi : ∀ x, Integrable (fun ω => (g x ω - f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x)^2 ∂p) ≤ σ^2)
    (R B : ℝ) (x0 y : Point d) :
    Integrable (fun ω => (centeredOracle g R B x0 y ω -
      ((f (x0 + (2*R) • y) - f x0) / B + 1/2))^2) (p.prod p) ∧
    (∫ ω, (centeredOracle g R B x0 y ω -
      ((f (x0 + (2*R) • y) - f x0) / B + 1/2))^2 ∂p.prod p) ≤ 2*σ^2/B^2 := by
  let u := x0 + (2*R) • y
  let a := fun ω : Ω => g u ω - f u
  let b := fun ω : Ω => g x0 ω - f x0
  have ha : Measurable a := hg.of_uncurry_left.sub_const _
  have hb : Measurable b := hg.of_uncurry_left.sub_const _
  have hma : MemLp a 2 p := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr (hi u)
  have hmb : MemLp b 2 p := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr (hi x0)
  have hia := hma.comp_measurePreserving (measurePreserving_fst (μ := p) (ν := p))
  have hib := hmb.comp_measurePreserving (measurePreserving_snd (μ := p) (ν := p))
  have hea : (∫ ω : Ω × Ω, a ω.1 ∂p.prod p) = 0 := by
    rw [integral_fun_fst a]
    simp only [probReal_univ, one_smul]
    dsimp only [a]
    rw [integral_sub (hgi u) (integrable_const _), hm]
    simp
  have heb : (∫ ω : Ω × Ω, b ω.2 ∂p.prod p) = 0 := by
    rw [integral_fun_snd b]
    simp only [probReal_univ, one_smul]
    dsimp only [b]
    rw [integral_sub (hgi x0) (integrable_const _), hm]
    simp
  have h := FiniteVariance.independent_difference_moment hia hib (indepFun_prod ha hb) hea heb B
  simp only [Function.comp_def] at h
  have he (ω : Ω × Ω) : centeredOracle g R B x0 y ω -
      ((f (x0 + (2*R) • y) - f x0) / B + 1/2) = (a ω.1 - b ω.2) / B := by
    dsimp [centeredOracle, a, b, u]
    ring
  simp_rw [he]
  refine ⟨h.1, ?_⟩
  rw [h.2, integral_fun_fst (fun ω => a ω ^ 2), integral_fun_snd (fun ω => b ω ^ 2)]
  simp only [probReal_univ, one_smul]
  apply div_le_div_of_nonneg_right _ (sq_nonneg B)
  exact (add_le_add (hv u) (hv x0)).trans_eq (by ring)

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma twoPointEstimate_mean {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} (p : Measure Ω) [IsProbabilityMeasure p]
    (hi : ∀ x, Integrable (g x) p) (hm : ∀ x, (∫ ω, g x ω ∂p)=f x)
    (h : ℝ) (x u : Point d) :
    Integrable (twoPointEstimate g h x u) (p.prod p) ∧
      (∫ ω, twoPointEstimate g h x u ω ∂p.prod p)=twoPointExact f h x u := by
  have ha := (measurePreserving_fst (μ := p) (ν := p)).integrable_comp_of_integrable (hi (x+h • u))
  have hb := (measurePreserving_snd (μ := p) (ν := p)).integrable_comp_of_integrable (hi (x-h • u))
  simp only [Function.comp_def] at ha hb
  refine ⟨(((ha.sub hb).const_mul (d:ℝ)).div_const (2*h)).smul_const u,?_⟩
  unfold twoPointEstimate twoPointExact
  rw [integral_smul_const,integral_div,integral_const_mul,integral_sub ha hb,
    integral_fun_fst,integral_fun_snd]
  simp [hm]

lemma twoPointEstimate_noise {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} (p : Measure Ω) [IsProbabilityMeasure p]
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) p) (hm : ∀ x, (∫ ω, g x ω ∂p)=f x)
    {σ : ℝ} (hvi : ∀ x, Integrable (fun ω => (g x ω-f x)^2) p)
    (hv : ∀ x, (∫ ω, (g x ω-f x)^2 ∂p) ≤ σ^2)
    (h : ℝ) (x u : Point d) (hu : ‖u‖=1) :
    Integrable (fun ω => ‖twoPointEstimate g h x u ω-twoPointExact f h x u‖^2) (p.prod p) ∧
      (∫ ω, ‖twoPointEstimate g h x u ω-twoPointExact f h x u‖^2 ∂p.prod p) ≤
        (d:ℝ)^2*σ^2/(2*h^2) := by
  let a := x+h • u
  let b := x-h • u
  have hab : b+(2*(1/2:ℝ)) • (a-b)=a := by norm_num
  have hn := centeredOracle_variance p hg hi hm hvi hv (1/2) (2*h) b (a-b)
  let e := fun ω : Ω × Ω => (g a ω.1-g b ω.2)/(2*h)-(f a-f b)/(2*h)
  have he : (fun ω => (centeredOracle g (1/2) (2*h) b (a-b) ω-
      ((f (b+(2*(1/2:ℝ)) • (a-b))-f b)/(2*h)+1/2))^2) = fun ω => e ω^2 := by
    funext ω
    simp only [centeredOracle,hab,e]
    ring
  rw [he] at hn
  have hnorm (ω : Ω × Ω) : ‖twoPointEstimate g h x u ω-twoPointExact f h x u‖^2=(d:ℝ)^2*e ω^2 := by
    have hh : twoPointEstimate g h x u ω-twoPointExact f h x u=((d:ℝ)*e ω) • u := by
      unfold twoPointEstimate twoPointExact e a b
      rw [← sub_smul]
      congr 1
      ring
    rw [hh,norm_smul,hu,mul_one,Real.norm_eq_abs,sq_abs,mul_pow]
  simp_rw [hnorm]
  refine ⟨hn.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left hn.2 (sq_nonneg (d:ℝ))
  convert hh using 1; ring

lemma central_directional_error {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x u : Point d) (hu : ‖u‖=1) :
    |(f (x+h • u)-f (x-h • u))/(2*h)-⟪gradient f x,u⟫| ≤ L*h/4 := by
  have hpa := Gradient.convex_support hc hg x (x+h • u)
  have hpb := Gradient.smooth_upper_bound hg hlip x (x+h • u)
  have hma := Gradient.convex_support hc hg x (x-h • u)
  have hmb := Gradient.smooth_upper_bound hg hlip x (x-h • u)
  have hp : x+h • u-x=h • u := by abel
  have hm : x-h • u-x=-(h • u) := by abel
  rw [hp,inner_smul_right] at hpa hpb
  rw [hm,inner_neg_right,inner_smul_right] at hma hmb
  rw [norm_smul,hu,mul_one,Real.norm_eq_abs,abs_of_pos hh] at hpb
  rw [norm_neg,norm_smul,hu,mul_one,Real.norm_eq_abs,abs_of_pos hh] at hmb
  rw [abs_le]
  constructor
  · apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ (by positivity : 0 < 2*h)).mpr
    nlinarith [hpa,hmb]
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ (by positivity : 0 < 2*h)).mpr
    nlinarith [hpb,hma]

lemma twoPointExact_directional_error {d : ℕ} {f : Point d → ℝ} {L h : ℝ}
    (hh : 0 < h) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x u : Point d) (hu : ‖u‖=1) :
    ‖twoPointExact f h x u-((d:ℝ)*⟪gradient f x,u⟫) • u‖ ≤ (d:ℝ)*L*h/4 := by
  have he := central_directional_error hh hc hg hlip x u hu
  have hid : twoPointExact f h x u-((d:ℝ)*⟪gradient f x,u⟫) • u=
      ((d:ℝ)*((f (x+h • u)-f (x-h • u))/(2*h)-⟪gradient f x,u⟫)) • u := by
    unfold twoPointExact
    rw [← sub_smul]
    congr 1
    ring
  rw [hid,norm_smul,hu,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Nat.cast_nonneg d)]
  exact (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg d)).trans_eq (by ring)

end OracleTemplate.ZerothOrder

end
