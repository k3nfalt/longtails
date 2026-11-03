import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import LongTails.Proofs.TailObliviousGeometry
import LongTails.Proofs.TailObliviousAnchoring
import LongTails.Proofs.QuadraticNoiseMoments
import LongTails.Setups.TailObliviousMonotoneRootFinding

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.TailObliviousNoise

open TailObliviousGeometry
open LongTails.Setups.TailObliviousMonotoneRootFinding

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

lemma centered_power_moment {P : Measure Ω} [IsProbabilityMeasure P] {α : ℝ}
    (hα1 : 1 < α) (hα2 : α ≤ 2)
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hXα : Integrable (fun ω => ‖X ω‖ ^ α) P)
    (hzero : (∫ ω, X ω ∂P) = 0) (y : E) :
    Integrable (fun ω => ‖y + X ω‖ ^ α) P ∧
    (∫ ω, ‖y + X ω‖ ^ α ∂P) ≤ ‖y‖ ^ α + 7 * ∫ ω, ‖X ω‖ ^ α ∂P := by
  set J := powerDual (innerSL ℝ) α y with hJ
  have hJi : Integrable (fun ω => J (X ω)) P := J.integrable_comp hXi
  have hfirst : Integrable (fun ω => ‖y‖ ^ α + α * J (X ω)) P :=
    (integrable_const _).add (hJi.const_mul α)
  have hu : Integrable (fun ω => ‖y‖ ^ α + α * J (X ω) + 7 * ‖X ω‖ ^ α) P :=
    hfirst.add (hXα.const_mul 7)
  have hbound (ω : Ω) : ‖y + X ω‖ ^ α ≤ ‖y‖ ^ α + α * J (X ω) + 7 * ‖X ω‖ ^ α :=
    inner_power_smooth hα1 hα2 y (X ω)
  have hm : Measurable (fun ω => ‖y + X ω‖ ^ α) :=
    (measurable_const.add hX).norm.pow_const α
  have hi : Integrable (fun ω => ‖y + X ω‖ ^ α) P := by
    apply hu.mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hbound ω)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, ‖y‖ ^ α + α * J (X ω) + 7 * ‖X ω‖ ^ α ∂P := integral_mono hi hu hbound
    _ = _ := by
      rw [integral_add hfirst (hXα.const_mul 7),
        integral_add (integrable_const _) (hJi.const_mul α), integral_const_mul,
        J.integral_comp_comm hXi, hzero, integral_const_mul]
      simp

lemma one_sub_rpow_half_le {t α : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hα1 : 1 < α)
    (hα2 : α ≤ 2) : (1 - t) ^ (α / 2) ≤ 1 - t / 2 := by
  have h := rpow_one_add_le_one_add_mul_self (s := -t) (by linarith) (p := α / 2)
    (by linarith) (by linarith)
  have hs : 1 + -t = 1 - t := by ring
  rw [hs] at h
  nlinarith

lemma eg_step_moment (F : E → E) (L : ℝ) (hFm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hFl : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (p : ProbabilityMeasure Ω) (g : E → Ω → E) (σ α : ℝ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (a η : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L) (hη : 0 ≤ η) (hηa : η * a ≤ 1 / 4)
    (hηL : η * (L + a) ≤ 1 / 4) (b x u : E) (hu : F u + a • u - b = 0) :
    Integrable (fun ω : Fin 2 → Ω =>
      ‖(x - η • (g (x - η • (g x (ω 0) + a • x - b)) (ω 1) +
        a • (x - η • (g x (ω 0) + a • x - b)) - b)) - u‖ ^ α)
      (Measure.pi fun _ => (p : Measure Ω)) ∧
    (∫ ω : Fin 2 → Ω,
      ‖(x - η • (g (x - η • (g x (ω 0) + a • x - b)) (ω 1) +
        a • (x - η • (g x (ω 0) + a • x - b)) - b)) - u‖ ^ α
      ∂Measure.pi fun _ => (p : Measure Ω)) ≤
      (1 - η * a / 2) * ‖x - u‖ ^ α + 9 * η ^ α * σ ^ α := by
  let H : E → E := fun y => F y + a • y - b
  let y : Ω → E := fun ω0 => x - η • (g x ω0 + a • x - b)
  let f : Ω × Ω → ℝ := fun w =>
    ‖(x - η • (g (y w.1) w.2 + a • y w.1 - b)) - u‖ ^ α
  have hgm := hg.measurable
  have hym : Measurable y := by
    dsimp only [y]
    exact measurable_const.sub ((hgm.comp (measurable_const.prodMk measurable_id)).add
      measurable_const |>.sub measurable_const |>.const_smul η)
  have hfm : Measurable f := by
    dsimp only [f]
    have h1 : Measurable (fun w : Ω × Ω => g (y w.1) w.2) :=
      hgm.comp ((hym.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable (fun w : Ω × Ω => y w.1) := hym.comp measurable_fst
    exact (((measurable_const.sub ((h1.add (h2.const_smul a)).sub measurable_const
      |>.const_smul η)).sub measurable_const).norm.pow_const α)
  have hHmono : ∀ y z, a * ‖y - z‖ ^ 2 ≤ ⟪H y - H z, y - z⟫ := by
    intro y z
    have hid : H y - H z = (F y - F z) + a • (y - z) := by
      simp only [H, smul_sub]; abel
    rw [hid, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    linarith [hFm y z]
  have hHlip : ∀ y z, ‖H y - H z‖ ≤ (L + a) * ‖y - z‖ := by
    intro y z
    exact TailObliviousAnchoring.anchored_residual_lipschitz F L hFl a ha b y z
  have hHu : H u = 0 := hu
  have hcoef : 0 ≤ 1 - η * a := by linarith
  let G : Ω → ℝ := fun ω0 => (1 - η * a) ^ (α / 2) * ‖x - u‖ ^ α +
    2 ^ (α / 2) * η ^ α * ‖g x ω0 - F x‖ ^ α + 7 * (η ^ α * σ ^ α)
  have hGi : Integrable G (p : Measure Ω) :=
    ((integrable_const _).add ((hg.moment_integrable x).const_mul _)).add (integrable_const _)
  have hfiber (ω0 : Ω) : Integrable (fun ω1 => f (ω0, ω1)) (p : Measure Ω) ∧
      (∫ ω1, f (ω0, ω1) ∂(p : Measure Ω)) ≤ G ω0 := by
    set z := y ω0 with hz
    let X : Ω → E := fun ω1 => -(η • (g z ω1 - F z))
    have hX : Measurable X := by
      dsimp only [X]
      exact ((hgm.comp (measurable_const.prodMk measurable_id)).sub measurable_const
        |>.const_smul η).neg
    have hXi : Integrable X (p : Measure Ω) :=
      (((hg.integrable z).sub (integrable_const _)).smul η).neg
    have hpow (ω1 : Ω) : ‖X ω1‖ ^ α = η ^ α * ‖g z ω1 - F z‖ ^ α := by
      simp only [X, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      exact Real.mul_rpow hη (norm_nonneg _)
    have hXα : Integrable (fun ω1 => ‖X ω1‖ ^ α) (p : Measure Ω) := by
      simp_rw [hpow]
      exact (hg.moment_integrable z).const_mul _
    have hzero : (∫ ω1, X ω1 ∂(p : Measure Ω)) = 0 := by
      dsimp only [X]
      rw [integral_neg, integral_smul, integral_sub (hg.integrable z) (integrable_const _),
        hg.unbiased z]
      simp
    let A : E := x - η • H z - u
    have hc := centered_power_moment hα1 hα2 hX hXi hXα hzero A
    have he (ω1 : Ω) : f (ω0, ω1) = ‖A + X ω1‖ ^ α := by
      dsimp only [f, A, X, H]
      rw [← hz]
      congr 2
      module
    simp_rw [he]
    refine ⟨hc.1, hc.2.trans ?_⟩
    have hmom : (∫ ω1, ‖X ω1‖ ^ α ∂(p : Measure Ω)) ≤ η ^ α * σ ^ α := by
      simp_rw [hpow]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hg.moment z) (Real.rpow_nonneg hη _)
    have hzdef : z = x - η • (H x + (g x ω0 - F x)) := by
      rw [hz]
      dsimp only [y, H]
      congr 1
      congr 1
      abel
    have hA : ‖A‖ ^ α ≤ (1 - η * a) ^ (α / 2) * ‖x - u‖ ^ α +
        2 ^ (α / 2) * η ^ α * ‖g x ω0 - F x‖ ^ α := by
      have := extragradient_power H a (L + a) η α u x (g x ω0 - F x) hHmono hHlip hHu ha
        (by linarith) hη hηa hηL hα1 hα2
      rw [← hzdef] at this
      exact this
    dsimp only [G]
    linarith
  have hfprod := OracleTemplate.StochasticConvexQuadratic.nonnegative_product_control hfm
    (fun w => Real.rpow_nonneg (norm_nonneg _) _) (fun ω0 => (hfiber ω0).1) hGi
    (fun ω0 => (hfiber ω0).2)
  have hpres := measurePreserving_finTwoArrow (p : Measure Ω)
  have hcomp : (fun ω : Fin 2 → Ω =>
      ‖(x - η • (g (x - η • (g x (ω 0) + a • x - b)) (ω 1) +
        a • (x - η • (g x (ω 0) + a • x - b)) - b)) - u‖ ^ α) =
      f ∘ MeasurableEquiv.finTwoArrow := by
    funext ω
    rfl
  rw [hcomp]
  refine ⟨hpres.integrable_comp_of_integrable hfprod.1, ?_⟩
  have hchg : (∫ ω, (f ∘ MeasurableEquiv.finTwoArrow) ω ∂Measure.pi fun _ => (p : Measure Ω)) =
      ∫ w, f w ∂(p : Measure Ω).prod (p : Measure Ω) := hpres.integral_comp' f
  rw [hchg]
  refine hfprod.2.trans ?_
  have hint : (∫ ω0, G ω0 ∂(p : Measure Ω)) ≤
      (1 - η * a) ^ (α / 2) * ‖x - u‖ ^ α + 2 * (η ^ α * σ ^ α) + 7 * (η ^ α * σ ^ α) := by
    dsimp only [G]
    have hi2 : Integrable (fun ω0 => 2 ^ (α / 2) * η ^ α * ‖g x ω0 - F x‖ ^ α)
        (p : Measure Ω) := (hg.moment_integrable x).const_mul _
    have hi1 : Integrable (fun ω0 => (1 - η * a) ^ (α / 2) * ‖x - u‖ ^ α +
        2 ^ (α / 2) * η ^ α * ‖g x ω0 - F x‖ ^ α) (p : Measure Ω) :=
      (integrable_const _).add hi2
    rw [integral_add hi1 (integrable_const _), integral_add (integrable_const _) hi2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [integral_const_mul]
    have h2 : (2 : ℝ) ^ (α / 2) ≤ 2 := by
      calc (2 : ℝ) ^ (α / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hm := hg.moment x
    have hη0 : 0 ≤ η ^ α := Real.rpow_nonneg hη _
    have hσ0 : 0 ≤ ∫ ω, ‖g x ω - F x‖ ^ α ∂(p : Measure Ω) :=
      integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    nlinarith [mul_le_mul h2 (mul_le_mul_of_nonneg_left hm hη0) (mul_nonneg hη0 hσ0)
      (by norm_num)]
  have hhalf := one_sub_rpow_half_le (mul_nonneg hη ha) (by linarith) hα1 hα2
  have hxu : 0 ≤ ‖x - u‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  nlinarith [mul_le_mul_of_nonneg_right hhalf hxu]

end LongTails.Proofs.TailObliviousNoise
