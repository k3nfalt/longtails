import LongTails.Algorithms.SlidingStochasticComposite
import LongTails.Proofs.AcceleratedStochastic
import LongTails.Proofs.GdConvex
import LongTails.Proofs.StochasticEnvelopeGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SlidingCompositeInner

open OracleTemplate LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def model (f h : E → ℝ) (gf : E → E) (ℓ : ℝ) (c y : E) : ℝ :=
  f c + ⟪gf c, y - c⟫ + h y + ℓ / 2 * ‖y - c‖ ^ 2

noncomputable def modelGrad (gf gh : E → E) (ℓ : ℝ) (c y : E) : E :=
  gf c + gh y + ℓ • (y - c)

lemma quad_expand (ℓ : ℝ) (c x z : E) :
    ℓ / 2 * ‖x - c‖ ^ 2 =
      ℓ / 2 * ‖z - c‖ ^ 2 + ⟪ℓ • (z - c), x - z⟫ + ℓ / 2 * ‖x - z‖ ^ 2 := by
  have e : x - c = (z - c) + (x - z) := by abel
  rw [e, norm_add_sq_real, inner_smul_left]
  simp only [conj_trivial]
  ring

lemma model_lower_strong {f h : E → ℝ} {gf gh : E → E} {ℓ : ℝ}
    (hlow : ∀ x y, h x + ⟪gh x, y - x⟫ ≤ h y) (c z x : E) :
    model f h gf ℓ c z + ⟪modelGrad gf gh ℓ c z, x - z⟫ + ℓ / 2 * ‖x - z‖ ^ 2 ≤
      model f h gf ℓ c x := by
  have h1 := hlow z x
  have h2 := quad_expand ℓ c x z
  have h3 : ⟪gf c, x - c⟫ = ⟪gf c, z - c⟫ + ⟪gf c, x - z⟫ := by
    rw [← inner_add_right]; congr 1; abel
  simp only [model, modelGrad, inner_add_left]
  linarith

lemma model_upper {f h : E → ℝ} {gf gh : E → E} {ℓ L : ℝ}
    (hup : ∀ x y, h y ≤ h x + ⟪gh x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) (c z x : E) :
    model f h gf ℓ c x ≤
      model f h gf ℓ c z + ⟪modelGrad gf gh ℓ c z, x - z⟫ + (L + ℓ) / 2 * ‖x - z‖ ^ 2 := by
  have h1 := hup z x
  have h2 := quad_expand ℓ c x z
  have h3 : ⟪gf c, x - c⟫ = ⟪gf c, z - c⟫ + ⟪gf c, x - z⟫ := by
    rw [← inner_add_right]; congr 1; abel
  simp only [model, modelGrad, inner_add_left]
  nlinarith

lemma model_isModel {f h : E → ℝ} {gf gh : E → E} {ℓ L : ℝ} (hpos : 0 < L + ℓ) (hℓ : 0 ≤ ℓ)
    (hlow : ∀ x y, h x + ⟪gh x, y - x⟫ ≤ h y)
    (hup : ∀ x y, h y ≤ h x + ⟪gh x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) (c : E) :
    Model (L + ℓ) (model f h gf ℓ c) (modelGrad gf gh ℓ c) where
  pos := hpos
  lower x y := by
    have := model_lower_strong (f := f) (gf := gf) (ℓ := ℓ) hlow c x y
    have : 0 ≤ ℓ / 2 * ‖y - x‖ ^ 2 := by positivity
    linarith
  upper x y := model_upper (f := f) (gf := gf) hup c x y

lemma modelGrad_lipschitz {gf gh : E → E} {ℓ L : ℝ} (hℓ : 0 ≤ ℓ)
    (hlip : ∀ x y, ‖gh x - gh y‖ ≤ L * ‖x - y‖) (c x y : E) :
    ‖modelGrad gf gh ℓ c x - modelGrad gf gh ℓ c y‖ ≤ (L + ℓ) * ‖x - y‖ := by
  have e : modelGrad gf gh ℓ c x - modelGrad gf gh ℓ c y = (gh x - gh y) + ℓ • (x - y) := by
    simp only [modelGrad, smul_sub]; abel
  rw [e]
  calc ‖(gh x - gh y) + ℓ • (x - y)‖ ≤ ‖gh x - gh y‖ + ‖ℓ • (x - y)‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ + ℓ * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓ]; linarith [hlip x y]
    _ = (L + ℓ) * ‖x - y‖ := by ring

lemma model_self (f h : E → ℝ) (gf : E → E) (ℓ : ℝ) (c : E) :
    model f h gf ℓ c c = f c + h c := by
  simp [model]

lemma objective_le_model [CompleteSpace E] {f h : E → ℝ} {ℓ : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hflip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ ℓ * ‖x - y‖) (c y : E) :
    f y + h y ≤ model f h (gradient f) ℓ c y := by
  have := Gradient.smooth_upper_bound hf hflip c y
  simp only [model]
  linarith

lemma model_le_envelope [CompleteSpace E] {f h : E → ℝ} {ℓ : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hflip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ ℓ * ‖x - y‖) (c y : E) :
    model f h (gradient f) ℓ c y ≤ f y + h y + ℓ * ‖y - c‖ ^ 2 := by
  have hn : ∀ x, HasGradientAt (fun x => -f x) (-gradient f x) x := fun x => by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hf x).hasFDerivAt.neg
  have hnl : ∀ x y, ‖-gradient f x - -gradient f y‖ ≤ ℓ * ‖x - y‖ := by
    intro x y
    rw [show -gradient f x - -gradient f y = -(gradient f x - gradient f y) by abel, norm_neg]
    exact hflip x y
  have := Gradient.smooth_upper_bound hn hnl c y
  simp only [inner_neg_left] at this
  simp only [model]
  linarith

section FiniteDim

variable [FiniteDimensional ℝ E]

lemma exists_model_min {f h : E → ℝ} {gf gh : E → E} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hlow : ∀ x y, h x + ⟪gh x, y - x⟫ ≤ h y)
    (hh : ∀ x, HasGradientAt h (gh x) x) (c : E) :
    ∃ u, ∀ y, model f h gf ℓ c u ≤ model f h gf ℓ c y := by
  have hcont : Continuous (model f h gf ℓ c) := by
    have hhc : Continuous h := continuous_iff_continuousAt.mpr (fun x => (hh x).continuousAt)
    unfold model
    fun_prop
  apply hcont.exists_forall_le
  set a := model f h gf ℓ c c
  set b := ‖modelGrad gf gh ℓ c c‖
  have hb : ∀ x, ℓ / 4 * ‖x - c‖ ^ 2 + (a - b ^ 2 / ℓ) ≤ model f h gf ℓ c x := by
    intro x
    have h1 := model_lower_strong (f := f) (gf := gf) (ℓ := ℓ) hlow c c x
    have h3 : -(b * ‖x - c‖) ≤ ⟪modelGrad gf gh ℓ c c, x - c⟫ := by
      have := abs_real_inner_le_norm (modelGrad gf gh ℓ c c) (x - c)
      have := neg_abs_le ⟪modelGrad gf gh ℓ c c, x - c⟫
      linarith
    have h4 : b * ‖x - c‖ ≤ ℓ / 4 * ‖x - c‖ ^ 2 + b ^ 2 / ℓ := by
      have h5 : 0 ≤ (ℓ / 2 * ‖x - c‖ - b) ^ 2 / ℓ := by positivity
      have h6 : (ℓ / 2 * ‖x - c‖ - b) ^ 2 / ℓ = ℓ / 4 * ‖x - c‖ ^ 2 - b * ‖x - c‖ + b ^ 2 / ℓ := by
        field_simp
        ring
      linarith
    linarith
  have hn : Tendsto (fun x : E => ‖x - c‖) (cocompact E) atTop := by
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖c‖)
      (tendsto_norm_cocompact_atTop (E := E)))
    have := norm_sub_norm_le x c
    linarith
  have hlim : Tendsto (fun x : E => ℓ / 4 * ‖x - c‖ ^ 2 + (a - b ^ 2 / ℓ)) (cocompact E) atTop :=
    tendsto_atTop_add_const_right _ _
      (((tendsto_pow_atTop two_ne_zero).comp hn).const_mul_atTop (by positivity))
  exact tendsto_atTop_mono hb hlim

end FiniteDim

lemma min_distance [CompleteSpace E] {f h : E → ℝ} {gf gh : E → E} {ℓ L : ℝ}
    (hpos : 0 < L + ℓ) (hℓ : 0 ≤ ℓ)
    (hlow : ∀ x y, h x + ⟪gh x, y - x⟫ ≤ h y)
    (hup : ∀ x y, h y ≤ h x + ⟪gh x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) (c u : E)
    (hu : ∀ y, model f h gf ℓ c u ≤ model f h gf ℓ c y) :
    ℓ / 2 * ‖c - u‖ ^ 2 ≤ model f h gf ℓ c c - model f h gf ℓ c u := by
  have hg := LongTails.Proofs.StochasticEnvelopeGeometry.model_hasGradientAt
    (model_isModel (f := f) (gf := gf) hpos hℓ hlow hup c) u
  have hmin : IsLocalMin (model f h gf ℓ c) u := Eventually.of_forall hu
  have hz := hmin.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.mp hg)
  have hz' : modelGrad gf gh ℓ c u = 0 := by
    have : (InnerProductSpace.toDual ℝ E) (modelGrad gf gh ℓ c u) =
        (InnerProductSpace.toDual ℝ E) 0 := by
      rw [map_zero]
      exact hz
    exact (InnerProductSpace.toDual ℝ E).injective this
  have := model_lower_strong (f := f) (gf := gf) (ℓ := ℓ) hlow c u c
  rw [hz', inner_zero_left, add_zero] at this
  linarith


noncomputable def gapAt (f h : E → ℝ) (ℓ : ℝ) (c : E) : ℝ :=
  f c + h c - ⨅ y, (f y + h y + ℓ * ‖y - c‖ ^ 2)

lemma gapAt_le [CompleteSpace E] {f h : E → ℝ} {ℓ : ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hflip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ ℓ * ‖x - y‖) (c u : E)
    (hu : ∀ y, model f h (gradient f) ℓ c u ≤ model f h (gradient f) ℓ c y) :
    gapAt f h ℓ c ≤ model f h (gradient f) ℓ c c - model f h (gradient f) ℓ c u := by
  have hi : model f h (gradient f) ℓ c u ≤ ⨅ y, (f y + h y + ℓ * ‖y - c‖ ^ 2) :=
    le_ciInf (fun y => (hu y).trans (model_le_envelope hf hflip c y))
  rw [model_self]
  unfold gapAt
  linarith

omit [InnerProductSpace ℝ E] in
lemma gapAt_nonneg {f h : E → ℝ} {ℓ : ℝ} {lower : ℝ} (hℓ : 0 ≤ ℓ)
    (hlow : ∀ x, lower ≤ f x + h x) (c : E) :
    0 ≤ gapAt f h ℓ c := by
  have hb : BddBelow (Set.range fun y => f y + h y + ℓ * ‖y - c‖ ^ 2) := by
    refine ⟨lower, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := hlow y
    have : 0 ≤ ℓ * ‖y - c‖ ^ 2 := by positivity
    linarith
  have := ciInf_le hb c
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero] at this
  unfold gapAt
  linarith

section Expected

open LongTails.Setups.StochasticSmoothAndConvex StochasticGradient

variable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

omit [FiniteDimensional ℝ E] in
lemma model_stochastic {f h : E → ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    {ℓ L σ : ℝ} (hpos : 0 < L + ℓ) (hℓ : 0 ≤ ℓ)
    (hlow : ∀ x y, h x + ⟪gradient h x, y - x⟫ ≤ h y)
    (hup : ∀ x y, h y ≤ h x + ⟪gradient h x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (ho : IsStochasticGradient E Ω p h g σ) (c : E) :
    IsStochasticGradient E Ω p (model f h (gradient f) ℓ c)
      (fun y ω => gradient f c + g y ω + ℓ • (y - c)) σ := by
  have hgrad : ∀ y, gradient (model f h (gradient f) ℓ c) y =
      modelGrad (gradient f) (gradient h) ℓ c y := fun y =>
    (LongTails.Proofs.StochasticEnvelopeGeometry.model_hasGradientAt
      (model_isModel (f := f) (gf := gradient f) hpos hℓ hlow hup c) y).gradient
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := ho.measurable
    exact (measurable_const.add hm).add ((measurable_fst.sub_const c).const_smul ℓ)
  · intro y
    exact ((integrable_const _).add (ho.integrable y)).add (integrable_const _)
  · intro y
    have hi1 : Integrable (fun ω => gradient f c + g y ω) p :=
      (integrable_const _).add (ho.integrable y)
    have e1 : (∫ ω, gradient f c + g y ω + ℓ • (y - c) ∂p) =
        (∫ ω, gradient f c + g y ω ∂p) + ℓ • (y - c) := by
      rw [integral_add hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    have e2 : (∫ ω, gradient f c + g y ω ∂p) = gradient f c + ∫ ω, g y ω ∂p := by
      rw [integral_add (integrable_const _) (ho.integrable y), integral_const, probReal_univ,
        one_smul]
    rw [hgrad, e1, e2, ho.unbiased y]
    rfl
  · intro y
    have e : (fun ω => ‖gradient f c + g y ω + ℓ • (y - c) -
        gradient (model f h (gradient f) ℓ c) y‖ ^ 2) =
        fun ω => ‖g y ω - gradient h y‖ ^ 2 := by
      funext ω; rw [hgrad]; simp only [modelGrad]; congr 2; abel
    rw [e]; exact ho.variance_integrable y
  · intro y
    have e : (fun ω => ‖gradient f c + g y ω + ℓ • (y - c) -
        gradient (model f h (gradient f) ℓ c) y‖ ^ 2) =
        fun ω => ‖g y ω - gradient h y‖ ^ 2 := by
      funext ω; rw [hgrad]; simp only [modelGrad]; congr 2; abel
    rw [e]; exact ho.variance y

lemma inner_expected {f h : E → ℝ} {g : E → Ω → E} {p : Measure Ω} [IsProbabilityMeasure p]
    {ℓ L σ lower : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hflip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ ℓ * ‖x - y‖)
    (hc : ConvexOn ℝ univ h) (hh : ∀ x, HasGradientAt h (gradient h x) x)
    (hhlip : ∀ x y, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖)
    (hbelow : ∀ x, lower ≤ f x + h x)
    (ho : IsStochasticGradient E Ω p h g σ) (N : ℕ) (hN : 0 < N)
    (hNL : 16 * (L + ℓ) ≤ ℓ * (N : ℝ) ^ 2) (c : E) :
    let D := ℓ * N * (N + 1) / 8
    let out := fun η : Fin N → Ω =>
      SlidingStochasticComposite.innerRun ℓ D N g c (gradient f c) η
    Integrable (fun η => f (out η) + h (out η)) (Measure.pi fun _ : Fin N => p) ∧
    (∫ η, f (out η) + h (out η) ∂Measure.pi fun _ : Fin N => p) ≤
      f c + h c - gapAt f h ℓ c / 2 + 8 * σ ^ 2 / (ℓ * (N + 1)) := by
  intro D out
  have hlow : ∀ x y, h x + ⟪gradient h x, y - x⟫ ≤ h y := fun x y => by
    have := Gradient.convex_support hc hh x y; linarith
  have hup : ∀ x y, h y ≤ h x + ⟪gradient h x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 :=
    Gradient.smooth_upper_bound hh hhlip
  have hpos : 0 < L + ℓ := by linarith
  have hM := model_isModel (f := f) (gf := gradient f) hpos hℓ.le hlow hup c
  obtain ⟨u, hu⟩ := exists_model_min (f := f) (gf := gradient f) hℓ hlow hh c
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hD : 0 < D := by dsimp [D]; positivity
  have hLD : 2 * (L + ℓ) ≤ D := by
    dsimp [D]
    nlinarith
  have hgm : ∀ x, HasGradientAt (model f h (gradient f) ℓ c)
      (gradient (model f h (gradient f) ℓ c) x) x := fun x => by
    have := LongTails.Proofs.StochasticEnvelopeGeometry.model_hasGradientAt hM x
    rwa [this.gradient]
  have hgrad : ∀ y, gradient (model f h (gradient f) ℓ c) y =
      modelGrad (gradient f) (gradient h) ℓ c y := fun y =>
    (LongTails.Proofs.StochasticEnvelopeGeometry.model_hasGradientAt hM y).gradient
  have hlipm : ∀ x y, ‖gradient (model f h (gradient f) ℓ c) x -
      gradient (model f h (gradient f) ℓ c) y‖ ≤ (L + ℓ) * ‖x - y‖ := fun x y => by
    rw [hgrad, hgrad]; exact modelGrad_lipschitz hℓ.le hhlip c x y
  have hconv := LongTails.Proofs.StochasticEnvelopeGeometry.model_convex hM
  have hos := model_stochastic (f := f) hpos hℓ.le hlow hup ho c
  have ha := accelerated_expected_rate hD hLD hconv hgm hlipm hos c u
    (fun y _ => hu y) N hN
  have hdist := min_distance (f := f) (gf := gradient f) hpos hℓ.le hlow hup c u hu
  have hgap := gapAt_le (h := h) hf hflip c u hu
  have hout : ∀ η, f (out η) + h (out η) ≤ model f h (gradient f) ℓ c (out η) :=
    fun η => objective_le_model hf hflip c (out η)
  have hmeas : Measurable out := by
    have := (measurable_acceleratedRun hos.measurable D N 0).comp
      (measurable_const.prodMk measurable_id :
        Measurable (fun η : Fin N → Ω => ((c, c), η)))
    exact this.fst
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hhc : Continuous h := continuous_iff_continuousAt.mpr (fun x => (hh x).continuousAt)
  have hFm : Measurable (fun η => f (out η) + h (out η)) :=
    (hfc.measurable.comp hmeas).add (hhc.measurable.comp hmeas)
  have hint : Integrable (fun η => f (out η) + h (out η)) (Measure.pi fun _ : Fin N => p) := by
    have hI : Integrable (fun η => model f h (gradient f) ℓ c (out η) -
        model f h (gradient f) ℓ c u) (Measure.pi fun _ : Fin N => p) := ha.1
    have hI2 : Integrable (fun η => model f h (gradient f) ℓ c (out η))
        (Measure.pi fun _ : Fin N => p) := by
      refine (hI.add (integrable_const (model f h (gradient f) ℓ c u))).congr ?_
      exact Eventually.of_forall (fun η => by simp)
    refine Integrable.mono' (hI2.norm.add (integrable_const |lower|)) hFm.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun η => ?_)
    have h1 := hout η
    have h2 := hbelow (out η)
    have h3 := le_abs_self (model f h (gradient f) ℓ c (out η))
    have h4 := neg_abs_le lower
    have h5 := abs_nonneg (model f h (gradient f) ℓ c (out η))
    show ‖f (out η) + h (out η)‖ ≤ ‖model f h (gradient f) ℓ c (out η)‖ + |lower|
    have h6 := abs_nonneg lower
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine ⟨hint, ?_⟩
  set I1 := ∫ η, (model f h (gradient f) ℓ c (out η) - model f h (gradient f) ℓ c u)
    ∂Measure.pi fun _ : Fin N => p with hI1
  have hbound : I1 ≤ ℓ / 4 * ‖c - u‖ ^ 2 + 8 * σ ^ 2 / (ℓ * (N + 1)) := by
    have hb := ha.2
    have hsimp : 2 * D * ‖c - u‖ ^ 2 / ((N : ℝ) * ((N : ℝ) + 1)) + N * σ ^ 2 / D =
        ℓ / 4 * ‖c - u‖ ^ 2 + 8 * σ ^ 2 / (ℓ * (N + 1)) := by
      dsimp [D]
      field_simp
      ring
    rw [hsimp] at hb
    exact hb
  have hI : Integrable (fun η => model f h (gradient f) ℓ c (out η) -
      model f h (gradient f) ℓ c u) (Measure.pi fun _ : Fin N => p) := ha.1
  have hle : (∫ η, f (out η) + h (out η) ∂Measure.pi fun _ : Fin N => p) ≤
      I1 + model f h (gradient f) ℓ c u := by
    have hI2' : Integrable (fun η => (model f h (gradient f) ℓ c (out η) -
        model f h (gradient f) ℓ c u) + model f h (gradient f) ℓ c u)
        (Measure.pi fun _ : Fin N => p) := hI.add (integrable_const _)
    have h1 := integral_mono hint hI2'
      (fun η => by simp only [sub_add_cancel]; exact hout η)
    rw [integral_add hI (integrable_const _), integral_const, probReal_univ, one_smul] at h1
    exact h1
  have hmc := model_self f h (gradient f) ℓ c
  have key : I1 + model f h (gradient f) ℓ c u ≤
      f c + h c - gapAt f h ℓ c / 2 + 8 * σ ^ 2 / (ℓ * (N + 1)) := by
    have : ℓ / 4 * ‖c - u‖ ^ 2 ≤ (model f h (gradient f) ℓ c c - model f h (gradient f) ℓ c u) / 2 := by
      linarith
    linarith
  exact hle.trans key

end Expected

end LongTails.Proofs.SlidingCompositeInner
