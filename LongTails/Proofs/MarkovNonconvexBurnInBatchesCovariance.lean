import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import LongTails.Proofs.MarkovNonconvexBurnInBatchesMixing

open MeasureTheory ProbabilityTheory Function Preorder
open scoped RealInnerProductSpace
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient
variable {Z E : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
lemma integrable_pair {S : Type} [MeasurableSpace S] {P : Measure S} {f g : S → E}
    (hf : Measurable f) (hg : Measurable g)
    (h1 : Integrable (fun z => ‖f z‖^2) P) (h2 : Integrable (fun z => ‖g z‖^2) P) :
    Integrable (fun z => ⟪f z,g z⟫) P := by
  refine (h1.add h2).mono' (hf.inner hg).aestronglyMeasurable (.of_forall fun z => ?_)
  apply (abs_real_inner_le_norm _ _).trans
  change _ ≤ ‖f z‖^2 + ‖g z‖^2
  nlinarith [sq_nonneg (‖f z‖-‖g z‖), sq_nonneg ‖f z‖, sq_nonneg ‖g z‖]

set_option maxHeartbeats 1000000 in
lemma lag_covariance (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) (s t : ℕ) {τ : ℝ}
    (hd : ∀ z, mixingDistance κ π t z ≤ 2*Real.exp (-(t:ℝ)/τ))
    {h : Z → E} (hm : Measurable h) (hi : Integrable h (π : Measure Z))
    (hz : (∫ z, h z ∂(π : Measure Z)) = 0)
    (hq : Integrable (fun z => ‖h z‖^2) (π : Measure Z)) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    (∫ ξ, ⟪h (ξ s), h (ξ (s+t))⟫ ∂P) ≤
      3*Real.exp (-(t:ℝ)/(2*τ))*(∫ z, ‖h z‖^2 ∂(π : Measure Z)) := by
  intro P
  let m := ∫ z, ‖h z‖^2 ∂(π : Measure Z)
  let v := fun z => ∫ y, h y ∂(κ^t) z
  have mv : Measurable v := (hm.stronglyMeasurable.integral_kernel (κ := κ^t)).measurable
  have sqv := stationary_square κ π hinv t hd hm hi hz hq
  let F := fun z => ⟪h z,v z⟫
  let last := fun a : Finset.Iic s → Z => a ⟨s,Finset.mem_Iic.mpr le_rfl⟩
  let ρ := P.map (frestrictLe s)
  let K := (κ^t).comap last (measurable_pi_apply _)
  let pair := fun ξ : ℕ → Z => (frestrictLe s ξ, ξ (s+t))
  let W := fun p : (Finset.Iic s → Z) × Z => ⟪h (last p.1), h p.2⟫
  have mlast : Measurable last := measurable_pi_apply _
  have mW : Measurable W := (hm.comp (mlast.comp measurable_fst)).inner (hm.comp measurable_snd)
  have mp : Measurable pair := by dsimp [pair]; fun_prop
  have law (k : ℕ) : MeasurePreserving (fun ξ : ℕ → Z => ξ k) P (π : Measure Z) :=
    ⟨measurable_pi_apply _, pathLaw_stationary_marginal κ π hinv _⟩
  have jl : ρ ⊗ₘ K = P.map pair := pathLaw_prefix_future κ π s t
  have iW : Integrable W (ρ ⊗ₘ K) := by
    rw [jl, integrable_map_measure mW.aestronglyMeasurable mp.aemeasurable]
    change Integrable (fun ξ : ℕ → Z => ⟪h (ξ s),h (ξ (s+t))⟫) P
    exact integrable_pair (P := P) (f := fun ξ : ℕ → Z => h (ξ s))
      (g := fun ξ : ℕ → Z => h (ξ (s+t))) (hm.comp (measurable_pi_apply s)) (hm.comp (measurable_pi_apply (s+t)))
      ((law s).integrable_comp_of_integrable (g := fun z => ‖h z‖^2) hq) ((law (s+t)).integrable_comp_of_integrable (g := fun z => ‖h z‖^2) hq)
  have e := Measure.integral_compProd iW
  rw [jl, integral_map mp.aemeasurable mW.aestronglyMeasurable] at e
  have ml : ρ.map last = (π : Measure Z) := by
    rw [show ρ = P.map (frestrictLe s) by rfl, Measure.map_map mlast (by fun_prop)]
    exact (law s).map_eq
  have pres : MeasurePreserving last ρ (π : Measure Z) := ⟨mlast,ml⟩
  have ik : Integrable h ((κ^t : Kernel Z Z) ∘ₘ (π : Measure Z)) := by
    rw [invariant_power κ π hinv]; exact hi
  have af := pres.quasiMeasurePreserving.ae (Measure.ae_integrable_of_integrable_comp ik)
  have ef : (∫ ξ, ⟪h (ξ s),h (ξ (s+t))⟫ ∂P) = ∫ z, F z ∂(π : Measure Z) := by
    refine e.trans ?_
    have mapF := integral_map (μ := ρ) mlast.aemeasurable (f := F)
      (show Measurable F from hm.inner mv).aestronglyMeasurable
    rw [ml] at mapF
    rw [mapF]
    apply integral_congr_ae
    filter_upwards [af] with a ha
    simpa only [K, Kernel.comap_apply, W, F, v] using integral_inner (𝕜 := ℝ) ha (h (last a))
  rw [ef]
  have mf := (memLp_two_iff_integrable_sq hm.norm.aestronglyMeasurable).2 hq
  have mg := (memLp_two_iff_integrable_sq mv.norm.aestronglyMeasurable).2 sqv.1
  have prodI := mf.integrable_mul mg
  have hle := integral_mono (integrable_pair hm mv hq sqv.1) prodI
    (fun z => (le_abs_self _).trans (abs_real_inner_le_norm (h z) (v z)))
  have cs := OracleTemplate.Scent.AnchorHyp.integral_mul_le_sqrt hm.norm mv.norm
    (fun z => norm_nonneg (h z)) (fun z => norm_nonneg (v z)) hq sqv.1
  apply (hle.trans cs).trans
  let r := Real.exp (-(t:ℝ)/(2*τ))
  have er : r^2 = Real.exp (-(t:ℝ)/τ) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hm0 : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hu : (∫ z, ‖v z‖^2 ∂(π : Measure Z)) ≤ (3*r*Real.sqrt m)^2 := by
    apply sqv.2.trans
    rw [← er]
    change 4*(2*r^2)*m ≤ _
    nlinarith [Real.sq_sqrt hm0, mul_nonneg (sq_nonneg r) hm0,
      congrArg (fun x : ℝ => r^2*x) (Real.sq_sqrt hm0)]
  have hs := Real.sqrt_le_sqrt hu
  rw [Real.sqrt_sq (by positivity)] at hs
  apply (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)).trans
  change Real.sqrt m * (3*r*Real.sqrt m) ≤ 3*r*m
  rw [show Real.sqrt m * (3*r*Real.sqrt m) = 3*r*(Real.sqrt m)^2 by ring,
    Real.sq_sqrt hm0]

end LongTails.Proofs.MarkovNonconvexBurnInBatches
