import LongTails.Proofs.DuelingReferencePotential
import LongTails.Proofs.DuelingReferenceProcess

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceDrift
open LongTails.Proofs.DuelingReferenceField
open LongTails.Proofs.DuelingReferenceSampling
open LongTails.Proofs.DuelingReferencePotential

namespace LongTails.Proofs.DuelingReferenceConvergence

noncomputable def step {Ω : Type} {p : Params} (g : (Ball p.d × Ball p.d) → Ω → Bool)
    (s : State p.d) (z : Draw p.d × Ω) : State p.d :=
  update p s z.1 (g (query p s z.1) z.2)

lemma step_measurable {Ω : Type} [MeasurableSpace Ω] {p : Params}
    {g : (Ball p.d × Ball p.d) → Ω → Bool} (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (step (p := p) g)) := by
  have hq := (measurable_query p).comp
    (show Measurable (fun z : State p.d × (Draw p.d × Ω) => (z.1,z.2.1)) by fun_prop)
  have hbit := hg.comp (hq.prodMk (show Measurable (fun z : State p.d × (Draw p.d × Ω) => z.2.2) by fun_prop))
  have hG := (measurable_estimate p).comp
    ((show Measurable (fun z : State p.d × (Draw p.d × Ω) => z.2.1) by fun_prop).prodMk hbit)
  unfold Function.uncurry step update
  refine Measurable.prodMk (by fun_prop) (Measurable.prodMk (measurable_retract.comp ?_) (measurable_retract.comp ?_))
  · apply Measurable.sub (by fun_prop)
    exact (show Measurable (fun z : State p.d × (Draw p.d × Ω) =>
      4 / (slope p * p.μ * ((z.1.1:ℝ)+2))) by fun_prop).smul hG
  · fun_prop

lemma storage_bounds {p : Params} {f : Point p.d → ℝ} (hf : Objective p f) (u : Ball p.d) :
    Measurable (energy (p := p) f u) ∧ ∃ B : ℕ → ℝ,
      ∀ s : State p.d, |energy (p := p) f u s| ≤ B s.1 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf.differentiable x).continuousAt
  constructor
  · unfold energy storage
    fun_prop
  · have h (t : ℕ) : ∃ c : ℝ, ∀ v : Ball p.d × Ball p.d, |energy (p := p) f u (t,v)| ≤ c := by
      have hc : Continuous (fun v : Ball p.d × Ball p.d => |energy (p := p) f u (t,v)|) := by
        unfold energy storage; fun_prop
      obtain ⟨c,hc'⟩ := isCompact_univ.bddAbove_image hc.continuousOn
      exact ⟨c,fun v => hc' ⟨v,Set.mem_univ _,rfl⟩⟩
    choose B hB using h
    exact ⟨B,fun s => hB s.1 s.2⟩

lemma conditional_descent {Ω : Type} [MeasurableSpace Ω] {p : Params}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hp : spec.valid p)
    {f : Point p.d → ℝ} {ρ : ℝ → ℝ} (hf : Objective p f) (hr : Transfer p ρ)
    {g : (Ball p.d × Ball p.d) → Ω → Bool} (hg : Measurable (Function.uncurry g))
    (hmean : ∀ x, (∫ z, score (g x z) ∂ν) = ρ (f x.1.val - f x.2.val))
    (u : Ball p.d) (hu : IsMinOn f (Ball p.d) u.val) (s : State p.d) :
    (∫ z, energy (p := p) f u (step g s z) ∂(drawLaw p : Measure _).prod ν) ≤ energy (p := p) f u s := by
  let Q := (drawLaw p : Measure (Draw p.d)).prod ν
  let G := fun z : Draw p.d × Ω => estimate p z.1 (g (query p s z.1) z.2)
  let x := s.2.1.val
  let c := ((s.1:ℝ)+1)/slope p
  let B := target (p := p) f x u
  have hq := (measurable_query p).of_uncurry_left (x := s)
  have hbit : Measurable (fun z : Draw p.d × Ω => g (query p s z.1) z.2) :=
    hg.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable G := (measurable_estimate p).comp (measurable_fst.prodMk hbit)
  have hi : Integrable G Q := Integrable.of_bound hG.aestronglyMeasurable (p.d/radius p)
    (Filter.Eventually.of_forall fun z => (norm_estimate p hp _ _).le)
  obtain ⟨he,B',hb⟩ := storage_bounds hf u
  have hs := (step_measurable hg).of_uncurry_left (x := s)
  have hei : Integrable (fun z => energy (p := p) f u (step g s z)) Q :=
    Integrable.of_bound (he.comp hs).aestronglyMeasurable (B' (s.1+1))
      (Filter.Eventually.of_forall fun z => hb (step g s z))
  have hinner := Integrable.const_inner (𝕜 := ℝ) (x-u.val) hi
  have hfield := sphere_drift hp hf hr s.2.1.property u.property (hu s.2.1.property)
  have hB : B ≤ ⟪x-u.val, ∫ z, G z ∂Q⟫ := by
    rw [show (∫ z, G z ∂Q) = _ from estimate_mean ν hp hg hmean s]
    exact hfield
  have hc : 0 ≤ c := div_nonneg (by positivity) (tuning hp).1.le
  calc
    _ ≤ ∫ z, energy (p := p) f u s + c*(B-⟪x-u.val,G z⟫) ∂Q :=
      integral_mono hei ((integrable_const _).add (((integrable_const B).sub hinner).const_mul c))
        (fun z => projected_step hp f hf u s z.1 _)
    _ = energy (p := p) f u s + c*(B-⟪x-u.val,∫ z, G z ∂Q⟫) := by
      rw [integral_add (f := fun _ => energy (p := p) f u s) (g := fun z => c*(B-⟪x-u.val,G z⟫))
        (integrable_const _) (((integrable_const B).sub hinner).const_mul c),
        integral_const_mul, integral_sub (integrable_const _) hinner,integral_inner hi]
      simp
    _ ≤ _ := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hB)]

end LongTails.Proofs.DuelingReferenceConvergence
