import LongTails.Proofs.RobustPLEstimator
import LongTails.Proofs.RobustSampleBlocks
import LongTails.Proofs.RobustPLContraction

open MeasureTheory

namespace OracleTemplate.HeavyTailedPLHessian

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma estimator_split_preserving :
    MeasurePreserving (fun ξ : Fin 65 → Ω =>
      ((fun i j : Fin 8 => ξ (pilotIndex i j)), ξ (Fin.last 64)))
      (Measure.pi fun _ : Fin 65 => P)
      ((Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin 8 => P).prod P) := by
  have hh := ((RobustGradient.finite_groups_preserving P 8 8).prod
    (MeasurePreserving.id P)).comp (MultiplicativeRobustEstimator.split_last_measurePreserving 64)
  convert hh using 1
  funext ξ
  apply Prod.ext
  · funext i j
    dsimp only [Function.comp_apply, Prod.map]
    apply congrArg ξ
    apply Fin.ext
    dsimp [pilotIndex]
    omega
  · rfl

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
lemma measurable_flatEstimate (τ : ℝ) : Measurable (flatEstimate (E := E) τ) := by
  have hm : Measurable (fun v : Fin 65 → E =>
      ((fun i j : Fin 8 => v (pilotIndex i j)), v (Fin.last 64))) :=
    (Measurable.of_eval fun i => Measurable.of_eval fun j => measurable_pi_apply (pilotIndex i j)).prodMk
      (measurable_pi_apply (Fin.last 64))
  exact (measurable_estimate (E := E) τ).comp hm

omit [CompleteSpace E] in
lemma measurable_sampledReply {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    Measurable (fun w : E × (Fin 65 → Ω) => flatEstimate τ (fun i => g w.1 (w.2 i))) :=
  (measurable_flatEstimate τ).comp (Measurable.of_eval fun i =>
    hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

lemma flatEstimate_moments {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (u : E) (hmean : ∫ ω, X ω ∂P = u)
    {p σ τ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hτ : 0 < τ) (hστ : σ ≤ τ)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpm : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    let Q := Measure.pi fun _ : Fin 65 => P
    let Z := fun ξ : Fin 65 → Ω => flatEstimate τ (fun i => X (ξ i)) - u
    Integrable Z Q ∧ Integrable (fun ξ => ‖Z ξ‖ ^ 2) Q ∧ Integrable (fun ξ => ‖Z ξ‖ ^ 4) Q ∧
    ‖∫ ξ, Z ξ ∂Q‖ ≤ 2 ^ 64 * σ ^ p * τ ^ (1 - p) ∧
    (∫ ξ, ‖Z ξ‖ ^ 2 ∂Q) ≤ 2 ^ 64 * σ ^ p * τ ^ (2 - p) ∧
    (∫ ξ, ‖Z ξ‖ ^ 4 ∂Q) ≤ 2 ^ 64 * σ ^ p * τ ^ (4 - p) := by
  have h := estimate_moments hX hXi u hmean hp hp2 hσ hτ hστ hpi hpm
  have hs := estimator_split_preserving (P := P)
  have hl := hs.hasLaw
  refine ⟨hs.integrable_comp_of_integrable h.1,
    hs.integrable_comp_of_integrable h.2.1, hs.integrable_comp_of_integrable h.2.2.1, ?_, ?_, ?_⟩
  · have he := hl.integral_comp h.1.aestronglyMeasurable
    change (∫ ξ, flatEstimate τ (fun i => X (ξ i)) - u ∂Measure.pi (fun _ : Fin 65 => P)) = _ at he
    change ‖∫ ξ, flatEstimate τ (fun i => X (ξ i)) - u ∂Measure.pi (fun _ : Fin 65 => P)‖ ≤ _
    rw [he]
    exact h.2.2.2.1
  · exact (hl.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2.2.2.1
  · exact (hl.integral_comp h.2.2.1.aestronglyMeasurable).trans_le h.2.2.2.2.2

lemma flatEstimate_moments_nonneg {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (u : E) (hmean : ∫ ω, X ω ∂P = u)
    {p σ τ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hστ : σ ≤ τ)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpm : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    let Q := Measure.pi fun _ : Fin 65 => P
    let Z := fun ξ : Fin 65 → Ω => flatEstimate τ (fun i => X (ξ i)) - u
    Integrable Z Q ∧ Integrable (fun ξ => ‖Z ξ‖ ^ 2) Q ∧ Integrable (fun ξ => ‖Z ξ‖ ^ 4) Q ∧
    ‖∫ ξ, Z ξ ∂Q‖ ≤ 2 ^ 64 * σ ^ p * τ ^ (1 - p) ∧
    (∫ ξ, ‖Z ξ‖ ^ 2 ∂Q) ≤ 2 ^ 64 * σ ^ p * τ ^ (2 - p) ∧
    (∫ ξ, ‖Z ξ‖ ^ 4 ∂Q) ≤ 2 ^ 64 * σ ^ p * τ ^ (4 - p) := by
  by_cases ht : 0 < τ
  · exact flatEstimate_moments hX hXi u hmean hp hp2 hσ ht hστ hpi hpm
  have hτ0 : τ = 0 := le_antisymm (not_lt.mp ht) hτ
  have hσ0 : σ = 0 := le_antisymm (by linarith) hσ
  have hp0 : p ≠ 0 := by linarith
  have ha := MultiplicativeRobustEstimator.ae_eq_of_zero_power u hp0 hpi
    (by simpa only [hσ0, Real.zero_rpow hp0] using hpm)
  let Q := Measure.pi fun _ : Fin 65 => P
  let Z := fun ξ : Fin 65 → Ω => flatEstimate τ (fun i => X (ξ i)) - u
  have hZ : Z =ᵐ[Q] fun _ => 0 := by
    have hall := Measure.ae_eq_pi (fun _ : Fin 65 => ha)
    filter_upwards [hall] with ξ hξ
    change flatEstimate τ (fun i => X (ξ i)) - u = 0
    rw [hξ]
    simp [flatEstimate, estimate, pilot, RobustGradient.centeredClip,
      MultiplicativeRobustEstimator.medoid, clip, hτ0]
  have hZ2 : (fun ξ => ‖Z ξ‖ ^ 2) =ᵐ[Q] fun _ => 0 := by
    filter_upwards [hZ] with ξ hξ
    simp [hξ]
  have hZ4 : (fun ξ => ‖Z ξ‖ ^ 4) =ᵐ[Q] fun _ => 0 := by
    filter_upwards [hZ] with ξ hξ
    simp [hξ]
  refine ⟨(integrable_congr hZ).mpr (integrable_const 0),
    (integrable_congr hZ2).mpr (integrable_const 0),
    (integrable_congr hZ4).mpr (integrable_const 0), ?_, ?_, ?_⟩
  · change ‖∫ ξ, Z ξ ∂Q‖ ≤ _
    rw [integral_congr_ae hZ]
    simp [hσ0, Real.zero_rpow hp0]
  · change (∫ ξ, ‖Z ξ‖ ^ 2 ∂Q) ≤ _
    rw [integral_congr_ae hZ2]
    simp [hσ0, Real.zero_rpow hp0]
  · change (∫ ξ, ‖Z ξ‖ ^ 4 ∂Q) ≤ _
    rw [integral_congr_ae hZ4]
    simp [hσ0, Real.zero_rpow hp0]

lemma sampled_contraction [FiniteDimensional ℝ E]
    {f : E → ℝ} {g : E → Ω → E} {u : E} {L μ ρ η lam t p σ τ : ℝ}
    (H : PLHessian.Hyp (Measure.pi fun _ : Fin 65 => P) f
      (fun x (_ : Fin 65 → Ω) => gradient f x) u L μ ρ 0 1)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = gradient f x)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hστ : σ ≤ τ)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ p) P)
    (hpm : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ p ∂P) ≤ σ ^ p)
    (hη : 0 < η) (ht : 0 < t) (hlam : lam * μ = 32 * Real.sqrt (L / μ))
    (hlocal : 36864 * ρ ^ 2 * t ≤ μ ^ 3)
    (hstep : 8 * L * η ≤ 1) (hsmall : 32 * Real.sqrt (L / μ) * η ^ 2 * L ^ 2 ≤ 1)
    (hVsmall : 96 * lam * L * η * (2 ^ 64 * σ ^ p * τ ^ (2 - p)) ≤ t)
    (hQsmall : 4 * lam * L ^ 2 * η ^ 2 * (2 ^ 64 * σ ^ p * τ ^ (4 - p)) ≤
      t * (2 ^ 64 * σ ^ p * τ ^ (2 - p)))
    (hBsmall : (2 ^ 64 * σ ^ p * τ ^ (1 - p)) ^ 2 ≤
      μ * η * (2 ^ 64 * σ ^ p * τ ^ (2 - p))) (x : E) :
    let Q := Measure.pi fun _ : Fin 65 => P
    let G := fun ξ : Fin 65 → Ω => flatEstimate τ (fun i => g x (ξ i))
    Integrable (fun ξ => PLHessian.pot f u lam t (x - η • G ξ)) Q ∧
    (∫ ξ, PLHessian.pot f u lam t (x - η • G ξ) ∂Q) ≤
      (1 - μ * η / 64) * PLHessian.pot f u lam t x - η / 2 * (f x - f u) +
        290 * η ^ 2 * (2 ^ 64 * σ ^ p * τ ^ (2 - p)) := by
  have hx : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi, hi2, hi4, hb, hv, hq⟩ := flatEstimate_moments_nonneg hx (hgi x)
    (gradient f x) (hmean x) hp hp2 hσ hτ hστ (hpi x) (hpm x)
  have hm : Measurable (fun ξ : Fin 65 → Ω =>
      flatEstimate τ (fun i => g x (ξ i)) - gradient f x) :=
    ((measurable_flatEstimate τ).comp (Measurable.of_eval fun i =>
      hx.comp (measurable_pi_apply i))).sub_const _
  have hh := RobustPLPotential.contraction H hm hi hi2 hi4 hb hv hq hη ht hlam
    hlocal hstep hsmall hVsmall hQsmall hBsmall x
  simpa only [add_sub_cancel, div_mul_eq_mul_div] using hh

end OracleTemplate.HeavyTailedPLHessian
