import LongTails.Proofs.BiasedSgdRate
import LongTails.Proofs.AbcSgdConvergence
import LongTails.Setups.BiasedNoiseNonconvex

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.BiasedSgdConvergence

open LongTails.Proofs.AbcSgdRate LongTails.Proofs.AbcSgdUpper LongTails.Algorithms.AbcSgd
open LongTails.Proofs.BiasedSgdRate LongTails.Proofs.AbcSgdConvergence
open LongTails.Setups.BiasedNoiseNonconvex
open OracleTemplate.MixedNoise

noncomputable def steps (q : Params) : ℕ :=
  ⌈16 * q.L * q.Δ * (1 + q.M + q.σ ^ 2 / ((1 - q.m) * q.ε ^ 2)) / ((1 - q.m) * q.ε ^ 2)⌉₊

noncomputable def upperBudget (q : Params) : ℕ := steps q + 1

noncomputable def scaleMax (q : Params) : ℝ :=
  max (q.L * (1 + q.M)) (4 * q.L * q.σ ^ 2 / ((1 - q.m) * q.ε ^ 2))

noncomputable def stepSize (q : Params) : ℝ := 1 / scaleMax q

noncomputable def algorithm (q : Params) : Algorithm q.E q.E q.E :=
  sampledSgd (stepSize q) (steps q) q.x0

section Tuning

variable (q : Params) (hv : spec.valid q)
include hv

lemma scaleMax_pos : 0 < scaleMax q := by
  obtain ⟨hL, _, _, hM, _⟩ := hv
  exact lt_max_of_lt_left (by positivity)

lemma stepSize_pos : 0 < stepSize q := one_div_pos.mpr (scaleMax_pos q hv)

lemma step_smooth : q.L * stepSize q * (1 + q.M) ≤ 1 := by
  have hD := scaleMax_pos q hv
  unfold stepSize
  rw [show q.L * (1 / scaleMax q) * (1 + q.M) = q.L * (1 + q.M) / scaleMax q by ring,
    div_le_one hD]
  exact le_max_left _ _

lemma step_noise : q.L * stepSize q * q.σ ^ 2 / (1 - q.m) ≤ q.ε ^ 2 / 4 := by
  have hD := scaleMax_pos q hv
  obtain ⟨hL, hm0, hm1, _, _, _, _, hε, _⟩ := hv
  have h1m : 0 < 1 - q.m := by linarith
  have hr : 0 < (1 - q.m) * q.ε ^ 2 := by positivity
  have h3 : 4 * q.L * q.σ ^ 2 / ((1 - q.m) * q.ε ^ 2) ≤ scaleMax q := le_max_right _ _
  rw [div_le_iff₀ hr] at h3
  unfold stepSize
  rw [show q.L * (1 / scaleMax q) * q.σ ^ 2 / (1 - q.m) =
      q.L * q.σ ^ 2 / (scaleMax q * (1 - q.m)) by field_simp,
    div_le_iff₀ (by positivity)]
  nlinarith

lemma step_initial :
    2 * q.Δ / (stepSize q * (1 - q.m) * ((steps q + 1 : ℕ) : ℝ)) ≤ q.ε ^ 2 / 2 := by
  have hD := scaleMax_pos q hv
  obtain ⟨hL, hm0, hm1, hM, hσ, _, hΔ, hε, _⟩ := hv
  have h1m : 0 < 1 - q.m := by linarith
  set r := (1 - q.m) * q.ε ^ 2 with hrdef
  have hr : 0 < r := by positivity
  set N : ℝ := ((steps q + 1 : ℕ) : ℝ)
  have hNpos : 0 < N := by positivity
  set X := 16 * q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) / r
  have hX : X ≤ N := by
    have h := Nat.le_ceil X
    have hs : ((steps q : ℕ) : ℝ) = ((⌈X⌉₊ : ℕ) : ℝ) := rfl
    dsimp only [N]; push_cast
    linarith
  have hmax : 4 * q.Δ * scaleMax q ≤ N * r := by
    have hXr : X * r = 16 * q.L * q.Δ * (1 + q.M) + 16 * q.L * q.Δ * q.σ ^ 2 / r := by
      dsimp only [X]
      rw [div_mul_cancel₀ _ hr.ne']
      ring
    have hXN : X * r ≤ N * r := mul_le_mul_of_nonneg_right hX hr.le
    have hA : 0 ≤ 16 * q.L * q.Δ * (1 + q.M) := by positivity
    have hB : 0 ≤ 16 * q.L * q.Δ * q.σ ^ 2 / r := by positivity
    unfold scaleMax
    rcases le_total (q.L * (1 + q.M)) (4 * q.L * q.σ ^ 2 / r) with h | h
    · rw [max_eq_right h]
      have : 4 * q.Δ * (4 * q.L * q.σ ^ 2 / r) = 16 * q.L * q.Δ * q.σ ^ 2 / r := by ring
      rw [this]; linarith
    · rw [max_eq_left h]
      nlinarith
  have hstep : stepSize q * (1 - q.m) * N = (1 - q.m) * N / scaleMax q := by
    unfold stepSize; ring
  rw [hstep, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  have hrN : q.ε ^ 2 / 2 * ((1 - q.m) * N) = N * r / 2 := by
    simp only [hrdef]; ring
  rw [hrN]
  linarith

end Tuning

theorem biased_sgd_convergence : Convergence spec (fun q _ => upperBudget q) := by
  refine ⟨fun q => algorithm q, ?_, fun _ _ => trivial⟩
  intro q hv f O hadm
  obtain ⟨g, p, P, fstar, hiid, rfl, hgrad, hlip, hlow, _, hΔ, hmeas, hint, hbias, hvarint,
    hvar⟩ := hadm
  have hBM : BiasedModel f g (p : Measure q.Ω) q.L q.m q.M q.σ q.ζ fstar :=
    ⟨hgrad, hlip, hlow, hmeas, hint, hbias, hvarint, hvar⟩
  have hv' : spec.valid q := hv
  obtain ⟨hL, hm0, hm1, -, hσ, hζ, hΔ0, hε, hfloor⟩ := hv
  have h1m : 0 < 1 - q.m := by linarith
  set η := stepSize q with hηdef
  set K := steps q
  have hη : 0 < η := stepSize_pos q hv'
  have hout : ∀ z : (algorithm q).Seed × ((k : ℕ) → q.Ω),
      execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm q) (fun _ => upperBudget q) z.1 z.2 =
          sgdIter g η q.x0 z.2 (Fin.val z.1) := by
    intro z
    exact execute_sampledSgd g η K q.x0 P z.1 z.2
  let unifM : Measure (Fin (K + 1)) := (PMF.uniformOfFintype (Fin (K + 1))).toMeasure
  let Q : Measure (Fin (K + 1) × (ℕ → q.Ω)) := unifM.prod (P : Measure (ℕ → q.Ω))
  let Y : Fin (K + 1) × (ℕ → q.Ω) → ℝ := fun z => ‖gradient f (sgdIter g η q.x0 z.2 z.1.val)‖
  have hgr := (gradient_continuous hlip).measurable
  have hYm : Measurable Y := by
    apply measurable_from_prod_countable_right
    intro τ
    exact (hgr.comp (sgdIter_measurable hmeas η q.x0 τ.val)).norm
  let Gs : (ℕ → q.Ω) → ℝ := fun ξ => gradLoss f g η (K + 1) q.x0 (fun i : Fin (K + 1) => ξ i)
  have hprefix := iid_prefix_law hiid (K + 1)
  have hbound := gradLoss_bound_biased hBM hL hm1 hη (step_smooth q hv') (K + 1) q.x0
  have hGm : Measurable (gradLoss f g η (K + 1) q.x0) :=
    (measurable_gradLoss hlip hmeas η (K + 1)).of_uncurry_left
  have hGs : Integrable Gs (P : Measure _) :=
    (hprefix.integrable_comp hGm.aestronglyMeasurable).mpr hbound.1
  have hGsint : ∫ ξ, Gs ξ ∂(P : Measure _) =
      ∫ ξ, gradLoss f g η (K + 1) q.x0 ξ ∂Measure.pi (fun _ : Fin (K + 1) => (p : Measure q.Ω)) := by
    rw [← hprefix.map_eq, integral_map hprefix.measurable.aemeasurable hGm.aestronglyMeasurable]
  have hYle : ∀ z, Y z ^ 2 ≤ Gs z.2 := by
    intro z
    dsimp only [Y, Gs]
    rw [gradLoss_eq_sum]
    exact Finset.single_le_sum (f := fun t => ‖gradient f (sgdIter g η q.x0 z.2 t)‖ ^ 2)
      (fun t _ => sq_nonneg _) (Finset.mem_range.mpr z.1.isLt)
  have hsnd : MeasurePreserving Prod.snd Q (P : Measure _) := by
    refine ⟨measurable_snd, ?_⟩
    dsimp only [Q]
    rw [Measure.map_snd_prod]
    simp [unifM]
  have hGsQ : Integrable (fun z : Fin (K + 1) × (ℕ → q.Ω) => Gs z.2) Q :=
    (hsnd.integrable_comp hGs.aestronglyMeasurable).mpr hGs
  have hY2 : Integrable (fun z => Y z ^ 2) Q :=
    hGsQ.mono_nonneg (hYm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg _)) (Filter.Eventually.of_forall hYle)
  have hsec : ∀ τ : Fin (K + 1), Integrable (fun ξ => Y (τ, ξ) ^ 2) (P : Measure _) := by
    intro τ
    exact hGs.mono_nonneg ((hgr.comp (sgdIter_measurable hmeas η q.x0 τ.val)).norm.pow_const
      2).aestronglyMeasurable (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall (fun ξ => hYle (τ, ξ)))
  have hEY2 : ∫ z, Y z ^ 2 ∂Q = ((K : ℝ) + 1)⁻¹ * ∫ ξ, Gs ξ ∂(P : Measure _) := by
    rw [integral_prod _ hY2, integral_uniform_finite, Fintype.card_fin]
    push_cast
    congr 1
    rw [← integral_finsetSum _ (fun τ _ => hsec τ)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp only [Y, Gs]
    rw [gradLoss_eq_sum, Fin.sum_univ_eq_sum_range (fun t => ‖gradient f (sgdIter g η q.x0 ξ t)‖ ^ 2)]
  have hfx : f q.x0 - fstar ≤ q.Δ := hΔ
  have hEbound : ∫ z, Y z ^ 2 ∂Q ≤ (13 / 16) * q.ε ^ 2 := by
    rw [hEY2, hGsint]
    have hb := hbound.2
    have hMpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hk : 0 ≤ 2 / (η * (1 - q.m)) := by positivity
    have h1 : 2 / (η * (1 - q.m)) * (f q.x0 - fstar) ≤ 2 / (η * (1 - q.m)) * q.Δ :=
      mul_le_mul_of_nonneg_left hfx hk
    have hinit := step_initial q hv'
    have hnoise := step_noise q hv'
    rw [← hηdef] at hinit hnoise
    push_cast at hinit hb
    have hζ' : q.ζ ^ 2 / (1 - q.m) ≤ q.ε ^ 2 / 16 := by
      rw [div_le_iff₀ h1m]; nlinarith
    have hsplit : ((K : ℝ) + 1)⁻¹ * (2 / (η * (1 - q.m)) * q.Δ +
        ((K : ℝ) + 1) * ((q.ζ ^ 2 + q.L * η * q.σ ^ 2) / (1 - q.m))) =
        2 * q.Δ / (η * (1 - q.m) * ((K : ℝ) + 1)) + q.ζ ^ 2 / (1 - q.m) +
          q.L * η * q.σ ^ 2 / (1 - q.m) := by
      field_simp
      ring
    calc _ ≤ ((K : ℝ) + 1)⁻¹ * (2 / (η * (1 - q.m)) * q.Δ +
          ((K : ℝ) + 1) * ((q.ζ ^ 2 + q.L * η * q.σ ^ 2) / (1 - q.m))) :=
          mul_le_mul_of_nonneg_left (hb.trans (by linarith)) (by positivity)
      _ = _ := hsplit
      _ ≤ q.ε ^ 2 / 2 + q.ε ^ 2 / 16 + q.ε ^ 2 / 4 := by gcongr
      _ = (13 / 16) * q.ε ^ 2 := by ring
  obtain ⟨hYi, hJ⟩ := integral_square_le Q hYm (fun _ => norm_nonneg _) hY2
  have hmeasout : Measurable (fun z : Fin (K + 1) × (ℕ → q.Ω) => sgdIter g η q.x0 z.2 z.1.val) := by
    apply measurable_from_prod_countable_right
    intro τ
    exact sgdIter_measurable hmeas η q.x0 τ.val
  change spec.successful q f
      (fun seed : (algorithm q).Seed × ((k : ℕ) → q.Ω) =>
        execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm q) (fun _ => upperBudget q) seed.1 seed.2)
      ⟨((algorithm q).law : Measure _).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩
  simp only [hout]
  refine ⟨hmeasout, hYi, ?_⟩
  change ∫ z, Y z ∂Q ≤ q.ε
  have hI0 : 0 ≤ ∫ z, Y z ∂Q := integral_nonneg (fun _ => norm_nonneg _)
  have hsq : (∫ z, Y z ∂Q) ^ 2 ≤ q.ε ^ 2 := by nlinarith [hJ.trans hEbound, sq_nonneg q.ε]
  exact (pow_le_pow_iff_left₀ hI0 hε.le two_ne_zero).mp hsq

end LongTails.Proofs.BiasedSgdConvergence
