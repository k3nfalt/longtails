import LongTails.Proofs.AbcSgdUpper
import Mathlib.Analysis.Convex.Integral

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.AbcSgdConvergence

open LongTails.Proofs.AbcSgdRate LongTails.Proofs.AbcSgdUpper LongTails.Algorithms.AbcSgd
open LongTails.Setups.AbcNoiseNonconvex
open OracleTemplate.MixedNoise

noncomputable def steps (q : Params) : ℕ :=
  ⌈144 * q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2⌉₊

noncomputable def upperBudget (q : Params) : ℕ := steps q + 1

noncomputable def scaleMax (q : Params) : ℝ :=
  max (q.L * (1 + q.B)) (max (Real.sqrt (q.L * q.A * (steps q + 1))) (6 * q.L * q.C / q.ε ^ 2))

noncomputable def stepSize (q : Params) : ℝ := 1 / scaleMax q

noncomputable def algorithm (q : Params) : Algorithm q.E q.E q.E :=
  sampledSgd (stepSize q) (steps q) q.x0

section Tuning

variable (q : Params) (hv : spec.valid q)
include hv

lemma scaleMax_pos : 0 < scaleMax q := by
  obtain ⟨hL, _, hB, _, _, _⟩ := hv
  exact lt_max_of_lt_left (by positivity)

lemma stepSize_pos : 0 < stepSize q := one_div_pos.mpr (scaleMax_pos q hv)

lemma step_smooth : q.L * stepSize q * (1 + q.B) ≤ 1 := by
  have hD := scaleMax_pos q hv
  unfold stepSize
  rw [show q.L * (1 / scaleMax q) * (1 + q.B) = q.L * (1 + q.B) / scaleMax q by ring,
    div_le_one hD]
  exact le_max_left _ _

lemma step_growth : ((steps q + 1 : ℕ) : ℝ) * (q.L * q.A * stepSize q ^ 2) ≤ 1 := by
  have hD := scaleMax_pos q hv
  obtain ⟨hL, hA, _, _, _, _⟩ := hv
  have hs : Real.sqrt (q.L * q.A * (steps q + 1)) ≤ scaleMax q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hsq : q.L * q.A * ((steps q : ℝ) + 1) ≤ scaleMax q ^ 2 := by
    have h0 : 0 ≤ q.L * q.A * ((steps q : ℝ) + 1) := by positivity
    rw [← Real.sq_sqrt h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  unfold stepSize
  rw [div_pow, one_pow]
  push_cast
  rw [show ((steps q : ℝ) + 1) * (q.L * q.A * (1 / scaleMax q ^ 2)) =
      q.L * q.A * ((steps q : ℝ) + 1) / scaleMax q ^ 2 by ring, div_le_one (by positivity)]
  exact hsq

lemma step_noise : 3 * (q.L * stepSize q * q.C) ≤ q.ε ^ 2 / 2 := by
  have hD := scaleMax_pos q hv
  obtain ⟨hL, _, _, hC, _, hε⟩ := hv
  have h3 : 6 * q.L * q.C / q.ε ^ 2 ≤ scaleMax q := (le_max_right _ _).trans (le_max_right _ _)
  unfold stepSize
  rw [div_le_iff₀ (by positivity)] at h3
  rw [show 3 * (q.L * (1 / scaleMax q) * q.C) = 3 * q.L * q.C / scaleMax q by ring,
    div_le_iff₀ hD]
  nlinarith

lemma step_initial : 6 * q.Δ / (stepSize q * ((steps q + 1 : ℕ) : ℝ)) ≤ q.ε ^ 2 / 2 := by
  have hD := scaleMax_pos q hv
  obtain ⟨hL, hA, hB, hC, hΔ, hε⟩ := hv
  set M : ℝ := ((steps q + 1 : ℕ) : ℝ)
  have hMpos : 0 < M := by positivity
  set X := 144 * q.L * q.Δ * (1 + q.B + q.A * q.Δ / q.ε ^ 2 + q.C / q.ε ^ 2) / q.ε ^ 2
  have hX : X ≤ M := by
    have h := Nat.le_ceil X
    have hs : ((steps q : ℕ) : ℝ) = ((⌈X⌉₊ : ℕ) : ℝ) := rfl
    dsimp only [M]; push_cast
    linarith
  have hε2 : 0 < q.ε ^ 2 := by positivity
  have hXe : X * q.ε ^ 2 = 144 * q.L * q.Δ * (1 + q.B) + 144 * q.L * q.A * q.Δ ^ 2 / q.ε ^ 2 +
      144 * q.L * q.Δ * q.C / q.ε ^ 2 := by
    dsimp only [X]; field_simp; try ring
  have hMe : X * q.ε ^ 2 ≤ M * q.ε ^ 2 := mul_le_mul_of_nonneg_right hX hε2.le
  have hBΔ : 0 ≤ 144 * q.L * q.Δ * (1 + q.B) := by positivity
  have hAΔ : 0 ≤ 144 * q.L * q.A * q.Δ ^ 2 / q.ε ^ 2 := by positivity
  have hCΔ : 0 ≤ 144 * q.L * q.Δ * q.C / q.ε ^ 2 := by positivity
  have h1 : 12 * q.Δ * (q.L * (1 + q.B)) ≤ M * q.ε ^ 2 := by nlinarith
  have h3 : 12 * q.Δ * (6 * q.L * q.C / q.ε ^ 2) ≤ M * q.ε ^ 2 := by
    have : 12 * q.Δ * (6 * q.L * q.C / q.ε ^ 2) = 72 * q.L * q.Δ * q.C / q.ε ^ 2 := by ring
    rw [this]
    have : 72 * q.L * q.Δ * q.C / q.ε ^ 2 ≤ 144 * q.L * q.Δ * q.C / q.ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ hε2.le; nlinarith [mul_nonneg (mul_nonneg hL.le hΔ) hC]
    linarith
  have h2 : 12 * q.Δ * Real.sqrt (q.L * q.A * (steps q + 1)) ≤ M * q.ε ^ 2 := by
    have hAM : 144 * q.L * q.A * q.Δ ^ 2 / q.ε ^ 2 ≤ M * q.ε ^ 2 := by linarith
    have hq : (12 * q.Δ * Real.sqrt (q.L * q.A * (steps q + 1))) ^ 2 ≤ (M * q.ε ^ 2) ^ 2 := by
      have h0 : 0 ≤ q.L * q.A * ((steps q : ℝ) + 1) := by positivity
      rw [mul_pow, Real.sq_sqrt h0]
      have hMsteps : ((steps q : ℝ) + 1) = M := by dsimp only [M]; push_cast; ring
      rw [hMsteps]
      have hk : 144 * q.L * q.A * q.Δ ^ 2 ≤ M * q.ε ^ 4 := by
        have := (div_le_iff₀ hε2).mp (by linarith : 144 * q.L * q.A * q.Δ ^ 2 / q.ε ^ 2 ≤ M * q.ε ^ 2)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hk hMpos.le]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hq
  have hmax : 12 * q.Δ * scaleMax q ≤ M * q.ε ^ 2 := by
    unfold scaleMax
    rcases le_total (q.L * (1 + q.B))
        (max (Real.sqrt (q.L * q.A * (steps q + 1))) (6 * q.L * q.C / q.ε ^ 2)) with h | h
    · rw [max_eq_right h]
      rcases le_total (Real.sqrt (q.L * q.A * (steps q + 1))) (6 * q.L * q.C / q.ε ^ 2) with h' | h'
      · rw [max_eq_right h']; exact h3
      · rw [max_eq_left h']; exact h2
    · rw [max_eq_left h]; exact h1
  unfold stepSize
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

end Tuning

lemma integral_square_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω → ℝ}
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω)
    (hF2 : Integrable (fun ω => (F ω) ^ 2) P) :
    Integrable F P ∧ (∫ ω, F ω ∂P) ^ 2 ≤ ∫ ω, (F ω) ^ 2 ∂P := by
  have hi : Integrable F P := by
    apply ((integrable_const (1 : ℝ)).add hF2).mono' hF.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hF0 ω)]
      change F ω ≤ 1 + (F ω) ^ 2
      nlinarith [sq_nonneg (F ω - 1)]
  refine ⟨hi, ?_⟩
  have hc : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun x : ℝ => x ^ 2 := convexOn_pow 2
  exact ConvexOn.map_integral_le hc (continuous_pow 2).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hF0) hi hF2

theorem sgd_convergence : Convergence spec (fun q _ => upperBudget q) := by
  refine ⟨fun q => algorithm q, ?_, fun _ _ => trivial⟩
  intro q hv f O hadm
  obtain ⟨g, p, P, fstar, hiid, rfl, hgrad, hlip, hlow, _, hΔ, hmeas, hint, hmean, hvarint,
    hvar⟩ := hadm
  have hM : AbcModel f g (p : Measure q.Ω) q.L q.A q.B q.C fstar :=
    ⟨hgrad, hlip, hlow, hmeas, hint, hmean, hvarint, hvar⟩
  obtain ⟨hL, hA, hB, hC, hΔ0, hε⟩ := hv
  have hv' : spec.valid q := ⟨hL, hA, hB, hC, hΔ0, hε⟩
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
  have hbound := gradLoss_bound hM hL hA hC hη (step_smooth q hv') (K + 1) q.x0
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
  have hρ := rho_pow_le (q.L * q.A * η ^ 2) (by positivity) (K + 1) (step_growth q hv')
  have hfx : f q.x0 - fstar ≤ q.Δ := hΔ
  have hfx0 : 0 ≤ f q.x0 - fstar := sub_nonneg.mpr (hlow _)
  have hEbound : ∫ z, Y z ^ 2 ∂Q ≤ q.ε ^ 2 := by
    rw [hEY2, hGsint]
    have hb := hbound.2
    have hMpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hpow0 : 0 ≤ (1 + q.L * q.A * η ^ 2) ^ (K + 1) := by positivity
    have h1 : 2 / η * (1 + q.L * q.A * η ^ 2) ^ (K + 1) * (f q.x0 - fstar) ≤ 2 / η * 3 * q.Δ := by
      have := mul_le_mul hρ hfx hfx0 (by norm_num)
      have h2η : 0 ≤ 2 / η := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h2η]
    have h2 : q.L * η * q.C * ((K + 1 : ℕ) : ℝ) * (1 + q.L * q.A * η ^ 2) ^ (K + 1) ≤
        q.L * η * q.C * ((K : ℝ) + 1) * 3 := by
      push_cast
      have h0 : 0 ≤ q.L * η * q.C * ((K : ℝ) + 1) := by positivity
      exact mul_le_mul_of_nonneg_left hρ h0
    have hsum := hb.trans (add_le_add h1 h2)
    have hinit := step_initial q hv'
    have hnoise := step_noise q hv'
    rw [← hηdef] at hinit hnoise
    push_cast at hinit
    have hsplit : ((K : ℝ) + 1)⁻¹ * (2 / η * 3 * q.Δ + q.L * η * q.C * ((K : ℝ) + 1) * 3) =
        6 * q.Δ / (η * ((K : ℝ) + 1)) + 3 * (q.L * η * q.C) := by
      field_simp
      try ring
    calc _ ≤ ((K : ℝ) + 1)⁻¹ * (2 / η * 3 * q.Δ + q.L * η * q.C * ((K : ℝ) + 1) * 3) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := hsplit
      _ ≤ q.ε ^ 2 / 2 + q.ε ^ 2 / 2 := add_le_add hinit hnoise
      _ = q.ε ^ 2 := by ring
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
  have hsq : (∫ z, Y z ∂Q) ^ 2 ≤ q.ε ^ 2 := hJ.trans hEbound
  exact (pow_le_pow_iff_left₀ hI0 hε.le two_ne_zero).mp hsq

end LongTails.Proofs.AbcSgdConvergence
