import LongTails.Proofs.BlockSgdRate
import LongTails.Proofs.AbcSgdConvergence
import LongTails.Proofs.MixedNoiseSelectors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.BlockSgdConvergence

open LongTails.Proofs.BlockSgdRate LongTails.Algorithms.BlockSgd
open LongTails.Setups.BlockHeterogeneousNonconvex
open OracleTemplate.MixedNoise

noncomputable def weight (q : Params) (j : Fin q.B) : ℝ := (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)

noncomputable def heterogeneity (q : Params) : ℝ := ∑ j, weight q j

noncomputable def smoothSum (q : Params) : ℝ := ∑ j, q.L j

noncomputable def boost (q : Params) : ℝ :=
  max (4 * heterogeneity q ^ 2 / q.ε ^ 2)
    (2 * Real.sqrt (smoothSum q * heterogeneity q) / q.ε)

noncomputable def stepSize (q : Params) (j : Fin q.B) : ℝ := 1 / (q.L j + boost q * weight q j)

noncomputable def steps (q : Params) : ℕ :=
  ⌈8 * (∑ j, q.L j) * q.Δ / q.ε ^ 2 +
    20 * (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4⌉₊

noncomputable def upperBudget (q : Params) : ℕ := steps q + 1

noncomputable def algorithm (q : Params) :
    Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d)) :=
  sampledPreconditionedSgd (precond q.blk (stepSize q)) (steps q) q.x0

section Tuning

variable (q : Params) (hv : spec.valid q)
include hv

lemma weight_nonneg (j : Fin q.B) : 0 ≤ weight q j :=
  Real.rpow_nonneg (mul_nonneg (hv.1 j).le (sq_nonneg _)) _

lemma weight_cube (j : Fin q.B) : weight q j ^ 3 = q.L j * q.σ j ^ 2 := by
  have h0 : 0 ≤ q.L j * q.σ j ^ 2 := mul_nonneg (hv.1 j).le (sq_nonneg _)
  unfold weight
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

lemma heterogeneity_nonneg : 0 ≤ heterogeneity q :=
  Finset.sum_nonneg (fun j _ => weight_nonneg q hv j)

lemma smoothSum_nonneg : 0 ≤ smoothSum q := Finset.sum_nonneg (fun j _ => (hv.1 j).le)

lemma boost_nonneg : 0 ≤ boost q :=
  le_max_of_le_left (by have := heterogeneity_nonneg q hv; positivity)

lemma denom_pos (j : Fin q.B) : 0 < q.L j + boost q * weight q j := by
  have := hv.1 j
  have := mul_nonneg (boost_nonneg q hv) (weight_nonneg q hv j)
  linarith

lemma stepSize_pos (j : Fin q.B) : 0 < stepSize q j := one_div_pos.mpr (denom_pos q hv j)

lemma stepSize_smooth (j : Fin q.B) : q.L j * stepSize q j ≤ 1 := by
  have hd := denom_pos q hv j
  unfold stepSize
  rw [mul_one_div, div_le_one hd]
  have := mul_nonneg (boost_nonneg q hv) (weight_nonneg q hv j)
  linarith

omit hv in
lemma inv_sum : ∑ j, 1 / stepSize q j = smoothSum q + boost q * heterogeneity q := by
  unfold stepSize smoothSum heterogeneity
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [one_div_one_div]

lemma noise_term_le (j : Fin q.B) (hb : 0 < boost q) :
    q.L j * stepSize q j ^ 2 * q.σ j ^ 2 ≤ weight q j / boost q ^ 2 := by
  have hw := weight_nonneg q hv j
  have hd := denom_pos q hv j
  have hc := weight_cube q hv j
  rcases hw.eq_or_lt with h0 | hpos
  · have h00 : q.L j * q.σ j ^ 2 = 0 := by rw [← hc, ← h0]; ring
    rw [← h0, zero_div, show q.L j * stepSize q j ^ 2 * q.σ j ^ 2 =
      (q.L j * q.σ j ^ 2) * stepSize q j ^ 2 by ring, h00, zero_mul]
  · unfold stepSize
    rw [div_pow, one_pow, show q.L j * (1 / (q.L j + boost q * weight q j) ^ 2) * q.σ j ^ 2 =
      (q.L j * q.σ j ^ 2) / (q.L j + boost q * weight q j) ^ 2 by ring, ← hc,
      div_le_div_iff₀ (pow_pos hd 2) (pow_pos hb 2)]
    have hle : boost q * weight q j ≤ q.L j + boost q * weight q j := by linarith [hv.1 j]
    have hsq : (boost q * weight q j) ^ 2 ≤ (q.L j + boost q * weight q j) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (boost_nonneg q hv) hw) hle 2
    nlinarith [mul_le_mul_of_nonneg_left hsq hw]

lemma noise_le : (∑ j, 1 / stepSize q j) * ∑ j, q.L j * stepSize q j ^ 2 * q.σ j ^ 2 ≤
    q.ε ^ 2 / 2 := by
  have hε := hv.2.2.2
  have hS := heterogeneity_nonneg q hv
  have hLs := smoothSum_nonneg q hv
  rw [inv_sum q]
  rcases hS.eq_or_lt with h0 | hSpos
  · have hz : ∀ j, q.L j * stepSize q j ^ 2 * q.σ j ^ 2 = 0 := by
      intro j
      have hwj : weight q j = 0 := by
        have hsum : ∑ i, weight q i = 0 := h0.symm
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => weight_nonneg q hv i)).mp hsum j
          (Finset.mem_univ _)
      have hc := weight_cube q hv j
      rw [hwj] at hc
      have : q.L j * q.σ j ^ 2 = 0 := by rw [← hc]; ring
      nlinarith [sq_nonneg (stepSize q j)]
    simp only [hz, Finset.sum_const_zero, mul_zero]
    positivity
  · have hb1 : 4 * heterogeneity q ^ 2 / q.ε ^ 2 ≤ boost q := le_max_left _ _
    have hb2 : 2 * Real.sqrt (smoothSum q * heterogeneity q) / q.ε ≤ boost q := le_max_right _ _
    have hbpos : 0 < boost q :=
      lt_of_lt_of_le (div_pos (mul_pos four_pos (pow_pos hSpos 2)) (pow_pos hε 2)) hb1
    have hb0 := hbpos.ne'
    have hN : ∑ j, q.L j * stepSize q j ^ 2 * q.σ j ^ 2 ≤ heterogeneity q / boost q ^ 2 := by
      unfold heterogeneity
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun j _ => noise_term_le q hv j hbpos)
    have hN0 : 0 ≤ ∑ j, q.L j * stepSize q j ^ 2 * q.σ j ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (hv.1 j).le (sq_nonneg _))
        (sq_nonneg _))
    have hA : 0 ≤ smoothSum q + boost q * heterogeneity q :=
      add_nonneg hLs (mul_nonneg (boost_nonneg q hv) hS)
    have hstep : (smoothSum q + boost q * heterogeneity q) *
        ∑ j, q.L j * stepSize q j ^ 2 * q.σ j ^ 2 ≤
        (smoothSum q + boost q * heterogeneity q) * (heterogeneity q / boost q ^ 2) :=
      mul_le_mul_of_nonneg_left hN hA
    have hsplit : (smoothSum q + boost q * heterogeneity q) * (heterogeneity q / boost q ^ 2) =
        smoothSum q * heterogeneity q / boost q ^ 2 + heterogeneity q ^ 2 / boost q := by
      field_simp
    have hr := Real.sq_sqrt (mul_nonneg hLs hS)
    have hb2' : 2 * Real.sqrt (smoothSum q * heterogeneity q) ≤ boost q * q.ε := by
      rwa [div_le_iff₀ hε] at hb2
    have hsqb : 4 * (smoothSum q * heterogeneity q) ≤ (boost q * q.ε) ^ 2 := by
      have h0 : 0 ≤ 2 * Real.sqrt (smoothSum q * heterogeneity q) := by positivity
      nlinarith [pow_le_pow_left₀ h0 hb2' 2]
    have ht1 : smoothSum q * heterogeneity q / boost q ^ 2 ≤ q.ε ^ 2 / 4 := by
      rw [div_le_iff₀ (pow_pos hbpos 2)]
      nlinarith
    have ht2 : heterogeneity q ^ 2 / boost q ≤ q.ε ^ 2 / 4 := by
      rw [div_le_iff₀ hbpos]
      rw [div_le_iff₀ (pow_pos hε 2)] at hb1
      nlinarith
    linarith

lemma initial_le : (∑ j, 1 / stepSize q j) * (2 * q.Δ / ((steps q : ℝ) + 1)) ≤ q.ε ^ 2 / 2 := by
  have hε := hv.2.2.2
  have hΔ := hv.2.2.1
  have hS := heterogeneity_nonneg q hv
  have hLs := smoothSum_nonneg q hv
  have hε0 : q.ε ≠ 0 := hε.ne'
  rw [inv_sum q]
  set S := heterogeneity q
  set Ls := smoothSum q
  set r := Real.sqrt (Ls * S)
  have hr2 : r ^ 2 = Ls * S := Real.sq_sqrt (mul_nonneg hLs hS)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hbS : boost q * S ≤ 4 * S ^ 3 / q.ε ^ 2 + 2 * S * r / q.ε := by
    have hmax : boost q ≤ 4 * S ^ 2 / q.ε ^ 2 + 2 * r / q.ε :=
      max_le (le_add_of_nonneg_right (div_nonneg (mul_nonneg zero_le_two hr0) hε.le))
        (le_add_of_nonneg_left (by positivity))
    have := mul_le_mul_of_nonneg_right hmax hS
    calc boost q * S ≤ (4 * S ^ 2 / q.ε ^ 2 + 2 * r / q.ε) * S := this
      _ = _ := by ring
  have hamgm : 2 * S * r / q.ε ≤ Ls + S ^ 3 / q.ε ^ 2 := by
    rcases hS.eq_or_lt with h0 | hSpos
    · have hz : 2 * S * r / q.ε = 0 := by rw [← h0]; ring
      rw [hz]
      have : 0 ≤ S ^ 3 / q.ε ^ 2 := div_nonneg (pow_nonneg hS 3) (sq_nonneg _)
      linarith
    · have hsq := sq_nonneg (S * S - r * q.ε)
      have hre : r ^ 2 * q.ε ^ 2 = Ls * S * q.ε ^ 2 := by rw [hr2]
      have hkey : 2 * S * r * q.ε ≤ Ls * q.ε ^ 2 + S ^ 3 := by
        have h4 : S * (2 * S * r * q.ε) ≤ S * (Ls * q.ε ^ 2 + S ^ 3) := by nlinarith
        exact le_of_mul_le_mul_left h4 hSpos
      rw [div_le_iff₀ hε]
      have : (Ls + S ^ 3 / q.ε ^ 2) * q.ε = (Ls * q.ε ^ 2 + S ^ 3) / q.ε := by
        field_simp
      rw [this, le_div_iff₀ hε]
      linarith
  have htot : Ls + boost q * S ≤ 2 * Ls + 5 * S ^ 3 / q.ε ^ 2 := by
    have : 4 * S ^ 3 / q.ε ^ 2 + S ^ 3 / q.ε ^ 2 = 5 * S ^ 3 / q.ε ^ 2 := by ring
    linarith
  have hK : 8 * Ls * q.Δ / q.ε ^ 2 + 20 * S ^ 3 * q.Δ / q.ε ^ 4 ≤ (steps q : ℝ) + 1 := by
    have h := Nat.le_ceil (8 * (∑ j, q.L j) * q.Δ / q.ε ^ 2 +
      20 * (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4)
    have he : (steps q : ℝ) = ((⌈8 * (∑ j, q.L j) * q.Δ / q.ε ^ 2 +
      20 * (∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3)) ^ 3 * q.Δ / q.ε ^ 4⌉₊ : ℕ) : ℝ) := rfl
    have hLs' : Ls = ∑ j, q.L j := rfl
    have hS' : S = ∑ j, (q.L j * q.σ j ^ 2) ^ ((1 : ℝ) / 3) := rfl
    rw [he, hLs', hS']
    linarith
  have hM : 0 < (steps q : ℝ) + 1 := by positivity
  rw [show (Ls + boost q * S) * (2 * q.Δ / ((steps q : ℝ) + 1)) =
    2 * q.Δ * (Ls + boost q * S) / ((steps q : ℝ) + 1) by ring, div_le_iff₀ hM]
  have hε2 : 0 < q.ε ^ 2 := by positivity
  have h1 : 2 * q.Δ * (Ls + boost q * S) ≤ 2 * q.Δ * (2 * Ls + 5 * S ^ 3 / q.ε ^ 2) :=
    mul_le_mul_of_nonneg_left htot (by linarith)
  have h2 : 2 * q.Δ * (2 * Ls + 5 * S ^ 3 / q.ε ^ 2) =
      q.ε ^ 2 / 2 * (8 * Ls * q.Δ / q.ε ^ 2 + 20 * S ^ 3 * q.Δ / q.ε ^ 4) := by
    field_simp; ring
  have h3 := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ q.ε ^ 2 / 2)
  linarith

end Tuning

theorem blockSgd_convergence : Convergence spec (fun q _ => upperBudget q) := by
  refine ⟨fun q => algorithm q, ?_, fun _ _ => trivial⟩
  intro q hv f O hadm
  obtain ⟨g, p, P, hiid, rfl, hgrad, hsmooth, hmeas, hint, hmean, hvarint, hvar, lower, hlow,
    hΔ⟩ := hadm
  have hM : BlockModel q.blk f g (p : Measure q.Ω) q.L q.σ lower :=
    ⟨hgrad, hsmooth, hlow, hmeas, hint, hmean, hvarint, hvar⟩
  set η := stepSize q with hηdef
  set K := steps q
  have hη : ∀ j, 0 < η j := stepSize_pos q hv
  have hL : ∀ j, 0 ≤ q.L j := fun j => (hv.1 j).le
  have hout : ∀ z : (algorithm q).Seed × ((k : ℕ) → q.Ω),
      execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm q) (fun _ => upperBudget q) z.1 z.2 =
          iter q.blk η g q.x0 z.2 (Fin.val z.1) := by
    intro z
    exact execute_blockSgd η g K q.x0 P z.1 z.2
  let unifM : Measure (Fin (K + 1)) := (PMF.uniformOfFintype (Fin (K + 1))).toMeasure
  let Q : Measure (Fin (K + 1) × (ℕ → q.Ω)) := unifM.prod (P : Measure (ℕ → q.Ω))
  let Y : Fin (K + 1) × (ℕ → q.Ω) → ℝ := fun z =>
    ∑ j, ‖blockProj q.blk j (gradient f (iter q.blk η g q.x0 z.2 z.1.val))‖
  have hgr := measurable_gradient f
  have hYm : Measurable Y := by
    apply measurable_from_prod_countable_right
    intro τ
    exact Finset.measurable_sum _ (fun j _ =>
      ((blockProj q.blk j).measurable.comp (hgr.comp (iter_measurable hmeas η q.x0 τ.val))).norm)
  let Gs : (ℕ → q.Ω) → ℝ := fun ξ => loss q.blk η f g (K + 1) q.x0 (fun i : Fin (K + 1) => ξ i)
  have hprefix := LongTails.Proofs.AbcSgdRate.iid_prefix_law hiid (K + 1)
  have hbound := loss_bound hM hL η (fun j => (hη j).le) (stepSize_smooth q hv) (K + 1) q.x0
  have hGm : Measurable (loss q.blk η f g (K + 1) q.x0) :=
    (measurable_loss hmeas η (K + 1)).of_uncurry_left
  have hGs : Integrable Gs (P : Measure _) :=
    (hprefix.integrable_comp hGm.aestronglyMeasurable).mpr hbound.1
  have hGsint : ∫ ξ, Gs ξ ∂(P : Measure _) =
      ∫ ξ, loss q.blk η f g (K + 1) q.x0 ξ ∂Measure.pi (fun _ : Fin (K + 1) => (p : Measure q.Ω)) := by
    rw [← hprefix.map_eq, integral_map hprefix.measurable.aemeasurable hGm.aestronglyMeasurable]
  set Cinv := ∑ j, 1 / η j with hCinv
  have hCpos : 0 ≤ Cinv := Finset.sum_nonneg (fun j _ => (one_div_pos.mpr (hη j)).le)
  let W : Fin (K + 1) × (ℕ → q.Ω) → ℝ := fun z =>
    weightedGrad q.blk η f (iter q.blk η g q.x0 z.2 z.1.val)
  have hYW : ∀ z, Y z ^ 2 ≤ Cinv * W z := by
    intro z
    exact sum_norm_sq_le η hη _
  have hWle : ∀ z, W z ≤ Gs z.2 := by
    intro z
    dsimp only [W, Gs]
    rw [loss_eq_sum]
    exact Finset.single_le_sum (f := fun t => weightedGrad q.blk η f (iter q.blk η g q.x0 z.2 t))
      (fun t _ => weightedGrad_nonneg q.blk η (fun j => (hη j).le) f _)
      (Finset.mem_range.mpr z.1.isLt)
  have hWm : Measurable W := by
    apply measurable_from_prod_countable_right
    intro τ
    exact (measurable_weightedGrad q.blk η f).comp (iter_measurable hmeas η q.x0 τ.val)
  have hsnd : MeasurePreserving Prod.snd Q (P : Measure _) := by
    refine ⟨measurable_snd, ?_⟩
    dsimp only [Q]
    rw [Measure.map_snd_prod]
    simp [unifM]
  have hGsQ : Integrable (fun z : Fin (K + 1) × (ℕ → q.Ω) => Gs z.2) Q :=
    (hsnd.integrable_comp hGs.aestronglyMeasurable).mpr hGs
  have hW0 : ∀ z, 0 ≤ W z := fun z => weightedGrad_nonneg q.blk η (fun j => (hη j).le) f _
  have hWi : Integrable W Q :=
    hGsQ.mono_nonneg hWm.aestronglyMeasurable (Filter.Eventually.of_forall hW0)
      (Filter.Eventually.of_forall hWle)
  have hY2 : Integrable (fun z => Y z ^ 2) Q :=
    (hWi.const_mul Cinv).mono_nonneg (hYm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg _)) (Filter.Eventually.of_forall hYW)
  have hsec : ∀ τ : Fin (K + 1), Integrable (fun ξ => W (τ, ξ)) (P : Measure _) := by
    intro τ
    exact hGs.mono_nonneg (((measurable_weightedGrad q.blk η f).comp
      (iter_measurable hmeas η q.x0 τ.val))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => hW0 _))
      (Filter.Eventually.of_forall (fun ξ => hWle (τ, ξ)))
  have hEW : ∫ z, W z ∂Q = ((K : ℝ) + 1)⁻¹ * ∫ ξ, Gs ξ ∂(P : Measure _) := by
    rw [integral_prod _ hWi, integral_uniform_finite, Fintype.card_fin]
    push_cast
    congr 1
    rw [← integral_finsetSum _ (fun τ _ => hsec τ)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp only [W, Gs]
    rw [loss_eq_sum, Fin.sum_univ_eq_sum_range
      (fun t => weightedGrad q.blk η f (iter q.blk η g q.x0 ξ t))]
  have hfx : f q.x0 - lower ≤ q.Δ := hΔ
  have hEbound : ∫ z, Y z ^ 2 ∂Q ≤ q.ε ^ 2 := by
    have hYle : ∫ z, Y z ^ 2 ∂Q ≤ ∫ z, Cinv * W z ∂Q :=
      integral_mono hY2 (hWi.const_mul Cinv) hYW
    rw [integral_const_mul, hEW, hGsint] at hYle
    have hb := hbound.2
    have hMpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have havg : ((K : ℝ) + 1)⁻¹ * ∫ ξ, loss q.blk η f g (K + 1) q.x0 ξ
        ∂Measure.pi (fun _ : Fin (K + 1) => (p : Measure q.Ω)) ≤
        2 * q.Δ / ((K : ℝ) + 1) + ∑ j, q.L j * η j ^ 2 * q.σ j ^ 2 := by
      have h1 : ((K : ℝ) + 1)⁻¹ * ∫ ξ, loss q.blk η f g (K + 1) q.x0 ξ
          ∂Measure.pi (fun _ : Fin (K + 1) => (p : Measure q.Ω)) ≤
          ((K : ℝ) + 1)⁻¹ * (2 * (f q.x0 - lower) +
            ((K + 1 : ℕ) : ℝ) * ∑ j, q.L j * η j ^ 2 * q.σ j ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have h2 : ((K : ℝ) + 1)⁻¹ * (2 * (f q.x0 - lower) +
          ((K + 1 : ℕ) : ℝ) * ∑ j, q.L j * η j ^ 2 * q.σ j ^ 2) =
          2 * (f q.x0 - lower) / ((K : ℝ) + 1) + ∑ j, q.L j * η j ^ 2 * q.σ j ^ 2 := by
        push_cast; field_simp
      have h3 : 2 * (f q.x0 - lower) / ((K : ℝ) + 1) ≤ 2 * q.Δ / ((K : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by linarith) hMpos.le
      linarith
    have hinit := initial_le q hv
    have hnoise := noise_le q hv
    rw [← hηdef] at hinit hnoise
    have hfin := mul_le_mul_of_nonneg_left havg hCpos
    have : Cinv * (2 * q.Δ / ((K : ℝ) + 1) + ∑ j, q.L j * η j ^ 2 * q.σ j ^ 2) =
        Cinv * (2 * q.Δ / ((K : ℝ) + 1)) + Cinv * ∑ j, q.L j * η j ^ 2 * q.σ j ^ 2 := by ring
    linarith
  obtain ⟨hYi, hJ⟩ := LongTails.Proofs.AbcSgdConvergence.integral_square_le Q hYm
    (fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hY2
  have hmeasout : Measurable (fun z : Fin (K + 1) × (ℕ → q.Ω) =>
      iter q.blk η g q.x0 z.2 z.1.val) := by
    apply measurable_from_prod_countable_right
    intro τ
    exact iter_measurable hmeas η q.x0 τ.val
  change spec.successful q f
      (fun seed : (algorithm q).Seed × ((k : ℕ) → q.Ω) =>
        execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm q) (fun _ => upperBudget q) seed.1 seed.2)
      ⟨((algorithm q).law : Measure _).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩
  simp only [hout]
  refine ⟨hmeasout, hYi, ?_⟩
  change ∫ z, Y z ∂Q ≤ q.ε
  have hI0 : 0 ≤ ∫ z, Y z ∂Q := integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ =>
    norm_nonneg _))
  have hsq : (∫ z, Y z ∂Q) ^ 2 ≤ q.ε ^ 2 := hJ.trans hEbound
  exact (pow_le_pow_iff_left₀ hI0 hv.2.2.2.le two_ne_zero).mp hsq

end LongTails.Proofs.BlockSgdConvergence
