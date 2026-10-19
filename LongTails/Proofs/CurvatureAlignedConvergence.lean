import LongTails.Proofs.CurvatureAlignedRun
import LongTails.Setups.CurvatureAlignedNoiseNonconvex

open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.CurvatureAligned

open OracleTemplate.PLHessian OracleTemplate.WindowSgd

section Window

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E} {Q : E → E →L[ℝ] E}
  {lower Lg Lξ σ : ℝ}

local notation "Pω" => Measure.infinitePi fun _ : ℕ => p

lemma Hyp.run_int (H : Hyp p f g Q lower Lg Lξ σ) (hg : Measurable (Function.uncurry g))
    {η : ℝ} (hη : 0 ≤ η) (hηL : η * Lg ≤ 1) (x0 : E) :
    ∀ n, Integrable (fun ξ => f (sgdSeq g η x0 ξ n) - lower) Pω
  | 0 => by simp only [sgdSeq]; exact integrable_const _
  | n + 1 => (H.run_step hg hη hηL x0 n (H.run_int hg hη hηL x0 n)).1

lemma Hyp.window_sum (H : Hyp p f g Q lower Lg Lξ σ) (hg : Measurable (Function.uncurry g))
    {η : ℝ} (hη : 0 ≤ η) (hηL : η * Lg ≤ 1) (x0 : E) :
    ∀ m, (∑ i ∈ Finset.range m, η / 2 * ∫ ξ, ‖gradient f (sgdSeq g η x0 ξ i)‖ ^ 2 ∂Pω) +
        ∫ ξ, (f (sgdSeq g η x0 ξ m) - lower) ∂Pω ≤
      (f x0 - lower) + m * (η ^ 2 * Lξ * σ ^ 2 / 2)
  | 0 => by simp [sgdSeq]
  | m + 1 => by
      have ih := H.window_sum hg hη hηL x0 m
      obtain ⟨-, -, hs⟩ := H.run_step hg hη hηL x0 m (H.run_int hg hη hηL x0 m)
      rw [Finset.sum_range_succ]
      push_cast
      linarith

lemma Hyp.grad_int (H : Hyp p f g Q lower Lg Lξ σ) (hg : Measurable (Function.uncurry g))
    {η : ℝ} (hη : 0 ≤ η) (hηL : η * Lg ≤ 1) (x0 : E) (n : ℕ) :
    Integrable (fun ξ => ‖gradient f (sgdSeq g η x0 ξ n)‖ ^ 2) Pω :=
  (H.run_step hg hη hηL x0 n (H.run_int hg hη hηL x0 n)).2.1

lemma measurable_gradient' (f : E → ℝ) : Measurable (gradient f) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem Hyp.window_grad_sq (H : Hyp p f g Q lower Lg Lξ σ) (hg : Measurable (Function.uncurry g))
    {η : ℝ} (hη : 0 < η) (hηL : η * Lg ≤ 1) (x0 : E) (Tb : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖gradient f (sgdSeq g η x0 ω.2 (0 + ω.1.val))‖ ^ 2)
      ∂((PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure.prod Pω) ≤
      ENNReal.ofReal (2 * (f x0 - lower) / (η * ((Tb : ℝ) + 1)) + η * Lξ * σ ^ 2) := by
  have hm : Measurable (fun ω : Fin (Tb + 1) × (ℕ → Ω) =>
      ENNReal.ofReal (‖gradient f (sgdSeq g η x0 ω.2 (0 + ω.1.val))‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_gradient' f).comp (measurable_window_out hg η 0 Tb x0)).norm.pow_const 2)
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (Tb + 1), (Fintype.card ({τ} : Set (Fin (Tb + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  have hj : ∀ τ : Fin (Tb + 1),
      ∫⁻ ξ, ENNReal.ofReal (‖gradient f (sgdSeq g η x0 ξ (0 + τ.val))‖ ^ 2) ∂Pω =
      ENNReal.ofReal (∫ ξ, ‖gradient f (sgdSeq g η x0 ξ (0 + τ.val))‖ ^ 2 ∂Pω) := by
    intro τ
    rw [ofReal_integral_eq_lintegral_ofReal (H.grad_int hg hη.le hηL x0 _)
      (Filter.Eventually.of_forall fun _ => by positivity)]
  simp_rw [hj]
  have hnn : ∀ i, 0 ≤ ∫ ξ, ‖gradient f (sgdSeq g η x0 ξ i)‖ ^ 2 ∂Pω :=
    fun i => integral_nonneg fun _ => by positivity
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun τ _ => hnn _)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, ‖gradient f (sgdSeq g η x0 ξ (0 + k))‖ ^ 2 ∂Pω)]
  set sum := ∑ k ∈ Finset.range (Tb + 1), ∫ ξ, ‖gradient f (sgdSeq g η x0 ξ (0 + k))‖ ^ 2 ∂Pω
  have hT : (0 : ℝ) < (Tb : ℝ) + 1 := by positivity
  have hinv : (((Tb + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((Tb : ℝ) + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  have hsum0 : 0 ≤ sum := Finset.sum_nonneg fun k _ => hnn _
  rw [hinv, ← ENNReal.ofReal_mul hsum0]
  apply ENNReal.ofReal_le_ofReal
  have hw := H.window_sum hg hη.le hηL x0 (Tb + 1)
  have hf0 : 0 ≤ ∫ ξ, (f (sgdSeq g η x0 ξ (Tb + 1)) - lower) ∂Pω :=
    integral_nonneg fun _ => sub_nonneg.mpr (H.lower_le _)
  rw [← Finset.mul_sum] at hw
  simp only at hw ⊢
  push_cast at hw
  have hsum : η / 2 * sum ≤ (f x0 - lower) + ((Tb : ℝ) + 1) * (η ^ 2 * Lξ * σ ^ 2 / 2) := by
    simp only [sum, zero_add]; linarith
  rw [div_add' _ _ _ (by positivity : η * ((Tb : ℝ) + 1) ≠ 0), le_div_iff₀ (by positivity)]
  rw [mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hT]
  nlinarith

end Window

lemma tuning {Lg Lξ σ Δ Δ' ε : ℝ} (hL : 0 < Lg) (hξ : 0 ≤ Lξ) (hε : 0 < ε) (hΔ' : 0 ≤ Δ')
    (hΔ : Δ' ≤ Δ) :
    let η := ε ^ 2 / (Lg * ε ^ 2 + 2 * Lξ * σ ^ 2)
    let T : ℝ := (⌈4 * Lg * Δ / ε ^ 2 + 8 * Lξ * σ ^ 2 * Δ / ε ^ 4⌉₊ : ℕ) + 1
    0 < η ∧ η * Lg ≤ 1 ∧ 2 * Δ' / (η * T) + η * Lξ * σ ^ 2 ≤ ε ^ 2 := by
  intro η T
  have hε2 : 0 < ε ^ 2 := by positivity
  have hden : 0 < Lg * ε ^ 2 + 2 * Lξ * σ ^ 2 := by positivity
  have hη : 0 < η := div_pos hε2 hden
  have hX : 4 * Lg * Δ / ε ^ 2 + 8 * Lξ * σ ^ 2 * Δ / ε ^ 4 ≤ T := by
    have := Nat.le_ceil (4 * Lg * Δ / ε ^ 2 + 8 * Lξ * σ ^ 2 * Δ / ε ^ 4)
    simp only [T]; linarith
  have hT : 0 < T := by simp only [T]; positivity
  refine ⟨hη, ?_, ?_⟩
  · simp only [η]
    rw [div_mul_eq_mul_div, div_le_one hden]
    nlinarith [sq_nonneg σ]
  · have h1 : η * Lξ * σ ^ 2 ≤ ε ^ 2 / 2 := by
      simp only [η]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [mul_pos hε2 (mul_pos hε2 hL)]
    have hηX : η * (4 * Lg * Δ / ε ^ 2 + 8 * Lξ * σ ^ 2 * Δ / ε ^ 4) = 4 * Δ / ε ^ 2 := by
      simp only [η]
      field_simp
      ring
    have hΔ0 : 0 ≤ Δ := hΔ'.trans hΔ
    have h2 : 4 * Δ / ε ^ 2 ≤ η * T := by
      rw [← hηX]; exact mul_le_mul_of_nonneg_left hX hη.le
    have h3 : 2 * Δ' / (η * T) ≤ ε ^ 2 / 2 := by
      rw [div_le_iff₀ (mul_pos hη hT)]
      have : 4 * Δ' ≤ ε ^ 2 * (η * T) := by
        have := mul_le_mul_of_nonneg_left h2 hε2.le
        rw [mul_div_cancel₀ _ hε2.ne'] at this
        linarith
      linarith
    linarith

open LongTails.Setups.CurvatureAlignedNoiseNonconvex in
theorem convergence : Convergence LongTails.Setups.CurvatureAlignedNoiseNonconvex.spec
    (fun q _ => ⌈4 * q.Lg * q.Δ / q.ε ^ 2 + 8 * q.Lξ * q.σ ^ 2 * q.Δ / q.ε ^ 4⌉₊ + 1) := by
  refine ⟨fun q => method (q.ε ^ 2 / (q.Lg * q.ε ^ 2 + 2 * q.Lξ * q.σ ^ 2)) 0
    ⌈4 * q.Lg * q.Δ / q.ε ^ 2 + 8 * q.Lξ * q.σ ^ 2 * q.Δ / q.ε ^ 4⌉₊ q.x0, ?_,
    fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hξ, hσ, hΔ, hε⟩ := hq
  obtain ⟨g, P0, P, Q, hIID, rfl, hgrad, hupper, halign, ⟨lower, hlow, hgap⟩, hgm, hint,
    hmean, hvi, hvar, hqi, hqvar⟩ := hadm
  have H : Hyp (P0 : Measure q.Ω) f g Q lower q.Lg q.Lξ q.σ :=
    ⟨hgrad, hupper, halign, hlow, hint, hmean, hvi, hvar, hqi, hqvar, hL, hξ⟩
  set η := q.ε ^ 2 / (q.Lg * q.ε ^ 2 + 2 * q.Lξ * q.σ ^ 2) with hηdef
  set Tb := ⌈4 * q.Lg * q.Δ / q.ε ^ 2 + 8 * q.Lξ * q.σ ^ 2 * q.Δ / q.ε ^ 4⌉₊ with hTbdef
  set B := Tb + 1
  have hΔ' : 0 ≤ f q.x0 - lower := sub_nonneg.mpr (hlow _)
  obtain ⟨hη, hηL, hacc⟩ := tuning (σ := q.σ) hL hξ hε hΔ' hgap
  have hB : 0 + Tb ≤ B := by omega
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (P0 : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hexec : ∀ (τ : Fin (Tb + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
        Oracle q.E q.E) (method η 0 Tb q.x0) (fun _ => B) τ ξ =
      sgdSeq g η q.x0 ξ (0 + τ.val) :=
    fun τ ξ => execute_window g P η 0 Tb q.x0 B τ ξ hB
  have hout : (fun seed : (method η 0 Tb q.x0).Seed × ((k : ℕ) → q.Ω) =>
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
        Oracle q.E q.E) (method η 0 Tb q.x0) (fun _ => B) seed.1 seed.2) =
      fun ω => sgdSeq g η q.x0 ω.2 (0 + ω.1.val) := by
    funext seed; exact hexec seed.1 seed.2
  have hfun : (fun seed : (method η 0 Tb q.x0).Seed × ((k : ℕ) → q.Ω) =>
      ‖gradient f (execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
          Oracle q.E q.E) (method η 0 Tb q.x0) (fun _ => B) seed.1 seed.2)‖) =
      fun ω => ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ := by
    funext seed; rw [hexec seed.1 seed.2]
  have hmo : Measurable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) => sgdSeq g η q.x0 ω.2 (0 + ω.1.val)) :=
    measurable_window_out hgm η 0 Tb q.x0
  refine ⟨by rw [hout]; exact hmo, ?_⟩
  rw [hfun]
  change Integrable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖)
      ((PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (Tb + 1) × (ℕ → q.Ω), ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖
      ∂((PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  set μ := (PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure.prod
    (Measure.infinitePi fun _ : ℕ => (P0 : Measure q.Ω))
  have hgr := measurable_gradient' f
  have hnm : Measurable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖) := (hgr.comp hmo).norm
  have hsqm : Measurable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ^ 2) := hnm.pow_const 2
  have hL2 := H.window_grad_sq hgm hη hηL q.x0 Tb
  have hTb : ((Tb : ℝ) + 1) = ((Tb : ℕ) : ℝ) + 1 := rfl
  have hacc' : 2 * (f q.x0 - lower) / (η * ((Tb : ℝ) + 1)) + η * q.Lξ * q.σ ^ 2 ≤ q.ε ^ 2 := by
    simpa [hTbdef] using hacc
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL2
  have isq : Integrable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ^ 2) μ := by
    have := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hsqm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ _)] using this
  have hsq : ∫ ω, ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ^ 2 ∂μ ≤ q.ε ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity)
      hsqm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (hL2.trans (ENNReal.ofReal_le_ofReal hacc'))
  have hpt : ∀ ω : Fin (Tb + 1) × (ℕ → q.Ω),
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ≤
        ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ^ 2 / (2 * q.ε) + q.ε / 2 := by
    intro ω
    set a := ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - q.ε)]
  have ibd : Integrable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ^ 2 / (2 * q.ε) + q.ε / 2) μ :=
    (isq.div_const _).add (integrable_const _)
  have inorm : Integrable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
      ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖) μ :=
    Integrable.mono' ibd hnm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hpt ω)
  refine ⟨inorm, ?_⟩
  have hmono := integral_mono inorm ibd hpt
  rw [integral_add (isq.div_const _) (integrable_const _), integral_div, integral_const] at hmono
  simp only [probReal_univ, one_smul] at hmono
  have : (∫ ω, ‖gradient f (sgdSeq g η q.x0 ω.2 (0 + ω.1.val))‖ ^ 2 ∂μ) / (2 * q.ε) ≤
      q.ε ^ 2 / (2 * q.ε) := div_le_div_of_nonneg_right hsq (by positivity)
  have e : q.ε ^ 2 / (2 * q.ε) = q.ε / 2 := by field_simp
  linarith

end OracleTemplate.CurvatureAligned
