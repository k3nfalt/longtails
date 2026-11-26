import LongTails.Proofs.RecursiveMomentumGapBatchTuning
import LongTails.Proofs.RecursiveMomentumGapBatchSum
import LongTails.Proofs.MixedNoiseSelectors

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.RecursiveMomentumGapBatch

open RecursiveMomentum NormalizedStorm LongTails.Setups.AffineVarianceMeanSquaredSmooth

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma output_moments (H : AffineHyp p F g L Lbar Γ Λ lower) {Δ ε : ℝ}
    (h : MTune L Lbar Γ Λ Δ ε) (x : E) (hx : F x - lower ≤ Δ) :
    let b := batch L Lbar Γ Λ Δ ε
    let T := horizon L Lbar Γ Λ Δ ε
    let γ := mGamma L Lbar Γ Λ ε
    let a := 1 / mInvA Γ Λ ε
    let Y := fun ω : Fin (T+1) × (ℕ → Ω) => ‖gradient F (momentumPair g γ a b x ω.2 ω.1.val).1‖
    let μ := (PMF.uniformOfFintype (Fin (T+1))).toMeasure.prod P
    Integrable Y μ ∧ (∫ ω, Y ω ^ 2 ∂μ) ≤ 57/60 * ε^2 ∧ (∫ ω, Y ω ∂μ) ≤ ε := by
  intro b T γ a Y μ
  have hi := h.ia_ge
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a ≤ 1 := (div_le_one (by linarith : 0 < mInvA Γ Λ ε)).2 hi
  have hav : a * Λ^2 ≤ ε^2/32 := by
    dsimp [a]; rw [one_div_mul_eq_div, div_le_iff₀ (by linarith)]
    linarith [h.a_Λ]
  have hs := mean_square_sum H h.gamma_pos h.gamma_L ha ha' h.a_Γ hav h.gamma_c b T x
    (initial_error H h x hx) (by linarith [horizon_gap h])
  have hm : Measurable Y :=
    (H.grad_continuous.measurable.comp (measurable_momentumOut H.meas γ a b T x)).norm
  have hsq : Integrable (fun ω => Y ω ^ 2) μ :=
    (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall (fun τ => (H.integrable_all h.gamma_pos.le h.gamma_L
        ha.le ha' b x τ.val).2.2.1), Integrable.of_finite⟩
  have hmem := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsq
  have hbound : (∫ ω, Y ω ^ 2 ∂μ) ≤ 57/60 * ε^2 := by
    rw [integral_prod _ hsq, MixedNoise.integral_uniform_finite, Fintype.card_fin]
    change ((T+1:ℕ):ℝ)⁻¹ * (∑ τ : Fin (T+1), ∫ ξ, ‖gradient F (momentumPair g γ a b x ξ τ.val).1‖ ^ 2 ∂P) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, ‖gradient F (momentumPair g γ a b x ξ j).1‖ ^ 2 ∂P),
      inv_mul_eq_div, div_le_iff₀ (by positivity)]
    push_cast
    linarith
  refine ⟨hmem.integrable (by norm_num), hbound, ?_⟩
  have hj := variance_nonneg Y μ
  rw [variance_eq_sub hmem] at hj
  change 0 ≤ (∫ ω, Y ω ^ 2 ∂μ) - (∫ ω, Y ω ∂μ)^2 at hj
  nlinarith [h.ε_pos, sq_nonneg ε]

lemma convergence : Convergence LongTails.Setups.AffineVarianceMeanSquaredSmooth.spec
    (fun q _ => batch q.L q.Lbar q.Γ q.Λ q.Δ q.ε + horizon q.L q.Lbar q.Γ q.Λ q.Δ q.ε) := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hL,hLb,hΓ,hΛ,hΔ,hε⟩ := hq
  obtain ⟨g,p,Q,hiid,rfl,hg,hl,hgap,hm,hi,he,hvi,hv,hdi,hd⟩ := hadm
  have H : AffineHyp (p : Measure q.Ω) f g q.L q.Lbar q.Γ q.Λ (f q.x0 - q.Δ) :=
    ⟨hg,hl,fun x => by linarith [hgap x],hm,hi,he,hvi,hv,hdi,hd,hL⟩
  have h : MTune q.L q.Lbar q.Γ q.Λ q.Δ q.ε := ⟨hL,hLb,hΓ,hΛ,hΔ,hε⟩
  let b := batch q.L q.Lbar q.Γ q.Λ q.Δ q.ε
  let T := horizon q.L q.Lbar q.Γ q.Λ q.Δ q.ε
  let γ := mGamma q.L q.Lbar q.Γ q.Λ q.ε
  let a := 1 / mInvA q.Γ q.Λ q.ε
  let out := fun ω : Fin (T+1) × (ℕ → q.Ω) => (momentumPair g γ a b q.x0 ω.2 ω.1.val).1
  let run := fun ω : Fin (T+1) × (ℕ → q.Ω) =>
    execute (pairOracle g Q) (algorithm q) (fun _ => b+T) ω.1 ω.2
  let μ := (PMF.uniformOfFintype (Fin (T+1))).toMeasure.prod (Q : Measure (ℕ → q.Ω))
  have exec_eq : run = out := by
    funext ω
    exact execute_recursiveMomentum g Q γ a b T q.x0 (b+T) ω.1 ω.2 le_rfl
  change Measurable run ∧ Integrable (fun ω => ‖gradient f (run ω)‖) μ ∧
    (∫ ω, ‖gradient f (run ω)‖ ∂μ) ≤ q.ε
  rw [exec_eq]
  refine ⟨measurable_momentumOut hm γ a b T q.x0, ?_⟩
  change Integrable _ ((PMF.uniformOfFintype (Fin (T+1))).toMeasure.prod (Q : Measure (ℕ → q.Ω))) ∧
    (∫ ω, ‖gradient f (out ω)‖ ∂((PMF.uniformOfFintype (Fin (T+1))).toMeasure.prod (Q : Measure (ℕ → q.Ω)))) ≤ _
  have law : (Q : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) :=
    (Measure.map_id' (μ := (Q : Measure (ℕ → q.Ω)))).symm.trans hiid.stream_law.map_eq
  rw [law]
  have hY := output_moments H h q.x0 (by linarith)
  exact ⟨hY.1,hY.2.2⟩

end OracleTemplate.RecursiveMomentumGapBatch
