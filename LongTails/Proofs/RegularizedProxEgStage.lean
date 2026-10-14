import LongTails.Proofs.CohypoEgStep
import LongTails.Proofs.RegularizedProxEgEval
import LongTails.Proofs.RegularizedProxEgSampling

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

structure StepOK (L ρ γ α Λ M : ℝ) : Prop where
  γ_pos : 0 < γ
  α_pos : 0 < α
  Λ_nonneg : 0 ≤ Λ
  ρΛ : 2 * ρ * Λ < 1
  γL : γ * (L + Λ) < 1
  M_nonneg : 0 ≤ M
  coef : (1 + α) * (2 * (ρ / (1 - 2 * ρ * Λ)) + α * γ) ≤ γ - M / 2
  contr : 2 * Λ * (γ / (1 - γ * (L + Λ))) ^ 2 ≤ M / 2
  q_le : α * γ * Λ ≤ 1

noncomputable def stepK (L ρ γ α Λ : ℝ) : ℝ :=
  α * γ ^ 2 / (1 - (γ * (L + Λ)) ^ 2) + α * γ * (2 * (ρ / (1 - 2 * ρ * Λ)) + α * γ) * (1 + 1 / α)

lemma stepK_nonneg {L ρ γ α Λ M : ℝ} (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (h : StepOK L ρ γ α Λ M) :
    0 ≤ stepK L ρ γ α Λ := by
  have h1 : 0 < 1 - (γ * (L + Λ)) ^ 2 := by
    have h0 : 0 ≤ γ * (L + Λ) := mul_nonneg h.γ_pos.le (by linarith [h.Λ_nonneg])
    nlinarith [h.γL]
  have h2 : 0 ≤ ρ / (1 - 2 * ρ * Λ) := div_nonneg hρ (by linarith [h.ρΛ])
  have := h.α_pos; have := h.γ_pos
  unfold stepK; positivity

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma egOut_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {J : ℝ → E → E}
    {γ : ℝ} (hJ : Continuous (J γ)) (α Λ : ℝ) (b : ℕ) :
    Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) =>
      egOut g J γ α Λ b q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hc : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) => q.1) := measurable_fst
  have hx : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) => q.2.1) :=
    measurable_fst.comp measurable_snd
  have hu : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) => q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have ht : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) => q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hS1 : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) => ∑ i, g q.2.1 (q.2.2.1 i)) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hg.comp (hx.prodMk ((measurable_pi_apply i).comp hu))
  have hy : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) =>
      q.2.1 - γ • ((1 / (b : ℝ)) • ∑ i, g q.2.1 (q.2.2.1 i) + Λ • (q.2.1 - q.1))) :=
    hx.sub (((hS1.const_smul _).add ((hx.sub hc).const_smul _)).const_smul _)
  have hxb := hJ.measurable.comp hy
  have hS2 : Measurable (fun q : E × E × (Fin b → Ω) × (ℕ → Ω) => ∑ i : Fin b,
      g (J γ (q.2.1 - γ • ((1 / (b : ℝ)) • ∑ i, g q.2.1 (q.2.2.1 i) + Λ • (q.2.1 - q.1))))
        (q.2.2.2 (1 + i))) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hg.comp (hxb.prodMk ((measurable_pi_apply (1 + (i : ℕ))).comp ht))
  unfold egOut
  exact hx.sub ((((((hx.sub hxb).const_smul _).sub ((hS1.const_smul _).add
    ((hx.sub hc).const_smul _))).add ((hS2.const_smul _).add
      ((hxb.sub hc).const_smul _)))).const_smul _)

variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ σ : ℝ} {g : E → Ω → E}
  {p : Measure Ω} [IsProbabilityMeasure p]

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma OpHyp.res_continuous (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) : Continuous (J γ) :=
  (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact H.res_nonexp hγ a b).continuous

lemma OpHyp.eg_expect (H : OpHyp F G J L ρ)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ)
    {γ α Λ M : ℝ} (hs : StepOK L ρ γ α Λ M) {b : ℕ} (hb : 0 < b) (c x z : E)
    (hz : -(F z + Λ • (z - c)) ∈ G z) :
    ∫⁻ ξ, ENNReal.ofReal (‖egOut g J γ α Λ b c x (fun i => ξ i) (fun i => ξ (b + i)) - z‖ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - α * γ * Λ) * ‖x - z‖ ^ 2 +
        (stepK L ρ γ α Λ + (α * γ) ^ 2) * (σ ^ 2 / b)) := by
  have hJ := H.res_continuous hs.γ_pos
  have hgm := hg.measurable
  have hmeas := egOut_measurable hgm hJ α Λ b (Ω := Ω)
  set P := Measure.infinitePi fun _ : ℕ => p
  set e1 : (Fin b → Ω) → E := fun u => (1 / (b : ℝ)) • ∑ i, g x (u i) - F x with he1
  set xb : (Fin b → Ω) → E := fun u => J γ (x - γ • (F x + Λ • (x - c) + e1 u)) with hxb
  set w : (Fin b → Ω) → E := fun u =>
    γ⁻¹ • (x - xb u) - (F x + Λ • (x - c)) - e1 u + (F (xb u) + Λ • (xb u - c)) with hw
  have hin : ∀ u, (1 / (b : ℝ)) • ∑ i, g x (u i) + Λ • (x - c) = F x + Λ • (x - c) + e1 u := by
    intro u; simp only [he1]; abel
  have hdecomp : ∀ u t, egOut g J γ α Λ b c x u t - z =
      (x - (α * γ) • w u - z) - (α * γ) • ((1 / (b : ℝ)) • ∑ i : Fin b, g (xb u) (t (1 + i)) - F (xb u)) := by
    intro u t
    simp only [egOut, hw, hxb, ← hin]
    module
  have hstep : ∀ u, ‖x - (α * γ) • w u - z‖ ^ 2 ≤
      (1 - α * γ * Λ) * ‖x - z‖ ^ 2 + stepK L ρ γ α Λ * ‖e1 u‖ ^ 2 := by
    intro u
    exact H.eg_step c z x (e1 u) (xb u) hs.γ_pos hs.α_pos hs.Λ_nonneg hs.ρΛ hs.γL
      hs.coef hs.contr hz rfl
  have hK := stepK_nonneg H.ρ_nonneg H.L_pos.le hs
  have hsplit := lintegral_split p b
    (fun u t => ENNReal.ofReal (‖egOut g J γ α Λ b c x u t - z‖ ^ 2))
    (by
      have : Measurable (fun q : (Fin b → Ω) × (ℕ → Ω) => egOut g J γ α Λ b c x q.1 q.2) :=
        hmeas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      exact ENNReal.measurable_ofReal.comp ((this.sub measurable_const).norm.pow_const 2))
  rw [hsplit]
  have hinner : ∀ u, ∫⁻ t, ENNReal.ofReal (‖egOut g J γ α Λ b c x u t - z‖ ^ 2) ∂P ≤
      ENNReal.ofReal (‖x - (α * γ) • w u - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b)) := by
    intro u
    simp_rw [hdecomp u]
    have ht := lintegral_tuple p (fun i : Fin b => 1 + (i : ℕ))
      (fun i j h => Fin.ext (by simpa using h))
      (fun v : Fin b → Ω => ENNReal.ofReal (‖(x - (α * γ) • w u - z) -
        (α * γ) • ((1 / (b : ℝ)) • ∑ i : Fin b, g (xb u) (v i) - F (xb u))‖ ^ 2))
      (by
        have hS : Measurable (fun v : Fin b → Ω => ∑ i : Fin b, g (xb u) (v i)) :=
          Finset.measurable_sum _ fun i _ =>
            hgm.comp (measurable_const.prodMk (measurable_pi_apply i))
        exact ENNReal.measurable_ofReal.comp
          (((measurable_const.sub (((hS.const_smul _).sub measurable_const).const_smul _)).norm).pow_const 2))
    rw [ht]
    exact batch_lintegral_centered hg (xb u) _ (α * γ) hb
  refine (lintegral_mono hinner).trans ?_
  have hpt : ∀ u, ENNReal.ofReal (‖x - (α * γ) • w u - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b)) ≤
      ENNReal.ofReal ((1 - α * γ * Λ) * ‖x - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b)) +
        ENNReal.ofReal (stepK L ρ γ α Λ) * ENNReal.ofReal (‖e1 u‖ ^ 2) := by
    intro u
    have hq : 0 ≤ (1 - α * γ * Λ) * ‖x - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b) := by
      have : 0 ≤ 1 - α * γ * Λ := by linarith [hs.q_le]
      positivity
    rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add hq (mul_nonneg hK (sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    linarith [hstep u]
  refine (lintegral_mono hpt).trans ?_
  have hm1 : Measurable (fun u : Fin b → Ω => ENNReal.ofReal (‖e1 u‖ ^ 2)) := by
    have hS : Measurable (fun v : Fin b → Ω => ∑ i : Fin b, g x (v i)) :=
      Finset.measurable_sum _ fun i _ => hgm.comp (measurable_const.prodMk (measurable_pi_apply i))
    exact ENNReal.measurable_ofReal.comp ((((hS.const_smul _).sub measurable_const).norm).pow_const 2)
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ hm1]
  have hv := batch_lintegral_sq hg x hb
  calc ENNReal.ofReal ((1 - α * γ * Λ) * ‖x - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b)) +
        ENNReal.ofReal (stepK L ρ γ α Λ) * ∫⁻ u, ENNReal.ofReal (‖e1 u‖ ^ 2) ∂(Measure.pi fun _ => p)
      ≤ ENNReal.ofReal ((1 - α * γ * Λ) * ‖x - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b)) +
          ENNReal.ofReal (stepK L ρ γ α Λ) * ENNReal.ofReal (σ ^ 2 / b) := by gcongr
    _ ≤ ENNReal.ofReal ((1 - α * γ * Λ) * ‖x - z‖ ^ 2 +
          (stepK L ρ γ α Λ + (α * γ) ^ 2) * (σ ^ 2 / b)) := by
        have hq : 0 ≤ (1 - α * γ * Λ) * ‖x - z‖ ^ 2 + (α * γ) ^ 2 * (σ ^ 2 / b) := by
          have : 0 ≤ 1 - α * γ * Λ := by linarith [hs.q_le]
          positivity
        rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add hq (mul_nonneg hK (by positivity))]
        apply le_of_eq; congr 1; ring

end OracleTemplate.StochasticCohypomonotone
