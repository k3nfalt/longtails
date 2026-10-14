import LongTails.Proofs.RegularizedProxEgStage

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

open QueryPlan

noncomputable def extendP {Ω : Type*} (ω0 : Ω) (k : ℕ) (u : Fin k → Ω) : ℕ → Ω :=
  fun i => if h : i < k then u ⟨i, h⟩ else ω0

lemma measurable_extendP {Ω : Type*} [MeasurableSpace Ω] (ω0 : Ω) (k : ℕ) :
    Measurable (extendP ω0 k) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i < k
  · simp only [extendP, h, dite_true]; exact measurable_pi_apply _
  · simp only [extendP, h, dite_false]; exact measurable_const

section Congr

variable {Q R U Ω : Type*}

lemma sampledEval_congr (g : Q → Ω → R) {k : ℕ} (plan : QueryPlan Q R U k) :
    ∀ (ξ ξ' : ℕ → Ω) (call : ℕ), (∀ i, i < k → ξ (call + i) = ξ' (call + i)) →
      sampledEval g ξ plan call = sampledEval g ξ' plan call := by
  induction plan with
  | done value => intro _ _ _ _; rfl
  | @ask k q next ih =>
      intro ξ ξ' call h
      simp only [sampledEval]
      have h0 : ξ call = ξ' call := by simpa using h 0 (Nat.succ_pos k)
      rw [h0]
      exact ih _ ξ ξ' (call + 1) fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show call + (i + 1) = call + 1 + i by omega] at this

lemma evalP_extend (g : Q → Ω → R) {k : ℕ} (plan : QueryPlan Q R U k) (ω0 : Ω) (ξ : ℕ → Ω) :
    evalP g plan ξ = evalP g plan (extendP ω0 k (fun i : Fin k => ξ i)) := by
  unfold evalP
  apply sampledEval_congr
  intro i hi
  simp [extendP, hi]

end Congr

section Prefix

variable {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]

lemma lintegral_prefix_only (ω0 : Ω) (k : ℕ) (f : (ℕ → Ω) → ℝ≥0∞) (hf : Measurable f)
    (hdep : ∀ ξ, f ξ = f (extendP ω0 k (fun i : Fin k => ξ i))) :
    ∫⁻ ξ, f ξ ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫⁻ u, f (extendP ω0 k u) ∂(Measure.pi fun _ : Fin k => p) := by
  have hm : Measurable (fun u : Fin k → Ω => f (extendP ω0 k u)) :=
    hf.comp (measurable_extendP ω0 k)
  have h := lintegral_split p k (fun u _ => f (extendP ω0 k u))
    (hm.comp measurable_fst)
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [← h]
  exact lintegral_congr fun ξ => hdep ξ

end Prefix

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma egEval_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {J : ℝ → E → E}
    {γ : ℝ} (hJ : Continuous (J γ)) (α Λ : ℝ) (b : ℕ) :
    Measurable (fun q : E × E × (ℕ → Ω) => evalP (reply g J) (egStep γ α Λ b q.1 q.2.1) q.2.2) := by
  simp_rw [evalP_egStep]
  exact (egOut_measurable hg hJ α Λ b).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (((by fun_prop : Measurable (fun ξ : ℕ → Ω => fun i : Fin b => ξ i)).comp
        (measurable_snd.comp measurable_snd)).prodMk
      ((by fun_prop : Measurable (fun ξ : ℕ → Ω => fun i => ξ (b + i))).comp
        (measurable_snd.comp measurable_snd)))))

omit [CompleteSpace E] in
lemma repeat_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {J : ℝ → E → E}
    {γ : ℝ} (hJ : Continuous (J γ)) (α Λ : ℝ) (b : ℕ) :
    ∀ n, Measurable (fun q : E × E × (ℕ → Ω) =>
      evalP (reply g J) (repeatPlan (egStep γ α Λ b q.1) n q.2.1) q.2.2)
  | 0 => by simp only [repeatPlan, evalP, sampledEval]; exact measurable_fst.comp measurable_snd
  | n + 1 => by
      have ih := repeat_measurable hg hJ α Λ b n
      have hY := egEval_measurable hg hJ α Λ b (Ω := Ω)
      simp_rw [evalP_repeat]
      exact ih.comp (measurable_fst.prodMk (hY.prodMk
        ((by fun_prop : Measurable (fun ξ : ℕ → Ω => fun i => ξ (b + 1 + b + i))).comp
          (measurable_snd.comp measurable_snd))))

variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ σ : ℝ} {g : E → Ω → E}
  {p : Measure Ω} [IsProbabilityMeasure p]

lemma OpHyp.repeat_expect (H : OpHyp F G J L ρ)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ)
    {γ α Λ M : ℝ} (hs : StepOK L ρ γ α Λ M) (hΛ : 0 < Λ) {b : ℕ} (hb : 0 < b) (c z : E)
    (hz : -(F z + Λ • (z - c)) ∈ G z) :
    ∀ (n : ℕ) (x : E),
      ∫⁻ ξ, ENNReal.ofReal (‖evalP (reply g J) (repeatPlan (egStep γ α Λ b c) n x) ξ - z‖ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal ((1 - α * γ * Λ) ^ n * ‖x - z‖ ^ 2 +
          (stepK L ρ γ α Λ + (α * γ) ^ 2) * (σ ^ 2 / b) * (1 - (1 - α * γ * Λ) ^ n) /
            (α * γ * Λ)) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hJ := H.res_continuous hs.γ_pos
  have hgm := hg.measurable
  set q := α * γ * Λ with hqdef
  have hq0 : 0 < q := by have := hs.α_pos; have := hs.γ_pos; positivity
  have hq1 : 0 ≤ 1 - q := by linarith [hs.q_le]
  set C := (stepK L ρ γ α Λ + (α * γ) ^ 2) * (σ ^ 2 / b) with hCdef
  have hC : 0 ≤ C := by
    have := stepK_nonneg H.ρ_nonneg H.L_pos.le hs
    positivity
  have hrm : ∀ n, Measurable (fun q : E × (ℕ → Ω) =>
      evalP (reply g J) (repeatPlan (egStep γ α Λ b c) n q.1) q.2) := fun n =>
    (repeat_measurable hgm hJ α Λ b n).comp (measurable_const.prodMk measurable_id)
  intro n
  induction n with
  | zero =>
      intro x
      simp only [repeatPlan, evalP, sampledEval, pow_zero, one_mul, sub_self, mul_zero, zero_div,
        add_zero, lintegral_const, measure_univ, mul_one, le_refl]
  | succ n ih =>
      intro x
      set Y : (ℕ → Ω) → E := fun ξ => evalP (reply g J) (egStep γ α Λ b c x) ξ with hY
      have hYm : Measurable Y :=
        (egEval_measurable hgm hJ α Λ b).comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      have hYe : ∀ ξ, Y ξ = Y (extendP ω0 (b + 1 + b) (fun i => ξ i)) :=
        fun ξ => evalP_extend (reply g J) (egStep γ α Λ b c x) ω0 ξ
      have heq : ∀ ξ, evalP (reply g J) (repeatPlan (egStep γ α Λ b c) (n + 1) x) ξ =
          evalP (reply g J) (repeatPlan (egStep γ α Λ b c) n
            (Y (extendP ω0 (b + 1 + b) (fun i => ξ i)))) (fun i => ξ (b + 1 + b + i)) := by
        intro ξ; rw [evalP_repeat, ← hYe]
      simp_rw [heq]
      have hext := measurable_extendP ω0 (b + 1 + b) (Ω := Ω)
      rw [lintegral_split p (b + 1 + b)
        (fun u t => ENNReal.ofReal (‖evalP (reply g J) (repeatPlan (egStep γ α Λ b c) n
          (Y (extendP ω0 (b + 1 + b) u))) t - z‖ ^ 2))
        (ENNReal.measurable_ofReal.comp (((hrm n).comp (((hYm.comp hext).comp measurable_fst).prodMk
          measurable_snd)).sub measurable_const |>.norm.pow_const 2))]
      have hinner := fun u => ih (Y (extendP ω0 (b + 1 + b) u))
      refine (lintegral_mono hinner).trans ?_
      have hsplit2 : ∀ u : Fin (b + 1 + b) → Ω,
          ENNReal.ofReal ((1 - q) ^ n * ‖Y (extendP ω0 (b + 1 + b) u) - z‖ ^ 2 +
            C * (1 - (1 - q) ^ n) / q) =
          ENNReal.ofReal ((1 - q) ^ n) *
              ENNReal.ofReal (‖Y (extendP ω0 (b + 1 + b) u) - z‖ ^ 2) +
            ENNReal.ofReal (C * (1 - (1 - q) ^ n) / q) := by
        intro u
        have h1 : 0 ≤ C * (1 - (1 - q) ^ n) / q := by
          have : (1 - q) ^ n ≤ 1 := pow_le_one₀ hq1 (by linarith)
          have : 0 ≤ 1 - (1 - q) ^ n := by linarith
          positivity
        rw [ENNReal.ofReal_add (by positivity) h1, ENNReal.ofReal_mul (pow_nonneg hq1 n)]
      simp_rw [hsplit2]
      have hm2 : Measurable (fun u : Fin (b + 1 + b) → Ω =>
          ENNReal.ofReal (‖Y (extendP ω0 (b + 1 + b) u) - z‖ ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((((hYm.comp hext).sub measurable_const).norm).pow_const 2)
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hm2, lintegral_const,
        measure_univ, mul_one]
      have hback := lintegral_prefix_only p ω0 (b + 1 + b)
        (fun ξ => ENNReal.ofReal (‖Y ξ - z‖ ^ 2))
        (ENNReal.measurable_ofReal.comp (((hYm.sub measurable_const).norm).pow_const 2))
        (fun ξ => by rw [← hYe])
      rw [← hback]
      have hA : ∫⁻ ξ, ENNReal.ofReal (‖Y ξ - z‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
          ENNReal.ofReal ((1 - q) * ‖x - z‖ ^ 2 + C) := by
        simp_rw [hY, evalP_egStep]
        exact H.eg_expect hg hs hb c x z hz
      calc ENNReal.ofReal ((1 - q) ^ n) *
            ∫⁻ ξ, ENNReal.ofReal (‖Y ξ - z‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
            ENNReal.ofReal (C * (1 - (1 - q) ^ n) / q)
          ≤ ENNReal.ofReal ((1 - q) ^ n) * ENNReal.ofReal ((1 - q) * ‖x - z‖ ^ 2 + C) +
            ENNReal.ofReal (C * (1 - (1 - q) ^ n) / q) := by gcongr
        _ = ENNReal.ofReal ((1 - q) ^ (n + 1) * ‖x - z‖ ^ 2 + C * (1 - (1 - q) ^ (n + 1)) / q) := by
            have h1 : 0 ≤ C * (1 - (1 - q) ^ n) / q := by
              have : (1 - q) ^ n ≤ 1 := pow_le_one₀ hq1 (by linarith)
              have : 0 ≤ 1 - (1 - q) ^ n := by linarith
              positivity
            rw [← ENNReal.ofReal_mul (pow_nonneg hq1 n), ← ENNReal.ofReal_add (by positivity) h1]
            congr 1
            field_simp
            ring

end OracleTemplate.StochasticCohypomonotone
