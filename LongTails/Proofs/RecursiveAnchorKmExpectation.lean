import LongTails.Proofs.RecursiveAnchorKmStochastic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleTemplate.RecursiveAnchorKm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} {T : E → E} {G : Ξ → E → E} {K σ : ℝ}

lemma lintegral_add_scaled {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) {r : ℝ}
    (hr : 0 ≤ r) :
    ∫⁻ ω, ENNReal.ofReal (f ω + r * g ω) ∂P =
      ∫⁻ ω, ENNReal.ofReal (f ω) ∂P + ENNReal.ofReal r * ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
  have h1 : ∀ ω, ENNReal.ofReal (f ω + r * g ω) =
      ENNReal.ofReal (f ω) + ENNReal.ofReal r * ENNReal.ofReal (g ω) := by
    intro ω
    rw [ENNReal.ofReal_add (hf0 ω) (mul_nonneg hr (hg0 ω)), ENNReal.ofReal_mul hr]
  simp_rw [h1]
  rw [lintegral_add_left hf.ennreal_ofReal, lintegral_const_mul _ hg.ennreal_ofReal]

lemma lintegral_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) {η : ℝ} (hη : 0 < η)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal (η ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal η := by
  have hpt : ∀ ω, f ω ≤ (1 / (2 * η)) * f ω ^ 2 + η / 2 := by
    intro ω
    have h2 : 0 ≤ (f ω - η) ^ 2 := sq_nonneg _
    rw [div_mul_eq_mul_div, one_mul, div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith
  calc ∫⁻ ω, ENNReal.ofReal (f ω) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((1 / (2 * η)) * f ω ^ 2 + η / 2) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (1 / (2 * η)) * ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P + ENNReal.ofReal (η / 2) :=
        lintegral_affine P (hf.pow_const 2) (fun ω => sq_nonneg _) (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal (1 / (2 * η)) * ENNReal.ofReal (η ^ 2) + ENNReal.ofReal (η / 2) := by
        gcongr
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

lemma lintegral_ofReal_le_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, f ω ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal c := by
  calc ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ∫⁻ _, ENNReal.ofReal c ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (h ω)
    _ = ENNReal.ofReal c := by rw [lintegral_const, measure_univ, mul_one]

theorem Hyp.residual_bound (h : Hyp p T G K σ) [IsProbabilityMeasure p] (lam Λ α : ℕ → ℝ)
    (N : ℕ → ℕ) (x0 xstar : E) {D : ℝ} (hstar : T xstar = xstar) (hD : ‖x0 - xstar‖ ≤ D) (S : ℕ)
    (η : ℕ → ℝ) {b : ℝ} (hlam : ∀ u, 0 < lam u) (hΛ0 : Λ 0 = lam 0)
    (hΛs : ∀ u, Λ (u + 1) = Λ u + lam (u + 1)) (hΛ : ∀ u, 0 < Λ u)
    (hα : ∀ u, 0 ≤ α u ∧ α u ≤ 1) (hη : ∀ u, 0 < η u)
    (hV : ∀ u, (1 - α u * Λ u / (1 + Λ u)) ^ 2 * (η u ^ 2 / 2) +
      K * (α u / (1 + Λ u)) ^ 2 * σ ^ 2 ≤ η u ^ 2 / 2)
    (hI0 : (1 - α 0 * Λ 0 / (1 + Λ 0)) ^ (2 * N 0) * (4 * D ^ 2) ≤ η 0 ^ 2 / 2)
    (hIs : ∀ u, u < S → (1 - α (u + 1) * Λ (u + 1) / (1 + Λ (u + 1))) ^ (2 * N (u + 1)) *
      (4 * η u ^ 2) ≤ η (u + 1) ^ 2 / 2)
    (hb : ∀ u, u < S → 3 * lam (u + 1) * η u ≤ b) (hb0 : 0 ≤ b) :
    ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ (S + 1)).1 -
        T (stage G lam Λ α N x0 ξ (S + 1)).1‖) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (2 * η S + 2 * lam 0 * D + S * b) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hT := h.nonexp
  have hst := measurable_stage h.meas lam Λ α N x0
  have hz : ∀ u, Measurable (fun ξ => anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2) :=
    fun u => (continuous_anchorPoint hT (hΛ u)).measurable.comp (hst u).snd
  set δ : ℕ → (ℕ → Ξ) → ℝ := fun u ξ =>
    ‖(stage G lam Λ α N x0 ξ (u + 1)).1 - anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖
  have hδm : ∀ u, Measurable (δ u) := fun u => ((hst (u + 1)).fst.sub (hz u)).norm
  set Q : ℕ → (ℕ → Ξ) → ℝ := fun u ξ =>
    ‖(stage G lam Λ α N x0 ξ u).2 - Λ u • anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖
  have hQm : ∀ u, Measurable (Q u) :=
    fun u => ((hst u).snd.sub ((hz u).const_smul _)).norm
  have hz0 : ∀ ξ, ‖(stage G lam Λ α N x0 ξ 0).1 - anchorPoint T (Λ 0) (stage G lam Λ α N x0 ξ 0).2‖ ≤
      2 * D := by
    intro ξ
    show ‖x0 - anchorPoint T (Λ 0) (lam 0 • x0)‖ ≤ 2 * D
    rw [hΛ0]
    have := initial_le hT (hlam 0) x0 xstar hstar
    linarith
  have hnext : ∀ u ξ, ‖(stage G lam Λ α N x0 ξ (u + 1)).1 -
      anchorPoint T (Λ (u + 1)) (stage G lam Λ α N x0 ξ (u + 1)).2‖ ≤ 2 * δ u ξ := by
    intro u ξ
    have hs : stage G lam Λ α N x0 ξ (u + 1) =
        ((stage G lam Λ α N x0 ξ (u + 1)).1,
          (stage G lam Λ α N x0 ξ u).2 + lam (u + 1) • (stage G lam Λ α N x0 ξ (u + 1)).1) := rfl
    conv_lhs => rw [hs, hΛs u]
    exact transition_start hT (hΛ u) (hlam (u + 1)).le _ _
  have hsq : ∀ u, u ≤ S → ∫⁻ ξ, ENNReal.ofReal (δ u ξ ^ 2) ∂P ≤ ENNReal.ofReal (η u ^ 2) := by
    intro u
    induction u with
    | zero =>
      intro _
      have hinit : ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ 0).1 -
          anchorPoint T (Λ 0) (stage G lam Λ α N x0 ξ 0).2‖ ^ 2) ∂P ≤ ENNReal.ofReal (4 * D ^ 2) := by
        apply lintegral_ofReal_le_const
        intro ξ
        have := hz0 ξ
        have h0 := norm_nonneg ((stage G lam Λ α N x0 ξ 0).1 -
          anchorPoint T (Λ 0) (stage G lam Λ α N x0 ξ 0).2)
        nlinarith
      have hs := h.stage_bound lam Λ α N x0 0 (hα 0).1 (hα 0).2 (hΛ 0) (by positivity) (hV 0)
        (by positivity) hinit (N 0)
      refine le_trans hs (ENNReal.ofReal_le_ofReal ?_)
      linarith [hI0]
    | succ u ih =>
      intro hu
      have ih' := ih (by omega)
      have hinit : ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ (u + 1)).1 -
          anchorPoint T (Λ (u + 1)) (stage G lam Λ α N x0 ξ (u + 1)).2‖ ^ 2) ∂P ≤
          ENNReal.ofReal (4 * η u ^ 2) := by
        calc _ ≤ ∫⁻ ξ, ENNReal.ofReal (4 * δ u ξ ^ 2) ∂P := by
              apply lintegral_mono
              intro ξ
              apply ENNReal.ofReal_le_ofReal
              have h1 := hnext u ξ
              have h0 := norm_nonneg ((stage G lam Λ α N x0 ξ (u + 1)).1 -
                anchorPoint T (Λ (u + 1)) (stage G lam Λ α N x0 ξ (u + 1)).2)
              nlinarith
          _ = ENNReal.ofReal 4 * ∫⁻ ξ, ENNReal.ofReal (δ u ξ ^ 2) ∂P := by
              have := lintegral_affine P ((hδm u).pow_const 2) (fun ξ => sq_nonneg (δ u ξ))
                (r := 4) (b := 0) (by norm_num) le_rfl
              simpa using this
          _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (η u ^ 2) := by gcongr
          _ = ENNReal.ofReal (4 * η u ^ 2) := (ENNReal.ofReal_mul (by norm_num)).symm
      have hs := h.stage_bound lam Λ α N x0 (u + 1) (hα (u + 1)).1 (hα (u + 1)).2 (hΛ (u + 1))
        (by positivity) (hV (u + 1)) (by positivity) hinit (N (u + 1))
      refine le_trans hs (ENNReal.ofReal_le_ofReal ?_)
      linarith [hIs u (by omega)]
  have hδ : ∀ u, u ≤ S → ∫⁻ ξ, ENNReal.ofReal (δ u ξ) ∂P ≤ ENNReal.ofReal (η u) :=
    fun u hu => lintegral_le_of_sq P (hδm u) (hη u) (hsq u hu)
  have hQ : ∀ u, u ≤ S → ∫⁻ ξ, ENNReal.ofReal (Q u ξ) ∂P ≤ ENNReal.ofReal (2 * lam 0 * D + u * b) := by
    intro u
    induction u with
    | zero =>
      intro _
      apply lintegral_ofReal_le_const
      intro ξ
      show ‖lam 0 • x0 - Λ 0 • anchorPoint T (Λ 0) (lam 0 • x0)‖ ≤ 2 * lam 0 * D + ((0 : ℕ) : ℝ) * b
      have h1 := hz0 ξ
      change ‖x0 - anchorPoint T (Λ 0) (lam 0 • x0)‖ ≤ 2 * D at h1
      rw [hΛ0] at h1 ⊢
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hlam 0)]
      have := hlam 0
      push_cast
      nlinarith
    | succ u ih =>
      intro hu
      have ih' := ih (by omega)
      have hpt : ∀ ξ, Q (u + 1) ξ ≤ Q u ξ + (3 * lam (u + 1)) * δ u ξ := by
        intro ξ
        have hs : stage G lam Λ α N x0 ξ (u + 1) =
            ((stage G lam Λ α N x0 ξ (u + 1)).1,
              (stage G lam Λ α N x0 ξ u).2 + lam (u + 1) • (stage G lam Λ α N x0 ξ (u + 1)).1) := rfl
        show ‖(stage G lam Λ α N x0 ξ (u + 1)).2 - Λ (u + 1) •
          anchorPoint T (Λ (u + 1)) (stage G lam Λ α N x0 ξ (u + 1)).2‖ ≤ _
        conv_lhs => rw [hs, hΛs u]
        have := transition_gap hT (hΛ u) (hlam (u + 1)).le (stage G lam Λ α N x0 ξ u).2
          (stage G lam Λ α N x0 ξ (u + 1)).1
        simp only [Q, δ]
        linarith
      calc ∫⁻ ξ, ENNReal.ofReal (Q (u + 1) ξ) ∂P
          ≤ ∫⁻ ξ, ENNReal.ofReal (Q u ξ + (3 * lam (u + 1)) * δ u ξ) ∂P :=
            lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpt ξ)
        _ = ∫⁻ ξ, ENNReal.ofReal (Q u ξ) ∂P +
              ENNReal.ofReal (3 * lam (u + 1)) * ∫⁻ ξ, ENNReal.ofReal (δ u ξ) ∂P :=
            lintegral_add_scaled P (hQm u) (hδm u) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
              (by linarith [hlam (u + 1)])
        _ ≤ ENNReal.ofReal (2 * lam 0 * D + u * b) +
              ENNReal.ofReal (3 * lam (u + 1)) * ENNReal.ofReal (η u) := by
            gcongr
            exact hδ u (by omega)
        _ = ENNReal.ofReal (2 * lam 0 * D + u * b + 3 * lam (u + 1) * η u) := by
            have h0 : 0 ≤ 2 * lam 0 * D + u * b := by
              have := hlam 0
              have : 0 ≤ D := le_trans (norm_nonneg _) hD
              positivity
            rw [← ENNReal.ofReal_mul (by linarith [hlam (u + 1)]),
              ← ENNReal.ofReal_add h0 (by have := hlam (u + 1); have := hη u; positivity)]
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            have := hb u (by omega)
            push_cast
            linarith
  have hres : ∀ ξ, ‖(stage G lam Λ α N x0 ξ (S + 1)).1 - T (stage G lam Λ α N x0 ξ (S + 1)).1‖ ≤
      Q S ξ + 2 * δ S ξ := by
    intro ξ
    have := residual_le hT (hΛ S) (stage G lam Λ α N x0 ξ S).2 (stage G lam Λ α N x0 ξ (S + 1)).1
    simp only [Q, δ]
    linarith
  calc _ ≤ ∫⁻ ξ, ENNReal.ofReal (Q S ξ + 2 * δ S ξ) ∂P :=
        lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hres ξ)
    _ = ∫⁻ ξ, ENNReal.ofReal (Q S ξ) ∂P + ENNReal.ofReal 2 * ∫⁻ ξ, ENNReal.ofReal (δ S ξ) ∂P :=
        lintegral_add_scaled P (hQm S) (hδm S) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
          (by norm_num)
    _ ≤ ENNReal.ofReal (2 * lam 0 * D + S * b) + ENNReal.ofReal 2 * ENNReal.ofReal (η S) := by
        gcongr
        · exact hQ S le_rfl
        · exact hδ S le_rfl
    _ = ENNReal.ofReal (2 * η S + 2 * lam 0 * D + S * b) := by
        have h0 : 0 ≤ 2 * lam 0 * D + S * b := by
          have := hlam 0
          have : 0 ≤ D := le_trans (norm_nonneg _) hD
          positivity
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add h0 (by have := hη S; positivity)]
        congr 1
        ring

end OracleTemplate.RecursiveAnchorKm
