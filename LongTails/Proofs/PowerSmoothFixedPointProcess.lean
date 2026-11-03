import LongTails.Proofs.PowerSmoothFixedPointIteration
import LongTails.Proofs.PowerSmoothAnchoringTuning
import LongTails.Proofs.RecursiveAnchorKmExpectation

open MeasureTheory

namespace LongTails.Proofs.PowerSmoothFixedPointProcess

open OracleTemplate.RecursiveAnchorKm
open PowerSmoothFixedPointIteration

lemma first_moment_of_power {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω ^ s) ∂P ≤ ENNReal.ofReal (η ^ s)) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal (2 * η) := by
  have hηp : 0 < η ^ s := Real.rpow_pos_of_pos hη _
  have hpt : ∀ ω, f ω ≤ (η / η ^ s) * f ω ^ s + η := by
    intro ω
    by_cases hsmall : f ω ≤ η
    · exact hsmall.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (Real.rpow_nonneg (hf0 ω) s)))
    · have hr : 1 ≤ f ω / η := (le_div_iff₀ hη).mpr (by linarith)
      have hp := Real.self_le_rpow_of_one_le hr hs
      rw [Real.div_rpow (hf0 ω) hη.le] at hp
      have hm := mul_le_mul_of_nonneg_left hp hη.le
      have he : η * (f ω / η) = f ω := by field_simp
      rw [he] at hm
      have he' : η * (f ω ^ s / η ^ s) = (η / η ^ s) * f ω ^ s := by ring
      rw [he'] at hm
      linarith
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((η / η ^ s) * f ω ^ s + η) ∂P :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (η / η ^ s) * ∫⁻ ω, ENNReal.ofReal (f ω ^ s) ∂P +
        ENNReal.ofReal η := lintegral_affine P (hf.pow_const s)
          (fun ω => Real.rpow_nonneg (hf0 ω) s) (by positivity) hη.le
    _ ≤ ENNReal.ofReal (η / η ^ s) * ENNReal.ofReal (η ^ s) + ENNReal.ofReal η := by
      gcongr
    _ = ENNReal.ofReal (2 * η) := by
      rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hηp.ne',
        ← ENNReal.ofReal_add hη.le hη.le]
      congr 1
      ring

lemma first_moment_of_scaled_power {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) {s η a : ℝ} (hs : 1 ≤ s) (hη : 0 < η) (ha : 0 < a)
    (h : ∫⁻ ω, ENNReal.ofReal ((a * f ω) ^ s) ∂P ≤ ENNReal.ofReal (η ^ s)) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal (2 * η / a) := by
  have hm := first_moment_of_power P (measurable_const.mul hf)
    (fun ω => mul_nonneg ha.le (hf0 ω)) hs hη h
  have he : (∫⁻ ω, ENNReal.ofReal (a * f ω) ∂P) =
      ENNReal.ofReal a * ∫⁻ ω, ENNReal.ofReal (f ω) ∂P := by
    simp_rw [ENNReal.ofReal_mul ha.le]
    exact lintegral_const_mul _ hf.ennreal_ofReal
  change (∫⁻ ω, ENNReal.ofReal (a * f ω) ∂P) ≤ ENNReal.ofReal (2 * η) at hm
  rw [he] at hm
  rw [ENNReal.ofReal_div_of_pos ha]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr ha)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  simpa only [mul_comm] using hm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ξ : Type*} [MeasurableSpace Ξ] {p : Measure Ξ} [IsProbabilityMeasure p]
  {T : E → E} {G : Ξ → E → E} {s K σ : ℝ}

lemma normalized_process_bound (h : PowerSmoothFixedPointIteration.Hyp p T G s K σ)
    (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (x0 xstar : E) {D B V : ℝ}
    (hstar : T xstar = xstar) (hD : ‖x0 - xstar‖ ≤ D)
    (hs2 : s ≤ 2) (hB : 0 ≤ B) (hV0 : 0 ≤ V)
    (hΛ0 : Λ 0 = lam 0) (hΛ : ∀ u, 0 < Λ u)
    (hlam : ∀ u, lam (u + 1) = Λ u) (hdouble : ∀ u, Λ (u + 1) = 2 * Λ u)
    (hα : ∀ u, 0 ≤ α u ∧ α u ≤ 1)
    (hV : ∀ u, (1 - α u * Λ u / (1 + Λ u)) * V +
      K * (α u / (1 + Λ u)) ^ s * σ ^ s * (Λ u) ^ s ≤ V)
    (hfirst : (1 - α 0 * Λ 0 / (1 + Λ 0)) ^ N 0 * (2 * Λ 0 * D) ^ s + V ≤ B)
    (hnext : ∀ u, (1 - α (u + 1) * Λ (u + 1) / (1 + Λ (u + 1))) ^ N (u + 1) *
      (9 * B) + V ≤ B) :
    ∀ u, ∫⁻ ξ, ENNReal.ofReal ((Λ u * ‖(stage G lam Λ α N x0 ξ (u + 1)).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖) ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal B := by
  let P := Measure.infinitePi fun _ : ℕ => p
  have hs0 : 0 ≤ s := le_trans (by norm_num) h.exponent_ge_one
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) hD
  intro u
  induction u with
  | zero =>
    have hinit : ∫⁻ ξ, ENNReal.ofReal ((Λ 0 * ‖(stage G lam Λ α N x0 ξ 0).1 -
        anchorPoint T (Λ 0) (stage G lam Λ α N x0 ξ 0).2‖) ^ s) ∂P ≤
        ENNReal.ofReal ((2 * Λ 0 * D) ^ s) := by
      apply lintegral_ofReal_le_const
      intro ξ
      apply Real.rpow_le_rpow (mul_nonneg (hΛ 0).le (norm_nonneg _)) _ hs0
      change Λ 0 * ‖x0 - anchorPoint T (Λ 0) (lam 0 • x0)‖ ≤ _
      rw [← hΛ0]
      have hi := initial_le h.nonexp (hΛ 0) x0 xstar hstar
      have hm := mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hD (by norm_num)))
        (hΛ 0).le
      nlinarith
    have hb := h.normalized_stage_bound lam Λ α N x0 0 (hα 0).1 (hα 0).2
      (hΛ 0) (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hΛ 0).le) hD0) _) hV0 (hV 0) hinit (N 0)
    exact hb.trans (ENNReal.ofReal_le_ofReal hfirst)
  | succ u ih =>
    let f : (ℕ → Ξ) → ℝ := fun ξ =>
      Λ u * ‖(stage G lam Λ α N x0 ξ (u + 1)).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖
    have hst := measurable_stage h.meas lam Λ α N x0
    have hf : Measurable f := measurable_const.mul
      ((hst (u + 1)).fst.sub
        ((continuous_anchorPoint h.nonexp (hΛ u)).measurable.comp (hst u).snd)).norm
    have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => mul_nonneg (hΛ u).le (norm_nonneg _)
    have hinit : ∫⁻ ξ, ENNReal.ofReal ((Λ (u + 1) *
        ‖(stage G lam Λ α N x0 ξ (u + 1)).1 - anchorPoint T (Λ (u + 1))
          (stage G lam Λ α N x0 ξ (u + 1)).2‖) ^ s) ∂P ≤ ENNReal.ofReal (9 * B) := by
      calc
        _ ≤ ∫⁻ ξ, ENNReal.ofReal (9 * f ξ ^ s) ∂P := by
          apply lintegral_mono
          intro ξ
          apply ENNReal.ofReal_le_ofReal
          have he : (stage G lam Λ α N x0 ξ (u + 1)).2 =
              (stage G lam Λ α N x0 ξ u).2 + lam (u + 1) •
                (stage G lam Λ α N x0 ξ (u + 1)).1 := rfl
          rw [he, hlam u, hdouble u]
          exact doubled_start_power h.nonexp (hΛ u) hs0 hs2 _ _
        _ = ENNReal.ofReal 9 * ∫⁻ ξ, ENNReal.ofReal (f ξ ^ s) ∂P := by
          simpa using lintegral_affine P (hf.pow_const s)
            (fun ξ => Real.rpow_nonneg (hf0 ξ) s) (r := 9) (b := 0) (by norm_num) le_rfl
        _ ≤ ENNReal.ofReal 9 * ENNReal.ofReal B := by gcongr
        _ = ENNReal.ofReal (9 * B) := (ENNReal.ofReal_mul (by norm_num)).symm
    have hb := h.normalized_stage_bound lam Λ α N x0 (u + 1) (hα (u + 1)).1
      (hα (u + 1)).2 (hΛ (u + 1)) (by positivity) hV0 (hV (u + 1)) hinit (N (u + 1))
    exact hb.trans (ENNReal.ofReal_le_ofReal (hnext u))

lemma residual_from_stage_errors (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (hG : Measurable (Function.uncurry G)) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ)
    (x0 xstar : E) {D : ℝ} (hstar : T xstar = xstar) (hD : ‖x0 - xstar‖ ≤ D)
    (S : ℕ) (η : ℕ → ℝ) {b : ℝ} (hlam : ∀ u, 0 < lam u) (hΛ0 : Λ 0 = lam 0)
    (hΛs : ∀ u, Λ (u + 1) = Λ u + lam (u + 1)) (hΛ : ∀ u, 0 < Λ u)
    (hη : ∀ u, 0 < η u) (hb : ∀ u, u < S → 3 * lam (u + 1) * η u ≤ b)
    (hb0 : 0 ≤ b)
    (herr : ∀ u, u ≤ S → ∫⁻ ξ, ENNReal.ofReal
      (‖(stage G lam Λ α N x0 ξ (u + 1)).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (η u)) :
    ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ (S + 1)).1 -
        T (stage G lam Λ α N x0 ξ (S + 1)).1‖) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (2 * η S + 2 * lam 0 * D + S * b) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hst := measurable_stage hG lam Λ α N x0
  have hz : ∀ u, Measurable (fun ξ => anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2) :=
    fun u => (continuous_anchorPoint hT (hΛ u)).measurable.comp (hst u).snd
  set δ : ℕ → (ℕ → Ξ) → ℝ := fun u ξ =>
    ‖(stage G lam Λ α N x0 ξ (u + 1)).1 - anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖
  have hδm : ∀ u, Measurable (δ u) := fun u => ((hst (u + 1)).fst.sub (hz u)).norm
  have hδ : ∀ u, u ≤ S → ∫⁻ ξ, ENNReal.ofReal (δ u ξ) ∂P ≤ ENNReal.ofReal (η u) := herr
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

open LongTails.Algorithms.PowerSmoothAnchoring PowerSmoothAnchoringTuning

lemma tuned_process_bound (q : LongTails.Setups.StochasticPowerSmoothFixedPoint.Params)
    {p : Measure q.Ξ} [IsProbabilityMeasure p] {T : q.E → q.E} {G : q.Ξ → q.E → q.E}
    (h : PowerSmoothFixedPointIteration.Hyp p T G q.exponent q.K q.σ)
    (hs : 1 < q.exponent) (hs2 : q.exponent ≤ 2) (hε : 0 < q.ε)
    (xstar : q.E) (hstar : T xstar = xstar) (hD : ‖q.x0 - xstar‖ ≤ q.D) :
    ∀ u, ∫⁻ ξ, ENNReal.ofReal ((strength q u *
        ‖(stage G (anchorWeight q) (strength q) (stageStep q) (fun _ => innerSteps q)
          q.x0 ξ (u + 1)).1 - anchorPoint T (strength q u)
          (stage G (anchorWeight q) (strength q) (stageStep q) (fun _ => innerSteps q)
            q.x0 ξ u).2‖) ^ q.exponent) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((q.ε / (32 * (levels q + 1 : ℝ))) ^ q.exponent) := by
  let B := (q.ε / (32 * (levels q + 1 : ℝ))) ^ q.exponent
  let V := q.K * relaxation q ^ (q.exponent - 1) * q.σ ^ q.exponent
  have hK := h.K_nonneg
  have hσ := h.sigma_nonneg
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg
      (relaxation_pos q hK hσ hε).le _)) (Real.rpow_nonneg hσ _)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hV : V ≤ B / 64 := bootstrap_noise hs2 hε (by positivity)
    (normalized_noise_floor q hs hK hσ hε)
  have hdec := innerSteps_decay q hK hσ hε
  apply normalized_process_bound h (anchorWeight q) (strength q) (stageStep q)
    (fun _ => innerSteps q) q.x0 xstar hstar hD hs2 hB0 hV0
    (by simp [LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight]) (strength_pos q)
    (fun u => by simp [LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight]) (strength_double q)
    (fun u => ⟨stageStep_nonneg q hK hσ hε u, stageStep_le_one q hK hσ hε u⟩)
  · intro u
    exact (stationary_noise q hK hσ hε u).le
  · rw [stageStep_drift]
    have hi := initial_strength_radius q hε
    have hD0 : 0 ≤ q.D := le_trans (norm_nonneg _) hD
    have hbase : 2 * strength q 0 * q.D ≤ q.ε / 8 := by nlinarith
    have hp := Real.rpow_le_rpow (mul_nonneg (mul_nonneg (by norm_num) (strength_pos q 0).le) hD0)
      hbase (by linarith : 0 ≤ q.exponent)
    have hc : 0 ≤ (1 - relaxation q) ^ innerSteps q :=
      pow_nonneg (by linarith [relaxation_le_one q hK hσ hε]) _
    have hm := mul_le_mul_of_nonneg_left hp hc
    have hb := bootstrap_initial hs2 hε (show 1 ≤ (levels q + 1 : ℝ) by have := Nat.cast_nonneg (α := ℝ) (levels q); linarith) hdec
    change _ + V ≤ B
    change _ ≤ B / 4 at hb
    linarith
  · intro u
    rw [stageStep_drift]
    exact bootstrap_next hB0 (by have := Nat.cast_nonneg (α := ℝ) (levels q); linarith) hdec hV

lemma tuned_residual_bound (q : LongTails.Setups.StochasticPowerSmoothFixedPoint.Params)
    {p : Measure q.Ξ} [IsProbabilityMeasure p] {T : q.E → q.E} {G : q.Ξ → q.E → q.E}
    (h : PowerSmoothFixedPointIteration.Hyp p T G q.exponent q.K q.σ)
    (hs : 1 < q.exponent) (hs2 : q.exponent ≤ 2) (hε : 0 < q.ε)
    (xstar : q.E) (hstar : T xstar = xstar) (hD : ‖q.x0 - xstar‖ ≤ q.D) :
    ∫⁻ ξ, ENNReal.ofReal (‖(stage G (anchorWeight q) (strength q) (stageStep q)
        (fun _ => innerSteps q) q.x0 ξ (levels q + 1)).1 -
        T (stage G (anchorWeight q) (strength q) (stageStep q)
          (fun _ => innerSteps q) q.x0 ξ (levels q + 1)).1‖)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal q.ε := by
  let r := q.ε / (32 * (levels q + 1 : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have herr := tuned_process_bound q h hs hs2 hε xstar hstar hD
  have hst := measurable_stage h.meas (anchorWeight q) (strength q) (stageStep q)
    (fun _ => innerSteps q) q.x0
  have hfirst : ∀ u, ∫⁻ ξ, ENNReal.ofReal
      (‖(stage G (anchorWeight q) (strength q) (stageStep q) (fun _ => innerSteps q)
        q.x0 ξ (u + 1)).1 - anchorPoint T (strength q u)
        (stage G (anchorWeight q) (strength q) (stageStep q) (fun _ => innerSteps q)
          q.x0 ξ u).2‖) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (2 * r / strength q u) := by
    intro u
    exact first_moment_of_scaled_power _
      (((hst (u + 1)).fst.sub ((continuous_anchorPoint h.nonexp (strength_pos q u)).measurable.comp
        (hst u).snd)).norm) (fun _ => norm_nonneg _) hs.le hr (strength_pos q u) (herr u)
  have hb := residual_from_stage_errors h.nonexp h.meas (anchorWeight q) (strength q)
    (stageStep q) (fun _ => innerSteps q) q.x0 xstar hstar hD (levels q)
    (fun u => 2 * r / strength q u) (b := 6 * r)
    (fun u => by
      unfold LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight
      split <;> exact strength_pos q _)
    (by simp [LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight])
    (fun u => by
      simp only [LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight, Nat.add_one_ne_zero,
        ↓reduceIte, Nat.add_sub_cancel, strength_double]
      ring)
    (strength_pos q) (fun u => div_pos (by positivity) (strength_pos q u))
    (fun u _ => by
      simp only [LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight, Nat.add_one_ne_zero,
        ↓reduceIte, Nat.add_sub_cancel]
      have ha := strength_pos q u
      field_simp
      ring_nf
      exact le_rfl)
    (by positivity) (fun u _ => hfirst u)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [strength_last, div_one, LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight,
    ↓reduceIte]
  have hi := initial_strength_radius q hε
  have he : (32 * (levels q + 1 : ℝ)) * r = q.ε := by
    dsimp [r]
    field_simp
  have hn : 0 ≤ (levels q : ℝ) := Nat.cast_nonneg _
  nlinarith

end LongTails.Proofs.PowerSmoothFixedPointProcess
