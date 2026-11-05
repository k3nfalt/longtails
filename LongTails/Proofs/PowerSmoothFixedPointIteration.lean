import LongTails.Proofs.PowerSmoothFixedPointNoise
import LongTails.Proofs.RecursiveAnchorKmStochastic

open MeasureTheory

namespace LongTails.Proofs.PowerSmoothFixedPointIteration

open LongTails.Setups.StochasticPowerSmoothFixedPoint
open OracleTemplate.RecursiveAnchorKm
open PowerSmoothFixedPointNoise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ξ : Type*} [MeasurableSpace Ξ]

structure Hyp (p : Measure Ξ) (T : E → E) (G : Ξ → E → E) (s K σ : ℝ) : Prop where
  smooth : ∃ j : E → E →L[ℝ] ℝ, PowerSmooth E s K j
  nonexp : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖
  meas : Measurable (Function.uncurry G)
  unbiased : ∀ x, Integrable (fun ω => G ω x) p ∧ ∫ ω, G ω x ∂p = T x
  moment : ∀ x, Integrable (fun ω => ‖G ω x - T x‖ ^ s) p ∧
    ∫ ω, ‖G ω x - T x‖ ^ s ∂p ≤ σ ^ s
  exponent_ge_one : 1 ≤ s
  K_nonneg : 0 ≤ K
  sigma_nonneg : 0 ≤ σ

variable {p : Measure Ξ} [IsProbabilityMeasure p] {T : E → E} {G : Ξ → E → E}
  {s K σ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.step_inner (h : Hyp p T G s K σ) {α Λ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hΛ : 0 < Λ) (x A : E) :
    ∫⁻ ω, ENNReal.ofReal (‖(1 - α) • x + (α / (1 + Λ)) • (G ω x + A) -
        anchorPoint T Λ A‖ ^ s) ∂p ≤
      ENNReal.ofReal ((1 - α * Λ / (1 + Λ)) * ‖x - anchorPoint T Λ A‖ ^ s +
        K * (α / (1 + Λ)) ^ s * σ ^ s) := by
  obtain ⟨j, hj⟩ := h.smooth
  have hpos : 0 < 1 + Λ := by linarith
  have he : α / (1 + Λ) * (1 + Λ) = α := div_mul_cancel₀ _ hpos.ne'
  have hr : α / (1 + Λ) * Λ = α * Λ / (1 + Λ) := by ring
  have hu : (1 + Λ) • anchorPoint T Λ A - T (anchorPoint T Λ A) - A = 0 := by
    rw [anchorPoint_spec h.nonexp hΛ A]
    abel
  have hp := picard_moment_bound hj h.exponent_ge_one h.K_nonneg hΛ.le
    (div_nonneg hα0 hpos.le) (by rw [he]; exact hα1) T h.nonexp A x
    (anchorPoint T Λ A) hu (fun ω => G ω x) (h.unbiased x).1 (h.unbiased x).2
    (h.moment x).1 (h.moment x).2
  simpa only [he, hr, smul_add, add_assoc] using hp

omit [IsProbabilityMeasure p] in
lemma Hyp.measurable_update (h : Hyp p T G s K σ) {Λ : ℝ} (hΛ : 0 < Λ) (α c : ℝ) :
    Measurable (Function.uncurry fun (w : E × E) (ω : Ξ) =>
      ENNReal.ofReal (‖(1 - α) • w.1 + c • (G ω w.1 + w.2) -
        anchorPoint T Λ w.2‖ ^ s)) := by
  have hG : Measurable (fun q : (E × E) × Ξ => G q.2 q.1.1) :=
    h.meas.comp (measurable_snd.prodMk measurable_fst.fst)
  have hz : Measurable (fun q : (E × E) × Ξ => anchorPoint T Λ q.1.2) :=
    (continuous_anchorPoint h.nonexp hΛ).measurable.comp measurable_fst.snd
  exact ((((measurable_fst.fst.const_smul (1 - α)).add
    ((hG.add measurable_fst.snd).const_smul c)).sub hz).norm.pow_const s).ennreal_ofReal

lemma Hyp.step_expect (h : Hyp p T G s K σ) {α Λ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hΛ : 0 < Λ)
    (m : ℕ) (W : (ℕ → Ξ) → E × E) (hW : Measurable W)
    (hdep : ∀ ξ ξ' : ℕ → Ξ, (∀ i, i < m → ξ i = ξ' i) → W ξ = W ξ') :
    ∫⁻ ξ, ENNReal.ofReal (‖(1 - α) • (W ξ).1 + (α / (1 + Λ)) •
        (G (ξ m) (W ξ).1 + (W ξ).2) - anchorPoint T Λ (W ξ).2‖ ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (1 - α * Λ / (1 + Λ)) *
        ∫⁻ ξ, ENNReal.ofReal (‖(W ξ).1 - anchorPoint T Λ (W ξ).2‖ ^ s)
          ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (K * (α / (1 + Λ)) ^ s * σ ^ s) := by
  rw [lintegral_prefix p m W hW hdep _ (h.measurable_update hΛ α (α / (1 + Λ)))]
  have hf : Measurable (fun ξ : ℕ → Ξ => ‖(W ξ).1 - anchorPoint T Λ (W ξ).2‖ ^ s) :=
    (hW.fst.sub ((continuous_anchorPoint h.nonexp hΛ).measurable.comp hW.snd)).norm.pow_const s
  have hpos : 0 < 1 + Λ := by linarith
  have hr : 0 ≤ 1 - α * Λ / (1 + Λ) := by
    have : α * Λ / (1 + Λ) ≤ α := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith
  have hn : 0 ≤ K * (α / (1 + Λ)) ^ s * σ ^ s :=
    mul_nonneg (mul_nonneg h.K_nonneg (Real.rpow_nonneg (div_nonneg hα0 hpos.le) _))
      (Real.rpow_nonneg h.sigma_nonneg _)
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal ((1 - α * Λ / (1 + Λ)) *
        ‖(W ξ).1 - anchorPoint T Λ (W ξ).2‖ ^ s + K * (α / (1 + Λ)) ^ s * σ ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) :=
      lintegral_mono fun ξ => h.step_inner hα0 hα1 hΛ (W ξ).1 (W ξ).2
    _ = _ := lintegral_affine _ hf (fun _ => Real.rpow_nonneg (norm_nonneg _) _) hr hn

lemma Hyp.stage_bound (h : Hyp p T G s K σ) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ)
    (x0 : E) (u : ℕ) (hα0 : 0 ≤ α u) (hα1 : α u ≤ 1) (hΛ : 0 < Λ u)
    {I V : ℝ} (hI0 : 0 ≤ I) (hV0 : 0 ≤ V)
    (hV : (1 - α u * Λ u / (1 + Λ u)) * V +
      K * (α u / (1 + Λ u)) ^ s * σ ^ s ≤ V)
    (hI : ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ u).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖ ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal I) :
    ∀ k, ∫⁻ ξ, ENNReal.ofReal (‖kmRun G (α u) (α u / (1 + Λ u))
        (stage G lam Λ α N x0 ξ u).2 (start N u) ξ (stage G lam Λ α N x0 ξ u).1 k -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖ ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - α u * Λ u / (1 + Λ u)) ^ k * I + V) := by
  set ρ := 1 - α u * Λ u / (1 + Λ u)
  have hpos : 0 < 1 + Λ u := by linarith
  have hρ0 : 0 ≤ ρ := by
    have : α u * Λ u / (1 + Λ u) ≤ α u := by
      rw [div_le_iff₀ hpos]
      nlinarith
    dsimp [ρ]
    linarith
  have hn : 0 ≤ K * (α u / (1 + Λ u)) ^ s * σ ^ s :=
    mul_nonneg (mul_nonneg h.K_nonneg (Real.rpow_nonneg (div_nonneg hα0 hpos.le) _))
      (Real.rpow_nonneg h.sigma_nonneg _)
  intro k
  induction k with
  | zero =>
    refine hI.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [pow_zero, one_mul]
    linarith
  | succ k ih =>
    have hst := measurable_stage h.meas lam Λ α N x0 u
    let W : (ℕ → Ξ) → E × E := fun ξ =>
      (kmRun G (α u) (α u / (1 + Λ u)) (stage G lam Λ α N x0 ξ u).2 (start N u) ξ
        (stage G lam Λ α N x0 ξ u).1 k, (stage G lam Λ α N x0 ξ u).2)
    have hW : Measurable W :=
      (measurable_inner h.meas _ _ _ hst.snd hst.fst k).prodMk hst.snd
    have hdep : ∀ ξ ξ' : ℕ → Ξ, (∀ i, i < start N u + k → ξ i = ξ' i) → W ξ = W ξ' := by
      intro ξ ξ' hξ
      have he := stage_congr G lam Λ α N x0 u (fun i hi => hξ i (by omega))
      dsimp [W]
      rw [he, inner_congr G _ _ _ _ _ k hξ]
    have hstep := h.step_expect hα0 hα1 hΛ (start N u + k) W hW hdep
    calc
      _ ≤ ENNReal.ofReal ρ *
          ∫⁻ ξ, ENNReal.ofReal (‖(W ξ).1 - anchorPoint T (Λ u) (W ξ).2‖ ^ s)
            ∂(Measure.infinitePi fun _ : ℕ => p) +
          ENNReal.ofReal (K * (α u / (1 + Λ u)) ^ s * σ ^ s) := hstep
      _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ k * I + V) +
          ENNReal.ofReal (K * (α u / (1 + Λ u)) ^ s * σ ^ s) := by
        gcongr
      _ = ENNReal.ofReal (ρ * (ρ ^ k * I + V) + K * (α u / (1 + Λ u)) ^ s * σ ^ s) := by
        rw [← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add
          (mul_nonneg hρ0 (by positivity)) hn]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [pow_succ]
        nlinarith

lemma scaled_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {c s : ℝ} (hc : 0 ≤ c) :
    ∫⁻ ω, ENNReal.ofReal ((c * f ω) ^ s) ∂P =
      ENNReal.ofReal (c ^ s) * ∫⁻ ω, ENNReal.ofReal (f ω ^ s) ∂P := by
  simp_rw [Real.mul_rpow hc (hf0 _), ENNReal.ofReal_mul (Real.rpow_nonneg hc s)]
  exact lintegral_const_mul _ (hf.pow_const s).ennreal_ofReal

lemma Hyp.normalized_stage_bound (h : Hyp p T G s K σ)
    (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (x0 : E) (u : ℕ)
    (hα0 : 0 ≤ α u) (hα1 : α u ≤ 1) (hΛ : 0 < Λ u)
    {I V : ℝ} (hI0 : 0 ≤ I) (hV0 : 0 ≤ V)
    (hV : (1 - α u * Λ u / (1 + Λ u)) * V +
      K * (α u / (1 + Λ u)) ^ s * σ ^ s * (Λ u) ^ s ≤ V)
    (hI : ∫⁻ ξ, ENNReal.ofReal ((Λ u * ‖(stage G lam Λ α N x0 ξ u).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖) ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal I) :
    ∀ k, ∫⁻ ξ, ENNReal.ofReal ((Λ u * ‖kmRun G (α u) (α u / (1 + Λ u))
        (stage G lam Λ α N x0 ξ u).2 (start N u) ξ (stage G lam Λ α N x0 ξ u).1 k -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖) ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - α u * Λ u / (1 + Λ u)) ^ k * I + V) := by
  have hpow : 0 < (Λ u) ^ s := Real.rpow_pos_of_pos hΛ _
  have hst := measurable_stage h.meas lam Λ α N x0 u
  have hz := (continuous_anchorPoint h.nonexp hΛ).measurable.comp hst.snd
  have hstart : Measurable (fun ξ => ‖(stage G lam Λ α N x0 ξ u).1 -
      anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖) := (hst.fst.sub hz).norm
  rw [scaled_moment _ hstart (fun _ => norm_nonneg _) hΛ.le] at hI
  have hI' : ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ u).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖ ^ s)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (I / (Λ u) ^ s) := by
    rw [ENNReal.ofReal_div_of_pos hpow]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hpow)))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hI
  have hV' : (1 - α u * Λ u / (1 + Λ u)) * (V / (Λ u) ^ s) +
      K * (α u / (1 + Λ u)) ^ s * σ ^ s ≤ V / (Λ u) ^ s := by
    calc
      _ = ((1 - α u * Λ u / (1 + Λ u)) * V +
          K * (α u / (1 + Λ u)) ^ s * σ ^ s * (Λ u) ^ s) / (Λ u) ^ s := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hV hpow.le
  intro k
  have hi : Measurable (fun ξ => kmRun G (α u) (α u / (1 + Λ u))
      (stage G lam Λ α N x0 ξ u).2 (start N u) ξ (stage G lam Λ α N x0 ξ u).1 k -
      anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2) :=
    (measurable_inner h.meas (α u) (α u / (1 + Λ u)) (start N u)
      hst.snd hst.fst k).sub hz
  rw [scaled_moment _ hi.norm (fun _ => norm_nonneg _) hΛ.le]
  have hb := h.stage_bound lam Λ α N x0 u hα0 hα1 hΛ
    (div_nonneg hI0 hpow.le) (div_nonneg hV0 hpow.le) hV' hI' k
  calc
    _ ≤ ENNReal.ofReal ((Λ u) ^ s) *
        ENNReal.ofReal ((1 - α u * Λ u / (1 + Λ u)) ^ k * (I / (Λ u) ^ s) +
          V / (Λ u) ^ s) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hpow.le]
      congr 1
      field_simp

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma doubled_start_power {T : E → E} (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    {a s : ℝ} (ha : 0 < a) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (A x : E) :
    ((2 * a) * ‖x - anchorPoint T (2 * a) (A + a • x)‖) ^ s ≤
      9 * (a * ‖x - anchorPoint T a A‖) ^ s := by
  have hm := transition_shift hT ha ha.le A x
  have ht := norm_sub_le (x - anchorPoint T a A)
    (anchorPoint T (2 * a) (A + a • x) - anchorPoint T a A)
  rw [show x - anchorPoint T a A -
      (anchorPoint T (2 * a) (A + a • x) - anchorPoint T a A) =
      x - anchorPoint T (2 * a) (A + a • x) by abel] at ht
  rw [show a + a = 2 * a by ring] at hm
  have hb : (2 * a) * ‖x - anchorPoint T (2 * a) (A + a • x)‖ ≤
      3 * (a * ‖x - anchorPoint T a A‖) := by nlinarith
  calc
    _ ≤ (3 * (a * ‖x - anchorPoint T a A‖)) ^ s :=
      Real.rpow_le_rpow (by positivity) hb hs0
    _ = (3 : ℝ) ^ s * (a * ‖x - anchorPoint T a A‖) ^ s :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 9 * (a * ‖x - anchorPoint T a A‖) ^ s := by
      have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hs2
      norm_num at hp
      exact mul_le_mul_of_nonneg_right hp (by positivity)

end LongTails.Proofs.PowerSmoothFixedPointIteration
