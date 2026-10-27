import LongTails.Proofs.RecursiveAnchorKmDeterministic
import LongTails.Proofs.LinearDecaySgdExpectation
import LongTails.Setups.StochasticFixedPointSmoothBanach

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleTemplate.RecursiveAnchorKm

open OracleTemplate.SampledConvex (map_prefix_pair extend measurable_extend extend_agree)
open LongTails.Setups.StochasticFixedPointSmoothBanach (TwoUniformlySmooth)

section Prefix

variable {Ξ : Type*} [MeasurableSpace Ξ] {Y : Type*} [MeasurableSpace Y]

lemma lintegral_prefix (p : Measure Ξ) [IsProbabilityMeasure p] (k : ℕ) (W : (ℕ → Ξ) → Y)
    (hW : Measurable W) (hdep : ∀ ξ ξ' : ℕ → Ξ, (∀ i, i < k → ξ i = ξ' i) → W ξ = W ξ')
    (Φ : Y → Ξ → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ξ, Φ (W ξ) (ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫⁻ ξ, ∫⁻ ω, Φ (W ξ) ω ∂p ∂(Measure.infinitePi fun _ : ℕ => p) := by
  have hne : Nonempty Ξ := by
    by_contra hn
    have : IsEmpty Ξ := not_nonempty_iff.mp hn
    have h1 : p Set.univ = 1 := measure_univ
    rw [Measure.eq_zero_of_isEmpty p] at h1
    simp at h1
  obtain ⟨ω0⟩ := hne
  set P := Measure.infinitePi fun _ : ℕ => p
  have hπ : Measurable (fun ξ : ℕ → Ξ => fun i : Fin k => ξ i) := by fun_prop
  let X : (Fin k → Ξ) → Y := fun u => W (extend ω0 u)
  have hX : Measurable X := hW.comp (measurable_extend ω0)
  have hWX : ∀ ξ, W ξ = X (fun i : Fin k => ξ i) := fun ξ => (hdep _ _ (extend_agree ω0 ξ)).symm
  have hpair : Measurable (fun ξ : ℕ → Ξ => ((fun i : Fin k => ξ i), ξ k)) := by fun_prop
  let H : (Fin k → Ξ) × Ξ → ℝ≥0∞ := fun z => Φ (X z.1) z.2
  have hH : Measurable H := hΦ.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hmap := map_prefix_pair p k
  have hL : ∫⁻ ξ, Φ (W ξ) (ξ k) ∂P = ∫⁻ ξ, H ((fun i : Fin k => ξ i), ξ k) ∂P := by
    congr 1; funext ξ; rw [hWX ξ]
  have hR : ∫⁻ ξ, ∫⁻ ω, Φ (W ξ) ω ∂p ∂P = ∫⁻ ξ, ∫⁻ ω, H ((fun i : Fin k => ξ i), ω) ∂p ∂P := by
    congr 1; funext ξ; rw [hWX ξ]
  rw [hL, hR]
  calc ∫⁻ ξ, H ((fun i : Fin k => ξ i), ξ k) ∂P
      = ∫⁻ z, H z ∂(P.map (fun ξ : ℕ → Ξ => ((fun i : Fin k => ξ i), ξ k))) :=
        (lintegral_map hH hpair).symm
    _ = ∫⁻ z, H z ∂((P.map (fun ξ : ℕ → Ξ => fun i : Fin k => ξ i)).prod p) := by rw [hmap]
    _ = ∫⁻ u, ∫⁻ ω, H (u, ω) ∂p ∂(P.map (fun ξ : ℕ → Ξ => fun i : Fin k => ξ i)) :=
        lintegral_prod H hH.aemeasurable
    _ = ∫⁻ ξ, ∫⁻ ω, H ((fun i : Fin k => ξ i), ω) ∂p ∂P :=
        lintegral_map hH.lintegral_prod_right' hπ

end Prefix

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

structure Hyp (p : Measure Ξ) (T : E → E) (G : Ξ → E → E) (K σ : ℝ) : Prop where
  smooth : ∃ j : E → E →L[ℝ] ℝ, TwoUniformlySmooth E K j
  nonexp : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖
  meas : Measurable (Function.uncurry G)
  unbiased : ∀ x, Integrable (fun ω => G ω x) p ∧ ∫ ω, G ω x ∂p = T x
  variance : ∀ x, Integrable (fun ω => ‖G ω x - T x‖ ^ 2) p ∧ ∫ ω, ‖G ω x - T x‖ ^ 2 ∂p ≤ σ ^ 2
  K_nonneg : 0 ≤ K

variable {p : Measure Ξ} {T : E → E} {G : Ξ → E → E} {K σ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.step_inner (h : Hyp p T G K σ) [IsProbabilityMeasure p] {α Λ : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hΛ : 0 < Λ) (y A : E) :
    ∫⁻ ω, ENNReal.ofReal (‖(1 - α) • y + (α / (1 + Λ)) • (G ω y + A) - anchorPoint T Λ A‖ ^ 2) ∂p ≤
      ENNReal.ofReal ((1 - α * Λ / (1 + Λ)) ^ 2 * ‖y - anchorPoint T Λ A‖ ^ 2 +
        K * (α / (1 + Λ)) ^ 2 * σ ^ 2) := by
  obtain ⟨j, hj⟩ := h.smooth
  have hpos : 0 < 1 + Λ := by linarith
  set z := anchorPoint T Λ A
  set c := α / (1 + Λ)
  have hc0 : 0 ≤ c := div_nonneg hα0 hpos.le
  have hz := anchorPoint_spec h.nonexp hΛ A
  have hcz : c • (T z + A) = α • z := by
    rw [← hz, smul_smul]
    congr 1
    simp only [c]
    field_simp
  set a := (1 - α) • (y - z) + c • (T y - T z)
  have hdec : ∀ ω, (1 - α) • y + c • (G ω y + A) - z = a + c • (G ω y - T y) := by
    intro ω
    have hz2 : z = (1 - α) • z + c • (T z + A) := by rw [hcz]; module
    calc (1 - α) • y + c • (G ω y + A) - z
        = (1 - α) • y + c • (G ω y + A) - ((1 - α) • z + c • (T z + A)) := by
          conv_lhs => rw [hz2]
      _ = a + c • (G ω y - T y) := by simp only [a]; module
  have hρ : 1 - α + c = 1 - α * Λ / (1 + Λ) := by
    simp only [c]; field_simp; ring
  have hρ0 : 0 ≤ 1 - α * Λ / (1 + Λ) := by
    have : α * Λ / (1 + Λ) ≤ α := by
      rw [div_le_iff₀ hpos]; nlinarith
    linarith
  have ha : ‖a‖ ≤ (1 - α * Λ / (1 + Λ)) * ‖y - z‖ := by
    have h1 := norm_add_le ((1 - α) • (y - z)) (c • (T y - T z))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg hc0] at h1
    have h2 : c * ‖T y - T z‖ ≤ c * ‖y - z‖ := mul_le_mul_of_nonneg_left (h.nonexp y z) hc0
    rw [← hρ]
    nlinarith [norm_nonneg (y - z)]
  have ha2 : ‖a‖ ^ 2 ≤ (1 - α * Λ / (1 + Λ)) ^ 2 * ‖y - z‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ha 2
  set ζ : Ξ → E := fun ω => G ω y - T y
  have hζi : Integrable ζ p := (h.unbiased y).1.sub (integrable_const _)
  have hζ0 : ∫ ω, ζ ω ∂p = 0 := by
    simp only [ζ]
    rw [integral_sub (h.unbiased y).1 (integrable_const _), (h.unbiased y).2, integral_const]
    simp
  let g : Ξ → ℝ := fun ω => ‖a‖ ^ 2 + 2 * c * j a (ζ ω) + K * c ^ 2 * ‖ζ ω‖ ^ 2
  have hpt : ∀ ω, ‖(1 - α) • y + c • (G ω y + A) - z‖ ^ 2 ≤ g ω := by
    intro ω
    rw [hdec ω]
    have h1 := hj a (c • ζ ω)
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, mul_pow] at h1
    simp only [g]
    linarith
  have hgi : Integrable g p := by
    have h1 : Integrable (fun ω => j a (ζ ω)) p := (j a).integrable_comp hζi
    exact ((integrable_const _).add (h1.const_mul (2 * c))).add ((h.variance y).1.const_mul _)
  have hgint : ∫ ω, g ω ∂p = ‖a‖ ^ 2 + 2 * c * j a (∫ ω, ζ ω ∂p) + K * c ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p := by
    have h1 : Integrable (fun ω => j a (ζ ω)) p := (j a).integrable_comp hζi
    have hI1 : Integrable (fun ω => 2 * c * j a (ζ ω)) p := h1.const_mul _
    have hI2 : Integrable (fun ω => K * c ^ 2 * ‖ζ ω‖ ^ 2) p := (h.variance y).1.const_mul _
    calc ∫ ω, g ω ∂p = ∫ ω, ((‖a‖ ^ 2 + 2 * c * j a (ζ ω)) + K * c ^ 2 * ‖ζ ω‖ ^ 2) ∂p := rfl
      _ = ∫ ω, (‖a‖ ^ 2 + 2 * c * j a (ζ ω)) ∂p + ∫ ω, K * c ^ 2 * ‖ζ ω‖ ^ 2 ∂p :=
          integral_add ((integrable_const _).add hI1) hI2
      _ = (∫ _ : Ξ, ‖a‖ ^ 2 ∂p + ∫ ω, 2 * c * j a (ζ ω) ∂p) + ∫ ω, K * c ^ 2 * ‖ζ ω‖ ^ 2 ∂p := by
          rw [integral_add (integrable_const _) hI1]
      _ = _ := by
          rw [integral_const_mul, integral_const_mul, (j a).integral_comp_comm hζi]
          simp
  have hgle : ∫ ω, g ω ∂p ≤ (1 - α * Λ / (1 + Λ)) ^ 2 * ‖y - z‖ ^ 2 + K * c ^ 2 * σ ^ 2 := by
    rw [hgint, hζ0, map_zero, mul_zero, add_zero]
    have h2 := (h.variance y).2
    have h3 : K * c ^ 2 * ∫ ω, ‖ζ ω‖ ^ 2 ∂p ≤ K * c ^ 2 * σ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg h.K_nonneg (sq_nonneg c))
    linarith
  calc ∫⁻ ω, ENNReal.ofReal (‖(1 - α) • y + c • (G ω y + A) - z‖ ^ 2) ∂p
      ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂p :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, g ω ∂p) :=
        (ofReal_integral_eq_lintegral_ofReal hgi
          (Filter.Eventually.of_forall fun ω => le_trans (sq_nonneg _) (hpt ω))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hgle

lemma Hyp.measurable_update (h : Hyp p T G K σ) {Λ : ℝ} (hΛ : 0 < Λ) (α c : ℝ) :
    Measurable (Function.uncurry fun (w : E × E) (ω : Ξ) =>
      ENNReal.ofReal (‖(1 - α) • w.1 + c • (G ω w.1 + w.2) - anchorPoint T Λ w.2‖ ^ 2)) := by
  have hG : Measurable (fun q : (E × E) × Ξ => G q.2 q.1.1) :=
    h.meas.comp (measurable_snd.prodMk measurable_fst.fst)
  have hz : Measurable (fun q : (E × E) × Ξ => anchorPoint T Λ q.1.2) :=
    (continuous_anchorPoint h.nonexp hΛ).measurable.comp measurable_fst.snd
  exact ((((measurable_fst.fst.const_smul (1 - α)).add
    ((hG.add measurable_fst.snd).const_smul c)).sub hz).norm.pow_const 2).ennreal_ofReal

lemma lintegral_affine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) :
    ∫⁻ ω, ENNReal.ofReal (r * f ω + b) ∂P =
      ENNReal.ofReal r * ∫⁻ ω, ENNReal.ofReal (f ω) ∂P + ENNReal.ofReal b := by
  have h1 : ∀ ω, ENNReal.ofReal (r * f ω + b) =
      ENNReal.ofReal r * ENNReal.ofReal (f ω) + ENNReal.ofReal b := by
    intro ω
    rw [ENNReal.ofReal_add (mul_nonneg hr (hf0 ω)) hb, ENNReal.ofReal_mul hr]
  simp_rw [h1]
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hf.ennreal_ofReal,
    lintegral_const, measure_univ, mul_one]

lemma Hyp.step_expect (h : Hyp p T G K σ) [IsProbabilityMeasure p] {α Λ : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hΛ : 0 < Λ) (m : ℕ) (W : (ℕ → Ξ) → E × E) (hW : Measurable W)
    (hdep : ∀ ξ ξ' : ℕ → Ξ, (∀ i, i < m → ξ i = ξ' i) → W ξ = W ξ') :
    ∫⁻ ξ, ENNReal.ofReal (‖(1 - α) • (W ξ).1 + (α / (1 + Λ)) • (G (ξ m) (W ξ).1 + (W ξ).2) -
        anchorPoint T Λ (W ξ).2‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - α * Λ / (1 + Λ)) ^ 2) *
        ∫⁻ ξ, ENNReal.ofReal (‖(W ξ).1 - anchorPoint T Λ (W ξ).2‖ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (K * (α / (1 + Λ)) ^ 2 * σ ^ 2) := by
  rw [lintegral_prefix p m W hW hdep _ (h.measurable_update hΛ α (α / (1 + Λ)))]
  have hf : Measurable (fun ξ : ℕ → Ξ => ‖(W ξ).1 - anchorPoint T Λ (W ξ).2‖ ^ 2) :=
    (hW.fst.sub ((continuous_anchorPoint h.nonexp hΛ).measurable.comp hW.snd)).norm.pow_const 2
  calc ∫⁻ ξ, ∫⁻ ω, ENNReal.ofReal (‖(1 - α) • (W ξ).1 + (α / (1 + Λ)) • (G ω (W ξ).1 + (W ξ).2) -
          anchorPoint T Λ (W ξ).2‖ ^ 2) ∂p ∂(Measure.infinitePi fun _ : ℕ => p)
      ≤ ∫⁻ ξ, ENNReal.ofReal ((1 - α * Λ / (1 + Λ)) ^ 2 * ‖(W ξ).1 - anchorPoint T Λ (W ξ).2‖ ^ 2 +
          K * (α / (1 + Λ)) ^ 2 * σ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) :=
        lintegral_mono fun ξ => h.step_inner hα0 hα1 hΛ (W ξ).1 (W ξ).2
    _ = _ := lintegral_affine _ hf (fun _ => sq_nonneg _) (sq_nonneg _)
        (mul_nonneg (mul_nonneg h.K_nonneg (sq_nonneg _)) (sq_nonneg _))

end Step

section Trajectory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ξ : Type*}

def start (N : ℕ → ℕ) (u : ℕ) : ℕ := ∑ v ∈ Finset.range u, N v

noncomputable def kmRun (G : Ξ → E → E) (a c : ℝ) (A : E) (n : ℕ) (ξ : ℕ → Ξ) (y0 : E) : ℕ → E
  | 0 => y0
  | k + 1 => (1 - a) • kmRun G a c A n ξ y0 k + c • (G (ξ (n + k)) (kmRun G a c A n ξ y0 k) + A)

noncomputable def nextStage (G : Ξ → E → E) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (u : ℕ) (ξ : ℕ → Ξ)
    (d : E × E) : E × E :=
  (kmRun G (α u) (α u / (1 + Λ u)) d.2 (start N u) ξ d.1 (N u),
    d.2 + lam (u + 1) • kmRun G (α u) (α u / (1 + Λ u)) d.2 (start N u) ξ d.1 (N u))

noncomputable def stage (G : Ξ → E → E) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (x0 : E) (ξ : ℕ → Ξ) :
    ℕ → E × E
  | 0 => (x0, lam 0 • x0)
  | u + 1 => nextStage G lam Λ α N u ξ (stage G lam Λ α N x0 ξ u)

lemma start_succ (N : ℕ → ℕ) (u : ℕ) : start N (u + 1) = start N u + N u := by
  simp [start, Finset.sum_range_succ]

lemma start_mono (N : ℕ → ℕ) {u v : ℕ} (h : u ≤ v) : start N u ≤ start N v :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma inner_congr (G : Ξ → E → E) (a c : ℝ) (A : E) (n : ℕ) (y0 : E) {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < n + k → ξ i = ξ' i) → kmRun G a c A n ξ y0 k = kmRun G a c A n ξ' y0 k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hξ
    simp only [kmRun]
    rw [ih (fun i hi => hξ i (by omega)), hξ (n + k) (by omega)]

lemma stage_congr (G : Ξ → E → E) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (x0 : E) {ξ ξ' : ℕ → Ξ} :
    ∀ u, (∀ i, i < start N u → ξ i = ξ' i) →
      stage G lam Λ α N x0 ξ u = stage G lam Λ α N x0 ξ' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro hξ
    rw [start_succ] at hξ
    simp only [stage, nextStage]
    rw [ih (fun i hi => hξ i (by omega)),
      inner_congr G _ _ _ _ _ (N u) (fun i hi => hξ i hi)]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]

lemma measurable_inner {G : Ξ → E → E} (hG : Measurable (Function.uncurry G)) (a c : ℝ) (n : ℕ)
    {A Y : (ℕ → Ξ) → E} (hA : Measurable A) (hY : Measurable Y) :
    ∀ k, Measurable (fun ξ => kmRun G a c (A ξ) n ξ (Y ξ) k) := by
  intro k
  induction k with
  | zero => exact hY
  | succ k ih =>
    simp only [kmRun]
    exact (ih.const_smul _).add
      (((hG.comp ((measurable_pi_apply (n + k)).prodMk ih)).add hA).const_smul c)

lemma measurable_stage {G : Ξ → E → E} (hG : Measurable (Function.uncurry G)) (lam Λ α : ℕ → ℝ)
    (N : ℕ → ℕ) (x0 : E) : ∀ u, Measurable (fun ξ => stage G lam Λ α N x0 ξ u) := by
  intro u
  induction u with
  | zero => exact measurable_const
  | succ u ih =>
    simp only [stage, nextStage]
    have hi := measurable_inner hG (α u) (α u / (1 + Λ u)) (start N u) ih.snd ih.fst (N u)
    exact hi.prodMk (ih.snd.add (hi.const_smul _))

end Trajectory

section Stages

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} {T : E → E} {G : Ξ → E → E} {K σ : ℝ}

lemma Hyp.stage_bound (h : Hyp p T G K σ) [IsProbabilityMeasure p] (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ)
    (x0 : E) (u : ℕ) (hα0 : 0 ≤ α u) (hα1 : α u ≤ 1) (hΛ : 0 < Λ u) {I V : ℝ} (hI0 : 0 ≤ I)
    (hV : (1 - α u * Λ u / (1 + Λ u)) ^ 2 * V + K * (α u / (1 + Λ u)) ^ 2 * σ ^ 2 ≤ V)
    (hV0 : 0 ≤ V)
    (hI : ∫⁻ ξ, ENNReal.ofReal (‖(stage G lam Λ α N x0 ξ u).1 -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal I) :
    ∀ k, ∫⁻ ξ, ENNReal.ofReal (‖kmRun G (α u) (α u / (1 + Λ u)) (stage G lam Λ α N x0 ξ u).2
        (start N u) ξ (stage G lam Λ α N x0 ξ u).1 k -
        anchorPoint T (Λ u) (stage G lam Λ α N x0 ξ u).2‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - α u * Λ u / (1 + Λ u)) ^ (2 * k) * I + V) := by
  set ρ := 1 - α u * Λ u / (1 + Λ u)
  have hpos : 0 < 1 + Λ u := by linarith
  have hρ0 : 0 ≤ ρ := by
    have : α u * Λ u / (1 + Λ u) ≤ α u := by
      rw [div_le_iff₀ hpos]; nlinarith
    simp only [ρ]; linarith
  intro k
  induction k with
  | zero =>
    refine le_trans hI (ENNReal.ofReal_le_ofReal ?_)
    simp only [Nat.mul_zero, pow_zero, one_mul]
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
      have hs := stage_congr G lam Λ α N x0 u (fun i hi => hξ i (by omega))
      simp only [W]
      rw [hs, inner_congr G _ _ _ _ _ k hξ]
    have hstep := h.step_expect hα0 hα1 hΛ (start N u + k) W hW hdep
    calc _ = ∫⁻ ξ, ENNReal.ofReal (‖(1 - α u) • (W ξ).1 + (α u / (1 + Λ u)) •
            (G (ξ (start N u + k)) (W ξ).1 + (W ξ).2) - anchorPoint T (Λ u) (W ξ).2‖ ^ 2)
            ∂(Measure.infinitePi fun _ : ℕ => p) := rfl
      _ ≤ _ := hstep
      _ ≤ ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (ρ ^ (2 * k) * I + V) +
            ENNReal.ofReal (K * (α u / (1 + Λ u)) ^ 2 * σ ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (ρ ^ 2 * (ρ ^ (2 * k) * I + V) + K * (α u / (1 + Λ u)) ^ 2 * σ ^ 2) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_add
            (mul_nonneg (sq_nonneg _) (by positivity))
            (mul_nonneg (mul_nonneg h.K_nonneg (sq_nonneg _)) (sq_nonneg _))]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have he : ρ ^ (2 * (k + 1)) = ρ ^ 2 * ρ ^ (2 * k) := by ring
          rw [he]
          nlinarith

end Stages

end OracleTemplate.RecursiveAnchorKm
