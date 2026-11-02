import LongTails.Proofs.LmoTrajectory
import LongTails.Proofs.LmoRecursions
import LongTails.Proofs.NormBallGeometry
import LongTails.Proofs.NormalizedStormMoments

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

noncomputable def err (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (f : Space d → ℝ) (g : Space d → Ω → Space d) (ξ : ℕ → Ω) (k : ℕ) : Space d :=
  (path step α x₁ g ξ (k + 1)).2 - gradient f (path step α x₁ g ξ k).1

omit [MeasurableSpace Ω] in
lemma err_eq (step : Space d → Space d → Space d) (α : ℕ → ℝ) (x₁ : Space d)
    (f : Space d → ℝ) (g : Space d → Ω → Space d) (ξ : ℕ → Ω) (k : ℕ) :
    err step α x₁ f g ξ k =
      (1 - α (k + 1)) • ((path step α x₁ g ξ k).2 - gradient f (path step α x₁ g ξ k).1) +
        α (k + 1) • (g (path step α x₁ g ξ k).1 (ξ k) - gradient f (path step α x₁ g ξ k).1) := by
  simp only [err, path_succ]
  module

lemma young_sq (u v : Space d) {β : ℝ} (hβ : 0 < β) :
    ‖u + v‖ ^ 2 ≤ (1 + β) * ‖u‖ ^ 2 + (1 + 1 / β) * ‖v‖ ^ 2 := by
  open scoped RealInnerProductSpace in
  (
    rw [norm_add_sq_real]
    have hcs : 2 * ⟪u, v⟫ ≤ 2 * (‖u‖ * ‖v‖) := by
      have := real_inner_le_norm u v; linarith
    have hy : 2 * (‖u‖ * ‖v‖) ≤ β * ‖u‖ ^ 2 + 1 / β * ‖v‖ ^ 2 := by
      have h := sq_nonneg (β * ‖u‖ - ‖v‖)
      have e : β * ‖u‖ ^ 2 + 1 / β * ‖v‖ ^ 2 - 2 * (‖u‖ * ‖v‖) = (β * ‖u‖ - ‖v‖) ^ 2 / β := by
        field_simp; ring
      have : 0 ≤ (β * ‖u‖ - ‖v‖) ^ 2 / β := div_nonneg h hβ.le
      linarith
    nlinarith)

lemma momentum_coeffs {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (1 - a) ^ 2 * (1 + a / 2) ≤ 1 - a / 2 ∧ (1 - a) ^ 2 * (1 + 1 / (a / 2)) ≤ 2 / a := by
  constructor
  · nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1)]
  · have e : (1 - a) ^ 2 * (1 + 1 / (a / 2)) = (1 - a) ^ 2 * (a + 2) / a := by field_simp
    rw [e, div_le_div_iff_of_pos_right ha0]
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1)]

variable {N : Seminorm ℝ (Space d)} {L L₂ σ Δ : ℝ} {x₁ : Space d} {f : Space d → ℝ}
  {g : Space d → Ω → Space d} {p : Measure Ω} [IsProbabilityMeasure p]

omit [IsProbabilityMeasure p] in
lemma continuous_gradient_of (H : Problem N L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) :
    Continuous (gradient f) := by
  have hl : LipschitzWith ⟨L₂, hL₂⟩ (gradient f) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm]
      exact H.lipschitz₂ x y
  exact hl.continuous

theorem err_moments_on {K : Set (Space d)} (hK : MeasurableSet K)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ K, Integrable (g x) p)
    (hmean : ∀ x ∈ K, ∫ ω, g x ω ∂p = gradient f x)
    (hvi : ∀ x ∈ K, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hvar : ∀ x ∈ K, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2)
    (hlip₂ : ∀ x ∈ K, ∀ y ∈ K, ‖gradient f x - gradient f y‖ ≤ L₂ * ‖x - y‖) (hL₂ : 0 ≤ L₂)
    {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2)) {α : ℕ → ℝ}
    (hα0 : ∀ k, 0 < α (k + 1)) (hα1 : ∀ k, α (k + 1) ≤ 1) (hαone : α 1 = 1) {δ : ℝ}
    (hmove : ∀ ξ k, ‖(path step α x₁ g ξ (k + 1)).1 - (path step α x₁ g ξ k).1‖ ≤ δ)
    (hpathK : ∀ ξ k, (path step α x₁ g ξ k).1 ∈ K) :
    (∀ k, Integrable (fun ξ => ‖err step α x₁ f g ξ k‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) ∧
      (∫ ξ, ‖err step α x₁ f g ξ 0‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ σ ^ 2 ∧
      ∀ k, (∫ ξ, ‖err step α x₁ f g ξ (k + 1)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
        (1 - α (k + 2) / 2) * (∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) +
          2 * L₂ ^ 2 * δ ^ 2 / α (k + 2) + α (k + 2) ^ 2 * σ ^ 2 := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hgc := measurable_gradient_space f
  have hpath := measurable_path hstep α x₁ hgm
  let U : Space d × Space d → Space d := fun y => y.2 - gradient f y.1
  have hU : Measurable U := measurable_snd.sub (hgc.comp measurable_fst)
  let W : ℝ → Space d × Space d → Ω → Space d := fun a y ω =>
    K.indicator (fun x => a • (g x ω - gradient f x)) y.1
  have hW : ∀ a, Measurable (Function.uncurry (W a)) := by
    intro a
    have h1 : Measurable (fun z : (Space d × Space d) × Ω => g z.1.1 z.2) :=
      hgm.comp (measurable_fst.fst.prodMk measurable_snd)
    have h2 : Measurable (fun z : (Space d × Space d) × Ω => a • (g z.1.1 z.2 - gradient f z.1.1)) :=
      (h1.sub (hgc.comp measurable_fst.fst)).const_smul a
    exact h2.indicator (hK.preimage measurable_fst.fst)
  have hWin : ∀ a y ω, y.1 ∈ K → W a y ω = a • (g y.1 ω - gradient f y.1) :=
    fun a y ω hy => Set.indicator_of_mem hy _
  have hWout : ∀ a y ω, y.1 ∉ K → W a y ω = 0 :=
    fun a y ω hy => Set.indicator_of_notMem hy _
  have hWi : ∀ a y, Integrable (W a y) p := by
    intro a y
    by_cases hy : y.1 ∈ K
    · rw [show W a y = fun ω => a • (g y.1 ω - gradient f y.1) from funext fun ω => hWin a y ω hy]
      exact ((hgi y.1 hy).sub (integrable_const _)).smul a
    · rw [show W a y = fun _ => 0 from funext fun ω => hWout a y ω hy]
      exact integrable_zero _ _ _
  have hW0 : ∀ a y, ∫ ω, W a y ω ∂p = 0 := by
    intro a y
    by_cases hy : y.1 ∈ K
    · simp only [hWin a y _ hy]
      rw [integral_smul, integral_sub (hgi y.1 hy) (integrable_const _), hmean y.1 hy]
      simp
    · simp only [hWout a y _ hy, integral_zero]
  have hW2 : ∀ a y, Integrable (fun ω => ‖W a y ω‖ ^ 2) p := by
    intro a y
    by_cases hy : y.1 ∈ K
    · simp only [hWin a y _ hy, norm_smul, mul_pow]
      exact (hvi y.1 hy).const_mul _
    · simp only [hWout a y _ hy, norm_zero]
      exact integrable_const _
  have hWle : ∀ a y, ∫ ω, ‖W a y ω‖ ^ 2 ∂p ≤ a ^ 2 * σ ^ 2 := by
    intro a y
    by_cases hy : y.1 ∈ K
    · simp only [hWin a y _ hy, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hvar y.1 hy) (sq_nonneg a)
    · simp only [hWout a y _ hy, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_const, smul_zero]
      positivity
  have hdep : ∀ k, ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) →
      path step α x₁ g ξ k = path step α x₁ g ξ' k :=
    fun k ξ ξ' h => path_congr step α x₁ g k h
  have hcomb : ∀ k ξ, err step α x₁ f g ξ k =
      (1 - α (k + 1)) • U (path step α x₁ g ξ k) + W (α (k + 1)) (path step α x₁ g ξ k) (ξ k) := by
    intro k ξ
    rw [err_eq, hWin _ _ _ (hpathK ξ k)]
  have hstepk : ∀ k, Integrable (fun ξ => ‖U (path step α x₁ g ξ k)‖ ^ 2) P →
      Integrable (fun ξ => ‖err step α x₁ f g ξ k‖ ^ 2) P ∧
        ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P ≤
          (1 - α (k + 1)) ^ 2 * ∫ ξ, ‖U (path step α x₁ g ξ k)‖ ^ 2 ∂P + α (k + 1) ^ 2 * σ ^ 2 := by
    intro k hU2
    have h := NormalizedStorm.fresh_step_sq p k (fun ξ => path step α x₁ g ξ k) (hpath k)
      (hdep k) U hU (W (α (k + 1))) (hW _) (hWi _) (hW0 _) (hW2 _) (fun _ => α (k + 1) ^ 2 * σ ^ 2)
      (hWle _) (integrable_const _) hU2 (1 - α (k + 1))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    simp_rw [hcomb k]
    exact h
  have hU_succ : ∀ k ξ, U (path step α x₁ g ξ (k + 1)) =
      err step α x₁ f g ξ k +
        (gradient f (path step α x₁ g ξ k).1 - gradient f (path step α x₁ g ξ (k + 1)).1) := by
    intro k ξ
    simp only [U, err]
    rw [sub_add_sub_cancel]
  have hgrad_move : ∀ k ξ, ‖gradient f (path step α x₁ g ξ k).1 -
      gradient f (path step α x₁ g ξ (k + 1)).1‖ ≤ L₂ * δ := by
    intro k ξ
    calc _ ≤ L₂ * ‖(path step α x₁ g ξ k).1 - (path step α x₁ g ξ (k + 1)).1‖ :=
          hlip₂ _ (hpathK ξ k) _ (hpathK ξ (k + 1))
      _ ≤ L₂ * δ := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hmove ξ k) hL₂
  have herr_meas : ∀ k, Measurable (fun ξ => err step α x₁ f g ξ k) := by
    intro k
    exact (hpath (k + 1)).snd.sub (hgc.comp (hpath k).fst)
  have hU2_succ : ∀ k, Integrable (fun ξ => ‖err step α x₁ f g ξ k‖ ^ 2) P →
      Integrable (fun ξ => ‖U (path step α x₁ g ξ (k + 1))‖ ^ 2) P := by
    intro k hk
    refine Integrable.mono' ((hk.const_mul 2).add (integrable_const (2 * (L₂ * δ) ^ 2))) ?_ ?_
    · exact ((hU.comp (hpath (k + 1))).norm.pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hU_succ]
      have h1 := NormalizedStorm.sq_norm_add_le (err step α x₁ f g ξ k)
        (gradient f (path step α x₁ g ξ k).1 - gradient f (path step α x₁ g ξ (k + 1)).1)
      have h2 := hgrad_move k ξ
      have h3 : ‖gradient f (path step α x₁ g ξ k).1 - gradient f (path step α x₁ g ξ (k + 1)).1‖ ^ 2
          ≤ (L₂ * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      simp only [Pi.add_apply]
      linarith
  have hint : ∀ k, Integrable (fun ξ => ‖err step α x₁ f g ξ k‖ ^ 2) P := by
    intro k
    induction k with
    | zero =>
        refine (hstepk 0 ?_).1
        simp only [U, path_zero]
        exact integrable_const _
    | succ k ih => exact (hstepk (k + 1) (hU2_succ k ih)).1
  refine ⟨hint, ?_, ?_⟩
  · have h := (hstepk 0 (by simp only [U, path_zero]; exact integrable_const _)).2
    rw [hαone] at h
    simpa using h
  · intro k
    have h := (hstepk (k + 1) (hU2_succ k (hint k))).2
    set a := α (k + 2)
    have ha0 : 0 < a := hα0 (k + 1)
    have ha1 : a ≤ 1 := hα1 (k + 1)
    obtain ⟨hc1, hc2⟩ := momentum_coeffs ha0 ha1
    have hyoung : ∀ ξ, ‖U (path step α x₁ g ξ (k + 1))‖ ^ 2 ≤
        (1 + a / 2) * ‖err step α x₁ f g ξ k‖ ^ 2 + (1 + 1 / (a / 2)) * (L₂ * δ) ^ 2 := by
      intro ξ
      rw [hU_succ]
      have hy := young_sq (err step α x₁ f g ξ k)
        (gradient f (path step α x₁ g ξ k).1 - gradient f (path step α x₁ g ξ (k + 1)).1)
        (by positivity : 0 < a / 2)
      have h3 : ‖gradient f (path step α x₁ g ξ k).1 - gradient f (path step α x₁ g ξ (k + 1)).1‖ ^ 2
          ≤ (L₂ * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgrad_move k ξ) 2
      have : 0 ≤ 1 + 1 / (a / 2) := by positivity
      nlinarith
    have hmono : ∫ ξ, ‖U (path step α x₁ g ξ (k + 1))‖ ^ 2 ∂P ≤
        (1 + a / 2) * ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P + (1 + 1 / (a / 2)) * (L₂ * δ) ^ 2 := by
      have e : ∫ ξ, ((1 + a / 2) * ‖err step α x₁ f g ξ k‖ ^ 2 + (1 + 1 / (a / 2)) * (L₂ * δ) ^ 2) ∂P
          = (1 + a / 2) * ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P + (1 + 1 / (a / 2)) * (L₂ * δ) ^ 2 := by
        rw [integral_add ((hint k).const_mul _) (integrable_const _), integral_const_mul,
          integral_const]
        simp
      rw [← e]
      exact integral_mono (hU2_succ k (hint k)) (((hint k).const_mul _).add (integrable_const _))
        hyoung
    have hsq : 0 ≤ (1 - a) ^ 2 := sq_nonneg _
    have hI : 0 ≤ ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P := integral_nonneg fun _ => by positivity
    have e1 : (1 - α (k + 1 + 1)) = 1 - a := rfl
    rw [e1] at h
    calc ∫ ξ, ‖err step α x₁ f g ξ (k + 1)‖ ^ 2 ∂P
        ≤ (1 - a) ^ 2 * ∫ ξ, ‖U (path step α x₁ g ξ (k + 1))‖ ^ 2 ∂P + a ^ 2 * σ ^ 2 := h
      _ ≤ (1 - a) ^ 2 * ((1 + a / 2) * ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P +
            (1 + 1 / (a / 2)) * (L₂ * δ) ^ 2) + a ^ 2 * σ ^ 2 := by gcongr
      _ = (1 - a) ^ 2 * (1 + a / 2) * ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P +
            (1 - a) ^ 2 * (1 + 1 / (a / 2)) * (L₂ * δ) ^ 2 + a ^ 2 * σ ^ 2 := by ring
      _ ≤ (1 - a / 2) * ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P + 2 / a * (L₂ * δ) ^ 2 +
            a ^ 2 * σ ^ 2 := by
          gcongr
      _ = (1 - a / 2) * ∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P + 2 * L₂ ^ 2 * δ ^ 2 / a +
            a ^ 2 * σ ^ 2 := by
          field_simp

theorem err_moments (H : Problem N L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂)
    {step : Space d → Space d → Space d}
    (hstep : Measurable (fun z : Space d × Space d => step z.1 z.2)) {α : ℕ → ℝ}
    (hα0 : ∀ k, 0 < α (k + 1)) (hα1 : ∀ k, α (k + 1) ≤ 1) (hαone : α 1 = 1) {δ : ℝ}
    (hmove : ∀ ξ k, ‖(path step α x₁ g ξ (k + 1)).1 - (path step α x₁ g ξ k).1‖ ≤ δ) :
    (∀ k, Integrable (fun ξ => ‖err step α x₁ f g ξ k‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) ∧
      (∫ ξ, ‖err step α x₁ f g ξ 0‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ σ ^ 2 ∧
      ∀ k, (∫ ξ, ‖err step α x₁ f g ξ (k + 1)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
        (1 - α (k + 2) / 2) * (∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) +
          2 * L₂ ^ 2 * δ ^ 2 / α (k + 2) + α (k + 2) ^ 2 * σ ^ 2 := by
  exact err_moments_on MeasurableSet.univ H.measurable (fun x _ => H.integrable x)
    (fun x _ => H.unbiased x) (fun x _ => H.variance_integrable x) (fun x _ => H.variance x)
    (fun x _ y _ => H.lipschitz₂ x y) hL₂ hstep hα0 hα1 hαone hmove (fun _ _ => Set.mem_univ _)

lemma sqrt_pow_mul_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    Real.sqrt (a ^ k * b ^ 2) = Real.sqrt a ^ k * b := by
  rw [Real.sqrt_mul (pow_nonneg ha k), Real.sqrt_sq hb]
  congr 1
  rw [Real.sqrt_eq_iff_mul_self_eq (pow_nonneg ha k) (pow_nonneg (Real.sqrt_nonneg a) k),
    ← mul_pow, Real.mul_self_sqrt ha]

lemma constant_err_bound {u : ℕ → ℝ} {α σ η₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hσ : 0 ≤ σ)
    (hη₀ : 0 ≤ η₀) (h0 : u 0 ≤ σ ^ 2)
    (h : ∀ k, u (k + 1) ≤ (1 - α / 2) * u k + 2 * η₀ ^ 2 / α + α ^ 2 * σ ^ 2) :
    ∀ k, u k ≤ 4 * η₀ ^ 2 / α ^ 2 + (2 * α + (1 - α / 2) ^ k) * σ ^ 2 ∧
      Real.sqrt (u k) ≤ 2 * η₀ / α + Real.sqrt (2 * α) * σ + Real.sqrt (1 - α / 2) ^ k * σ := by
  have hrec := geometric_recursion (u := u) (β := α / 2) (η := 2 * η₀ ^ 2 / α + α ^ 2 * σ ^ 2)
    (by positivity) (by linarith) (by positivity) (fun k => by
      have := h k; linarith)
  set q := Real.sqrt (1 - α / 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  have hb : ∀ k, u k ≤ (2 * η₀ / α) ^ 2 + 2 * α * σ ^ 2 + (1 - α / 2) ^ k * σ ^ 2 := by
      intro k
      have h1 := hrec k
      have e : (2 * η₀ ^ 2 / α + α ^ 2 * σ ^ 2) / (α / 2) = (2 * η₀ / α) ^ 2 + 2 * α * σ ^ 2 := by
        field_simp
      rw [e] at h1
      have : (1 - α / 2) ^ k * u 0 ≤ (1 - α / 2) ^ k * σ ^ 2 :=
        mul_le_mul_of_nonneg_left h0 (pow_nonneg (by linarith) k)
      linarith
  have hk : ∀ k, Real.sqrt (u k) ≤ 2 * η₀ / α + Real.sqrt (2 * α) * σ + q ^ k * σ := by
    intro k
    calc Real.sqrt (u k) ≤ Real.sqrt ((2 * η₀ / α) ^ 2 + 2 * α * σ ^ 2 + (1 - α / 2) ^ k * σ ^ 2) :=
          Real.sqrt_le_sqrt (hb k)
      _ ≤ Real.sqrt ((2 * η₀ / α) ^ 2) + Real.sqrt (2 * α * σ ^ 2) +
            Real.sqrt ((1 - α / 2) ^ k * σ ^ 2) :=
          sqrt_add3_le (by positivity) (by positivity) (mul_nonneg (pow_nonneg (by linarith) k) (sq_nonneg σ))
      _ = 2 * η₀ / α + Real.sqrt (2 * α) * σ + q ^ k * σ := by
          rw [Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hσ,
            sqrt_pow_mul_sq (by linarith) hσ]
  intro k
  refine ⟨?_, hk k⟩
  have e : (2 * η₀ / α) ^ 2 + 2 * α * σ ^ 2 + (1 - α / 2) ^ k * σ ^ 2 =
      4 * η₀ ^ 2 / α ^ 2 + (2 * α + (1 - α / 2) ^ k) * σ ^ 2 := by
    field_simp; ring
  rw [← e]; exact hb k

lemma constant_err_sum {u : ℕ → ℝ} {α σ η₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hσ : 0 ≤ σ)
    (hη₀ : 0 ≤ η₀) (h0 : u 0 ≤ σ ^ 2)
    (h : ∀ k, u (k + 1) ≤ (1 - α / 2) * u k + 2 * η₀ ^ 2 / α + α ^ 2 * σ ^ 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.sqrt (u k) ≤
      n * (2 * η₀ / α + Real.sqrt (2 * α) * σ) + 4 * σ / α := by
  have hk := fun k => (constant_err_bound hα hα1 hσ hη₀ h0 h k).2
  set q := Real.sqrt (1 - α / 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hk k
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul] at hsum
  have hg := geom_sum_le hq0 hq1 n
  have hinv := inv_one_sub_sqrt_le hα hα1
  have : (∑ k ∈ Finset.range n, q ^ k) * σ ≤ 4 / α * σ :=
    mul_le_mul_of_nonneg_right (hg.trans hinv) hσ
  have e : 4 / α * σ = 4 * σ / α := by ring
  linarith

lemma vanishing_err_bound {u : ℕ → ℝ} {σ η₀ γ : ℝ} {n : ℕ}
    (hγn : γ ^ 2 * ((n : ℝ) * Real.sqrt n) ≤ 1) (hu : ∀ k, 0 ≤ u k) (h0 : u 0 ≤ σ ^ 2)
    (h : ∀ k, u (k + 1) ≤ (1 - 1 / Real.sqrt ((k : ℝ) + 2) / 2) * u k +
      2 * (γ * η₀) ^ 2 / (1 / Real.sqrt ((k : ℝ) + 2)) + (1 / Real.sqrt ((k : ℝ) + 2)) ^ 2 * σ ^ 2) :
    ∀ k, k < n → u k ≤ (4 * σ ^ 2 + 8 * η₀ ^ 2) / Real.sqrt ((k : ℝ) + 1) := by
  set c := σ ^ 2 + 2 * η₀ ^ 2
  have hc : 0 ≤ c := by positivity
  have hb := vanishing_recursion_lt (n := n) hc hu (by simp only [c]; nlinarith [sq_nonneg η₀])
    (fun k hk => by
      have h1 := h k
      set s := Real.sqrt ((k : ℝ) + 2)
      have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have hs2 : s ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
      have hkn : (k : ℝ) + 2 ≤ n := by exact_mod_cast hk
      have hmono : ((k : ℝ) + 2) * s ≤ (n : ℝ) * Real.sqrt n :=
        mul_le_mul hkn (Real.sqrt_le_sqrt hkn) hs0.le (by positivity)
      have hγs : γ ^ 2 * (((k : ℝ) + 2) * s) ≤ 1 :=
        (mul_le_mul_of_nonneg_left hmono (sq_nonneg γ)).trans hγn
      have e1 : 1 - 1 / s / 2 = 1 - 1 / (2 * s) := by ring
      have e2 : 2 * (γ * η₀) ^ 2 / (1 / s) + (1 / s) ^ 2 * σ ^ 2 =
          2 * η₀ ^ 2 * (γ ^ 2 * (((k : ℝ) + 2) * s)) / ((k : ℝ) + 2) + σ ^ 2 / ((k : ℝ) + 2) := by
        rw [← hs2]; field_simp
      rw [e1, add_assoc, e2] at h1
      have h3 : 2 * η₀ ^ 2 * (γ ^ 2 * (((k : ℝ) + 2) * s)) / ((k : ℝ) + 2) ≤
          2 * η₀ ^ 2 / ((k : ℝ) + 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc 2 * η₀ ^ 2 * (γ ^ 2 * (((k : ℝ) + 2) * s)) ≤ 2 * η₀ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hγs (by positivity)
          _ = 2 * η₀ ^ 2 := mul_one _
      have e3 : 2 * η₀ ^ 2 / ((k : ℝ) + 2) + σ ^ 2 / ((k : ℝ) + 2) = c / ((k : ℝ) + 2) := by
        simp only [c]; ring
      linarith)
  intro k hk
  have := hb k hk
  have e : 4 * c = 4 * σ ^ 2 + 8 * η₀ ^ 2 := by simp only [c]; ring
  rwa [e] at this

lemma vanishing_err_sum {u : ℕ → ℝ} {σ η₀ γ : ℝ} {n : ℕ}
    (hγn : γ ^ 2 * ((n : ℝ) * Real.sqrt n) ≤ 1) (hu : ∀ k, 0 ≤ u k) (h0 : u 0 ≤ σ ^ 2)
    (h : ∀ k, u (k + 1) ≤ (1 - 1 / Real.sqrt ((k : ℝ) + 2) / 2) * u k +
      2 * (γ * η₀) ^ 2 / (1 / Real.sqrt ((k : ℝ) + 2)) + (1 / Real.sqrt ((k : ℝ) + 2)) ^ 2 * σ ^ 2) :
    ∑ k ∈ Finset.range n, Real.sqrt (u k) ≤
      Real.sqrt (4 * σ ^ 2 + 8 * η₀ ^ 2) * (4 / 3 * (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hb := vanishing_err_bound hγn hu h0 h
  have hk : ∀ k, k < n → Real.sqrt (u k) ≤ Real.sqrt (4 * σ ^ 2 + 8 * η₀ ^ 2) *
      (1 / ((k : ℝ) + 1) ^ (1 / 4 : ℝ)) := by
    intro k hkn
    have h1 := hb k hkn
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hq : Real.sqrt (Real.sqrt ((k : ℝ) + 1)) = ((k : ℝ) + 1) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hk1.le]; norm_num
    calc Real.sqrt (u k) ≤ Real.sqrt ((4 * σ ^ 2 + 8 * η₀ ^ 2) / Real.sqrt ((k : ℝ) + 1)) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (4 * σ ^ 2 + 8 * η₀ ^ 2) * (1 / ((k : ℝ) + 1) ^ (1 / 4 : ℝ)) := by
          rw [Real.sqrt_div' _ (Real.sqrt_nonneg _), hq]
          ring
  have hsum := Finset.sum_le_sum fun k (hk' : k ∈ Finset.range n) => hk k (Finset.mem_range.mp hk')
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left (sum_quarter_le n) (Real.sqrt_nonneg _))

lemma integrable_norm_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {e : α → Space d} (hm : Measurable e) (h : Integrable (fun a => ‖e a‖ ^ 2) μ) :
    Integrable (fun a => ‖e a‖) μ := by
  refine Integrable.mono' (h.add (integrable_const 1)) hm.norm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun a => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply]
  nlinarith [norm_nonneg (e a), sq_nonneg (‖e a‖ - 1)]

lemma vanishing_momentum_props :
    (∀ k, 0 < vanishingMomentum (k + 1)) ∧ (∀ k, vanishingMomentum (k + 1) ≤ 1) ∧
      vanishingMomentum 1 = 1 ∧ ∀ k : ℕ, vanishingMomentum (k + 2) = 1 / Real.sqrt ((k : ℝ) + 2) := by
  refine ⟨fun k => ?_, fun k => ?_, by simp [vanishingMomentum], fun k => ?_⟩
  · simp only [vanishingMomentum]; positivity
  · simp only [vanishingMomentum]
    rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by simp)
    rwa [Real.sqrt_one] at this
  · simp only [vanishingMomentum]; push_cast; ring_nf

attribute [local simp] err

end OracleTemplate.NormBallLMO
