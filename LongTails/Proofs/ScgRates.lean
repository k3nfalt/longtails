import LongTails.Proofs.LmoDescent
import LongTails.Proofs.LmoErrorBounds
import LongTails.Proofs.LmoOutput
import LongTails.Setups.ScgConstant
import LongTails.Setups.ScgVanishing

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {N : Seminorm ℝ (Space d)} {L L₂ σ Δ ρ D₂ : ℝ} {x₁ : Space d} {f : Space d → ℝ}
  {g : Space d → Ω → Space d} {p : Measure Ω} [IsProbabilityMeasure p] {lmo : Space d → Space d}

omit [MeasurableSpace Ω] in
lemma scg_path_feasible (hlmo : IsBallLMO N ρ lmo) (hx₁ : N x₁ ≤ ρ) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (α : ℕ → ℝ) (ξ : ℕ → Ω) :
    ∀ k, N (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1 ≤ ρ := by
  intro k
  induction k with
  | zero => exact hx₁
  | succ k ih =>
      rw [path_succ]
      exact scg_feasible hγ0 hγ1 ih (hlmo.feasible _)

omit [MeasurableSpace Ω] in
lemma scg_move (hlmo : IsBallLMO N ρ lmo) (hx₁ : N x₁ ≤ ρ)
    (hD₂ : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖x - y‖ ≤ D₂) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (α : ℕ → ℝ) (ξ : ℕ → Ω) (k : ℕ) :
    ‖(path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ (k + 1)).1 -
      (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1‖ ≤ γ * D₂ := by
  have hk := scg_path_feasible (g := g) hlmo hx₁ hγ0 hγ1 α ξ k
  rw [path_succ]
  set x := (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1
  set m := α (k + 1) • g x (ξ k) +
    (1 - α (k + 1)) • (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).2
  have e : (1 - γ) • x + γ • lmo m - x = γ • (lmo m - x) := by module
  simp only
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
  exact mul_le_mul_of_nonneg_left (hD₂ _ _ (hlmo.feasible m) hk) hγ0

theorem scg_template (H : ConstrainedProblem N ρ L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) (hL : 0 ≤ L)
    (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hD₂ : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖x - y‖ ≤ D₂) (hx₁ : N x₁ ≤ ρ) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) {α : ℕ → ℝ} (hα0 : ∀ k, 0 < α (k + 1)) (hα1 : ∀ k, α (k + 1) ≤ 1)
    (hαone : α 1 = 1) (n : ℕ) {u : Space d} (hu : N u ≤ ρ) :
    (∀ k, Integrable (fun ξ => ⟪gradient f (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1,
        (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1 - u⟫)
        (Measure.infinitePi fun _ : ℕ => p)) ∧
    (∀ k ξ, |⟪gradient f (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1,
        (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1 - u⟫| ≤
        (‖gradient f x₁‖ + L₂ * D₂) * D₂) ∧
    γ * ∑ k ∈ Finset.range n, ∫ ξ, ⟪gradient f (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1,
        (path (fun x m => (1 - γ) • x + γ • lmo m) α x₁ g ξ k).1 - u⟫
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      Δ + γ * D₂ * ∑ k ∈ Finset.range n,
          Real.sqrt (∫ ξ, ‖err (fun x m => (1 - γ) • x + γ • lmo m) α x₁ f g ξ k‖ ^ 2
            ∂(Measure.infinitePi fun _ : ℕ => p)) + n * (2 * L * ρ ^ 2 * γ ^ 2) := by
  open scoped RealInnerProductSpace in
  (
    set P := Measure.infinitePi fun _ : ℕ => p
    set step := fun (x m : Space d) => (1 - γ) • x + γ • lmo m
    have hstep : Measurable (fun z : Space d × Space d => step z.1 z.2) :=
      (measurable_fst.const_smul (1 - γ)).add ((hlmo.measurable.comp measurable_snd).const_smul γ)
    have hgc := measurable_gradient_space f
    have hpath := measurable_path hstep α x₁ H.measurable
    have hfeas := scg_path_feasible (g := g) hlmo hx₁ hγ0 hγ1 α
    have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ x₁ x₁ hx₁ hx₁)
    have hbound : ∀ k ξ, |⟪gradient f (path step α x₁ g ξ k).1, (path step α x₁ g ξ k).1 - u⟫| ≤
        (‖gradient f x₁‖ + L₂ * D₂) * D₂ := by
      intro k ξ
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hx := hfeas ξ k
      have h1 : ‖gradient f (path step α x₁ g ξ k).1‖ ≤ ‖gradient f x₁‖ + L₂ * D₂ := by
        calc ‖gradient f (path step α x₁ g ξ k).1‖
            ≤ ‖gradient f x₁‖ + ‖gradient f (path step α x₁ g ξ k).1 - gradient f x₁‖ := by
              have := norm_add_le (gradient f x₁) (gradient f (path step α x₁ g ξ k).1 - gradient f x₁)
              rwa [add_sub_cancel] at this
          _ ≤ ‖gradient f x₁‖ + L₂ * D₂ := by
              gcongr
              exact (H.lipschitz₂ _ _ hx hx₁).trans (mul_le_mul_of_nonneg_left (hD₂ _ _ hx hx₁) hL₂)
      exact mul_le_mul h1 (hD₂ _ _ hx hu) (norm_nonneg _) (by positivity)
    have hint : ∀ k, Integrable (fun ξ => ⟪gradient f (path step α x₁ g ξ k).1,
        (path step α x₁ g ξ k).1 - u⟫) P := by
      intro k
      have hm : Measurable (fun ξ => ⟪gradient f (path step α x₁ g ξ k).1,
          (path step α x₁ g ξ k).1 - u⟫) :=
        Measurable.inner (hgc.comp (hpath k).fst) ((hpath k).fst.sub measurable_const)
      refine Integrable.of_bound hm.aestronglyMeasurable ((‖gradient f x₁‖ + L₂ * D₂) * D₂)
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs]; exact hbound k ξ
    refine ⟨hint, hbound, ?_⟩
    obtain ⟨hsq, -, -⟩ := err_moments_on (K := {x | N x ≤ ρ}) (isClosed_le (seminorm_continuous N) continuous_const).measurableSet
      H.measurable (fun x hx => H.integrable x hx) (fun x hx => H.unbiased x hx)
      (fun x hx => H.variance_integrable x hx) (fun x hx => H.variance x hx)
      (fun x hx y hy => H.lipschitz₂ x y hx hy) hL₂ hstep hα0 hα1 hαone (δ := γ * D₂)
      (fun ξ k => scg_move hlmo hx₁ hD₂ hγ0 hγ1 α ξ k) (fun ξ k => hfeas ξ k)
    have herr_meas : ∀ k, Measurable (fun ξ => err step α x₁ f g ξ k) := fun k =>
      (hpath (k + 1)).snd.sub (hgc.comp (hpath k).fst)
    have herr_int : ∀ k, Integrable (fun ξ => ‖err step α x₁ f g ξ k‖) P := fun k =>
      integrable_norm_of_sq (herr_meas k) (hsq k)
    obtain ⟨fmin, hfmin, hgap⟩ := H.lower
    have hpw : ∀ ξ, γ * ∑ k ∈ Finset.range n, ⟪gradient f (path step α x₁ g ξ k).1,
        (path step α x₁ g ξ k).1 - u⟫ ≤
        Δ + γ * D₂ * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖ + n * (2 * L * ρ ^ 2 * γ ^ 2) := by
      intro ξ
      have hk : ∀ k, γ * ⟪gradient f (path step α x₁ g ξ k).1, (path step α x₁ g ξ k).1 - u⟫ ≤
          f (path step α x₁ g ξ k).1 - f (path step α x₁ g ξ (k + 1)).1 +
            γ * D₂ * ‖err step α x₁ f g ξ k‖ + 2 * L * ρ ^ 2 * γ ^ 2 := by
        intro k
        have h := scg_step (f := f) hdef hρ hlmo hD₂ H.differentiable H.lipschitz hL hγ0 hγ1 (hfeas ξ k)
          (path step α x₁ g ξ (k + 1)).2 hu
        have e : (path step α x₁ g ξ (k + 1)).1 =
            (1 - γ) • (path step α x₁ g ξ k).1 + γ • lmo (path step α x₁ g ξ (k + 1)).2 := by
          rw [path_succ]
        rw [← e] at h
        simpa only [err] using h
      have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hk k
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have h0 : (path step α x₁ g ξ 0).1 = x₁ := rfl
      rw [h0] at hsum
      have := hfmin _ (hfeas ξ n)
      linarith
    have hlhs : ∫ ξ, γ * ∑ k ∈ Finset.range n, ⟪gradient f (path step α x₁ g ξ k).1,
        (path step α x₁ g ξ k).1 - u⟫ ∂P =
        γ * ∑ k ∈ Finset.range n, ∫ ξ, ⟪gradient f (path step α x₁ g ξ k).1,
          (path step α x₁ g ξ k).1 - u⟫ ∂P := by
      rw [integral_const_mul, integral_finsetSum _ fun k _ => hint k]
    have hS : Integrable (fun ξ => ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖) P :=
      integrable_finsetSum _ fun k _ => herr_int k
    have hrint : Integrable (fun ξ => Δ + γ * D₂ * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖ +
        n * (2 * L * ρ ^ 2 * γ ^ 2)) P :=
      ((integrable_const _).add (hS.const_mul _)).add (integrable_const _)
    have hrhs : ∫ ξ, (Δ + γ * D₂ * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖ +
        n * (2 * L * ρ ^ 2 * γ ^ 2)) ∂P =
        Δ + γ * D₂ * ∑ k ∈ Finset.range n, ∫ ξ, ‖err step α x₁ f g ξ k‖ ∂P +
          n * (2 * L * ρ ^ 2 * γ ^ 2) := by
      rw [integral_add (f := fun ξ => Δ + γ * D₂ * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖)
        (g := fun _ => (n : ℝ) * (2 * L * ρ ^ 2 * γ ^ 2))
        ((integrable_const _).add (hS.const_mul _)) (integrable_const _)]
      rw [integral_add (f := fun _ => Δ)
        (g := fun ξ => γ * D₂ * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖)
        (integrable_const _) (hS.const_mul _)]
      rw [integral_const_mul, integral_finsetSum _ fun k _ => herr_int k]
      simp
    have hmono := integral_mono ((integrable_finsetSum _ fun k _ => hint k).const_mul _) hrint hpw
    rw [hlhs, hrhs] at hmono
    have hjensen : ∀ k, ∫ ξ, ‖err step α x₁ f g ξ k‖ ∂P ≤
        Real.sqrt (∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P) := fun k =>
      NormalizedStorm.integral_norm_le_sqrt (herr_meas k).aestronglyMeasurable (hsq k)
    have hcoef : 0 ≤ γ * D₂ := mul_nonneg hγ0 hD₂0
    have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hjensen k) hcoef
    linarith)

lemma scg_constant_algebra {E Δ ρ D₂ L L₂ σ α s r : ℝ} (hs : 1 ≤ s) (hα : 0 < α)
    (hσ : 0 ≤ σ) (hD : 0 ≤ D₂)
    (h : 1 / s * E ≤ Δ + 1 / s * D₂ * (s ^ 2 * (2 * (L₂ * (1 / s * D₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (2 * L * ρ ^ 2 * (1 / s) ^ 2)) :
    1 / s ^ 2 * E ≤ (Δ + 2 * L * ρ ^ 2 + (2 * L₂ * D₂ ^ 2 + 4 * D₂ * σ) / α) / s + D₂ * r * σ := by
  have hs0 : 0 < s := by linarith
  have hE : E ≤ s * (Δ + 1 / s * D₂ * (s ^ 2 * (2 * (L₂ * (1 / s * D₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (2 * L * ρ ^ 2 * (1 / s) ^ 2)) := by
    have := mul_le_mul_of_nonneg_left h hs0.le
    calc E = s * (1 / s * E) := by field_simp
      _ ≤ _ := this
  have key : 1 / s ^ 2 * (s * (Δ + 1 / s * D₂ * (s ^ 2 * (2 * (L₂ * (1 / s * D₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (2 * L * ρ ^ 2 * (1 / s) ^ 2))) =
      (Δ + 2 * L * ρ ^ 2 + 2 * L₂ * D₂ ^ 2 / α) / s + D₂ * r * σ + 4 * D₂ * σ / α / s ^ 2 := by
    field_simp
    ring
  have hfin : 4 * D₂ * σ / α / s ^ 2 ≤ 4 * D₂ * σ / α / s := by
    apply div_le_div_of_nonneg_left (by positivity) hs0
    nlinarith
  have e2 : (Δ + 2 * L * ρ ^ 2 + (2 * L₂ * D₂ ^ 2 + 4 * D₂ * σ) / α) / s =
      (Δ + 2 * L * ρ ^ 2 + 2 * L₂ * D₂ ^ 2 / α) / s + 4 * D₂ * σ / α / s := by
    field_simp; ring
  calc 1 / s ^ 2 * E ≤ 1 / s ^ 2 * (s * (Δ + 1 / s * D₂ * (s ^ 2 * (2 * (L₂ * (1 / s * D₂)) / α +
      r * σ) + 4 * σ / α) + s ^ 2 * (2 * L * ρ ^ 2 * (1 / s) ^ 2))) := by gcongr
    _ = _ := key
    _ ≤ _ := by rw [e2]; linarith

theorem scg_constant_rate (H : ConstrainedProblem N ρ L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) (hL : 0 ≤ L)
    (hσ : 0 ≤ σ) (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hD₂ : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖x - y‖ ≤ D₂) (hx₁ : N x₁ ≤ ρ) {α₀ : ℝ}
    (hα0 : 0 < α₀) (hα1 : α₀ < 1) (T : ℕ) {u : Space d} (hu : N u ≤ ρ) :
    1 / ((T : ℝ) + 1) * ∑ k ∈ Finset.range (T + 1),
        ∫ ξ, ⟪gradient f (path (fun x m => (1 - 1 / Real.sqrt ((T : ℝ) + 1)) • x +
            (1 / Real.sqrt ((T : ℝ) + 1)) • lmo m) (constantMomentum α₀) x₁ g ξ k).1,
          (path (fun x m => (1 - 1 / Real.sqrt ((T : ℝ) + 1)) • x +
            (1 / Real.sqrt ((T : ℝ) + 1)) • lmo m) (constantMomentum α₀) x₁ g ξ k).1 - u⟫
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      (Δ + 2 * L * ρ ^ 2 + (2 * L₂ * D₂ ^ 2 + 4 * D₂ * σ) / α₀) / Real.sqrt ((T : ℝ) + 1) +
        D₂ * Real.sqrt (2 * α₀) * σ := by
  set s := Real.sqrt ((T : ℝ) + 1)
  have hs1 : 1 ≤ s := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (T : ℝ) + 1 by linarith [(T.cast_nonneg : (0 : ℝ) ≤ T)])
    rwa [Real.sqrt_one] at this
  have hs2 : s ^ 2 = (T : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hγ : 0 ≤ 1 / s := by positivity
  have hγ1 : 1 / s ≤ 1 := by rw [div_le_one (by linarith)]; exact hs1
  set α := constantMomentum α₀
  have hαk : ∀ k, α (k + 2) = α₀ := fun k => by simp [α, constantMomentum]
  have hα0' : ∀ k, 0 < α (k + 1) := fun k => by
    simp only [α, constantMomentum]; split_ifs <;> linarith
  have hα1' : ∀ k, α (k + 1) ≤ 1 := fun k => by
    simp only [α, constantMomentum]; split_ifs <;> linarith
  have hαone : α 1 = 1 := by simp [α, constantMomentum]
  have hstep : Measurable (fun z : Space d × Space d => (1 - 1 / s) • z.1 + (1 / s) • lmo z.2) :=
    (measurable_fst.const_smul (1 - 1 / s)).add ((hlmo.measurable.comp measurable_snd).const_smul (1 / s))
  obtain ⟨-, -, htemp⟩ := scg_template H hL₂ hL hdef hρ hlmo hD₂ hx₁ hγ hγ1 hα0' hα1' hαone (T + 1) hu
  obtain ⟨hsq, h0, hrec⟩ := err_moments_on (K := {x | N x ≤ ρ}) (isClosed_le (seminorm_continuous N) continuous_const).measurableSet
    H.measurable (fun x hx => H.integrable x hx) (fun x hx => H.unbiased x hx)
    (fun x hx => H.variance_integrable x hx) (fun x hx => H.variance x hx)
    (fun x hx y hy => H.lipschitz₂ x y hx hy) hL₂ hstep hα0' hα1' hαone (δ := 1 / s * D₂)
    (fun ξ k => scg_move hlmo hx₁ hD₂ hγ hγ1 α ξ k)
    (fun ξ k => scg_path_feasible hlmo hx₁ hγ hγ1 α ξ k)
  have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ x₁ x₁ hx₁ hx₁)
  have hsum := constant_err_sum (u := fun k => ∫ ξ, ‖err (fun x m => (1 - 1 / s) • x + (1 / s) • lmo m)
      α x₁ f g ξ k‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) (η₀ := L₂ * (1 / s * D₂)) hα0 hα1.le hσ
    (by positivity) h0
    (fun k => by
      have := hrec k
      rw [hαk k] at this
      have e : 2 * L₂ ^ 2 * (1 / s * D₂) ^ 2 / α₀ = 2 * (L₂ * (1 / s * D₂)) ^ 2 / α₀ := by ring
      linarith) (T + 1)
  have hcomb := htemp.trans (by
    have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hγ hD₂0)
    linarith : Δ + 1 / s * D₂ * ∑ k ∈ Finset.range (T + 1),
        Real.sqrt (∫ ξ, ‖err (fun x m => (1 - 1 / s) • x + (1 / s) • lmo m) α x₁ f g ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p)) + ((T + 1 : ℕ) : ℝ) * (2 * L * ρ ^ 2 * (1 / s) ^ 2) ≤
      Δ + 1 / s * D₂ * (((T + 1 : ℕ) : ℝ) * (2 * (L₂ * (1 / s * D₂)) / α₀ +
        Real.sqrt (2 * α₀) * σ) + 4 * σ / α₀) + ((T + 1 : ℕ) : ℝ) * (2 * L * ρ ^ 2 * (1 / s) ^ 2))
  have hn : ((T + 1 : ℕ) : ℝ) = s ^ 2 := by rw [hs2]; push_cast; ring
  rw [hn] at hcomb
  rw [← hs2]
  exact scg_constant_algebra hs1 hα0 hσ hD₂0 hcomb

lemma scg_vanishing_algebra {E Δ ρ D₂ S L τ v : ℝ} (hv : 1 ≤ v) (hτ1 : 1 / 2 < τ)
    (hτ2 : τ < 1) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (h : τ / v ^ 3 * E ≤ Δ + τ / v ^ 3 * D₂ * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (2 * L * ρ ^ 2 * (τ / v ^ 3) ^ 2)) :
    1 / v ^ 4 * E ≤ (2 * Δ + 4 / 3 * D₂ * S) / v + 2 * L * ρ ^ 2 / v ^ 3 := by
  have hv0 : 0 < v := by linarith
  have hτ0 : 0 < τ := by linarith
  have hk : 0 < τ / v ^ 3 := by positivity
  have hE : E ≤ (Δ + τ / v ^ 3 * D₂ * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (2 * L * ρ ^ 2 * (τ / v ^ 3) ^ 2)) / (τ / v ^ 3) := by
    rw [le_div_iff₀ hk]; linarith
  have e : 1 / v ^ 4 * ((Δ + τ / v ^ 3 * D₂ * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (2 * L * ρ ^ 2 * (τ / v ^ 3) ^ 2)) / (τ / v ^ 3)) =
      Δ / (τ * v) + 4 / 3 * D₂ * S / v + 2 * L * ρ ^ 2 * τ / v ^ 3 := by
    field_simp
  have h1 : Δ / (τ * v) ≤ 2 * Δ / v := by
    rw [div_le_div_iff₀ (by positivity) hv0]
    nlinarith [mul_nonneg hΔ hv0.le]
  have h3 : 2 * L * ρ ^ 2 * τ / v ^ 3 ≤ 2 * L * ρ ^ 2 / v ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ 2 * L * ρ ^ 2 := by positivity
    nlinarith
  calc 1 / v ^ 4 * E ≤ 1 / v ^ 4 * ((Δ + τ / v ^ 3 * D₂ * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (2 * L * ρ ^ 2 * (τ / v ^ 3) ^ 2)) / (τ / v ^ 3)) := by gcongr
    _ = _ := e
    _ ≤ 2 * Δ / v + 4 / 3 * D₂ * S / v + 2 * L * ρ ^ 2 / v ^ 3 := by linarith
    _ = _ := by field_simp

theorem scg_vanishing_rate (H : ConstrainedProblem N ρ L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) (hL : 0 ≤ L)
    (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hD₂ : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖x - y‖ ≤ D₂) (hx₁ : N x₁ ≤ ρ) {τ : ℝ}
    (hτ1 : 1 / 2 < τ) (hτ2 : τ < 1) (T : ℕ) {u : Space d} (hu : N u ≤ ρ) :
    1 / ((T : ℝ) + 1) * ∑ k ∈ Finset.range (T + 1),
        ∫ ξ, ⟪gradient f (path (fun x m => (1 - τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) • x +
            (τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) • lmo m) vanishingMomentum x₁ g ξ k).1,
          (path (fun x m => (1 - τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) • x +
            (τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) • lmo m) vanishingMomentum x₁ g ξ k).1 - u⟫
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      (2 * Δ + 4 / 3 * D₂ * Real.sqrt (4 * σ ^ 2 + 8 * L₂ ^ 2 * D₂ ^ 2)) /
        ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) + 2 * L * ρ ^ 2 / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
  open scoped RealInnerProductSpace in
  (
    obtain ⟨hv1, hw, hn, hsq⟩ := quarter_powers T
    set v := ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
    set γ := τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)
    have hγe : γ = τ / v ^ 3 := by simp only [γ, hw]
    have hv0 : 0 < v := by linarith
    have hτ0 : 0 < τ := by linarith
    have hγ : 0 ≤ γ := by rw [hγe]; positivity
    have hγ1 : γ ≤ 1 := by
      rw [hγe, div_le_one (by positivity)]
      have hv2 : 1 ≤ v ^ 2 := by nlinarith
      nlinarith
    obtain ⟨hα0, hα1, hαone, hα2⟩ := vanishing_momentum_props
    have hstep : Measurable (fun z : Space d × Space d => (1 - γ) • z.1 + γ • lmo z.2) :=
      (measurable_fst.const_smul (1 - γ)).add ((hlmo.measurable.comp measurable_snd).const_smul γ)
    obtain ⟨-, -, htemp⟩ := scg_template H hL₂ hL hdef hρ hlmo hD₂ hx₁ hγ hγ1 hα0 hα1 hαone (T + 1) hu
    obtain ⟨hsqi, h0, hrec⟩ := err_moments_on (K := {x | N x ≤ ρ}) (isClosed_le (seminorm_continuous N) continuous_const).measurableSet
      H.measurable (fun x hx => H.integrable x hx) (fun x hx => H.unbiased x hx)
      (fun x hx => H.variance_integrable x hx) (fun x hx => H.variance x hx)
      (fun x hx y hy => H.lipschitz₂ x y hx hy) hL₂ hstep hα0 hα1 hαone (δ := γ * D₂)
      (fun ξ k => scg_move hlmo hx₁ hD₂ hγ hγ1 vanishingMomentum ξ k)
      (fun ξ k => scg_path_feasible hlmo hx₁ hγ hγ1 vanishingMomentum ξ k)
    have hγn : γ ^ 2 * (((T + 1 : ℕ) : ℝ) * Real.sqrt ((T + 1 : ℕ) : ℝ)) ≤ 1 := by
      rw [hγe, hsq, hn]
      rw [show (τ / v ^ 3) ^ 2 * (v ^ 4 * v ^ 2) = τ ^ 2 by field_simp]
      nlinarith
    have hsum := vanishing_err_sum (u := fun k => ∫ ξ, ‖err (fun x m => (1 - γ) • x + γ • lmo m)
        vanishingMomentum x₁ f g ξ k‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) (σ := σ)
      (η₀ := L₂ * D₂) hγn (fun k => integral_nonneg fun _ => by positivity) h0
      (fun k => by
        have := hrec k
        rw [hα2 k] at this
        have e : 2 * L₂ ^ 2 * (γ * D₂) ^ 2 = 2 * (γ * (L₂ * D₂)) ^ 2 := by ring
        rw [e] at this
        exact this)
    have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ x₁ x₁ hx₁ hx₁)
    have hS : Real.sqrt (4 * σ ^ 2 + 8 * (L₂ * D₂) ^ 2) = Real.sqrt (4 * σ ^ 2 + 8 * L₂ ^ 2 * D₂ ^ 2) := by
      ring_nf
    rw [hS] at hsum
    have hcomb := htemp.trans (by
      have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hγ hD₂0)
      linarith : Δ + γ * D₂ * ∑ k ∈ Finset.range (T + 1),
          Real.sqrt (∫ ξ, ‖err (fun x m => (1 - γ) • x + γ • lmo m) vanishingMomentum x₁ f g ξ k‖ ^ 2
            ∂(Measure.infinitePi fun _ : ℕ => p)) + ((T + 1 : ℕ) : ℝ) * (2 * L * ρ ^ 2 * γ ^ 2) ≤
        Δ + γ * D₂ * (Real.sqrt (4 * σ ^ 2 + 8 * L₂ ^ 2 * D₂ ^ 2) *
          (4 / 3 * ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))) + ((T + 1 : ℕ) : ℝ) * (2 * L * ρ ^ 2 * γ ^ 2))
    set E := ∑ k ∈ Finset.range (T + 1), ∫ ξ, ⟪gradient f
      (path (fun x m => (1 - γ) • x + γ • lmo m) vanishingMomentum x₁ g ξ k).1,
        (path (fun x m => (1 - γ) • x + γ • lmo m) vanishingMomentum x₁ g ξ k).1 - u⟫
        ∂(Measure.infinitePi fun _ : ℕ => p)
    rw [hw, hn, hγe] at hcomb
    have hΔ : 0 ≤ Δ := by
      obtain ⟨fmin, hfmin, hgap⟩ := H.lower; linarith [hfmin x₁ hx₁]
    have hT : (T : ℝ) + 1 = v ^ 4 := by rw [← hn]; push_cast; ring
    rw [hT, hw]
    exact scg_vanishing_algebra hv1 hτ1 hτ2 hL hΔ hcomb)

theorem scg_constant_convergence :
    Convergence LongTails.Setups.ScgConstant.spec
      (fun p _ => ⌈((p.Δ + 2 * p.L * p.ρ ^ 2 + (2 * p.L₂ * p.D₂ ^ 2 + 4 * p.D₂ * p.σ) / p.α) /
        p.ε) ^ 2⌉₊ + 1) := by
  open scoped RealInnerProductSpace in
  (
    apply convergence_of_public_budget (S := LongTails.Setups.ScgConstant.spec)
      (fun p => LongTails.Setups.ScgConstant.horizon p + 1)
    refine ⟨LongTails.Setups.ScgConstant.method, ?_, fun p _ => rfl⟩
    intro p hp f O hadm
    obtain ⟨hdef, hρ, hlmo, hD₂, hx₁, hL, hL₂, hσ, hΔ, hα0, hα1, hε⟩ := hp
    obtain ⟨g, P₀, P, hIID, rfl, H⟩ := hadm
    set T := LongTails.Setups.ScgConstant.horizon p
    set γ := 1 / Real.sqrt ((T : ℝ) + 1)
    have hs1 : 1 ≤ Real.sqrt ((T : ℝ) + 1) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (T : ℝ) + 1 by linarith [(T.cast_nonneg : (0 : ℝ) ≤ T)])
      rwa [Real.sqrt_one] at this
    have hγ : 0 ≤ γ := by positivity
    have hγ1 : γ ≤ 1 := by rw [div_le_one (by linarith)]; exact hs1
    have hgc := measurable_gradient_space f
    have hα0' : ∀ k, 0 < constantMomentum p.α (k + 1) := fun k => by
      simp only [constantMomentum]; split_ifs <;> linarith
    have hα1' : ∀ k, constantMomentum p.α (k + 1) ≤ 1 := fun k => by
      simp only [constantMomentum]; split_ifs <;> linarith
    have hαone : constantMomentum p.α 1 = 1 := by simp [constantMomentum]
    have hstep : Measurable (fun z : Space p.d × Space p.d => (1 - γ) • z.1 + γ • p.lmo z.2) :=
      (measurable_fst.const_smul (1 - γ)).add ((hlmo.measurable.comp measurable_snd).const_smul γ)
    have hall := fun (u : Space p.d) (hu : p.N u ≤ p.ρ) =>
      output_integral (fun x m => (1 - γ) • x + γ • p.lmo m) hstep (constantMomentum p.α) T p.x₁
        H.measurable P₀ P hIID (T + 1) (Nat.le_succ T) (fun x => ⟪gradient f x, x - u⟫)
        (Measurable.inner hgc (measurable_id.sub measurable_const))
        (B := (‖gradient f p.x₁‖ + p.L₂ * p.D₂) * p.D₂)
        (fun j _ ξ => (scg_template H hL₂ hL.le hdef hρ hlmo hD₂ hx₁ hγ hγ1 hα0' hα1' hαone 0 hu).2.1 j ξ)
    have hfeas : ∀ ω : (lmoMethod (fun x m => (1 - γ) • x + γ • p.lmo m) (constantMomentum p.α) T p.x₁).Seed ×
        ((k : ℕ) → p.Ω), p.N (execute
          ({ Seed := fun _ => p.Ω, law := P, answer := fun _ q ω => g q.2 ω } : Oracle (Space p.d) (Space p.d))
          (lmoMethod (fun x m => (1 - γ) • x + γ • p.lmo m) (constantMomentum p.α) T p.x₁) (fun _ => T + 1) ω.1 ω.2) ≤ p.ρ := by
      intro ω
      rw [execute_lmoMethod _ _ T p.x₁ g P (T + 1) (Nat.le_succ T) ω.1 ω.2]
      exact scg_path_feasible hlmo hx₁ hγ hγ1 _ ω.2 _
    refine ⟨(hall 0 (by simp; linarith)).1, hfeas, fun u hu => ⟨(hall u hu).2.1, (hall u hu).2.2.le.trans ?_⟩⟩
    have hrate := scg_constant_rate H hL₂ hL.le hσ hdef hρ hlmo hD₂ hx₁ hα0 hα1 T hu
    set M := p.Δ + 2 * p.L * p.ρ ^ 2 + (2 * p.L₂ * p.D₂ ^ 2 + 4 * p.D₂ * p.σ) / p.α
    have hD₂0 : 0 ≤ p.D₂ := (norm_nonneg _).trans (hD₂ p.x₁ p.x₁ hx₁ hx₁)
    have hfin : M / Real.sqrt ((T : ℝ) + 1) ≤ p.ε := horizon_sqrt_le (by positivity) hε
    linarith)

theorem scg_vanishing_convergence :
    Convergence LongTails.Setups.ScgVanishing.spec
      (fun p _ => ⌈((2 * p.Δ + 4 / 3 * p.D₂ * Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.D₂ ^ 2) +
        2 * p.L * p.ρ ^ 2) / p.ε) ^ 4⌉₊ + 1) := by
  open scoped RealInnerProductSpace in
  (
    apply convergence_of_public_budget (S := LongTails.Setups.ScgVanishing.spec)
      (fun p => LongTails.Setups.ScgVanishing.horizon p + 1)
    refine ⟨LongTails.Setups.ScgVanishing.method, ?_, fun p _ => rfl⟩
    intro p hp f O hadm
    obtain ⟨hdef, hρ, hlmo, hD₂, hx₁, hL, hL₂, hσ, hΔ, hτ1, hτ2, hε⟩ := hp
    obtain ⟨g, P₀, P, hIID, rfl, H⟩ := hadm
    set T := LongTails.Setups.ScgVanishing.horizon p
    set γ := p.τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)
    obtain ⟨hv1, hw, -, -⟩ := quarter_powers T
    have hτ0 : 0 < p.τ := by linarith
    have hγ : 0 ≤ γ := by positivity
    have hγ1 : γ ≤ 1 := by
      simp only [γ]
      rw [hw, div_le_one (by positivity)]
      have hv2 : 1 ≤ (((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by nlinarith
      nlinarith
    have hgc := measurable_gradient_space f
    obtain ⟨hα0, hα1, hαone, -⟩ := vanishing_momentum_props
    have hstep : Measurable (fun z : Space p.d × Space p.d => (1 - γ) • z.1 + γ • p.lmo z.2) :=
      (measurable_fst.const_smul (1 - γ)).add ((hlmo.measurable.comp measurable_snd).const_smul γ)
    have hall := fun (u : Space p.d) (hu : p.N u ≤ p.ρ) =>
      output_integral (fun x m => (1 - γ) • x + γ • p.lmo m) hstep vanishingMomentum T p.x₁
        H.measurable P₀ P hIID (T + 1) (Nat.le_succ T) (fun x => ⟪gradient f x, x - u⟫)
        (Measurable.inner hgc (measurable_id.sub measurable_const))
        (B := (‖gradient f p.x₁‖ + p.L₂ * p.D₂) * p.D₂)
        (fun j _ ξ => (scg_template H hL₂ hL.le hdef hρ hlmo hD₂ hx₁ hγ hγ1 hα0 hα1 hαone 0 hu).2.1 j ξ)
    have hfeas : ∀ ω : (lmoMethod (fun x m => (1 - γ) • x + γ • p.lmo m) (vanishingMomentum) T p.x₁).Seed ×
        ((k : ℕ) → p.Ω), p.N (execute
          ({ Seed := fun _ => p.Ω, law := P, answer := fun _ q ω => g q.2 ω } : Oracle (Space p.d) (Space p.d))
          (lmoMethod (fun x m => (1 - γ) • x + γ • p.lmo m) (vanishingMomentum) T p.x₁) (fun _ => T + 1) ω.1 ω.2) ≤ p.ρ := by
      intro ω
      rw [execute_lmoMethod _ _ T p.x₁ g P (T + 1) (Nat.le_succ T) ω.1 ω.2]
      exact scg_path_feasible hlmo hx₁ hγ hγ1 _ ω.2 _
    refine ⟨(hall 0 (by simp; linarith)).1, hfeas, fun u hu => ⟨(hall u hu).2.1, (hall u hu).2.2.le.trans ?_⟩⟩
    have hrate := scg_vanishing_rate H hL₂ hL.le hdef hρ hlmo hD₂ hx₁ hτ1 hτ2 T hu
    set M := 2 * p.Δ + 4 / 3 * p.D₂ * Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.D₂ ^ 2) +
      2 * p.L * p.ρ ^ 2
    have hD₂0 : 0 ≤ p.D₂ := (norm_nonneg _).trans (hD₂ p.x₁ p.x₁ hx₁ hx₁)
    have hfin : M / ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ p.ε := horizon_quarter_le hε
    have hsplit := quarter_split (A := 2 * p.Δ + 4 / 3 * p.D₂ *
      Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.D₂ ^ 2)) (by positivity : 0 ≤ 2 * p.L * p.ρ ^ 2) T
    linarith)

end OracleTemplate.NormBallLMO
