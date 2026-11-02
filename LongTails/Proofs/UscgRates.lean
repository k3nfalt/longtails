import LongTails.Proofs.LmoDescent
import LongTails.Proofs.LmoErrorBounds
import LongTails.Proofs.LmoOutput
import LongTails.Setups.UscgConstant
import LongTails.Setups.UscgVanishing

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

variable {N : Seminorm ℝ (Space d)} {L L₂ σ Δ ρ ρ₂ ζ : ℝ} {x₁ : Space d} {f : Space d → ℝ}
  {g : Space d → Ω → Space d} {p : Measure Ω} [IsProbabilityMeasure p] {lmo : Space d → Space d}

omit [MeasurableSpace Ω] in
lemma uscg_move (hlmo : IsBallLMO N ρ lmo) (hρ₂ : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂)
    {γ : ℝ} (hγ : 0 ≤ γ) (α : ℕ → ℝ) (ξ : ℕ → Ω) (k : ℕ) :
    ‖(path (fun x m => x + γ • lmo m) α x₁ g ξ (k + 1)).1 -
      (path (fun x m => x + γ • lmo m) α x₁ g ξ k).1‖ ≤ γ * ρ₂ := by
  rw [path_succ]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
  exact mul_le_mul_of_nonneg_left (hρ₂ _ (hlmo.feasible _)) hγ

omit [MeasurableSpace Ω] in
lemma uscg_dist (hlmo : IsBallLMO N ρ lmo) (hρ₂ : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂)
    {γ : ℝ} (hγ : 0 ≤ γ) (α : ℕ → ℝ) (ξ : ℕ → Ω) :
    ∀ k, ‖(path (fun x m => x + γ • lmo m) α x₁ g ξ k).1 - x₁‖ ≤ k * (γ * ρ₂) := by
  intro k
  induction k with
  | zero => simp [path_zero]
  | succ k ih =>
      have hm := uscg_move (x₁ := x₁) (g := g) hlmo hρ₂ hγ α ξ k
      calc _ = ‖((path (fun x m => x + γ • lmo m) α x₁ g ξ (k + 1)).1 -
              (path (fun x m => x + γ • lmo m) α x₁ g ξ k).1) +
            ((path (fun x m => x + γ • lmo m) α x₁ g ξ k).1 - x₁)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ γ * ρ₂ + k * (γ * ρ₂) := add_le_add hm ih
        _ = ((k + 1 : ℕ) : ℝ) * (γ * ρ₂) := by push_cast; ring

theorem uscg_template (H : Problem N L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) (hL : 0 ≤ L)
    (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hρ₂ : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂) (hζ0 : 0 ≤ ζ) (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖) {γ : ℝ}
    (hγ : 0 ≤ γ) {α : ℕ → ℝ} (hα0 : ∀ k, 0 < α (k + 1)) (hα1 : ∀ k, α (k + 1) ≤ 1) (hαone : α 1 = 1) (n : ℕ) :
    (∀ k, Integrable (fun ξ => dualNorm N (gradient f (path (fun x m => x + γ • lmo m) α x₁ g ξ k).1))
        (Measure.infinitePi fun _ : ℕ => p)) ∧
    (∀ k ξ, |dualNorm N (gradient f (path (fun x m => x + γ • lmo m) α x₁ g ξ k).1)| ≤
        ρ₂ / ρ * (‖gradient f x₁‖ + L₂ * (k * (γ * ρ₂)))) ∧
    γ * ρ * ∑ k ∈ Finset.range n, ∫ ξ, dualNorm N (gradient f (path (fun x m => x + γ • lmo m) α x₁ g ξ k).1)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n,
          Real.sqrt (∫ ξ, ‖err (fun x m => x + γ • lmo m) α x₁ f g ξ k‖ ^ 2
            ∂(Measure.infinitePi fun _ : ℕ => p)) + n * (L * γ ^ 2 * ρ ^ 2 / 2) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set step := fun (x m : Space d) => x + γ • lmo m
  have hstep : Measurable (fun z : Space d × Space d => step z.1 z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul γ)
  have hR := unit_bound_of_radius hρ hρ₂
  have hR0 : 0 ≤ ρ₂ / ρ := by
    have := hρ₂ 0 (by simp; linarith); simp at this; exact div_nonneg this hρ.le
  have hgc := continuous_gradient_of H hL₂
  have hdc := continuous_dualNorm hR hR0
  have hpath := measurable_path hstep α x₁ H.measurable
  have hbound : ∀ k ξ, |dualNorm N (gradient f (path step α x₁ g ξ k).1)| ≤
      ρ₂ / ρ * (‖gradient f x₁‖ + L₂ * (k * (γ * ρ₂))) := by
    intro k ξ
    rw [abs_of_nonneg (dualNorm_nonneg hR _)]
    refine (dualNorm_le_norm hR _).trans (mul_le_mul_of_nonneg_left ?_ hR0)
    calc ‖gradient f (path step α x₁ g ξ k).1‖
        ≤ ‖gradient f x₁‖ + ‖gradient f (path step α x₁ g ξ k).1 - gradient f x₁‖ := by
          have := norm_add_le (gradient f x₁) (gradient f (path step α x₁ g ξ k).1 - gradient f x₁)
          rwa [add_sub_cancel] at this
      _ ≤ ‖gradient f x₁‖ + L₂ * (k * (γ * ρ₂)) := by
          gcongr
          exact (H.lipschitz₂ _ _).trans (mul_le_mul_of_nonneg_left (uscg_dist hlmo hρ₂ hγ α ξ k) hL₂)
  have hint : ∀ k, Integrable (fun ξ => dualNorm N (gradient f (path step α x₁ g ξ k).1)) P := by
    intro k
    refine Integrable.of_bound ((hdc.comp hgc).measurable.comp (hpath k).fst).aestronglyMeasurable
      (ρ₂ / ρ * (‖gradient f x₁‖ + L₂ * (k * (γ * ρ₂)))) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact hbound k ξ
  refine ⟨hint, hbound, ?_⟩
  obtain ⟨hsq, -, -⟩ := err_moments H hL₂ hstep hα0 hα1 hαone (δ := γ * ρ₂)
    (fun ξ k => uscg_move hlmo hρ₂ hγ α ξ k)
  have herr_meas : ∀ k, Measurable (fun ξ => err step α x₁ f g ξ k) := fun k =>
    (hpath (k + 1)).snd.sub (hgc.measurable.comp (hpath k).fst)
  have herr_int : ∀ k, Integrable (fun ξ => ‖err step α x₁ f g ξ k‖) P := fun k =>
    integrable_norm_of_sq (herr_meas k) (hsq k)
  obtain ⟨fmin, hfmin, hgap⟩ := H.lower
  have hpw : ∀ ξ, γ * ρ * ∑ k ∈ Finset.range n, dualNorm N (gradient f (path step α x₁ g ξ k).1) ≤
      Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖ +
        n * (L * γ ^ 2 * ρ ^ 2 / 2) := by
    intro ξ
    have hk : ∀ k, γ * ρ * dualNorm N (gradient f (path step α x₁ g ξ k).1) ≤
        f (path step α x₁ g ξ k).1 - f (path step α x₁ g ξ (k + 1)).1 +
          γ * (ρ₂ + ζ * ρ) * ‖err step α x₁ f g ξ k‖ + L * γ ^ 2 * ρ ^ 2 / 2 := by
      intro k
      have h := uscg_step (f := f) hdef hρ hlmo hρ₂ hζ H.differentiable H.lipschitz hL hγ
        (path step α x₁ g ξ k).1 (path step α x₁ g ξ (k + 1)).2
      have e : (path step α x₁ g ξ (k + 1)).1 =
          (path step α x₁ g ξ k).1 + γ • lmo (path step α x₁ g ξ (k + 1)).2 := by
        rw [path_succ]
      rw [← e] at h
      simpa only [err] using h
    have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hk k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have h0 : (path step α x₁ g ξ 0).1 = x₁ := rfl
    rw [h0] at hsum
    have := hfmin (path step α x₁ g ξ n).1
    linarith
  have hlhs : ∫ ξ, γ * ρ * ∑ k ∈ Finset.range n, dualNorm N (gradient f (path step α x₁ g ξ k).1) ∂P =
      γ * ρ * ∑ k ∈ Finset.range n, ∫ ξ, dualNorm N (gradient f (path step α x₁ g ξ k).1) ∂P := by
    rw [integral_const_mul, integral_finsetSum _ fun k _ => hint k]
  have hrint : Integrable (fun ξ => Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n,
      ‖err step α x₁ f g ξ k‖ + n * (L * γ ^ 2 * ρ ^ 2 / 2)) P :=
    ((integrable_const _).add ((integrable_finsetSum _ fun k _ => herr_int k).const_mul _)).add
      (integrable_const _)
  have hS : Integrable (fun ξ => ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖) P :=
    integrable_finsetSum _ fun k _ => herr_int k
  have hrhs : ∫ ξ, (Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖ +
      n * (L * γ ^ 2 * ρ ^ 2 / 2)) ∂P =
      Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n, ∫ ξ, ‖err step α x₁ f g ξ k‖ ∂P +
        n * (L * γ ^ 2 * ρ ^ 2 / 2) := by
    rw [integral_add (f := fun ξ => Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖)
      (g := fun _ => (n : ℝ) * (L * γ ^ 2 * ρ ^ 2 / 2))
      ((integrable_const _).add (hS.const_mul _)) (integrable_const _)]
    rw [integral_add (f := fun _ => Δ)
      (g := fun ξ => γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range n, ‖err step α x₁ f g ξ k‖)
      (integrable_const _) (hS.const_mul _)]
    rw [integral_const_mul, integral_finsetSum _ fun k _ => herr_int k]
    simp
  have hmono := integral_mono ((integrable_finsetSum _ fun k _ => hint k).const_mul _) hrint hpw
  rw [hlhs, hrhs] at hmono
  have hjensen : ∀ k, ∫ ξ, ‖err step α x₁ f g ξ k‖ ∂P ≤
      Real.sqrt (∫ ξ, ‖err step α x₁ f g ξ k‖ ^ 2 ∂P) := fun k =>
    NormalizedStorm.integral_norm_le_sqrt (herr_meas k).aestronglyMeasurable (hsq k)
  have hρ₂0 : 0 ≤ ρ₂ := by have := hρ₂ 0 (by simp; linarith); simpa using this
  have hcoef : 0 ≤ γ * (ρ₂ + ζ * ρ) := mul_nonneg hγ (by positivity)
  have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hjensen k) hcoef
  linarith

lemma uscg_constant_algebra {E Δ ρ ρ₂ ζ L L₂ σ α s r : ℝ} (hρ : 0 < ρ) (hs : 1 ≤ s) (hα : 0 < α)
    (hσ : 0 ≤ σ) (hc : 0 ≤ ρ₂ + ζ * ρ)
    (h : 1 / s * ρ * E ≤ Δ + 1 / s * (ρ₂ + ζ * ρ) * (s ^ 2 * (2 * (L₂ * (1 / s * ρ₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (L * (1 / s) ^ 2 * ρ ^ 2 / 2)) :
    1 / s ^ 2 * E ≤ (Δ / ρ + L * ρ / 2 + (ρ₂ / ρ + ζ) * (2 * L₂ * ρ₂ + 4 * σ) / α) / s +
      (ρ₂ / ρ + ζ) * r * σ := by
  have hs0 : 0 < s := by linarith
  have hE : E ≤ s / ρ * (Δ + 1 / s * (ρ₂ + ζ * ρ) * (s ^ 2 * (2 * (L₂ * (1 / s * ρ₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (L * (1 / s) ^ 2 * ρ ^ 2 / 2)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
    have := mul_le_mul_of_nonneg_left h hs0.le
    calc E * ρ = s * (1 / s * ρ * E) := by field_simp
      _ ≤ _ := this
  have key : 1 / s ^ 2 * (s / ρ * (Δ + 1 / s * (ρ₂ + ζ * ρ) * (s ^ 2 * (2 * (L₂ * (1 / s * ρ₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (L * (1 / s) ^ 2 * ρ ^ 2 / 2))) =
      (Δ / ρ + L * ρ / 2 + (ρ₂ / ρ + ζ) * (2 * L₂ * ρ₂) / α) / s + (ρ₂ / ρ + ζ) * r * σ +
        (ρ₂ / ρ + ζ) * (4 * σ / α) / s ^ 2 := by
    field_simp
    ring
  have hfin : (ρ₂ / ρ + ζ) * (4 * σ / α) / s ^ 2 ≤ (ρ₂ / ρ + ζ) * (4 * σ / α) / s := by
    have h1 : 0 ≤ (ρ₂ / ρ + ζ) * (4 * σ / α) := by
      have : 0 ≤ ρ₂ / ρ + ζ := by
        have e : ρ₂ / ρ + ζ = (ρ₂ + ζ * ρ) / ρ := by field_simp
        rw [e]; positivity
      positivity
    apply div_le_div_of_nonneg_left h1 hs0
    nlinarith
  have e2 : (Δ / ρ + L * ρ / 2 + (ρ₂ / ρ + ζ) * (2 * L₂ * ρ₂ + 4 * σ) / α) / s =
      (Δ / ρ + L * ρ / 2 + (ρ₂ / ρ + ζ) * (2 * L₂ * ρ₂) / α) / s + (ρ₂ / ρ + ζ) * (4 * σ / α) / s := by
    field_simp; ring
  calc 1 / s ^ 2 * E ≤ 1 / s ^ 2 * (s / ρ * (Δ + 1 / s * (ρ₂ + ζ * ρ) * (s ^ 2 * (2 * (L₂ * (1 / s * ρ₂)) / α + r * σ) +
      4 * σ / α) + s ^ 2 * (L * (1 / s) ^ 2 * ρ ^ 2 / 2))) := by gcongr
    _ = _ := key
    _ ≤ _ := by rw [e2]; linarith

theorem uscg_constant_rate (H : Problem N L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) (hL : 0 ≤ L)
    (hσ : 0 ≤ σ) (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hρ₂ : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂) (hζ0 : 0 ≤ ζ) (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖) {α₀ : ℝ}
    (hα0 : 0 < α₀) (hα1 : α₀ < 1) (T : ℕ) :
    1 / ((T : ℝ) + 1) * ∑ k ∈ Finset.range (T + 1),
        ∫ ξ, dualNorm N (gradient f (path (fun x m => x + (1 / Real.sqrt ((T : ℝ) + 1)) • lmo m)
          (constantMomentum α₀) x₁ g ξ k).1) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      (Δ / ρ + L * ρ / 2 + (ρ₂ / ρ + ζ) * (2 * L₂ * ρ₂ + 4 * σ) / α₀) / Real.sqrt ((T : ℝ) + 1) +
        (ρ₂ / ρ + ζ) * Real.sqrt (2 * α₀) * σ := by
  set s := Real.sqrt ((T : ℝ) + 1)
  have hs1 : 1 ≤ s := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (T : ℝ) + 1 by linarith [(T.cast_nonneg : (0 : ℝ) ≤ T)])
    rwa [Real.sqrt_one] at this
  have hs2 : s ^ 2 = (T : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hγ : 0 ≤ 1 / s := by positivity
  set α := constantMomentum α₀
  have hαk : ∀ k, α (k + 2) = α₀ := fun k => by simp [α, constantMomentum]
  have hα0' : ∀ k, 0 < α (k + 1) := fun k => by
    simp only [α, constantMomentum]; split_ifs <;> linarith
  have hα1' : ∀ k, α (k + 1) ≤ 1 := fun k => by
    simp only [α, constantMomentum]; split_ifs <;> linarith
  have hαone : α 1 = 1 := by simp [α, constantMomentum]
  have hstep : Measurable (fun z : Space d × Space d => z.1 + (1 / s) • lmo z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul (1 / s))
  obtain ⟨-, -, htemp⟩ := uscg_template H hL₂ hL hdef hρ hlmo hρ₂ hζ0 hζ hγ hα0' hα1' hαone (T + 1)
  obtain ⟨hsq, h0, hrec⟩ := err_moments H hL₂ hstep hα0' hα1' hαone (δ := 1 / s * ρ₂)
    (fun ξ k => uscg_move hlmo hρ₂ hγ α ξ k)
  have hsum := constant_err_sum (u := fun k => ∫ ξ, ‖err (fun x m => x + (1 / s) • lmo m) α x₁ f g ξ k‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => p)) (η₀ := L₂ * (1 / s * ρ₂)) hα0 hα1.le hσ
    (by have : 0 ≤ ρ₂ := by have := hρ₂ 0 (by simp; linarith); simpa using this
        positivity) h0
    (fun k => by
      have := hrec k
      rw [hαk k] at this
      have e : 2 * L₂ ^ 2 * (1 / s * ρ₂) ^ 2 / α₀ = 2 * (L₂ * (1 / s * ρ₂)) ^ 2 / α₀ := by ring
      linarith) (T + 1)
  have hρ₂0 : 0 ≤ ρ₂ := by have := hρ₂ 0 (by simp; linarith); simpa using this
  have hc : 0 ≤ ρ₂ + ζ * ρ := by positivity
  have hcomb := htemp.trans (by
    have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hγ hc)
    linarith : Δ + 1 / s * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range (T + 1),
        Real.sqrt (∫ ξ, ‖err (fun x m => x + (1 / s) • lmo m) α x₁ f g ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p)) + ((T + 1 : ℕ) : ℝ) * (L * (1 / s) ^ 2 * ρ ^ 2 / 2) ≤
      Δ + 1 / s * (ρ₂ + ζ * ρ) * (((T + 1 : ℕ) : ℝ) * (2 * (L₂ * (1 / s * ρ₂)) / α₀ +
        Real.sqrt (2 * α₀) * σ) + 4 * σ / α₀) + ((T + 1 : ℕ) : ℝ) * (L * (1 / s) ^ 2 * ρ ^ 2 / 2))
  have hn : ((T + 1 : ℕ) : ℝ) = s ^ 2 := by rw [hs2]; push_cast; ring
  rw [hn] at hcomb
  rw [← hs2]
  exact uscg_constant_algebra hρ hs1 hα0 hσ hc hcomb

lemma vanishing_algebra {E Δ ρ ρ₂ ζ S L τ v : ℝ} (hρ : 0 < ρ) (hv : 1 ≤ v) (hτ1 : 1 / 2 < τ)
    (hτ2 : τ < 1) (hc : 0 ≤ ρ₂ + ζ * ρ) (hS : 0 ≤ S) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (h : τ / v ^ 3 * ρ * E ≤ Δ + τ / v ^ 3 * (ρ₂ + ζ * ρ) * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (L * (τ / v ^ 3) ^ 2 * ρ ^ 2 / 2)) :
    1 / v ^ 4 * E ≤ (2 * Δ / ρ + 8 / 3 * (ρ₂ / ρ + ζ) * S) / v + L * ρ / v ^ 3 := by
  have hv0 : 0 < v := by linarith
  have hτ0 : 0 < τ := by linarith
  have hk : 0 < τ / v ^ 3 * ρ := by positivity
  have hE : E ≤ (Δ + τ / v ^ 3 * (ρ₂ + ζ * ρ) * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (L * (τ / v ^ 3) ^ 2 * ρ ^ 2 / 2)) / (τ / v ^ 3 * ρ) := by
    rw [le_div_iff₀ hk]; linarith
  have e : 1 / v ^ 4 * ((Δ + τ / v ^ 3 * (ρ₂ + ζ * ρ) * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (L * (τ / v ^ 3) ^ 2 * ρ ^ 2 / 2)) / (τ / v ^ 3 * ρ)) =
      Δ / (τ * ρ * v) + 4 / 3 * (ρ₂ / ρ + ζ) * S / v + L * τ * ρ / (2 * v ^ 3) := by
    field_simp
  have h1 : Δ / (τ * ρ * v) ≤ 2 * Δ / ρ / v := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hΔ (mul_pos hρ hv0).le]
  have hcρ : 0 ≤ ρ₂ / ρ + ζ := by
    have e : ρ₂ / ρ + ζ = (ρ₂ + ζ * ρ) / ρ := by field_simp
    rw [e]; positivity
  have h2 : 4 / 3 * (ρ₂ / ρ + ζ) * S / v ≤ 8 / 3 * (ρ₂ / ρ + ζ) * S / v := by
    apply div_le_div_of_nonneg_right _ hv0.le
    nlinarith [mul_nonneg hcρ hS]
  have h3 : L * τ * ρ / (2 * v ^ 3) ≤ L * ρ / v ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_nonneg (mul_nonneg hL hρ.le) (pow_pos hv0 3).le
    nlinarith
  calc 1 / v ^ 4 * E ≤ 1 / v ^ 4 * ((Δ + τ / v ^ 3 * (ρ₂ + ζ * ρ) * (S * (4 / 3 * v ^ 3)) +
      v ^ 4 * (L * (τ / v ^ 3) ^ 2 * ρ ^ 2 / 2)) / (τ / v ^ 3 * ρ)) := by gcongr
    _ = _ := e
    _ ≤ 2 * Δ / ρ / v + 8 / 3 * (ρ₂ / ρ + ζ) * S / v + L * ρ / v ^ 3 := by linarith
    _ = _ := by field_simp

theorem uscg_vanishing_rate (H : Problem N L L₂ σ Δ x₁ f g p) (hL₂ : 0 ≤ L₂) (hL : 0 ≤ L)
    (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hρ₂ : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂) (hζ0 : 0 ≤ ζ) (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖) {τ : ℝ}
    (hτ1 : 1 / 2 < τ) (hτ2 : τ < 1) (T : ℕ) :
    1 / ((T : ℝ) + 1) * ∑ k ∈ Finset.range (T + 1),
        ∫ ξ, dualNorm N (gradient f (path (fun x m => x + (τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) • lmo m)
          vanishingMomentum x₁ g ξ k).1) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      (2 * Δ / ρ + 8 / 3 * (ρ₂ / ρ + ζ) * Real.sqrt (4 * σ ^ 2 + 8 * L₂ ^ 2 * ρ₂ ^ 2)) /
        ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) + L * ρ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨hv1, hw, hn, hsq⟩ := quarter_powers T
  set v := ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
  set γ := τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)
  have hγe : γ = τ / v ^ 3 := by simp only [γ, hw]
  have hv0 : 0 < v := by linarith
  have hγ : 0 ≤ γ := by rw [hγe]; have : 0 < τ := by linarith
                        positivity
  obtain ⟨hα0, hα1, hαone, hα2⟩ := vanishing_momentum_props
  have hstep : Measurable (fun z : Space d × Space d => z.1 + γ • lmo z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul γ)
  obtain ⟨-, -, htemp⟩ := uscg_template H hL₂ hL hdef hρ hlmo hρ₂ hζ0 hζ hγ hα0 hα1 hαone (T + 1)
  obtain ⟨hsqi, h0, hrec⟩ := err_moments H hL₂ hstep hα0 hα1 hαone (δ := γ * ρ₂)
    (fun ξ k => uscg_move hlmo hρ₂ hγ vanishingMomentum ξ k)
  have hγn : γ ^ 2 * (((T + 1 : ℕ) : ℝ) * Real.sqrt ((T + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [hγe, hsq, hn]
    rw [show (τ / v ^ 3) ^ 2 * (v ^ 4 * v ^ 2) = τ ^ 2 by field_simp]
    nlinarith
  have hsum := vanishing_err_sum (u := fun k => ∫ ξ, ‖err (fun x m => x + γ • lmo m) vanishingMomentum
      x₁ f g ξ k‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) (σ := σ) (η₀ := L₂ * ρ₂) hγn
    (fun k => integral_nonneg fun _ => by positivity) h0
    (fun k => by
      have := hrec k
      rw [hα2 k] at this
      have e : 2 * L₂ ^ 2 * (γ * ρ₂) ^ 2 = 2 * (γ * (L₂ * ρ₂)) ^ 2 := by ring
      rw [e] at this
      exact this)
  have hρ₂0 : 0 ≤ ρ₂ := by have := hρ₂ 0 (by simp; linarith); simpa using this
  have hc : 0 ≤ ρ₂ + ζ * ρ := by positivity
  have hS : Real.sqrt (4 * σ ^ 2 + 8 * (L₂ * ρ₂) ^ 2) = Real.sqrt (4 * σ ^ 2 + 8 * L₂ ^ 2 * ρ₂ ^ 2) := by
    ring_nf
  rw [hS] at hsum
  have hcomb := htemp.trans (by
    have := mul_le_mul_of_nonneg_left hsum (mul_nonneg hγ hc)
    linarith : Δ + γ * (ρ₂ + ζ * ρ) * ∑ k ∈ Finset.range (T + 1),
        Real.sqrt (∫ ξ, ‖err (fun x m => x + γ • lmo m) vanishingMomentum x₁ f g ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p)) + ((T + 1 : ℕ) : ℝ) * (L * γ ^ 2 * ρ ^ 2 / 2) ≤
      Δ + γ * (ρ₂ + ζ * ρ) * (Real.sqrt (4 * σ ^ 2 + 8 * L₂ ^ 2 * ρ₂ ^ 2) *
        (4 / 3 * ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))) + ((T + 1 : ℕ) : ℝ) * (L * γ ^ 2 * ρ ^ 2 / 2))
  set E := ∑ k ∈ Finset.range (T + 1), ∫ ξ, dualNorm N (gradient f
    (path (fun x m => x + γ • lmo m) vanishingMomentum x₁ g ξ k).1) ∂(Measure.infinitePi fun _ : ℕ => p)
  rw [hw, hn, hγe] at hcomb
  have hΔ : 0 ≤ Δ := by
    obtain ⟨fmin, hfmin, hgap⟩ := H.lower; linarith [hfmin x₁]
  have hT : (T : ℝ) + 1 = v ^ 4 := by rw [← hn]; push_cast; ring
  rw [hT, hw]
  exact vanishing_algebra hρ hv1 hτ1 hτ2 hc (Real.sqrt_nonneg _) hL hΔ hcomb

theorem uscg_constant_convergence :
    Convergence LongTails.Setups.UscgConstant.spec
      (fun p _ => ⌈((p.Δ / p.ρ + p.L * p.ρ / 2 + (p.ρ₂ / p.ρ + p.ζ) * (2 * p.L₂ * p.ρ₂ + 4 * p.σ) /
        p.α) / p.ε) ^ 2⌉₊ + 1) := by
  apply convergence_of_public_budget (S := LongTails.Setups.UscgConstant.spec)
    (fun p => LongTails.Setups.UscgConstant.horizon p + 1)
  refine ⟨LongTails.Setups.UscgConstant.method, ?_, fun p _ => rfl⟩
  intro p hp f O hadm
  obtain ⟨hdef, hρ, hlmo, hρ₂, hζ0, hζ, hL, hL₂, hσ, hΔ, hα0, hα1, hε⟩ := hp
  obtain ⟨g, P₀, P, hIID, rfl, H⟩ := hadm
  set T := LongTails.Setups.UscgConstant.horizon p
  set γ := 1 / Real.sqrt ((T : ℝ) + 1)
  have hγ : 0 ≤ γ := by positivity
  have hρ₂0 : 0 ≤ p.ρ₂ := by have := hρ₂ 0 (by simp; linarith); simpa using this
  have hR := OracleTemplate.NormBallLMO.unit_bound_of_radius hρ hρ₂
  have hgc := continuous_gradient_of H hL₂
  have hF : Measurable (fun x => dualNorm p.N (gradient f x)) :=
    ((continuous_dualNorm hR (div_nonneg hρ₂0 hρ.le)).comp hgc).measurable
  obtain ⟨-, hbd, -⟩ := uscg_template H hL₂ hL.le hdef hρ hlmo hρ₂ hζ0 hζ hγ
    (α := constantMomentum p.α) (fun k => by simp only [constantMomentum]; split_ifs <;> linarith)
    (fun k => by simp only [constantMomentum]; split_ifs <;> linarith) (by simp [constantMomentum]) 0
  have hstep : Measurable (fun z : Space p.d × Space p.d => z.1 + γ • p.lmo z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul γ)
  have hout := output_integral (fun x m => x + γ • p.lmo m) hstep (constantMomentum p.α) T p.x₁
    H.measurable P₀ P hIID (T + 1) (Nat.le_succ T) (fun x => dualNorm p.N (gradient f x)) hF
    (B := p.ρ₂ / p.ρ * (‖gradient f p.x₁‖ + p.L₂ * (T * (γ * p.ρ₂))))
    (fun j hj ξ => (hbd j ξ).trans (by
      gcongr))
  obtain ⟨hm, hi, he⟩ := hout
  refine ⟨hm, hi, he.le.trans ?_⟩
  have hrate := uscg_constant_rate H hL₂ hL.le hσ hdef hρ hlmo hρ₂ hζ0 hζ hα0 hα1 T
  set M := p.Δ / p.ρ + p.L * p.ρ / 2 + (p.ρ₂ / p.ρ + p.ζ) * (2 * p.L₂ * p.ρ₂ + 4 * p.σ) / p.α
  have hfin : M / Real.sqrt ((T : ℝ) + 1) ≤ p.ε := horizon_sqrt_le (by positivity) hε
  linarith

theorem uscg_vanishing_convergence :
    Convergence LongTails.Setups.UscgVanishing.spec
      (fun p _ => ⌈((2 * p.Δ / p.ρ + 8 / 3 * (p.ρ₂ / p.ρ + p.ζ) *
        Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.ρ₂ ^ 2) + p.L * p.ρ) / p.ε) ^ 4⌉₊ + 1) := by
  apply convergence_of_public_budget (S := LongTails.Setups.UscgVanishing.spec)
    (fun p => LongTails.Setups.UscgVanishing.horizon p + 1)
  refine ⟨LongTails.Setups.UscgVanishing.method, ?_, fun p _ => rfl⟩
  intro p hp f O hadm
  obtain ⟨hdef, hρ, hlmo, hρ₂, hζ0, hζ, hL, hL₂, hσ, hΔ, hτ1, hτ2, hε⟩ := hp
  obtain ⟨g, P₀, P, hIID, rfl, H⟩ := hadm
  set T := LongTails.Setups.UscgVanishing.horizon p
  set γ := p.τ / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)
  have hγ : 0 ≤ γ := by
    have : 0 < p.τ := by linarith
    positivity
  have hρ₂0 : 0 ≤ p.ρ₂ := by have := hρ₂ 0 (by simp; linarith); simpa using this
  have hR := OracleTemplate.NormBallLMO.unit_bound_of_radius hρ hρ₂
  have hgc := continuous_gradient_of H hL₂
  have hF : Measurable (fun x => dualNorm p.N (gradient f x)) :=
    ((continuous_dualNorm hR (div_nonneg hρ₂0 hρ.le)).comp hgc).measurable
  obtain ⟨hα0, hα1, hαone, -⟩ := vanishing_momentum_props
  obtain ⟨-, hbd, -⟩ := uscg_template H hL₂ hL.le hdef hρ hlmo hρ₂ hζ0 hζ hγ hα0 hα1 hαone 0
  have hstep : Measurable (fun z : Space p.d × Space p.d => z.1 + γ • p.lmo z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul γ)
  have hout := output_integral (fun x m => x + γ • p.lmo m) hstep vanishingMomentum T p.x₁
    H.measurable P₀ P hIID (T + 1) (Nat.le_succ T) (fun x => dualNorm p.N (gradient f x)) hF
    (B := p.ρ₂ / p.ρ * (‖gradient f p.x₁‖ + p.L₂ * (T * (γ * p.ρ₂))))
    (fun j hj ξ => (hbd j ξ).trans (by
      gcongr))
  obtain ⟨hm, hi, he⟩ := hout
  refine ⟨hm, hi, he.le.trans ?_⟩
  have hrate := uscg_vanishing_rate H hL₂ hL.le hdef hρ hlmo hρ₂ hζ0 hζ hτ1 hτ2 T
  set M := 2 * p.Δ / p.ρ + 8 / 3 * (p.ρ₂ / p.ρ + p.ζ) *
    Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.ρ₂ ^ 2) + p.L * p.ρ
  have hfin : M / ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ p.ε := horizon_quarter_le hε
  have hsplit := quarter_split (A := 2 * p.Δ / p.ρ + 8 / 3 * (p.ρ₂ / p.ρ + p.ζ) *
    Real.sqrt (4 * p.σ ^ 2 + 8 * p.L₂ ^ 2 * p.ρ₂ ^ 2)) (by positivity : 0 ≤ p.L * p.ρ) T
  linarith

end OracleTemplate.NormBallLMO
