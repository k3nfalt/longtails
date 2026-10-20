import LongTails.Proofs.RiverValleyHillA
import LongTails.Proofs.HessianNcscProcess
import LongTails.Proofs.NormalizedStormOrthogonality

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.RiverValley

section Fresh

variable {Ω : Type*} [MeasurableSpace Ω] {St : Type*} [MeasurableSpace St]

local notation "Pω" p => Measure.infinitePi fun _ : ℕ => p

lemma fresh_expect (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ) (S : (ℕ → Ω) → St)
    (hS : Measurable S) (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ')
    (Φ : St → Ω → ℝ) (hΦ : Measurable (Function.uncurry Φ)) (hΦ0 : ∀ y ω, 0 ≤ Φ y ω)
    (b : St → ℝ) (hb : ∀ y, Integrable (Φ y) p ∧ ∫ ω, Φ y ω ∂p ≤ b y)
    (hbS : Integrable (fun ξ => b (S ξ)) (Pω p)) :
    Integrable (fun ξ : ℕ → Ω => Φ (S ξ) (ξ k)) (Pω p) ∧
      ∫ ξ, Φ (S ξ) (ξ k) ∂(Pω p) ≤ ∫ ξ, b (S ξ) ∂(Pω p) := by
  have hmeas : Measurable (fun ξ : ℕ → Ω => Φ (S ξ) (ξ k)) :=
    hΦ.comp (hS.prodMk (measurable_pi_apply k))
  have hh : Measurable fun z : St × Ω => ENNReal.ofReal (Φ z.1 z.2) :=
    ENNReal.measurable_ofReal.comp hΦ
  have hlin : ∫⁻ ξ, ENNReal.ofReal (Φ (S ξ) (ξ k)) ∂(Pω p) ≤
      ∫⁻ ξ, ENNReal.ofReal (b (S ξ)) ∂(Pω p) := by
    rw [HessianNcsc.fresh_lintegral p k S hS hdep (fun z => ENNReal.ofReal (Φ z.1 z.2)) hh]
    refine lintegral_mono fun ξ => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hb (S ξ)).1
      (Filter.Eventually.of_forall fun ω => hΦ0 _ _)]
    exact ENNReal.ofReal_le_ofReal (hb (S ξ)).2
  have hint := NormalizedStorm.integrable_of_lintegral_le hmeas (fun ξ => hΦ0 _ _) hbS hlin
  refine ⟨hint, ?_⟩
  rw [TwoSidedPL.integral_prefix_dep p k S hS hdep Φ hΦ hint]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ =>
    integral_nonneg fun ω => hΦ0 _ _) hbS (Filter.Eventually.of_forall fun ξ => (hb (S ξ)).2)

end Fresh

section Seq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type*}

noncomputable def schedSeq (g : E → Ω → E) (ηf : ℕ → ℝ) (x0 : E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => x0
  | n + 1 => schedSeq g ηf x0 ξ n - ηf n • g (schedSeq g ηf x0 ξ n) (ξ n)

lemma schedSeq_congr (g : E → Ω → E) (ηf : ℕ → ℝ) (x0 : E) {ξ ξ' : ℕ → Ω} :
    ∀ n, (∀ i, i < n → ξ i = ξ' i) → schedSeq g ηf x0 ξ n = schedSeq g ηf x0 ξ' n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [schedSeq]
      rw [schedSeq_congr g ηf x0 n (fun i hi => h i (by omega)), h n (by omega)]

lemma measurable_schedSeq [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (ηf : ℕ → ℝ)
    (x0 : E) : ∀ n, Measurable (fun ξ : ℕ → Ω => schedSeq g ηf x0 ξ n)
  | 0 => measurable_const
  | n + 1 => by
      have hn := measurable_schedSeq hg ηf x0 n
      simp only [schedSeq]
      exact hn.sub ((hg.comp (hn.prodMk (measurable_pi_apply n))).const_smul _)

lemma schedSeq_eq_of_agree (g : E → Ω → E) {ηf ηf' : ℕ → ℝ} (x0 : E) (ξ : ℕ → Ω) (m : ℕ)
    (h : ∀ i, i < m → ηf i = ηf' i) : ∀ n, n ≤ m → schedSeq g ηf x0 ξ n = schedSeq g ηf' x0 ξ n
  | 0, _ => rfl
  | n + 1, hn => by
      simp only [schedSeq]
      rw [schedSeq_eq_of_agree g x0 ξ m h n (by omega), h n (by omega)]

end Seq

end OracleTemplate.RiverValley

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma grad_dom {hstar : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y) {y : E} (hy : y ∈ Kᗮ) :
    ‖ar K gh y‖ ^ 2 ≤ 2 * Lh * (h y - hstar) := by
  set a := ar K gh y
  have ha : a ∈ Kᗮ := Q_mem _
  have hinner : ⟪gh y, a⟫ = ‖a‖ ^ 2 := by
    have hpq := P_add_Q (K := K) (gh y)
    have h0 : ⟪K.starProjection (gh y), a⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _) ha
    conv_lhs => rw [← hpq]
    rw [inner_add_left, h0, zero_add]
    exact real_inner_self_eq_norm_sq a
  have hdesc : ∀ t : ℝ, t * ‖a‖ ^ 2 - Lh / 2 * t ^ 2 * ‖a‖ ^ 2 ≤ h y - hstar := by
    intro t
    have hb := Gradient.smooth_upper_bound H.hgh H.gh_lip y (y - t • a)
    have hm : y - t • a ∈ Kᗮ := Kᗮ.sub_mem hy (Kᗮ.smul_mem _ ha)
    have hl := hlow _ hm
    rw [show y - t • a - y = -(t • a) by abel, inner_neg_right, inner_smul_right, hinner,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hb
    nlinarith
  rcases H.Lh_nn.lt_or_eq with hL | hL
  · have := hdesc (1 / Lh)
    have e : 1 / Lh * ‖a‖ ^ 2 - Lh / 2 * (1 / Lh) ^ 2 * ‖a‖ ^ 2 = ‖a‖ ^ 2 / (2 * Lh) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at this
    linarith
  · rw [← hL]
    by_contra hc
    have hpos : 0 < ‖a‖ ^ 2 := by
      rcases (sq_nonneg ‖a‖).lt_or_eq with h1 | h1
      · exact h1
      · exfalso; apply hc; rw [← h1]; simp
    have := hdesc ((h y - hstar + 1) / ‖a‖ ^ 2)
    rw [← hL] at this
    have hne : ‖a‖ ≠ 0 := by intro h0; rw [h0] at hpos; simp at hpos
    have e : (h y - hstar + 1) / ‖a‖ ^ 2 * ‖a‖ ^ 2 - 0 / 2 * ((h y - hstar + 1) / ‖a‖ ^ 2) ^ 2 *
        ‖a‖ ^ 2 = h y - hstar + 1 := by field_simp; ring
    linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma V_lower {hstar lam : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y)
    (hlam : Lh * (Luv / μ) ^ 2 / 2 ≤ lam) (x : E) :
    hstar ≤ Vfun K h gh φ Jφ lam x := by
  set y := Kᗮ.starProjection x
  set a := ar K gh y
  set w := wv K φ x
  set Γ := Luv / μ
  have hy : y ∈ Kᗮ := Q_mem _
  have hD := H.grad_dom hlow hy
  have hm := (H.mr_bounds y).1
  have hD0 : 0 ≤ h y - hstar := sub_nonneg.mpr (hlow y hy)
  have hcross : -⟪mr K gh Jφ y, w⟫ ≤ Γ * ‖a‖ * ‖w‖ := by
    have := real_inner_le_norm (-(mr K gh Jφ y)) w
    rw [inner_neg_left, norm_neg] at this
    have := mul_le_mul_of_nonneg_right hm (norm_nonneg w)
    linarith
  have key : Γ * ‖a‖ * ‖w‖ ≤ (h y - hstar) + Lh * Γ ^ 2 / 2 * ‖w‖ ^ 2 := by
    rcases (show 0 ≤ Lh * Γ ^ 2 / 2 by have := H.Lh_nn; positivity).lt_or_eq with hc | hc
    · have hLh : Lh ≠ 0 := by intro h2; rw [h2] at hc; simp at hc
      have hΓne : Γ ≠ 0 := by intro h2; rw [h2] at hc; simp at hc
      have hLhpos : 0 < Lh := lt_of_le_of_ne H.Lh_nn (Ne.symm hLh)
      have h1 : Γ * ‖a‖ * ‖w‖ ≤ ‖a‖ ^ 2 / (2 * Lh) + Lh * Γ ^ 2 / 2 * ‖w‖ ^ 2 := by
        have h0 : 0 ≤ (Lh * Γ * ‖w‖ - ‖a‖) ^ 2 / (2 * Lh) := by positivity
        have e : (Lh * Γ * ‖w‖ - ‖a‖) ^ 2 / (2 * Lh) =
            ‖a‖ ^ 2 / (2 * Lh) + Lh * Γ ^ 2 / 2 * ‖w‖ ^ 2 - Γ * ‖a‖ * ‖w‖ := by
          field_simp; ring
        linarith
      have h3 : ‖a‖ ^ 2 / (2 * Lh) ≤ h y - hstar := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    · rw [← hc, zero_mul, add_zero]
      have : Lh * Γ ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h2 | h2
      · have : ‖a‖ ^ 2 ≤ 0 := by rw [h2] at hD; linarith
        have : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
        rw [this]; simp; linarith
      · have : Γ = 0 := by nlinarith [sq_nonneg Γ]
        rw [this]; simp; linarith
  have hl : Lh * Γ ^ 2 / 2 * ‖w‖ ^ 2 ≤ lam * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hlam (sq_nonneg _)
  show hstar ≤ h y + ⟪mr K gh Jφ y, w⟫ + lam * ‖w‖ ^ 2
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma V_init {hstar lam : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y) (hlamμ : lam ≤ μ / 8) (hΓ : 16 * Luv ≤ μ)
    (hLh : 16 * Lh ≤ μ) (x : E) :
    Vfun K h gh φ Jφ lam x - hstar ≤ 2 * (fval K h φ A x - hstar) := by
  set y := Kᗮ.starProjection x
  set a := ar K gh y
  set w := wv K φ x
  set Γ := Luv / μ
  have hy : y ∈ Kᗮ := Q_mem _
  have hD := H.grad_dom hlow hy
  have hm := (H.mr_bounds y).1
  have hD0 : 0 ≤ h y - hstar := sub_nonneg.mpr (hlow y hy)
  have hcross : ⟪mr K gh Jφ y, w⟫ ≤ Γ * ‖a‖ * ‖w‖ := by
    have := real_inner_le_norm (mr K gh Jφ y) w
    have := mul_le_mul_of_nonneg_right hm (norm_nonneg w)
    linarith
  have hμ := H.μpos
  have hAw : μ * ‖w‖ ^ 2 ≤ ⟪A w, w⟫ := H.A_lower w (wv_mem H x)
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn hμ.le
  have hΓ16 : Γ ≤ 1 / 16 := by simp only [Γ]; rw [div_le_iff₀ hμ]; linarith
  have key : Γ * ‖a‖ * ‖w‖ ≤ (h y - hstar) + μ / 8 * ‖w‖ ^ 2 := by
    have h1 : Γ * ‖a‖ * ‖w‖ ≤ 2 * Γ ^ 2 * ‖a‖ ^ 2 / μ + μ / 8 * ‖w‖ ^ 2 := by
      have h0 : 0 ≤ (μ / 8) * (‖w‖ - 4 * Γ * ‖a‖ / μ) ^ 2 := by positivity
      have e : (μ / 8) * (‖w‖ - 4 * Γ * ‖a‖ / μ) ^ 2 =
          μ / 8 * ‖w‖ ^ 2 + 2 * Γ ^ 2 * ‖a‖ ^ 2 / μ - Γ * ‖a‖ * ‖w‖ := by field_simp; ring
      linarith
    have h2 : 2 * Γ ^ 2 * ‖a‖ ^ 2 / μ ≤ h y - hstar := by
      rw [div_le_iff₀ hμ]
      have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
      have := mul_le_mul hΓ2 hD (sq_nonneg _) (by norm_num)
      nlinarith
    linarith
  have hfv : fval K h φ A x = h y + 1 / 2 * ⟪A w, w⟫ := rfl
  show h y + ⟪mr K gh Jφ y, w⟫ + lam * ‖w‖ ^ 2 - hstar ≤ 2 * (fval K h φ A x - hstar)
  rw [hfv]
  have := mul_le_mul_of_nonneg_right hlamμ (sq_nonneg ‖w‖)
  nlinarith

end Model

end OracleTemplate.RiverValley
