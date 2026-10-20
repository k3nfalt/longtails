import LongTails.Proofs.RiverValleyRun
import LongTails.Proofs.RiverValleySequences

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.RiverValley

lemma int_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hfm : AEStronglyMeasurable f μ)
    (hf2 : Integrable (fun a => f a ^ 2) μ) :
    Integrable f μ ∧ ∫ a, f a ∂μ ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) := by
  have hfi : Integrable f μ := by
    refine Integrable.mono' ((hf2.add (integrable_const 1)).div_const 2) hfm
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 a)]
    show f a ≤ (f a ^ 2 + 1) / 2
    nlinarith [sq_nonneg (f a - 1)]
  refine ⟨hfi, ?_⟩
  set c := ∫ a, f a ∂μ
  have hc0 : 0 ≤ c := integral_nonneg hf0
  have h0 : 0 ≤ ∫ a, (f a - c) ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have e : ∀ a, (f a - c) ^ 2 = f a ^ 2 + (-2 * c) * f a + c ^ 2 := fun a => by ring
  simp_rw [e] at h0
  have g1 : Integrable (fun a => (-2 * c) * f a) μ := hfi.const_mul _
  have g12 : Integrable (fun a => f a ^ 2 + (-2 * c) * f a) μ := hf2.add g1
  rw [integral_add g12 (integrable_const _), integral_add hf2 g1, integral_const_mul,
    integral_const] at h0
  simp only [probReal_univ, one_smul] at h0
  rw [Real.le_sqrt hc0 (integral_nonneg fun a => sq_nonneg _)]
  nlinarith

lemma sum_sqrt_le (s : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i ∈ s, Real.sqrt (x i) ≤ Real.sqrt (s.card * ∑ i ∈ s, x i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (x i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have e : ∀ i ∈ s, Real.sqrt (x i) ^ 2 = x i := fun i _ => Real.sq_sqrt (hx i)
  rw [Finset.sum_congr rfl e] at h
  have h0 : 0 ≤ ∑ i ∈ s, Real.sqrt (x i) := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  rw [Real.le_sqrt h0 (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hx i))]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

local notation "Pω" p => Measure.infinitePi fun _ : ℕ => p

noncomputable def schedOf (ηs ηc : ℝ) (τ : ℕ) : ℕ → ℝ := fun n => if n < τ then ηs else ηc

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradF_norm (x : E) : ‖gradF K gh φ Jφ A x‖ ≤
    ‖ar K gh (Kᗮ.starProjection x)‖ + (1 + Luv / μ) * ‖A (wv K φ x)‖ := by
  rw [gradF_eq]
  have h1 := H.adjJ_norm (Kᗮ.starProjection x) (A (wv K φ x))
  calc _ ≤ ‖ar K gh (Kᗮ.starProjection x) + A (wv K φ x)‖ +
        ‖ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x))‖ :=
        norm_sub_le _ _
    _ ≤ ‖ar K gh (Kᗮ.starProjection x)‖ + ‖A (wv K φ x)‖ + Luv / μ * ‖A (wv K φ x)‖ :=
        add_le_add (norm_add_le _ _) h1
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
lemma lam_le {σu σv : ℝ} (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) :
    lamOf Lh ρh G Luv μ Lv LJ ρJ σu ≤ μ / 8 := by
  have hμ := H.μpos
  have hLv : 0 < Lv := lt_of_lt_of_le hμ H.μ_le
  have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; have := H.Luv_nn
  set Lm' := Luv / μ * Lh + 2 * LJ * G
  set c' := 2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2
  have hLm0 : 0 ≤ Lm' := by positivity
  have hLm := R.hLm
  have h1 : 256 * Lm' ^ 2 / μ ≤ μ / 16 := by
    rw [div_le_div_iff₀ hμ (by norm_num)]
    have := mul_le_mul hLm hLm (by positivity) hμ.le
    nlinarith
  have h2 : 32 * Lm' * Luv / μ ≤ μ / 32 := by
    rw [div_le_div_iff₀ hμ (by norm_num)]
    have := mul_le_mul hLm R.hΓ (by positivity) hμ.le
    nlinarith
  have h3 : 2 * c' * σu / Lv ≤ μ / 32 := by
    rw [div_le_div_iff₀ hLv (by norm_num)]; linarith [R.hc]
  simp only [lamOf]
  rw [add_div]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma w0_bound {hstar : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y) (x : E) :
    μ * ‖wv K φ x‖ ^ 2 ≤ 2 * (fval K h φ A x - hstar) := by
  have h1 := hlow _ (Q_mem (K := K) x)
  have h2 : μ * ‖wv K φ x‖ ^ 2 ≤ ⟪A (wv K φ x), wv K φ x⟫ := H.A_lower _ (wv_mem H x)
  show μ * ‖wv K φ x‖ ^ 2 ≤ 2 * (h (Kᗮ.starProjection x) +
    1 / 2 * ⟪A (wv K φ x), wv K φ x⟫ - hstar)
  linarith

lemma stable_avg {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {hstar Δ : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y)
    (x0 : E) (hΔ : fval K h φ A x0 - hstar ≤ Δ) {ηs : ℝ} (hηs0 : 0 < ηs)
    (hηs : 8 * ηs * Lv ≤ 1) (M : ℕ) :
    let Γ := Luv / μ
    let Y := fun n ξ => schedSeq g (fun _ => ηs) x0 ξ n
    let N := NOf Lh ρh G Luv μ Lv LJ ρJ σu σv
    let Sw := (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) / μ
    let Hw := 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)
    (∑ n ∈ Finset.range M, ∫ ξ, ‖ar K gh (Kᗮ.starProjection (Y n ξ))‖ ^ 2 ∂(Pω p)) ≤
        M * (4 * Δ / (ηs * M) + 2 * ηs * N) ∧
      (∑ n ∈ Finset.range M, ∫ ξ, ‖wv K φ (Y n ξ)‖ ^ 2 ∂(Pω p)) ≤
        M * (4 * Δ / (μ ^ 2 * ηs * M) + 2 * Sw * (4 * Δ / (ηs * M) + 2 * ηs * N) / μ +
          2 * ηs * Hw / μ) := by
  intro Γ Y N Sw Hw
  have hμ := H.μpos
  have hηf : ∀ n, 0 ≤ (fun _ => ηs) n ∧ 8 * (fun (_ : ℕ) => ηs) n * Lv ≤ 1 :=
    fun _ => ⟨hηs0.le, hηs⟩
  have rr := fun n => H.run_rec O R hlow (fun _ => ηs) hηf x0 n
  set lam := lamOf Lh ρh G Luv μ Lv LJ ρJ σu
  have hlam0 : 0 ≤ lam := le_trans (by have := H.Lh_nn; positivity) (H.lam_ge (ρh := ρh)
    (ρJ := ρJ) R.hσu)
  set vY := fun n => ∫ ξ, (Vfun K h gh φ Jφ lam (Y n ξ) - hstar) ∂(Pω p)
  set pY := fun n => ∫ ξ, ‖ar K gh (Kᗮ.starProjection (Y n ξ))‖ ^ 2 ∂(Pω p)
  set sY := fun n => ∫ ξ, ‖wv K φ (Y n ξ)‖ ^ 2 ∂(Pω p)
  have hv0 : ∀ n, 0 ≤ vY n := fun n => integral_nonneg fun ξ =>
    sub_nonneg.mpr (H.V_lower hlow (H.lam_ge (ρh := ρh) (ρJ := ρJ) R.hσu) _)
  have hs0 : ∀ n, 0 ≤ sY n := fun n => integral_nonneg fun ξ => sq_nonneg _
  have hp0 : ∀ n, 0 ≤ pY n := fun n => integral_nonneg fun ξ => sq_nonneg _
  have htele : ∀ n, vY (n + 1) ≤ vY n - ηs / 2 * pY n + ηs ^ 2 * N := by
    intro n
    have h1 := (rr n).1
    have : 0 ≤ ηs * lam * μ / 2 * sY n := by have := hs0 n; positivity
    simp only [vY, pY, sY, Y] at h1 this ⊢
    linarith
  have hsum := tele_sum hv0 htele M
  have hV0 : vY 0 ≤ 2 * Δ := by
    have := H.V_init hlow (H.lam_le R) R.hΓ R.hLh x0
    simp only [vY, Y, schedSeq, integral_const, probReal_univ, one_smul]
    linarith
  have hpsum : ∑ n ∈ Finset.range M, pY n ≤ M * (4 * Δ / (ηs * M) + 2 * ηs * N) := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have e : (M : ℝ) * (4 * Δ / (ηs * M) + 2 * ηs * N) = (2 / ηs) * (2 * Δ + M * ηs ^ 2 * N) := by
        field_simp; ring
      rw [e]
      have : ηs / 2 * ∑ n ∈ Finset.range M, pY n ≤ 2 * Δ + M * ηs ^ 2 * N := by
        have := hsum; nlinarith
      calc ∑ n ∈ Finset.range M, pY n = (2 / ηs) * (ηs / 2 * ∑ n ∈ Finset.range M, pY n) := by
            field_simp
        _ ≤ (2 / ηs) * (2 * Δ + M * ηs ^ 2 * N) :=
            mul_le_mul_of_nonneg_left this (by positivity)
  refine ⟨hpsum, ?_⟩
  have hcontr : ∀ n, sY (n + 1) ≤ (1 - ηs * μ / 2) * sY n + ηs * Sw * pY n + ηs ^ 2 * Hw := by
    intro n
    have h1 := (rr n).2.1
    simp only [sY, pY, Y, Sw, Hw, Γ] at h1 ⊢
    have e : ηs * (8 * (Luv / μ) ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Luv / μ * (LJ * G) / μ) / μ *
        ∫ ξ, ‖ar K gh (Kᗮ.starProjection (schedSeq g (fun _ => ηs) x0 ξ n))‖ ^ 2 ∂(Pω p) =
        ηs * ((8 * (Luv / μ) ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Luv / μ * (LJ * G) / μ) / μ) *
        ∫ ξ, ‖ar K gh (Kᗮ.starProjection (schedSeq g (fun _ => ηs) x0 ξ n))‖ ^ 2 ∂(Pω p) := by
      ring
    linarith
  have hcs := contract_sum hs0 hcontr M
  have hs00 : sY 0 ≤ 2 * Δ / μ := by
    have := H.w0_bound hlow x0
    simp only [sY, Y, schedSeq, integral_const, probReal_univ, one_smul]
    rw [le_div_iff₀ hμ]; linarith
  have hSw : 0 ≤ Sw := by
    have := H.Luv_nn; have := H.LJ_nn; have := H.G_nn; simp only [Sw, Γ]; positivity
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hk : 0 < ηs * μ / 2 := by positivity
    have h1 : ηs * μ / 2 * ∑ n ∈ Finset.range M, sY n ≤
        2 * Δ / μ + ηs * Sw * (M * (4 * Δ / (ηs * M) + 2 * ηs * N)) + M * (ηs ^ 2 * Hw) := by
      have := mul_le_mul_of_nonneg_left hpsum (by positivity : (0:ℝ) ≤ ηs * Sw)
      linarith
    have e : (M : ℝ) * (4 * Δ / (μ ^ 2 * ηs * M) + 2 * Sw * (4 * Δ / (ηs * M) + 2 * ηs * N) / μ +
        2 * ηs * Hw / μ) = (2 / (ηs * μ)) * (2 * Δ / μ + ηs * Sw * (M * (4 * Δ / (ηs * M) +
          2 * ηs * N)) + M * (ηs ^ 2 * Hw)) := by
      field_simp; ring
    rw [e]
    calc ∑ n ∈ Finset.range M, sY n = (2 / (ηs * μ)) * (ηs * μ / 2 * ∑ n ∈ Finset.range M, sY n) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradF_cont : Continuous (gradF K gh φ Jφ A) := by
  have hQ : Continuous (Kᗮ.starProjection : E → E) := Kᗮ.starProjection.continuous
  have hgh : Continuous gh := LipschitzWith.continuous (K := ⟨Lh, H.Lh_nn⟩)
    (LipschitzWith.of_dist_le_mul fun y y' => by
      rw [dist_eq_norm, dist_eq_norm]; exact H.gh_lip y y')
  have hJ : Continuous Jφ := LipschitzWith.continuous (K := ⟨LJ, H.LJ_nn⟩)
    (LipschitzWith.of_dist_le_mul fun y y' => by
      rw [dist_eq_norm, dist_eq_norm]; exact H.J_lip y y')
  have hAw : Continuous (fun x => A (wv K φ x)) := A.continuous.comp H.wv_cont
  have hadj : Continuous (fun x => ContinuousLinearMap.adjoint (Jφ (Kᗮ.starProjection x))) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).continuous.comp (hJ.comp hQ)
  exact ((hQ.comp (hgh.comp hQ)).add hAw).sub (hQ.comp (hadj.clm_apply hAw))

lemma cool_tau {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {hstar : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y)
    (x0 : E) {ηs ηc : ℝ} (hηs0 : 0 ≤ ηs) (hηs : 8 * ηs * Lv ≤ 1) (hηc0 : 0 ≤ ηc)
    (hηc : 8 * ηc * Lv ≤ 1) (τ Kc : ℕ) (hK : 10 * Lh * ηc * Kc ≤ 1) :
    let Γ := Luv / μ
    let Y := fun n ξ => schedSeq g (fun _ => ηs) x0 ξ n
    let Hw := 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)
    let SA := 8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)
    let HA := 4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4
    let Ca := (2 * G * ρh + Lh ^ 2) * σu ^ 2
    let θ := 8 * Lh * Luv ^ 2 / μ
    let P := 2 * (∫ ξ, ‖ar K gh (Kᗮ.starProjection (Y τ ξ))‖ ^ 2 ∂(Pω p) +
      θ * ∫ ξ, ‖wv K φ (Y τ ξ)‖ ^ 2 ∂(Pω p) + Kc * ηc ^ 2 * (Ca + θ * Hw))
    Integrable (fun ξ => ‖gradF K gh φ Jφ A (schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + Kc))‖) (Pω p) ∧
    ∫ ξ, ‖gradF K gh φ Jφ A (schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + Kc))‖ ∂(Pω p) ≤
      Real.sqrt P + (1 + Γ) * Real.sqrt ((1 - ηc * μ / 2) ^ Kc * (Lv ^ 2 *
        ∫ ξ, ‖wv K φ (Y τ ξ)‖ ^ 2 ∂(Pω p)) + 2 / μ * (SA * P + ηc * HA)) := by
  intro Γ Y Hw SA HA Ca θ P
  set Sw := (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) / μ
  have hμ := H.μpos
  have hLv : 0 < Lv := lt_of_lt_of_le hμ H.μ_le
  have hηf : ∀ n, 0 ≤ schedOf ηs ηc τ n ∧ 8 * schedOf ηs ηc τ n * Lv ≤ 1 := by
    intro n; simp only [schedOf]; split_ifs <;> exact ⟨by assumption, by assumption⟩
  have rr := fun n => H.run_rec O R hlow (schedOf ηs ηc τ) hηf x0 n
  have ri := H.run_int O R hlow (schedOf ηs ηc τ) hηf x0
  set X := fun n ξ => schedSeq g (schedOf ηs ηc τ) x0 ξ n
  have hXY : ∀ ξ, X τ ξ = Y τ ξ := fun ξ =>
    schedSeq_eq_of_agree g x0 ξ τ (fun i hi => by simp [schedOf, hi]) τ le_rfl
  have hsch : ∀ k, schedOf ηs ηc τ (τ + k) = ηc := fun k => by simp [schedOf]
  set pc := fun k => ∫ ξ, ‖ar K gh (Kᗮ.starProjection (X (τ + k) ξ))‖ ^ 2 ∂(Pω p)
  set sc := fun k => ∫ ξ, ‖wv K φ (X (τ + k) ξ)‖ ^ 2 ∂(Pω p)
  set qc := fun k => ∫ ξ, ‖A (wv K φ (X (τ + k) ξ))‖ ^ 2 ∂(Pω p)
  have hp : ∀ k, k < Kc → pc (k + 1) ≤ (1 + 4 * Lh * ηc) * pc k +
      2 * Lh * ηc * Luv ^ 2 * sc k + ηc ^ 2 * Ca := by
    intro k _
    have := (rr (τ + k)).2.2.2
    rw [hsch k] at this
    exact this
  have hs : ∀ k, k < Kc → sc (k + 1) ≤ (1 - ηc * μ / 2) * sc k + ηc * Sw * pc k + ηc ^ 2 * Hw := by
    intro k _
    have h0 := (rr (τ + k)).2.1
    rw [hsch k] at h0
    have h1 : sc (k + 1) ≤ (1 - ηc * μ / 2) * sc k +
        ηc * (8 * (Luv / μ) ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Luv / μ * (LJ * G) / μ) / μ * pc k +
        ηc ^ 2 * Hw := h0
    have e : ηc * (8 * (Luv / μ) ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Luv / μ * (LJ * G) / μ) / μ *
        pc k = ηc * Sw * pc k := by simp only [Sw, Γ]; ring
    linarith
  have hq : ∀ k, k < Kc → qc (k + 1) ≤ (1 - ηc * μ / 2) * qc k + ηc * SA * pc k + ηc ^ 2 * HA := by
    intro k _
    have h0 := (rr (τ + k)).2.2.1
    rw [hsch k] at h0
    exact h0
  have hregΓ : Γ ≤ 1 / 16 := by simp only [Γ]; rw [div_le_iff₀ hμ]; linarith [R.hΓ]
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn hμ.le
  have hLJG : 128 * (LJ * G) ≤ μ := by
    have := R.hLm; have := mul_nonneg hΓ0 H.Lh_nn; nlinarith
  have hθ : 8 * Luv ^ 2 * Sw ≤ μ := by
    have hLuv : Luv = Γ * μ := by simp only [Γ]; field_simp
    have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
    have a1 : (LJ * G) / μ ≤ 1 / 128 := by rw [div_le_iff₀ hμ]; linarith
    have a0 : 0 ≤ (LJ * G) / μ := by have := H.LJ_nn; have := H.G_nn; positivity
    have a2 : 16 * (LJ * G) ^ 2 / μ ^ 2 ≤ 16 / 16384 := by
      have : (LJ * G) ^ 2 / μ ^ 2 = ((LJ * G) / μ) ^ 2 := by ring
      rw [mul_div_assoc, this]
      nlinarith
    have a3 : Γ * (LJ * G) / μ ≤ 1 / 2048 := by
      rw [mul_div_assoc]; nlinarith
    have e : 8 * Luv ^ 2 * Sw = μ * (8 * Γ ^ 2 * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 +
        Γ * (LJ * G) / μ)) := by simp only [Sw]; rw [hLuv]; field_simp
    rw [e]
    have : 8 * Γ ^ 2 * (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) ≤ 1 := by
      have h1 : 8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ ≤ 1 := by linarith
      have h2 : 8 * Γ ^ 2 ≤ 1 := by linarith
      have h3 : 0 ≤ 8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ := by
        have : 0 ≤ Γ * (LJ * G) / μ := by rw [mul_div_assoc]; exact mul_nonneg hΓ0 a0
        have : 0 ≤ 16 * (LJ * G) ^ 2 / μ ^ 2 := by positivity
        have : 0 ≤ 8 * Γ ^ 2 := by positivity
        linarith
      nlinarith
    nlinarith
  have hημ : ηc * μ ≤ 1 := by have := mul_le_mul_of_nonneg_left H.μ_le hηc0; linarith
  have hLJ := H.LJ_nn
  have hG := H.G_nn
  have hσu := R.hσu
  have hLJG0 : 0 ≤ LJ * G := mul_nonneg hLJ hG
  have hSA : 0 ≤ SA := by
    have := mul_nonneg hΓ0 hLJG0
    have : 0 ≤ 8 * Γ ^ 2 * μ := by positivity
    have : 0 ≤ 16 * (LJ * G) ^ 2 / μ := by positivity
    simp only [SA]; linarith
  have hCa : 0 ≤ Ca := by have := H.ρh_nn; simp only [Ca]; positivity
  have hHw : 0 ≤ Hw := by
    have : 0 ≤ Γ * G * LJ * σu ^ 2 / (4 * Lv) := by
      apply div_nonneg _ (by positivity)
      have := mul_nonneg (mul_nonneg hΓ0 hG) hLJ; positivity
    have : 0 ≤ 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
        8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) := by positivity
    simp only [Hw]; linarith
  have hHA : 0 ≤ HA := by
    have : 0 ≤ Γ * μ * G * LJ * σu ^ 2 / 4 := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hΓ0 hμ.le) hG) hLJ; positivity
    have : 0 ≤ 4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
        8 * Lv * LJ ^ 2 * σu ^ 4 / μ := by positivity
    simp only [HA]; linarith
  have hcb := cooldown_bound (p := pc) (s := sc) (q := qc) hηc0 H.Lh_nn hμ hημ hSA hCa hHw hHA
    (fun k => integral_nonneg fun ξ => sq_nonneg _) (fun k => integral_nonneg fun ξ => sq_nonneg _)
    hp hs hq hθ hK
  have hpc0 : pc 0 = ∫ ξ, ‖ar K gh (Kᗮ.starProjection (Y τ ξ))‖ ^ 2 ∂(Pω p) := by
    simp only [pc, add_zero]; congr 1; funext ξ; rw [hXY ξ]
  have hsc0 : sc 0 = ∫ ξ, ‖wv K φ (Y τ ξ)‖ ^ 2 ∂(Pω p) := by
    simp only [sc, add_zero]; congr 1; funext ξ; rw [hXY ξ]
  have hqc0 : qc 0 ≤ Lv ^ 2 * ∫ ξ, ‖wv K φ (Y τ ξ)‖ ^ 2 ∂(Pω p) := by
    rw [← hsc0, ← integral_const_mul]
    refine integral_mono (ri τ).2.2.1 ((ri τ).2.1.const_mul _) fun ξ => ?_
    have h1 := H.A_upper _ (wv_mem H (X (τ + 0) ξ))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow] at h2
    exact h2
  rw [hpc0, hsc0] at hcb
  obtain ⟨hpK, hqK⟩ := hcb
  have hqK' : qc Kc ≤ (1 - ηc * μ / 2) ^ Kc * (Lv ^ 2 * ∫ ξ, ‖wv K φ (Y τ ξ)‖ ^ 2 ∂(Pω p)) +
      2 / μ * (SA * P + ηc * HA) := by
    have hr : 0 ≤ (1 - ηc * μ / 2) ^ Kc := pow_nonneg (by linarith) _
    have := mul_le_mul_of_nonneg_left hqc0 hr
    simp only [P]
    linarith
  -- final
  obtain ⟨iV, iw, iA, ia⟩ := ri (τ + Kc)
  have hma : AEStronglyMeasurable (fun ξ => ‖ar K gh (Kᗮ.starProjection (X (τ + Kc) ξ))‖) (Pω p) :=
    (((H.ar_cont.comp Kᗮ.starProjection.continuous).measurable.comp
      (measurable_schedSeq O.meas _ x0 (τ + Kc))).norm).aestronglyMeasurable
  have hmA : AEStronglyMeasurable (fun ξ => ‖A (wv K φ (X (τ + Kc) ξ))‖) (Pω p) :=
    ((((A.continuous.comp H.wv_cont).measurable.comp
      (measurable_schedSeq O.meas _ x0 (τ + Kc))).norm)).aestronglyMeasurable
  obtain ⟨ia1, ha⟩ := int_le_sqrt (fun ξ => norm_nonneg _) hma ia
  obtain ⟨iA1, hA⟩ := int_le_sqrt (fun ξ => norm_nonneg _) hmA iA
  have hgm : Measurable (fun ξ => ‖gradF K gh φ Jφ A (X (τ + Kc) ξ)‖) :=
    (H.gradF_cont.measurable.comp (measurable_schedSeq O.meas _ x0 (τ + Kc))).norm
  have hbd : ∀ ξ, ‖gradF K gh φ Jφ A (X (τ + Kc) ξ)‖ ≤
      ‖ar K gh (Kᗮ.starProjection (X (τ + Kc) ξ))‖ + (1 + Γ) * ‖A (wv K φ (X (τ + Kc) ξ))‖ :=
    fun ξ => H.gradF_norm _
  have hbd' : ∀ ξ, ‖‖gradF K gh φ Jφ A (X (τ + Kc) ξ)‖‖ ≤
      ‖ar K gh (Kᗮ.starProjection (X (τ + Kc) ξ))‖ + (1 + Γ) * ‖A (wv K φ (X (τ + Kc) ξ))‖ := by
    intro ξ; rw [norm_norm]; exact hbd ξ
  have hgi : Integrable (fun ξ => ‖gradF K gh φ Jφ A (X (τ + Kc) ξ)‖) (Pω p) :=
    Integrable.mono' (ia1.add (iA1.const_mul _)) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd')
  refine ⟨hgi, ?_⟩
  have iB : Integrable (fun ξ => ‖ar K gh (Kᗮ.starProjection (X (τ + Kc) ξ))‖ +
      (1 + Γ) * ‖A (wv K φ (X (τ + Kc) ξ))‖) (Pω p) := ia1.add (iA1.const_mul _)
  have h1 := integral_mono hgi iB hbd
  have iC : Integrable (fun ξ => (1 + Γ) * ‖A (wv K φ (X (τ + Kc) ξ))‖) (Pω p) := iA1.const_mul _
  rw [integral_add ia1 iC, integral_const_mul] at h1
  have h2 : Real.sqrt (pc Kc) ≤ Real.sqrt P := Real.sqrt_le_sqrt (by simpa [P] using hpK)
  have h3 : Real.sqrt (qc Kc) ≤ Real.sqrt ((1 - ηc * μ / 2) ^ Kc * (Lv ^ 2 *
      ∫ ξ, ‖wv K φ (Y τ ξ)‖ ^ 2 ∂(Pω p)) + 2 / μ * (SA * P + ηc * HA)) := Real.sqrt_le_sqrt hqK'
  have h4 := mul_le_mul_of_nonneg_left (hA.trans h3) (by linarith : (0:ℝ) ≤ 1 + Γ)
  have h5 := ha.trans h2
  linarith

set_option maxHeartbeats 800000 in
lemma master {g : E → Ω → E} {σu σv : ℝ} (O : Orc K p g (gradF K gh φ Jφ A) σu σv)
    (R : Regime Lh ρh G Luv μ Lv LJ ρJ σu σv) {hstar Δ : ℝ} (hlow : ∀ y ∈ Kᗮ, hstar ≤ h y)
    (x0 : E) (hΔ : fval K h φ A x0 - hstar ≤ Δ) {ηs ηc : ℝ} (hηs0 : 0 < ηs)
    (hηs : 8 * ηs * Lv ≤ 1) (hηc0 : 0 ≤ ηc) (hηc : 8 * ηc * Lv ≤ 1) (T Kc : ℕ)
    (hK : 10 * Lh * ηc * Kc ≤ 1) :
    let Γ := Luv / μ
    let N := NOf Lh ρh G Luv μ Lv LJ ρJ σu σv
    let Sw := (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) / μ
    let Hw := 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)
    let SA := 8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)
    let HA := 4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4
    let Ca := (2 * G * ρh + Lh ^ 2) * σu ^ 2
    let θ := 8 * Lh * Luv ^ 2 / μ
    let M : ℝ := T + 1
    let A1 := 4 * Δ / (ηs * M) + 2 * ηs * N
    let A2 := 4 * Δ / (μ ^ 2 * ηs * M) + 2 * Sw * A1 / μ + 2 * ηs * Hw / μ
    let Pb := 2 * (A1 + θ * A2 + Kc * ηc ^ 2 * (Ca + θ * Hw))
    let Qb := (1 - ηc * μ / 2) ^ Kc * (Lv ^ 2 * A2) + 2 / μ * (SA * Pb + ηc * HA)
    (∀ τ, Integrable (fun ξ => ‖gradF K gh φ Jφ A (schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + Kc))‖)
      (Pω p)) ∧
    1 / M * ∑ τ ∈ Finset.range (T + 1),
        ∫ ξ, ‖gradF K gh φ Jφ A (schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + Kc))‖ ∂(Pω p) ≤
      Real.sqrt Pb + (1 + Γ) * Real.sqrt Qb := by
  intro Γ N Sw Hw SA HA Ca θ M A1 A2 Pb Qb
  have hμ := H.μpos
  have hM : (0 : ℝ) < M := by positivity
  have ct := fun τ => H.cool_tau O R hlow x0 hηs0.le hηs hηc0 hηc τ Kc hK
  refine ⟨fun τ => (ct τ).1, ?_⟩
  obtain ⟨hpS, hsS⟩ := H.stable_avg O R hlow x0 hΔ hηs0 hηs (T + 1)
  set Y := fun n ξ => schedSeq g (fun _ => ηs) x0 ξ n
  set pY := fun n => ∫ ξ, ‖ar K gh (Kᗮ.starProjection (Y n ξ))‖ ^ 2 ∂(Pω p)
  set sY := fun n => ∫ ξ, ‖wv K φ (Y n ξ)‖ ^ 2 ∂(Pω p)
  have hp0 : ∀ n, 0 ≤ pY n := fun n => integral_nonneg fun ξ => sq_nonneg _
  have hs0 : ∀ n, 0 ≤ sY n := fun n => integral_nonneg fun ξ => sq_nonneg _
  set Pt := fun τ => 2 * (pY τ + θ * sY τ + Kc * ηc ^ 2 * (Ca + θ * Hw))
  set Qt := fun τ => (1 - ηc * μ / 2) ^ Kc * (Lv ^ 2 * sY τ) + 2 / μ * (SA * Pt τ + ηc * HA)
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn hμ.le
  have hθ0 : 0 ≤ θ := by have := H.Lh_nn; have := H.Luv_nn; positivity
  have hLJ := H.LJ_nn; have hG := H.G_nn; have hσu := R.hσu
  have hLv : 0 < Lv := lt_of_lt_of_le hμ H.μ_le
  have hCa : 0 ≤ Ca := by have := H.ρh_nn; positivity
  have hHw : 0 ≤ Hw := by
    have : 0 ≤ Γ * G * LJ * σu ^ 2 / (4 * Lv) := by
      apply div_nonneg _ (by positivity)
      have := mul_nonneg (mul_nonneg hΓ0 hG) hLJ; positivity
    have : 0 ≤ 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
        8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) := by positivity
    simp only [Hw]; linarith
  have hHA : 0 ≤ HA := by
    have : 0 ≤ Γ * μ * G * LJ * σu ^ 2 / 4 := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hΓ0 hμ.le) hG) hLJ; positivity
    have : 0 ≤ 4 * (Lv ^ 2 * σv ^ 2 + Luv ^ 2 * σu ^ 2) + 16 * Luv ^ 2 * σu ^ 2 +
        8 * Lv * LJ ^ 2 * σu ^ 4 / μ := by positivity
    simp only [HA]; linarith
  have hSA : 0 ≤ SA := by
    have := mul_nonneg hΓ0 (mul_nonneg hLJ hG)
    have : 0 ≤ 8 * Γ ^ 2 * μ := by positivity
    have : 0 ≤ 16 * (LJ * G) ^ 2 / μ := by positivity
    simp only [SA]; linarith
  have hr : 0 ≤ (1 - ηc * μ / 2) ^ Kc := by
    have := mul_le_mul_of_nonneg_left H.μ_le hηc0
    exact pow_nonneg (by linarith) _
  have hPt0 : ∀ τ, 0 ≤ Pt τ := fun τ => by
    have := hp0 τ; have := hs0 τ; simp only [Pt]; positivity
  have hQt0 : ∀ τ, 0 ≤ Qt τ := fun τ => by
    have := hs0 τ; have := hPt0 τ; simp only [Qt]; positivity
  have hstep : ∀ τ ∈ Finset.range (T + 1),
      ∫ ξ, ‖gradF K gh φ Jφ A (schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + Kc))‖ ∂(Pω p) ≤
        Real.sqrt (Pt τ) + (1 + Γ) * Real.sqrt (Qt τ) := fun τ _ => (ct τ).2
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hc1 := sum_sqrt_le (Finset.range (T + 1)) Pt hPt0
  have hc2 := sum_sqrt_le (Finset.range (T + 1)) Qt hQt0
  simp only [Finset.card_range] at hc1 hc2
  have hcast : ((T + 1 : ℕ) : ℝ) = M := by simp [M]
  rw [hcast] at hc1 hc2
  -- averages
  have hPsum : ∑ τ ∈ Finset.range (T + 1), Pt τ ≤ M * Pb := by
    simp only [Pt, Pb]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range]
    have h1 : ∑ τ ∈ Finset.range (T + 1), pY τ ≤ M * A1 := by
      have := hpS; simp only [pY, Y] at this ⊢; push_cast at this; exact this
    have h2 : ∑ τ ∈ Finset.range (T + 1), sY τ ≤ M * A2 := by
      have := hsS; simp only [sY, Y] at this ⊢; push_cast at this; exact this
    have h3 := mul_le_mul_of_nonneg_left h2 hθ0
    rw [nsmul_eq_mul, hcast]
    nlinarith
  have hQsum : ∑ τ ∈ Finset.range (T + 1), Qt τ ≤ M * Qb := by
    have h2 : ∑ τ ∈ Finset.range (T + 1), sY τ ≤ M * A2 := by
      have := hsS; simp only [sY, Y] at this ⊢; push_cast at this; exact this
    have hpt : ∀ τ ∈ Finset.range (T + 1), Qt τ =
        ((1 - ηc * μ / 2) ^ Kc * Lv ^ 2) * sY τ + (2 / μ * SA) * Pt τ + 2 / μ * (ηc * HA) :=
      fun τ _ => by simp only [Qt]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hcast]
    have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hr (sq_nonneg Lv))
    have h5 := mul_le_mul_of_nonneg_left hPsum (by positivity : (0:ℝ) ≤ 2 / μ * SA)
    have e : M * Qb = (1 - ηc * μ / 2) ^ Kc * Lv ^ 2 * (M * A2) + 2 / μ * SA * (M * Pb) +
        M * (2 / μ * (ηc * HA)) := by simp only [Qb]; ring
    rw [e]
    linarith
  have hP' : Real.sqrt (M * ∑ τ ∈ Finset.range (T + 1), Pt τ) ≤ M * Real.sqrt Pb := by
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPsum hM.le)
    rw [show M * (M * Pb) = M ^ 2 * Pb by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hM.le] at this
    exact this
  have hQ' : Real.sqrt (M * ∑ τ ∈ Finset.range (T + 1), Qt τ) ≤ M * Real.sqrt Qb := by
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hQsum hM.le)
    rw [show M * (M * Qb) = M ^ 2 * Qb by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hM.le] at this
    exact this
  have hfin : ∑ τ ∈ Finset.range (T + 1),
      ∫ ξ, ‖gradF K gh φ Jφ A (schedSeq g (schedOf ηs ηc τ) x0 ξ (τ + Kc))‖ ∂(Pω p) ≤
      M * (Real.sqrt Pb + (1 + Γ) * Real.sqrt Qb) := by
    have h1 := mul_le_mul_of_nonneg_left (hc2.trans hQ') (by linarith : (0:ℝ) ≤ 1 + Γ)
    have h2 := hc1.trans hP'
    have e : M * (Real.sqrt Pb + (1 + Γ) * Real.sqrt Qb) =
        M * Real.sqrt Pb + (1 + Γ) * (M * Real.sqrt Qb) := by ring
    rw [e]
    linarith
  rw [one_div, inv_mul_le_iff₀ hM]
  exact hfin

end Model

end OracleTemplate.RiverValley
