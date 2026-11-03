import LongTails.Proofs.KernelPerceptronBridge
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.KernelPerceptronParameters

open LongTails.Setups.KernelConvolutionalPerceptron
open LongTails.Algorithms.KernelConvolutionalPerceptron
open KernelPerceptronDynamics
open KernelPerceptronGeometry
open KernelPerceptronExecution
open KernelPerceptronTrajectory

variable (p : Params)

noncomputable def ρ : ℝ := p.derivativeMargin * p.lower / (16 * p.upper)
noncomputable def β : ℝ := p.derivativeMargin / 16
noncomputable def δ : ℝ := (stepSize p * p.contrast) ^ 2
noncomputable def L : ℝ :=
  Real.log (128 * p.kernel * p.upper ^ 2 / (p.derivativeMargin * p.contrast) ^ 2)
noncomputable def M₁ : ℕ := ⌈2 / ρ p ^ 2 * L p⌉₊ + 1
noncomputable def ε₁ : ℝ := δ p * 2 * (M₁ p + 1)
noncomputable def φ : ℝ :=
  Real.sqrt (60 * δ p * (M₁ p + 1) / (β p * ρ p)) + 24 * δ p * (M₁ p + 1) / ρ p ^ 2
noncomputable def τ : ℝ := δ p * 2 * (M₁ p + 1) * (M₁ p + 1)
noncomputable def Wres : ℝ :=
  (1 + β p / (2 - β p)) * (φ p ^ 2 / (1 - 3 * β p) + φ p ^ 2) / (2 * δ p)
noncomputable def Λ : ℝ := 2 * M₁ p + Real.sqrt (Wres p) + 32 / p.derivativeMargin
noncomputable def ω : ℝ := 2 * M₁ p + Λ p + Real.sqrt (Wres p)
noncomputable def σ : ℝ := Real.sqrt (2 * δ p) * ω p
noncomputable def ζ : ℝ := Λ p + ω p
noncomputable def nbar : ℝ :=
  (1 + β p / (2 - β p)) * (2 * (1 + β p) * ζ p * σ p + δ p * ζ p ^ 2)
noncomputable def τ₁ : ℝ := δ p * 2 * (M₁ p + 1) * M₁ p
noncomputable def τ₂ : ℝ := 4 * ω p ^ 2 * δ p * ζ p / (Λ p * (p.derivativeMargin / 2))
noncomputable def κ₀ : ℝ := p.derivativeMargin * Real.sqrt (1 - (p.kernel : ℝ)⁻¹)
noncomputable def Y : ℝ := Real.sqrt (δ p) * (M₁ p + 1)
noncomputable def lengthBound : ℕ :=
  ⌊(M₁ p : ℝ) + 4 * ω p ^ 2 / (Λ p * (p.derivativeMargin / 2))⌋₊

structure Facts : Prop where
  d_pos : 0 < p.dimension
  k_ge : 2 ≤ p.kernel
  g_pos : 0 < p.lower
  g_le : p.lower ≤ p.upper
  μ_pos : 0 < p.contrast
  κ_pos : 0 < p.derivativeMargin
  κ_le : p.derivativeMargin ≤ 1
  L_ge : 27 ≤ L p
  Y_le : Y p ≤ p.derivativeMargin ^ 2 / 40000
  M1_ge : 27 * (2 / ρ p ^ 2) ≤ (M₁ p : ℝ)

section Basic

variable {p}

lemma kappa_sq_le (h : Facts p) : p.derivativeMargin ^ 2 ≤ p.derivativeMargin := by
  nlinarith [h.κ_pos, h.κ_le]

lemma R_pos (h : Facts p) : 0 < p.upper := lt_of_lt_of_le h.g_pos h.g_le

lemma k_pos (h : Facts p) : 0 < p.kernel := by have := h.k_ge; omega

lemma k_real_ge (h : Facts p) : (2 : ℝ) ≤ p.kernel := by exact_mod_cast h.k_ge

lemma rho_pos (h : Facts p) : 0 < ρ p := by
  unfold ρ; have := R_pos h; have := h.g_pos; have := h.κ_pos; positivity

lemma beta_pos (h : Facts p) : 0 < β p := by unfold β; have := h.κ_pos; positivity

lemma rho_le_beta (h : Facts p) : ρ p ≤ β p := by
  unfold ρ β
  have hR := R_pos h
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [h.κ_pos, h.g_le]

lemma beta_le (h : Facts p) : β p ≤ 1 / 16 := by
  unfold β; linarith [h.κ_le]

lemma beta_le_eighth (h : Facts p) : β p ≤ 1 / 8 := by linarith [beta_le h]

lemma rho_le (h : Facts p) : ρ p ≤ 1 / 16 := (rho_le_beta h).trans (beta_le h)

lemma rho_sq_le (h : Facts p) : ρ p ^ 2 ≤ 1 / 256 := by
  have := rho_pos h; have := rho_le h; nlinarith

lemma sqrt_half_k_pos (hk : 0 < p.kernel) : 0 < Real.sqrt ((p.kernel : ℝ) / 2) := by
  apply Real.sqrt_pos.mpr; have : (0:ℝ) < p.kernel := by exact_mod_cast hk
  positivity

lemma stepSize_mul (hk : 0 < p.kernel) (hR : 0 < p.upper) :
    stepSize p * Real.sqrt ((p.kernel : ℝ) / 2) = p.derivativeMargin / (16 * p.upper) := by
  unfold stepSize
  have hs := sqrt_half_k_pos hk
  field_simp

lemma delta_eq (hk : 0 < p.kernel) (hR : 0 < p.upper) :
    δ p = p.derivativeMargin ^ 2 * p.contrast ^ 2 / (128 * p.kernel * p.upper ^ 2) := by
  unfold δ stepSize
  have hs := sqrt_half_k_pos hk
  have hkr : (0 : ℝ) < p.kernel := by exact_mod_cast hk
  have h2 : Real.sqrt ((p.kernel : ℝ) / 2) ^ 2 = (p.kernel : ℝ) / 2 := Real.sq_sqrt (by positivity)
  simp only [mul_pow, div_pow, h2]
  field_simp
  ring

lemma delta_pos' (hk : 0 < p.kernel) (hR : 0 < p.upper) (hκ : 0 < p.derivativeMargin)
    (hμ : 0 < p.contrast) : 0 < δ p := by
  rw [delta_eq hk hR]
  have : (0:ℝ) < p.kernel := by exact_mod_cast hk
  positivity

lemma L_eq (hk : 0 < p.kernel) (hR : 0 < p.upper) (_hκ : 0 < p.derivativeMargin)
    (_hμ : 0 < p.contrast) : L p = Real.log (1 / δ p) := by
  rw [delta_eq hk hR]
  unfold L
  rw [one_div, inv_div, mul_pow]

lemma delta_pos (h : Facts p) : 0 < δ p := delta_pos' (k_pos h) (R_pos h) h.κ_pos h.μ_pos

lemma delta_lt_one (h : Facts p) : δ p < 1 := by
  have hL := h.L_ge
  rw [L_eq (k_pos h) (R_pos h) h.κ_pos h.μ_pos] at hL
  have hδ := delta_pos h
  by_contra hcon
  push Not at hcon
  have : Real.log (1 / δ p) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    rw [div_le_one hδ]; exact hcon
  linarith

lemma exp_neg_L (h : Facts p) : Real.exp (-L p) = δ p := by
  rw [L_eq (k_pos h) (R_pos h) h.κ_pos h.μ_pos, ← Real.log_inv, one_div, inv_inv,
    Real.exp_log (delta_pos h)]

end Basic

section Numerics

variable {p} (h : Facts p)
include h

omit h in
lemma M1_pos : (1 : ℝ) ≤ M₁ p := by
  unfold M₁; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 / ρ p ^ 2 * L p⌉₊]

omit h in
lemma M1_ge_L : 2 / ρ p ^ 2 * L p ≤ (M₁ p : ℝ) := by
  unfold M₁; push_cast
  linarith [Nat.le_ceil (2 / ρ p ^ 2 * L p)]

lemma M1_bound : (M₁ p : ℝ) + 1 ≤ 2 / ρ p ^ 2 * L p + 3 := by
  unfold M₁
  push_cast
  have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / ρ p ^ 2 * L p by
    have := rho_pos h; have := h.L_ge; positivity)
  linarith

lemma M1_ge_big : 54 / ρ p ^ 2 ≤ (M₁ p : ℝ) := by
  have := h.M1_ge
  have hρ := rho_pos h
  have : 27 * (2 / ρ p ^ 2) = 54 / ρ p ^ 2 := by ring
  linarith

lemma M1_ge_two_over_kappa : 32 / p.derivativeMargin ≤ (M₁ p : ℝ) := by
  have h1 := M1_ge_big h
  have hρ := rho_pos h
  have hκ := h.κ_pos
  have hρ2 := rho_sq_le h
  have hρκ : ρ p ≤ p.derivativeMargin / 16 := by
    have := rho_le_beta h; unfold β at this; exact this
  have hρ2κ : ρ p ^ 2 ≤ p.derivativeMargin ^ 2 / 256 := by nlinarith
  have h2 : 54 / (p.derivativeMargin ^ 2 / 256) ≤ 54 / ρ p ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hρ2κ
  have h3 : 32 / p.derivativeMargin ≤ 54 / (p.derivativeMargin ^ 2 / 256) := by
    rw [div_le_div_iff₀ hκ (by positivity)]
    nlinarith [h.κ_le]
  linarith

lemma Y_nonneg : 0 ≤ Y p := by unfold Y; have := delta_pos h; positivity

lemma Y_sq : Y p ^ 2 = δ p * (M₁ p + 1) ^ 2 := by
  unfold Y
  rw [mul_pow, Real.sq_sqrt (delta_pos h).le]

lemma Y_le_small : Y p ≤ 1 / 40000 := by
  have := h.Y_le
  have := kappa_sq_le h
  have := h.κ_le
  linarith

omit h in
lemma sqrt_delta_le : Real.sqrt (δ p) ≤ Y p := by
  unfold Y
  have := M1_pos (p := p)
  have := Real.sqrt_nonneg (δ p)
  nlinarith

lemma tau_eq : τ p = 2 * Y p ^ 2 := by
  rw [Y_sq h]; unfold τ; ring

lemma tau_le : τ p ≤ 1 / 10 := by
  rw [tau_eq h]
  have := Y_le_small h
  have := Y_nonneg h
  nlinarith

lemma tau1_le_tau : τ₁ p ≤ τ p := by
  unfold τ₁ τ
  have := delta_pos h
  have := M1_pos (p := p)
  have h1 : (0:ℝ) ≤ δ p * 2 * (M₁ p + 1) := by positivity
  nlinarith

lemma delta_M1 : δ p * (M₁ p + 1) ≤ Y p ^ 2 * ρ p ^ 2 / 54 := by
  rw [Y_sq h]
  have h1 := M1_ge_big h
  have hρ := rho_pos h
  have hδ := delta_pos h
  have hM : (0:ℝ) ≤ M₁ p + 1 := by linarith [M1_pos (p := p)]
  have hM' : (M₁ p : ℝ) + 1 ≠ 0 := by linarith [M1_pos (p := p)]
  have hρ' : ρ p ≠ 0 := hρ.ne'
  have h2 : 54 / ρ p ^ 2 ≤ M₁ p + 1 := by linarith
  have h3 : 54 ≤ (M₁ p + 1) * ρ p ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at h2; linarith
  calc δ p * (M₁ p + 1) = δ p * (M₁ p + 1) ^ 2 * ρ p ^ 2 / ((M₁ p + 1) * ρ p ^ 2) := by
        field_simp
    _ ≤ δ p * (M₁ p + 1) ^ 2 * ρ p ^ 2 / 54 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h3

lemma phi_first_sq : 60 * δ p * (M₁ p + 1) / (β p * ρ p) ≤ 2 * Y p ^ 2 := by
  have h1 := delta_M1 h
  have hβ := beta_pos h
  have hρ := rho_pos h
  have hρβ := rho_le_beta h
  rw [div_le_iff₀ (by positivity)]
  have : 60 * (Y p ^ 2 * ρ p ^ 2 / 54) ≤ 2 * Y p ^ 2 * (β p * ρ p) := by
    have hY := sq_nonneg (Y p)
    have : ρ p ^ 2 ≤ β p * ρ p := by nlinarith
    nlinarith
  nlinarith

lemma phi_second : 24 * δ p * (M₁ p + 1) / ρ p ^ 2 ≤ Y p ^ 2 / 2 := by
  have h1 := delta_M1 h
  have hρ := rho_pos h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma phi_nonneg : 0 ≤ φ p := by
  unfold φ
  have := delta_pos h; have := rho_pos h; have := M1_pos (p := p)
  positivity

lemma phi_le_Y : φ p ≤ 2 * Y p := by
  unfold φ
  have h1 := phi_first_sq h
  have h2 := phi_second h
  have hY := Y_nonneg h
  have hYs := Y_le_small h
  have h3 : Real.sqrt (60 * δ p * (M₁ p + 1) / (β p * ρ p)) ≤ Real.sqrt 2 * Y p := by
    rw [← Real.sqrt_sq hY, ← Real.sqrt_mul (by norm_num), Real.sqrt_le_sqrt_iff (by positivity)]
    linarith
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : Y p ^ 2 / 2 ≤ Y p / 2 := by nlinarith
  nlinarith

lemma phi_le_one : φ p ≤ 1 := by
  have := phi_le_Y h; have := Y_le_small h; linarith

lemma phi_sq_ge : 60 * δ p * (M₁ p + 1) / (β p * ρ p) ≤ φ p ^ 2 := by
  unfold φ
  have hA : 0 ≤ Real.sqrt (60 * δ p * (M₁ p + 1) / (β p * ρ p)) := Real.sqrt_nonneg _
  have hB : 0 ≤ 24 * δ p * (M₁ p + 1) / ρ p ^ 2 := by
    have := delta_pos h; have := rho_pos h; have := M1_pos (p := p); positivity
  have hsq := Real.sq_sqrt (show 0 ≤ 60 * δ p * (M₁ p + 1) / (β p * ρ p) by
    have := delta_pos h; have := rho_pos h; have := beta_pos h; have := M1_pos (p := p); positivity)
  nlinarith

omit h in
lemma phi_ge_second : 24 * δ p * (M₁ p + 1) / ρ p ^ 2 ≤ φ p := by
  unfold φ
  linarith [Real.sqrt_nonneg (60 * δ p * (M₁ p + 1) / (β p * ρ p))]

lemma phi_pos : 0 < φ p := by
  have := phi_ge_second (p := p)
  have : 0 < 24 * δ p * (M₁ p + 1) / ρ p ^ 2 := by
    have := delta_pos h; have := rho_pos h; have := M1_pos (p := p); positivity
  linarith

noncomputable def control₁ : KernelPerceptronPhaseOne.Control where
  ρ := ρ p
  β := β p
  ε := ε₁ p
  U := 2
  φ := φ p
  rho_pos := rho_pos h
  rho_le := rho_le_beta h
  beta_le := beta_le_eighth h
  eps_nonneg := by unfold ε₁; have := delta_pos h; have := M1_pos (p := p); positivity
  U_ge := by norm_num
  phi_pos := phi_pos h
  phi_le := phi_le_one h
  noise_expand := by
    unfold ε₁
    have := phi_sq_ge h
    have hβ := beta_pos h; have hρ := rho_pos h
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  noise_contract := by
    unfold ε₁
    have := phi_ge_second (p := p)
    have hρ := rho_pos h
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith

end Numerics


section PhaseTwo

variable {p} (h : Facts p)
include h

lemma gamma_le : 1 + β p / (2 - β p) ≤ 1.1 := by
  have hβ := beta_le h
  have hβ0 := beta_pos h
  have : β p / (2 - β p) ≤ 0.1 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma gamma_nonneg : 0 ≤ 1 + β p / (2 - β p) := by
  have hβ := beta_le h; have hβ0 := beta_pos h
  have : 0 ≤ β p / (2 - β p) := div_nonneg hβ0.le (by linarith)
  linarith

lemma inv_one_sub_le : 1 / (1 - 3 * β p) ≤ 16 / 13 := by
  have hβ := beta_le h; have hβ0 := beta_pos h
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

lemma Wres_nonneg : 0 ≤ Wres p := by
  unfold Wres
  have hβ := beta_le h; have hβ0 := beta_pos h
  have := gamma_nonneg h; have := delta_pos h
  have : 0 ≤ φ p ^ 2 / (1 - 3 * β p) + φ p ^ 2 := by
    have : 0 < 1 - 3 * β p := by linarith
    positivity
  positivity

lemma delta_Wres : δ p * Wres p ≤ 1.3 * φ p ^ 2 := by
  unfold Wres
  have hδ := delta_pos h
  have hγ := gamma_le h
  have hγ0 := gamma_nonneg h
  have hinv := inv_one_sub_le h
  have hβ := beta_le h; have hβ0 := beta_pos h
  have hpos : 0 < 1 - 3 * β p := by linarith
  have h1 : φ p ^ 2 / (1 - 3 * β p) ≤ 16 / 13 * φ p ^ 2 := by
    rw [div_eq_mul_one_div]
    have := sq_nonneg (φ p)
    nlinarith
  have h2 : (1 + β p / (2 - β p)) * (φ p ^ 2 / (1 - 3 * β p) + φ p ^ 2) ≤ 1.1 * (16 / 13 * φ p ^ 2 + φ p ^ 2) := by
    apply mul_le_mul hγ (by linarith) (by positivity) (by norm_num)
  calc δ p * ((1 + β p / (2 - β p)) * (φ p ^ 2 / (1 - 3 * β p) + φ p ^ 2) / (2 * δ p))
      = (1 + β p / (2 - β p)) * (φ p ^ 2 / (1 - 3 * β p) + φ p ^ 2) / 2 := by
        field_simp
    _ ≤ 1.1 * (16 / 13 * φ p ^ 2 + φ p ^ 2) / 2 := by linarith
    _ ≤ 1.3 * φ p ^ 2 := by nlinarith [sq_nonneg (φ p)]

lemma sqrt_delta_Wres : Real.sqrt (δ p) * Real.sqrt (Wres p) ≤ 1.15 * φ p := by
  rw [← Real.sqrt_mul (delta_pos h).le]
  have h1 := delta_Wres h
  have hφ := phi_nonneg h
  calc Real.sqrt (δ p * Wres p) ≤ Real.sqrt (1.3 * φ p ^ 2) := Real.sqrt_le_sqrt h1
    _ ≤ 1.15 * φ p := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [sq_nonneg (φ p)]

lemma Lambda_ge : 2 * M₁ p + Real.sqrt (Wres p) ≤ Λ p := by
  unfold Λ
  have := h.κ_pos
  have : 0 ≤ 32 / p.derivativeMargin := by positivity
  linarith

omit h in
lemma Lambda_ge_kappa : 32 / p.derivativeMargin ≤ Λ p := by
  unfold Λ
  have := M1_pos (p := p); have := Real.sqrt_nonneg (Wres p)
  linarith

lemma Lambda_pos : 0 < Λ p := by
  have := Lambda_ge_kappa (p := p); have := h.κ_pos
  have : 0 < 32 / p.derivativeMargin := by positivity
  linarith

lemma omega_le : ω p ≤ 2 * Λ p := by
  unfold ω; have := Lambda_ge h; linarith

lemma omega_nonneg : 0 ≤ ω p := by
  unfold ω; have := M1_pos (p := p); have := Lambda_pos h; have := Real.sqrt_nonneg (Wres p); linarith

lemma zeta_le : ζ p ≤ 3 * Λ p := by unfold ζ; have := omega_le h; linarith

lemma zeta_nonneg : 0 ≤ ζ p := by unfold ζ; have := omega_nonneg h; have := Lambda_pos h; linarith

lemma sqrt_delta_Lambda : Real.sqrt (δ p) * Λ p ≤ p.derivativeMargin / 1000 := by
  unfold Λ
  have hY := h.Y_le
  have hYs := Y_le_small h
  have hsd := sqrt_delta_le (p := p)
  have hs0 := Real.sqrt_nonneg (δ p)
  have hκ := h.κ_pos
  have hκ1 := h.κ_le
  have hM : Real.sqrt (δ p) * (2 * M₁ p) ≤ 2 * Y p := by
    unfold Y; have := M1_pos (p := p); nlinarith
  have hW := sqrt_delta_Wres h
  have hφ := phi_le_Y h
  have h32 : Real.sqrt (δ p) * (32 / p.derivativeMargin) ≤ 32 * Y p / p.derivativeMargin := by
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hκ.le
    nlinarith
  have hYκ : Y p ≤ p.derivativeMargin ^ 2 / 40000 := hY
  have hA : 2 * Y p + 1.15 * (2 * Y p) ≤ 4.3 * p.derivativeMargin ^ 2 / 40000 := by nlinarith
  have hB : 32 * Y p / p.derivativeMargin ≤ 32 * p.derivativeMargin / 40000 := by
    rw [div_le_iff₀ hκ]
    nlinarith
  have hκ2 : p.derivativeMargin ^ 2 ≤ p.derivativeMargin := kappa_sq_le h
  calc Real.sqrt (δ p) * (2 * M₁ p + Real.sqrt (Wres p) + 32 / p.derivativeMargin)
      = Real.sqrt (δ p) * (2 * M₁ p) + Real.sqrt (δ p) * Real.sqrt (Wres p) +
        Real.sqrt (δ p) * (32 / p.derivativeMargin) := by ring
    _ ≤ 2 * Y p + 1.15 * (2 * Y p) + 32 * Y p / p.derivativeMargin := by
        have : Real.sqrt (δ p) * Real.sqrt (Wres p) ≤ 1.15 * (2 * Y p) := by
          have := Y_nonneg h; nlinarith
        linarith
    _ ≤ 4.3 * p.derivativeMargin ^ 2 / 40000 + 32 * p.derivativeMargin / 40000 := by linarith
    _ ≤ p.derivativeMargin / 1000 := by nlinarith

lemma sigma_le : σ p ≤ 3 * (Real.sqrt (δ p) * Λ p) := by
  unfold σ
  have h1 : Real.sqrt (2 * δ p) = Real.sqrt 2 * Real.sqrt (δ p) := Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hω := omega_le h
  have hω0 := omega_nonneg h
  have hs0 := Real.sqrt_nonneg (δ p)
  have hΛ := Lambda_pos h
  rw [h1]
  calc Real.sqrt 2 * Real.sqrt (δ p) * ω p ≤ 1.5 * Real.sqrt (δ p) * (2 * Λ p) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hs2 hs0) hω hω0 (by positivity)
    _ = 3 * (Real.sqrt (δ p) * Λ p) := by ring

lemma sigma_nonneg : 0 ≤ σ p := by unfold σ; have := omega_nonneg h; positivity

lemma nbar_le : 4 * nbar p ≤ Λ p * (p.derivativeMargin / 2) := by
  unfold nbar
  have hγ := gamma_le h
  have hγ0 := gamma_nonneg h
  have hβ := beta_le h
  have hβ0 := beta_pos h
  have hζ := zeta_le h
  have hζ0 := zeta_nonneg h
  have hσ := sigma_le h
  have hσ0 := sigma_nonneg h
  have hΛ := Lambda_pos h
  have hsd := Real.sqrt_nonneg (δ p)
  have hδ := delta_pos h
  have hδ1 := delta_lt_one h
  have hA := sqrt_delta_Lambda h
  have hδs : δ p ≤ Real.sqrt (δ p) := by
    have : Real.sqrt (δ p) ≤ 1 := by rw [Real.sqrt_le_one]; exact hδ1.le
    have := Real.sq_sqrt hδ.le
    nlinarith
  set X := Real.sqrt (δ p) * Λ p with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : 2 * (1 + β p) * ζ p * σ p ≤ 2 * 1.1 * (3 * Λ p) * (3 * X) := by
    have hb : 1 + β p ≤ 1.1 := by linarith
    have h3 : ζ p * σ p ≤ (3 * Λ p) * (3 * X) := mul_le_mul hζ hσ hσ0 (by positivity)
    have h4 : 0 ≤ ζ p * σ p := mul_nonneg hζ0 hσ0
    calc 2 * (1 + β p) * ζ p * σ p = 2 * ((1 + β p) * (ζ p * σ p)) := by ring
      _ ≤ 2 * (1.1 * ((3 * Λ p) * (3 * X))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb h3 h4 (by norm_num)) (by norm_num)
      _ = 2 * 1.1 * (3 * Λ p) * (3 * X) := by ring
  have h2 : δ p * ζ p ^ 2 ≤ 9 * X * Λ p := by
    have h3 : ζ p ^ 2 ≤ 9 * Λ p ^ 2 := by nlinarith
    have h4 : δ p * ζ p ^ 2 ≤ δ p * (9 * Λ p ^ 2) := mul_le_mul_of_nonneg_left h3 hδ.le
    have h5 : δ p * (9 * Λ p ^ 2) ≤ Real.sqrt (δ p) * (9 * Λ p ^ 2) :=
      mul_le_mul_of_nonneg_right hδs (by positivity)
    have h6 : Real.sqrt (δ p) * (9 * Λ p ^ 2) = 9 * X * Λ p := by rw [hX]; ring
    linarith
  have h3 : (1 + β p / (2 - β p)) * (2 * (1 + β p) * ζ p * σ p + δ p * ζ p ^ 2) ≤
      1.1 * (2 * 1.1 * (3 * Λ p) * (3 * X) + 9 * X * Λ p) := by
    apply mul_le_mul hγ (by linarith) (by positivity) (by norm_num)
  have h4 : X ≤ p.derivativeMargin / 1000 := hA
  have hκ := h.κ_pos
  have h5 : Λ p * X ≤ Λ p * (p.derivativeMargin / 1000) := mul_le_mul_of_nonneg_left h4 hΛ.le
  have h6 : 0 ≤ Λ p * p.derivativeMargin := by positivity
  nlinarith

lemma c_le : 4 * β p / (2 - β p) ≤ 0.14 * p.derivativeMargin := by
  have hβ := beta_le h; have hβ0 := beta_pos h
  unfold β at *
  rw [div_le_iff₀ (by linarith)]
  nlinarith [h.κ_le, h.κ_pos]

lemma c_nonneg : 0 ≤ 4 * β p / (2 - β p) := by
  have hβ := beta_le h; have hβ0 := beta_pos h
  exact div_nonneg (by linarith) (by linarith)

lemma violation_small :
    (4 * β p / (2 - β p)) * 2 * ω p ≤
      (3 / 2 + 4 * β p / (2 - β p)) * Λ p * (p.derivativeMargin / 2) - 2 ^ 2 := by
  have hc := c_le h
  have hc0 := c_nonneg h
  have hω := omega_le h
  have hω0 := omega_nonneg h
  have hΛ := Lambda_pos h
  have hΛκ := Lambda_ge_kappa (p := p)
  have hκ := h.κ_pos
  have h1 : (4 * β p / (2 - β p)) * 2 * ω p ≤ 0.14 * p.derivativeMargin * 2 * (2 * Λ p) := by
    have := mul_le_mul hc hω hω0 (by positivity)
    nlinarith
  have h2 : 32 ≤ Λ p * p.derivativeMargin := by
    rw [div_le_iff₀ hκ] at hΛκ; linarith
  nlinarith [mul_nonneg hc0 (mul_nonneg hΛ.le hκ.le)]

lemma kappa0_ge : 0.7 * p.derivativeMargin ≤ κ₀ p := by
  unfold κ₀
  have hk := k_real_ge h
  have hκ := h.κ_pos
  have h1 : (p.kernel : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    simpa using hk
  have h2 : (0.7 : ℝ) ≤ Real.sqrt (1 - (p.kernel : ℝ)⁻¹) := by
    apply Real.le_sqrt_of_sq_le
    have e : (0.7 : ℝ) ^ 2 = 0.49 := by norm_num
    rw [e]; linarith
  nlinarith

lemma tau2_eq : τ₂ p * (Λ p * (p.derivativeMargin / 2)) = 4 * ω p ^ 2 * δ p * ζ p := by
  unfold τ₂
  have := Lambda_pos h; have := h.κ_pos
  field_simp

lemma tau2_le : τ₂ p ≤ p.derivativeMargin / 1000 := by
  unfold τ₂
  have hΛ := Lambda_pos h; have hκ := h.κ_pos
  rw [div_le_iff₀ (by positivity)]
  have hω := omega_le h; have hω0 := omega_nonneg h
  have hζ := zeta_le h; have hζ0 := zeta_nonneg h
  have hδ := delta_pos h
  have hA := sqrt_delta_Lambda h
  have hsq : δ p = Real.sqrt (δ p) ^ 2 := (Real.sq_sqrt hδ.le).symm
  set X := Real.sqrt (δ p) * Λ p with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : ω p ^ 2 ≤ 4 * Λ p ^ 2 := by nlinarith
  have h2 : 4 * ω p ^ 2 * δ p * ζ p ≤ 4 * (4 * Λ p ^ 2) * δ p * (3 * Λ p) := by
    have := mul_le_mul h1 hζ hζ0 (by positivity)
    nlinarith
  have h3 : 4 * (4 * Λ p ^ 2) * δ p * (3 * Λ p) = 48 * X ^ 2 * Λ p := by
    rw [hX, mul_pow, Real.sq_sqrt hδ.le]; ring
  have hX2 : X ^ 2 ≤ (p.derivativeMargin / 1000) ^ 2 := pow_le_pow_left₀ hX0 hA 2
  have h4 : X ^ 2 * Λ p ≤ (p.derivativeMargin / 1000) ^ 2 * Λ p :=
    mul_le_mul_of_nonneg_right hX2 hΛ.le
  have h5 : 0 ≤ p.derivativeMargin ^ 2 * Λ p := by positivity
  nlinarith

lemma tau1_le : τ₁ p ≤ p.derivativeMargin / 1000 := by
  have h1 := tau1_le_tau h
  rw [tau_eq h] at h1
  have hY := h.Y_le
  have hY0 := Y_nonneg h
  have hκ := h.κ_pos; have hκ1 := h.κ_le
  have h2 : Y p ^ 2 ≤ (p.derivativeMargin ^ 2 / 40000) ^ 2 := pow_le_pow_left₀ hY0 hY 2
  have hκ2 : p.derivativeMargin ^ 2 ≤ 1 := by nlinarith
  have h7 : (p.derivativeMargin ^ 2) ^ 2 ≤ p.derivativeMargin ^ 2 := by
    nlinarith [sq_nonneg p.derivativeMargin]
  nlinarith [kappa_sq_le h]

lemma kstar_le : p.derivativeMargin / 2 ≤ κ₀ p - (τ₁ p + τ₂ p) - σ p := by
  have h1 := kappa0_ge h
  have h2 := tau1_le h
  have h3 := tau2_le h
  have h4 := sigma_le h
  have h5 := sqrt_delta_Lambda h
  have hκ := h.κ_pos
  linarith

lemma tnorm_le : ‖startFilter p.kernel‖ ≤ 1 := by
  have hk := k_pos h
  have h1 := startFilter_norm_sq (k := p.kernel) hk
  have hinv : 0 ≤ (p.kernel : ℝ)⁻¹ := by positivity
  nlinarith [norm_nonneg (startFilter p.kernel)]

noncomputable def control₂ : KernelPerceptronTrajectory.Control where
  Λ := Λ p
  κstar := p.derivativeMargin / 2
  κ₀ := κ₀ p
  U := 2
  β := β p
  δ := δ p
  Wbar := ω p ^ 2
  ω := ω p
  σ := σ p
  ζ := ζ p
  nbar := nbar p
  τ₁ := τ₁ p
  τ₂ := τ₂ p
  tnorm := 1
  beta_pos := beta_pos h
  beta_le := beta_le_eighth h
  delta_pos := delta_pos h
  lambda_nonneg := (Lambda_pos h).le
  kstar_pos := by have := h.κ_pos; positivity
  U_pos := by norm_num
  omega_nonneg := omega_nonneg h
  sigma_nonneg := sigma_nonneg h
  tau1_nonneg := by unfold τ₁; have := delta_pos h; have := M1_pos (p := p); positivity
  tau2_nonneg := by
    unfold τ₂; have := delta_pos h; have := Lambda_pos h; have := h.κ_pos
    have := zeta_nonneg h; have := omega_nonneg h; positivity
  wbar_nonneg := sq_nonneg _
  wbar_le := le_refl _
  mass_le := by
    unfold σ
    rw [mul_pow, Real.sq_sqrt (by have := delta_pos h; positivity)]
  zeta_ge := le_refl _
  noise_le := le_refl _
  noise_small := nbar_le h
  gain := by
    have := Lambda_ge_kappa (p := p); have hκ := h.κ_pos
    rw [div_le_iff₀ hκ] at this
    nlinarith
  violation_small := violation_small h
  kstar_le := kstar_le h
  U_ge := by
    have := tau1_le h; have := tau2_le h; have := sigma_le h; have := sqrt_delta_Lambda h
    have := h.κ_le; have := h.κ_pos
    linarith
  drift_le := by rw [← tau2_eq h]; ring_nf; exact le_refl _

end PhaseTwo

section Valid

lemma log_two_bounds : (0.69 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

structure Basic : Prop where
  d_pos : 0 < p.dimension
  k_ge : 2 ≤ p.kernel
  g_pos : 0 < p.lower
  g_le : p.lower ≤ p.upper
  μ_pos : 0 < p.contrast
  μ_le : p.contrast ≤ p.upper
  κ_pos : 0 < p.derivativeMargin
  κ_le : p.derivativeMargin ≤ 1
  main : p.contrast ^ 2 * (p.upper / p.lower) ^ 4 * L p ^ 2 ≤
    p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 / 10 ^ 13

variable {p}

lemma basic_of_valid (hp : spec.valid p) : Basic p := by
  obtain ⟨hd, hk, hg, hgR, hμ, hμR, hκ, hκ1, hmain⟩ := hp
  exact ⟨hd, hk, hg, hgR, hμ, hμR, hκ, hκ1, hmain⟩

variable (h : Basic p)
include h

lemma R_pos' : 0 < p.upper := lt_of_lt_of_le h.g_pos h.g_le

lemma k_pos' : 0 < p.kernel := by have := h.k_ge; omega

lemma k_real_pos : (0 : ℝ) < p.kernel := by exact_mod_cast k_pos' h

lemma delta_pos_basic : 0 < δ p := delta_pos' (k_pos' h) (R_pos' h) h.κ_pos h.μ_pos

lemma kappa_sq_le' : p.derivativeMargin ^ 2 ≤ 1 := by nlinarith [h.κ_pos, h.κ_le]

lemma kappa_mu_sq : p.derivativeMargin ^ 2 * p.contrast ^ 2 ≤ p.contrast ^ 2 := by
  have := kappa_sq_le' h
  nlinarith [sq_nonneg p.contrast]

lemma delta_le_256 : δ p ≤ 1 / 256 := by
  have hR := R_pos' h
  have hkr : (2 : ℝ) ≤ p.kernel := by exact_mod_cast h.k_ge
  rw [delta_eq (k_pos' h) hR, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hκμ := kappa_mu_sq h
  have h2 : p.contrast ^ 2 ≤ p.upper ^ 2 := by nlinarith [h.μ_pos, h.μ_le]
  have h3 : (2 : ℝ) * p.upper ^ 2 ≤ p.kernel * p.upper ^ 2 := by nlinarith [sq_nonneg p.upper]
  nlinarith

lemma L_ge_five : 5.5 ≤ L p := by
  have hδ := delta_pos_basic h
  rw [L_eq (k_pos' h) (R_pos' h) h.κ_pos h.μ_pos]
  have h256 : (256 : ℝ) ≤ 1 / δ p := by
    rw [le_div_iff₀ hδ]; linarith [delta_le_256 h]
  have hlog : Real.log 256 ≤ Real.log (1 / δ p) := Real.log_le_log (by norm_num) h256
  have h2 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  linarith [log_two_bounds]

lemma main_thirty :
    p.contrast ^ 2 * 30 ≤ p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 / 10 ^ 13 := by
  have hL := L_ge_five h
  have hL2 : 30 ≤ L p ^ 2 := by nlinarith
  have hRg : 1 ≤ p.upper / p.lower := by rw [le_div_iff₀ h.g_pos]; linarith [h.g_le]
  have hRg4 : 1 ≤ (p.upper / p.lower) ^ 4 := one_le_pow₀ hRg
  have h1 : (1 : ℝ) * 30 ≤ (p.upper / p.lower) ^ 4 * L p ^ 2 :=
    mul_le_mul hRg4 hL2 (by norm_num) (by positivity)
  have h2 : p.contrast ^ 2 * 30 ≤ p.contrast ^ 2 * ((p.upper / p.lower) ^ 4 * L p ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : p.contrast ^ 2 * ((p.upper / p.lower) ^ 4 * L p ^ 2) =
      p.contrast ^ 2 * (p.upper / p.lower) ^ 4 * L p ^ 2 := by ring
  linarith [h.main]

lemma delta_small : δ p ≤ 1 / (3 * 10 ^ 16) := by
  have hR := R_pos' h
  have hkpos := k_real_pos h
  have hκ := h.κ_pos
  rw [delta_eq (k_pos' h) hR, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hκμ := kappa_mu_sq h
  have hkR : 0 ≤ (p.kernel : ℝ) * p.upper ^ 2 := by positivity
  have hk6 : p.derivativeMargin ^ 6 ≤ 1 := pow_le_one₀ hκ.le h.κ_le
  have hB : p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 ≤ p.kernel * p.upper ^ 2 := by
    nlinarith
  have h1 : p.contrast ^ 2 * 30 * 10 ^ 13 ≤ p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 := by
    have := main_thirty h
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  nlinarith

lemma L_ge_27 : 27 ≤ L p := by
  have hδ := delta_pos_basic h
  rw [L_eq (k_pos' h) (R_pos' h) h.κ_pos h.μ_pos]
  have hbig : (2 : ℝ) ^ 54 ≤ 1 / δ p := by
    rw [le_div_iff₀ hδ]
    have h1 : (2 : ℝ) ^ 54 ≤ 3 * 10 ^ 16 := by norm_num
    have h2 := delta_small h
    have h3 : δ p * (3 * 10 ^ 16) ≤ 1 := by
      rw [le_div_iff₀ (by norm_num)] at h2; exact h2
    nlinarith
  have hlog : Real.log (2 ^ 54) ≤ Real.log (1 / δ p) := Real.log_le_log (by positivity) hbig
  rw [Real.log_pow] at hlog
  have := log_two_bounds
  push_cast at hlog
  linarith

lemma rho_pos' : 0 < ρ p := by
  unfold ρ; have := R_pos' h; have := h.g_pos; have := h.κ_pos; positivity

lemma rho_le_kappa : ρ p ≤ p.derivativeMargin / 16 := by
  unfold ρ
  have hR := R_pos' h
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [h.κ_pos, h.g_le]

lemma rho_sq_le' : ρ p ^ 2 ≤ 1 / 256 := by
  have h1 := rho_pos' h; have h2 := rho_le_kappa h; have h3 := h.κ_le
  have : ρ p ≤ 1 / 16 := by linarith
  nlinarith

lemma M1_succ_le : (M₁ p : ℝ) + 1 ≤ (11 / 5) * L p / ρ p ^ 2 := by
  have hρ := rho_pos' h
  have hL := L_ge_27 h
  have hρ2 := rho_sq_le' h
  unfold M₁
  push_cast
  have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / ρ p ^ 2 * L p by positivity)
  have h3 : (3 : ℝ) ≤ (1 / 5) * L p / ρ p ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : 2 / ρ p ^ 2 * L p + (1 / 5) * L p / ρ p ^ 2 = (11 / 5) * L p / ρ p ^ 2 := by ring
  linarith

lemma Y_bound : Y p ≤ p.derivativeMargin ^ 2 / 40000 := by
  have hδ := delta_pos_basic h
  have hR := R_pos' h
  have hk0 := k_pos' h
  have hkpos := k_real_pos h
  have hg := h.g_pos
  have hκ := h.κ_pos
  have hR' : p.upper ≠ 0 := hR.ne'
  have hk' : (p.kernel : ℝ) ≠ 0 := hkpos.ne'
  have hg' : p.lower ≠ 0 := hg.ne'
  have hκ' : p.derivativeMargin ≠ 0 := hκ.ne'
  have hρ := rho_pos' h
  have hM1 := M1_succ_le h
  have hY0 : 0 ≤ Y p := by unfold Y; positivity
  have hYsq : Y p ^ 2 = δ p * (M₁ p + 1) ^ 2 := by
    unfold Y; rw [mul_pow, Real.sq_sqrt hδ.le]
  have hM1sq : ((M₁ p : ℝ) + 1) ^ 2 ≤ ((11 / 5) * L p / ρ p ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hM1 2
  have hρ2 : ρ p ^ 2 = p.derivativeMargin ^ 2 * p.lower ^ 2 / (16 * p.upper) ^ 2 := by
    unfold ρ; rw [div_pow, mul_pow]
  have hδeq := delta_eq hk0 hR
  have hmain := h.main
  have e1 : δ p * ((11 / 5) * L p / ρ p ^ 2) ^ 2 = (121 / 25 * 65536 / 128) *
      (p.contrast ^ 2 * (p.upper / p.lower) ^ 4 * L p ^ 2) /
      (p.kernel * p.derivativeMargin ^ 2 * p.upper ^ 2) := by
    rw [hδeq, hρ2]
    field_simp
    ring
  have e2 : (121 / 25 * 65536 / 128) * (p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 / 10 ^ 13) /
      (p.kernel * p.derivativeMargin ^ 2 * p.upper ^ 2) =
      (121 / 25 * 65536 / 128 / 10 ^ 13) * p.derivativeMargin ^ 4 := by
    field_simp
  have h4 : 0 ≤ p.derivativeMargin ^ 4 := by positivity
  have e3 : (p.derivativeMargin ^ 2 / 40000) ^ 2 = p.derivativeMargin ^ 4 / 1600000000 := by ring
  have key : Y p ^ 2 ≤ (p.derivativeMargin ^ 2 / 40000) ^ 2 := by
    rw [hYsq]
    calc δ p * (M₁ p + 1) ^ 2 ≤ δ p * ((11 / 5) * L p / ρ p ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hM1sq hδ.le
      _ = _ := e1
      _ ≤ (121 / 25 * 65536 / 128) * (p.kernel * p.derivativeMargin ^ 6 * p.upper ^ 2 / 10 ^ 13) /
          (p.kernel * p.derivativeMargin ^ 2 * p.upper ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmain (by norm_num))
            (by positivity)
      _ = _ := e2
      _ ≤ (p.derivativeMargin ^ 2 / 40000) ^ 2 := by rw [e3]; nlinarith
  exact (abs_le_of_sq_le_sq' key (by positivity)).2

lemma M1_ge_valid : 27 * (2 / ρ p ^ 2) ≤ (M₁ p : ℝ) := by
  have hρ := rho_pos' h
  have hL := L_ge_27 h
  unfold M₁; push_cast
  have := Nat.le_ceil (2 / ρ p ^ 2 * L p)
  have h0 : 0 ≤ 2 / ρ p ^ 2 := by positivity
  have h2 : 27 * (2 / ρ p ^ 2) ≤ 2 / ρ p ^ 2 * L p := by nlinarith
  linarith

omit h in
lemma facts_of_valid (hp : spec.valid p) : Facts p := by
  have h := basic_of_valid hp
  exact ⟨h.d_pos, h.k_ge, h.g_pos, h.g_le, h.μ_pos, h.κ_pos, h.κ_le, L_ge_27 h, Y_bound h,
    M1_ge_valid h⟩

end Valid

section Persist

variable {p}

lemma separates_persist (D : Data p.dimension p.samples) (η : ℝ) (N m : ℕ)
    (hN : Separates D ((scanStep D η)^[N]
      (initialScan (k := p.kernel) (d := p.dimension) (n := p.samples))).point) :
    Separates D ((scanStep D η)^[N + m]
      (initialScan (k := p.kernel) (d := p.dimension) (n := p.samples))).point := by
  induction m with
  | zero => simpa using hN
  | succ m ih =>
    rw [show N + (m + 1) = (N + m) + 1 by omega, Function.iterate_succ_apply']
    exact scanStep_good ih

end Persist

section Geometry

variable {p} (h : Facts p) {D : Data p.dimension p.samples}
  (G : Geometry p.kernel D p.lower p.upper p.contrast p.derivativeMargin)
include h

lemma bcoef_abs (i : Fin (p.samples + 1)) :
    |bcoef G (stepSize p) i| = p.derivativeMargin / (16 * p.upper) * |G.background i| := by
  unfold bcoef
  have hs := stepSize_pos p h.κ_pos (k_pos h) (R_pos h)
  have hk : (0 : ℝ) ≤ p.kernel := by positivity
  have hsq : Real.sqrt (p.kernel : ℝ) / Real.sqrt 2 = Real.sqrt ((p.kernel : ℝ) / 2) :=
    (Real.sqrt_div hk 2).symm
  have hmul := stepSize_mul (k_pos h) (R_pos h)
  have hpos : 0 ≤ stepSize p * Real.sqrt ((p.kernel : ℝ) / 2) := by positivity
  rw [show stepSize p * (Real.sqrt (p.kernel : ℝ) * G.background i / Real.sqrt 2) =
      (stepSize p * Real.sqrt ((p.kernel : ℝ) / 2)) * G.background i by
    rw [← hsq]; ring]
  rw [abs_mul, abs_of_nonneg hpos, hmul]

lemma abstract_geometry :
    KernelPerceptronTrajectory.Geometry (ρ p) (β p) (κ₀ p) (fun i => bcoef G (stepSize p) i)
      (plusFeature G) (highOp G) G.separator (startFilter p.kernel) where
  bl := by
    intro i
    rw [bcoef_abs h G i]
    unfold ρ
    have hR := R_pos h
    have := G.background_lower i
    have hκ := h.κ_pos
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hκ hR]
  bu := by
    intro i
    rw [bcoef_abs h G i]
    unfold β
    have hR := R_pos h
    have := G.background_upper i
    have hκ := h.κ_pos
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  pn := plusFeature_norm G (k_pos h)
  Rn := highOp_norm G (k_pos h)
  wn := G.separator_unit
  margin := startFilter_margin G h.k_ge

lemma start_a_sq : ((Real.sqrt (p.kernel : ℝ))⁻¹) ^ 2 ≤ 1 / 2 := by
  have hk := k_real_ge h
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  simpa using hk

lemma hUa_bound :
    Real.sqrt (((Real.sqrt (p.kernel : ℝ))⁻¹) ^ 2 / (1 - 3 * β p)) + ‖startFilter p.kernel‖ + τ p ≤ 2 := by
  have h1 := start_a_sq h
  have hβ := beta_le h
  have hβ0 := beta_pos h
  have hτ := tau_le h
  have ht := tnorm_le h
  have h2 : ((Real.sqrt (p.kernel : ℝ))⁻¹) ^ 2 / (1 - 3 * β p) ≤ (1 / 2) / (13 / 16) := by
    apply div_le_div₀ (by norm_num) h1 (by norm_num) (by linarith)
  have h3 : Real.sqrt (((Real.sqrt (p.kernel : ℝ))⁻¹) ^ 2 / (1 - 3 * β p)) ≤ 0.8 := by
    calc _ ≤ Real.sqrt ((1 / 2) / (13 / 16)) := Real.sqrt_le_sqrt h2
      _ ≤ 0.8 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

lemma hend_bound : (1 - ρ p ^ 2 / 2) ^ M₁ p * ((Real.sqrt (p.kernel : ℝ))⁻¹) ^ 2 < φ p ^ 2 := by
  have hρ := rho_pos h
  have hρ2 := rho_sq_le h
  have hδ := delta_pos h
  have h1 : (1 - ρ p ^ 2 / 2) ^ M₁ p ≤ δ p := by
    have hx : 0 ≤ 1 - ρ p ^ 2 / 2 := by linarith
    have h2 : (1 - ρ p ^ 2 / 2) ^ M₁ p ≤ Real.exp (-(ρ p ^ 2 / 2)) ^ M₁ p :=
      pow_le_pow_left₀ hx (Real.one_sub_le_exp_neg _) _
    rw [← Real.exp_nat_mul] at h2
    have h3 : Real.exp ((M₁ p : ℝ) * -(ρ p ^ 2 / 2)) ≤ Real.exp (-L p) := by
      apply Real.exp_le_exp.mpr
      have := M1_ge_L (p := p)
      have : L p ≤ ρ p ^ 2 / 2 * M₁ p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
        have h4 : 2 / ρ p ^ 2 * L p * ρ p ^ 2 ≤ (M₁ p : ℝ) * ρ p ^ 2 :=
          mul_le_mul_of_nonneg_right this (by positivity)
        have h5 : 2 / ρ p ^ 2 * L p * ρ p ^ 2 = 2 * L p := by field_simp
        linarith
      linarith
    rw [exp_neg_L h] at h3
    linarith
  have h2 := start_a_sq h
  have h3 := phi_sq_ge h
  have hβ := beta_pos h
  have hM := M1_pos (p := p)
  have h4 : δ p < 60 * δ p * (M₁ p + 1) / (β p * ρ p) := by
    rw [lt_div_iff₀ (by positivity)]
    have hβρ : β p * ρ p ≤ 1 := by
      have := beta_le h; have := rho_le h; nlinarith
    nlinarith
  have h5 : (1 - ρ p ^ 2 / 2) ^ M₁ p * ((Real.sqrt (p.kernel : ℝ))⁻¹) ^ 2 ≤ δ p * (1 / 2) := by
    apply mul_le_mul h1 h2 (by positivity) hδ.le
  linarith

lemma hW_bound : (2 * M₁ p + Λ p) ^ 2 +
    (1 + β p / (2 - β p)) * (φ p ^ 2 / (1 - 3 * β p) + φ p ^ 2) / (2 * δ p) ≤ ω p ^ 2 := by
  unfold ω
  have hW := Wres_nonneg h
  have hs := Real.sq_sqrt hW
  have hΛ := Lambda_pos h
  have hM := M1_pos (p := p)
  have hsq := Real.sqrt_nonneg (Wres p)
  change (2 * M₁ p + Λ p) ^ 2 + Wres p ≤ (2 * M₁ p + Λ p + Real.sqrt (Wres p)) ^ 2
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * M₁ p + Λ p) hsq]

theorem trace_length_le (t : Trace G (stepSize p)) :
    (t.length : ℝ) ≤ M₁ p + 4 * ω p ^ 2 / (Λ p * (p.derivativeMargin / 2)) := by
  have hG := abstract_geometry h G
  have := KernelPerceptronTrajectory.length_le (control₁ h) (control₂ h) (delta_pos h) hG hG
    (tnorm_le h) (M₁ := M₁ p) (τ := τ p) (le_refl _) (hUa_bound h) (le_refl _) (le_refl _)
    (hend_bound h) (hW_bound h) t.valid
  exact this

lemma trace_length_le_nat (t : Trace G (stepSize p)) : t.length ≤ lengthBound p := by
  apply Nat.le_floor
  exact trace_length_le h G t

lemma lengthBound_le :
    (lengthBound p : ℝ) + 2 ≤ 200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p := by
  have hfl : (lengthBound p : ℝ) ≤ M₁ p + 4 * ω p ^ 2 / (Λ p * (p.derivativeMargin / 2)) :=
    Nat.floor_le (by
      have := M1_pos (p := p); have := Lambda_pos h; have := h.κ_pos; have := omega_nonneg h
      positivity)
  have hκ := h.κ_pos
  have hκ1 := h.κ_le
  have hΛ := Lambda_pos h
  have hM := M1_pos (p := p)
  have hω := omega_le h
  have hω0 := omega_nonneg h
  have h1 : 4 * ω p ^ 2 / (Λ p * (p.derivativeMargin / 2)) ≤ 32 * Λ p / p.derivativeMargin := by
    rw [div_le_div_iff₀ (by positivity) hκ]
    have : ω p ^ 2 ≤ 4 * Λ p ^ 2 := by nlinarith
    nlinarith
  have hWres : Wres p ≤ 20.8 * (M₁ p : ℝ) ^ 2 := by
    have hδ := delta_pos h
    have h2 := delta_Wres h
    have hφ := phi_le_Y h
    have hφ0 := phi_nonneg h
    have hY0 := Y_nonneg h
    have hYsq := Y_sq h
    have h3 : φ p ^ 2 ≤ 4 * Y p ^ 2 := by nlinarith
    have h4 : δ p * Wres p ≤ 5.2 * (δ p * (M₁ p + 1) ^ 2) := by rw [← hYsq]; linarith
    have h5 : Wres p ≤ 5.2 * (M₁ p + 1) ^ 2 := by
      have := le_of_mul_le_mul_left (by linarith : δ p * Wres p ≤ δ p * (5.2 * (M₁ p + 1) ^ 2)) hδ
      exact this
    have h6 : ((M₁ p : ℝ) + 1) ^ 2 ≤ 4 * (M₁ p : ℝ) ^ 2 := by nlinarith
    linarith
  have hsqW : Real.sqrt (Wres p) ≤ 4.6 * M₁ p := by
    calc Real.sqrt (Wres p) ≤ Real.sqrt (20.8 * (M₁ p : ℝ) ^ 2) := Real.sqrt_le_sqrt hWres
      _ ≤ 4.6 * M₁ p := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
  have hΛle : Λ p ≤ 7.6 * M₁ p := by
    unfold Λ
    have := M1_ge_two_over_kappa h
    linarith
  have hM1le : (M₁ p : ℝ) ≤ 513 * (p.upper / p.lower) ^ 2 * L p / p.derivativeMargin ^ 2 := by
    have hb := M1_bound h
    have hρ := rho_pos h
    have hL := h.L_ge
    have hρ2 : ρ p ^ 2 = p.derivativeMargin ^ 2 * p.lower ^ 2 / (16 * p.upper) ^ 2 := by
      unfold ρ; rw [div_pow, mul_pow]
    have hg := h.g_pos
    have hR := R_pos h
    have h7 : 2 / ρ p ^ 2 * L p = 512 * ((p.upper / p.lower) ^ 2 * L p / p.derivativeMargin ^ 2) := by
      rw [hρ2]; field_simp; ring
    have h8 : (3 : ℝ) ≤ (p.upper / p.lower) ^ 2 * L p / p.derivativeMargin ^ 2 := by
      have hRg : 1 ≤ (p.upper / p.lower) ^ 2 := by
        have : 1 ≤ p.upper / p.lower := by rw [le_div_iff₀ hg]; linarith [h.g_le]
        nlinarith
      have hκ2 : p.derivativeMargin ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h9 : 513 * (p.upper / p.lower) ^ 2 * L p / p.derivativeMargin ^ 2 =
        513 * ((p.upper / p.lower) ^ 2 * L p / p.derivativeMargin ^ 2) := by ring
    rw [h9]
    linarith
  have hκ3 : 0 < p.derivativeMargin ^ 3 := by positivity
  have h9 : (M₁ p : ℝ) + 32 * Λ p / p.derivativeMargin + 2 ≤ 250 * M₁ p / p.derivativeMargin := by
    rw [le_div_iff₀ hκ, add_mul, add_mul, div_mul_cancel₀ _ hκ.ne']
    have h10 : (M₁ p : ℝ) * p.derivativeMargin ≤ M₁ p := by nlinarith
    linarith
  have h12 : 250 * (M₁ p : ℝ) / p.derivativeMargin ≤
      200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p := by
    have hpos : 0 ≤ (p.upper / p.lower) ^ 2 * L p := by
      have := h.L_ge; positivity
    have key : (M₁ p : ℝ) * p.derivativeMargin ^ 2 ≤ 513 * ((p.upper / p.lower) ^ 2 * L p) := by
      have := hM1le
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have e : 200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p =
        200000 * ((p.upper / p.lower) ^ 2 * L p) / p.derivativeMargin ^ 3 := by ring
    rw [e, div_le_div_iff₀ hκ hκ3]
    have h13 := mul_le_mul_of_nonneg_right key hκ.le
    nlinarith
  linarith

theorem budget_separates'
    (G : Geometry p.kernel D p.lower p.upper p.contrast p.derivativeMargin) :
    Separates D ((scanStep D (stepSize p))^[(p.samples + 1) *
      ⌈200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p⌉₊]
      (initialScan (k := p.kernel) (d := p.dimension) (n := p.samples))).point := by
  have hd := h.d_pos
  have hk := k_pos h
  have hη := stepSize_pos p h.κ_pos hk (R_pos h)
  have hsep := iterate_separates G hd hk hη (L := lengthBound p) (trace_length_le_nat h G)
  have hle : (p.samples + 1) * (lengthBound p + 2) ≤
      (p.samples + 1) * ⌈200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p⌉₊ := by
    apply Nat.mul_le_mul_left
    have h1 := lengthBound_le h
    have h2 : ((lengthBound p + 2 : ℕ) : ℝ) ≤ 200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p := by
      push_cast; exact h1
    have h3 : ((lengthBound p + 2 : ℕ) : ℝ) ≤
        ((⌈200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 * L p⌉₊ : ℕ) : ℝ) :=
      h2.trans (Nat.le_ceil _)
    exact_mod_cast h3
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
  rw [hm]
  exact separates_persist D (stepSize p) _ m hsep

end Geometry

theorem budget_separates (p : Params) (hp : spec.valid p) {D : Data p.dimension p.samples}
    (G : Geometry p.kernel D p.lower p.upper p.contrast p.derivativeMargin) :
    Separates D ((scanStep D (stepSize p))^[(p.samples + 1) *
      ⌈200000 * (p.upper / p.lower) ^ 2 / p.derivativeMargin ^ 3 *
        Real.log (128 * p.kernel * p.upper ^ 2 / (p.derivativeMargin * p.contrast) ^ 2)⌉₊]
      (initialScan (k := p.kernel) (d := p.dimension) (n := p.samples))).point :=
  budget_separates' (facts_of_valid hp) G

end LongTails.Proofs.KernelPerceptronParameters
