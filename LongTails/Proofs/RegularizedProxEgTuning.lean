import LongTails.Proofs.RegularizedProxEgConfig
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

section Step

variable {L ρ : ℝ}

lemma tuned_stepOK (hL : 0 < L) (hρ : 0 ≤ ρ) (hρL : 2 * ρ * L < 1) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ (1 - 2 * ρ * L) ^ 3 * L / 256) :
    StepOK L ρ ((1 + 2 * ρ * L) / (2 * L)) ((1 - 2 * ρ * L) / 16) Λ ((1 - 2 * ρ * L) / (4 * L)) := by
  set τ := 1 - 2 * ρ * L with hτ
  have hτ0 : 0 < τ := by linarith
  have hτ1 : τ ≤ 1 := by have : 0 ≤ ρ * L := mul_nonneg hρ hL.le; linarith
  have hρe : ρ = (1 - τ) / (2 * L) := by field_simp; try linarith
  set κ := Λ / L with hκ
  have hΛe : Λ = κ * L := by rw [hκ]; field_simp
  have hκ0 : 0 ≤ κ := div_nonneg hΛ0 hL.le
  have hτ3 : τ ^ 3 ≤ τ := by
    have h2 := pow_le_one₀ (n := 2) hτ0.le hτ1
    have := mul_le_mul_of_nonneg_left h2 hτ0.le
    nlinarith
  have hκ1 : κ ≤ τ ^ 3 / 256 := by
    rw [hκ, div_le_div_iff₀ hL (by norm_num)]; nlinarith
  have hκτ : κ ≤ τ / 256 := by linarith
  set γ := (1 + 2 * ρ * L) / (2 * L) with hγ
  have hγe : γ = (2 - τ) / (2 * L) := by rw [hγ]; congr 1; linarith
  have hγ0 : 0 < γ := by rw [hγe]; apply div_pos <;> linarith
  have hγL1 : γ * L ≤ 1 := by rw [hγe]; field_simp; try linarith
  have h2ρΛ : 2 * ρ * Λ = (1 - τ) * κ := by rw [hρe, hΛe]; field_simp
  have hγL' : γ * (L + Λ) = (2 - τ) * (1 + κ) / 2 := by rw [hγe, hΛe]; field_simp
  have hgap : τ / 4 ≤ 1 - γ * (L + Λ) := by rw [hγL']; nlinarith
  refine ⟨hγ0, by positivity, hΛ0, ?_, ?_, by positivity, ?_, ?_, ?_⟩
  · rw [h2ρΛ]; nlinarith
  · linarith
  ·
    have hk : 0 < 1 - 2 * ρ * Λ := by rw [h2ρΛ]; nlinarith
    have hr : 2 * (ρ / (1 - 2 * ρ * Λ)) ≤ (1 - τ + τ / 64) / L := by
      rw [h2ρΛ, hρe]
      rw [div_div, show 2 * ((1 - τ) / (2 * L * (1 - (1 - τ) * κ))) =
        (1 - τ) / (L * (1 - (1 - τ) * κ)) by field_simp; try ring]
      have hpos : 0 < 1 - (1 - τ) * κ := by nlinarith
      rw [div_le_div_iff₀ (mul_pos hL hpos) hL]
      have h1 : (1 - τ + τ / 64) * ((1 - τ) * κ) ≤ κ := by
        have a1 : 0 ≤ 1 - τ := by linarith
        have a2 : 1 - τ + τ / 64 ≤ 1 := by linarith
        have a3 : (1 - τ) * κ ≤ κ := by nlinarith
        have a4 : 0 ≤ (1 - τ) * κ := mul_nonneg a1 hκ0
        nlinarith
      have h2 : 1 - τ ≤ (1 - τ + τ / 64) * (1 - (1 - τ) * κ) := by nlinarith
      have := mul_le_mul_of_nonneg_left h2 hL.le
      nlinarith
    have hαγ : (1 - 2 * ρ * L) / 16 * γ = τ * (2 - τ) / (32 * L) := by
      rw [hγe, ← hτ]; field_simp; try ring
    rw [hαγ, hγe]
    have h1 : (1 + (1 - 2 * ρ * L) / 16) * (2 * (ρ / (1 - 2 * ρ * Λ)) + τ * (2 - τ) / (32 * L)) ≤
        (1 + τ / 16) * ((1 - τ + τ / 64) / L + τ * (2 - τ) / (32 * L)) := by
      rw [← hτ]; gcongr
    refine h1.trans ?_
    rw [show (1 + τ / 16) * ((1 - τ + τ / 64) / L + τ * (2 - τ) / (32 * L)) =
      ((1 + τ / 16) * (1 - τ + τ / 64 + τ * (2 - τ) / 32)) / L by field_simp; try ring]
    rw [show (2 - τ) / (2 * L) - (1 - 2 * ρ * L) / (4 * L) / 2 = (1 - 5 * τ / 8) / L by
      rw [← hτ]; field_simp; try ring]
    rw [div_le_div_iff_of_pos_right hL]
    nlinarith
  ·
    have hγ1 : γ ≤ 1 / L := by rw [le_div_iff₀ hL]; exact hγL1
    have hq : γ / (1 - γ * (L + Λ)) ≤ (1 / L) / (τ / 4) :=
      div_le_div₀ (by positivity) hγ1 (by positivity) hgap
    have hq2 : (γ / (1 - γ * (L + Λ))) ^ 2 ≤ ((1 / L) / (τ / 4)) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg hγ0.le (by linarith)) hq 2
    have : 2 * Λ * ((1 / L) / (τ / 4)) ^ 2 ≤ (1 - 2 * ρ * L) / (4 * L) / 2 := by
      rw [← hτ, hΛe]
      rw [show 2 * (κ * L) * (1 / L / (τ / 4)) ^ 2 = 32 * κ / (L * τ ^ 2) by field_simp; try ring]
      rw [show τ / (4 * L) / 2 = τ / (8 * L) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc 2 * Λ * (γ / (1 - γ * (L + Λ))) ^ 2 ≤ 2 * Λ * ((1 / L) / (τ / 4)) ^ 2 := by gcongr
      _ ≤ _ := this
  ·
    have hγ1 : γ ≤ 1 / L := by rw [le_div_iff₀ hL]; exact hγL1
    have hΛ' : Λ ≤ L / 256 := by rw [hΛe]; nlinarith
    have hτ16 : τ / 16 ≤ 1 / 16 := by linarith
    have hm := mul_le_mul (mul_le_mul hτ16 hγ1 hγ0.le (by norm_num)) hΛ' hΛ0 (by positivity)
    have he : 1 / 16 * (1 / L) * (L / 256) = 1 / 4096 := by field_simp; try norm_num
    linarith

end Step


section Config

noncomputable def tτ (L ρ : ℝ) : ℝ := 1 - 2 * ρ * L
noncomputable def tγ (L ρ : ℝ) : ℝ := (1 + 2 * ρ * L) / (2 * L)
noncomputable def tΛm (L ρ : ℝ) : ℝ := tτ L ρ ^ 3 * L / 256
noncomputable def tl0 (L ρ R ε : ℝ) : ℝ := ε * tΛm L ρ / (2 * ε + 24 * R * tΛm L ρ)
noncomputable def tS (L ρ R ε : ℝ) : ℕ := Nat.log 2 ⌊tΛm L ρ / tl0 L ρ R ε⌋₊ - 1
noncomputable def tK0 (L ρ : ℝ) : ℝ := 2 ^ 15 / tτ L ρ ^ 3
noncomputable def tδ (L ρ R ε : ℝ) (s : ℕ) : ℝ :=
  ε / (tK0 L ρ * ((tS L ρ R ε : ℝ) + 1) * (2 ^ (s + 1) * tl0 L ρ R ε))
noncomputable def tℓ (L ρ R ε : ℝ) : ℝ :=
  Real.log (16 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2)

noncomputable def tunedCfg (L ρ R σ ε : ℝ) : RegCfg where
  γ := tγ L ρ
  α := tτ L ρ / 16
  S := tS L ρ R ε
  lam s := 2 ^ s * tl0 L ρ R ε
  Lam s := (2 ^ (s + 1) - 1) * tl0 L ρ R ε
  T s := ⌈tℓ L ρ R ε / (tτ L ρ / 16 * tγ L ρ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε))⌉₊
  b s := ⌈44 * tγ L ρ * σ ^ 2 /
    (tτ L ρ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) * tδ L ρ R ε s ^ 2)⌉₊ + 1
  bf := ⌈256 * σ ^ 2 / ε ^ 2⌉₊ + 1

structure TuneHyp (L ρ R σ ε : ℝ) : Prop where
  L_pos : 0 < L
  ρ_nonneg : 0 ≤ ρ
  ρL : 2 * ρ * L < 1
  R_nonneg : 0 ≤ R
  σ_nonneg : 0 ≤ σ
  ε_pos : 0 < ε

variable {L ρ R σ ε : ℝ}

lemma TuneHyp.τ_pos (h : TuneHyp L ρ R σ ε) : 0 < tτ L ρ := by unfold tτ; linarith [h.ρL]
lemma TuneHyp.τ_le (h : TuneHyp L ρ R σ ε) : tτ L ρ ≤ 1 := by
  unfold tτ; have := mul_nonneg h.ρ_nonneg h.L_pos.le; nlinarith
lemma TuneHyp.Λm_pos (h : TuneHyp L ρ R σ ε) : 0 < tΛm L ρ := by
  unfold tΛm; have := h.τ_pos; have := h.L_pos; positivity
lemma TuneHyp.l0_pos (h : TuneHyp L ρ R σ ε) : 0 < tl0 L ρ R ε := by
  unfold tl0; have := h.Λm_pos; have := h.ε_pos; have := h.R_nonneg; positivity
lemma TuneHyp.l0_le (h : TuneHyp L ρ R σ ε) : 2 * tl0 L ρ R ε ≤ tΛm L ρ := by
  have hm := h.Λm_pos; have he := h.ε_pos; have hr := h.R_nonneg
  unfold tl0
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hr hm.le) hm.le]
lemma TuneHyp.l0R (h : TuneHyp L ρ R σ ε) : 24 * R * tl0 L ρ R ε ≤ ε := by
  have hm := h.Λm_pos; have he := h.ε_pos; have hr := h.R_nonneg
  unfold tl0
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hr hm.le]
lemma TuneHyp.K0_ge (h : TuneHyp L ρ R σ ε) : 2 ^ 15 ≤ tK0 L ρ := by
  unfold tK0; rw [le_div_iff₀ (pow_pos h.τ_pos 3)]
  have := pow_le_one₀ h.τ_pos.le h.τ_le (n := 3); nlinarith

lemma TuneHyp.n0_ge (h : TuneHyp L ρ R σ ε) : 2 ≤ ⌊tΛm L ρ / tl0 L ρ R ε⌋₊ := by
  apply Nat.le_floor
  rw [le_div_iff₀ h.l0_pos]; push_cast; linarith [h.l0_le]

lemma TuneHyp.S_spec (h : TuneHyp L ρ R σ ε) :
    2 ^ (tS L ρ R ε + 1) * tl0 L ρ R ε ≤ tΛm L ρ ∧ tΛm L ρ < 2 ^ (tS L ρ R ε + 2) * tl0 L ρ R ε := by
  set n := ⌊tΛm L ρ / tl0 L ρ R ε⌋₊ with hn
  have hn2 := h.n0_ge
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn2
  have hS : tS L ρ R ε + 1 = Nat.log 2 n := by unfold tS; rw [← hn]; omega
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hl := h.l0_pos
  constructor
  · rw [hS]
    have : ((2 : ℝ) ^ Nat.log 2 n) ≤ tΛm L ρ / tl0 L ρ R ε := by
      calc ((2 : ℝ) ^ Nat.log 2 n) = ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) := by exact_mod_cast h1
        _ ≤ tΛm L ρ / tl0 L ρ R ε := Nat.floor_le (div_nonneg h.Λm_pos.le hl.le)
    rwa [le_div_iff₀ hl] at this
  · rw [show tS L ρ R ε + 2 = Nat.log 2 n + 1 by omega]
    have : tΛm L ρ / tl0 L ρ R ε < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      calc tΛm L ρ / tl0 L ρ R ε < (n : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (2 : ℝ) ^ (Nat.log 2 n + 1) := by push_cast; ring
    rwa [div_lt_iff₀ hl] at this

lemma TuneHyp.Lam_le (h : TuneHyp L ρ R σ ε) {s : ℕ} (hs : s ≤ tS L ρ R ε) :
    (2 ^ (s + 1) - 1) * tl0 L ρ R ε ≤ tΛm L ρ := by
  have h1 := h.S_spec.1
  have h2 : (2 : ℝ) ^ (s + 1) ≤ 2 ^ (tS L ρ R ε + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hl := h.l0_pos
  nlinarith

lemma TuneHyp.Lam_pos (h : TuneHyp L ρ R σ ε) (s : ℕ) : 0 < (2 ^ (s + 1) - 1) * tl0 L ρ R ε := by
  have : (2 : ℝ) ≤ 2 ^ (s + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have := h.l0_pos; nlinarith


lemma TuneHyp.gap (h : TuneHyp L ρ R σ ε) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ tΛm L ρ) :
    tτ L ρ / 4 ≤ 1 - tγ L ρ * (L + Λ) := by
  have hL := h.L_pos
  have hτ0 := h.τ_pos
  have hτ1 := h.τ_le
  have hγe : tγ L ρ = (2 - tτ L ρ) / (2 * L) := by unfold tγ tτ; congr 1; ring
  have hκ : Λ / L ≤ tτ L ρ / 256 := by
    rw [div_le_iff₀ hL]; unfold tΛm at hΛ
    have : tτ L ρ ^ 3 ≤ tτ L ρ := by nlinarith [pow_le_one₀ hτ0.le hτ1 (n := 2)]
    nlinarith
  have : tγ L ρ * (L + Λ) = (2 - tτ L ρ) * (1 + Λ / L) / 2 := by rw [hγe]; field_simp
  rw [this]
  have : 0 ≤ Λ / L := div_nonneg hΛ0 hL.le
  nlinarith

lemma TuneHyp.stepK_le (h : TuneHyp L ρ R σ ε) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ tΛm L ρ) :
    stepK L ρ (tγ L ρ) (tτ L ρ / 16) Λ + (tτ L ρ / 16 * tγ L ρ) ^ 2 ≤
      22 * (tτ L ρ / 16) * tγ L ρ ^ 2 / tτ L ρ := by
  have hst := tuned_stepOK h.L_pos h.ρ_nonneg h.ρL hΛ0 hΛ
  have hτ0 := h.τ_pos
  have hτ1 := h.τ_le
  have hg := h.gap hΛ0 hΛ
  unfold tγ tτ at *
  set τ := 1 - 2 * ρ * L with hτ
  set γ := (1 + 2 * ρ * L) / (2 * L) with hγ
  have hγ0 : 0 < γ := hst.γ_pos
  have hcoef := hst.coef
  have hM : 0 ≤ τ / (4 * L) / 2 := by have := hst.M_nonneg; positivity
  have hr0 : 0 ≤ ρ / (1 - 2 * ρ * Λ) := div_nonneg h.ρ_nonneg (by linarith [hst.ρΛ])
  have hsum : 2 * (ρ / (1 - 2 * ρ * Λ)) + τ / 16 * γ ≤ γ := by
    have h1 : 0 ≤ τ / 16 * (2 * (ρ / (1 - 2 * ρ * Λ)) + τ / 16 * γ) := by positivity
    nlinarith
  have hden : τ / 4 ≤ 1 - (γ * (L + Λ)) ^ 2 := by
    have h0 : 0 ≤ γ * (L + Λ) := mul_nonneg hγ0.le (by linarith [h.L_pos])
    have h1 : γ * (L + Λ) ≤ 1 := by linarith
    nlinarith
  unfold stepK
  have e1 : τ / 16 * γ ^ 2 / (1 - (γ * (L + Λ)) ^ 2) ≤ 4 * (τ / 16) * γ ^ 2 / τ := by
    rw [div_le_div_iff₀ (by linarith) hτ0]
    nlinarith [mul_pos (mul_pos hτ0 hτ0) (mul_pos hγ0 hγ0)]
  have e2 : τ / 16 * γ * (2 * (ρ / (1 - 2 * ρ * Λ)) + τ / 16 * γ) * (1 + 1 / (τ / 16)) ≤
      17 * (τ / 16) * γ ^ 2 / τ := by
    have : τ / 16 * γ * (2 * (ρ / (1 - 2 * ρ * Λ)) + τ / 16 * γ) ≤ τ / 16 * γ * γ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h17 : 1 + 1 / (τ / 16) ≤ 17 / τ := by
      rw [show (1:ℝ) + 1 / (τ / 16) = (τ + 16) / τ by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hτ0.le
    calc τ / 16 * γ * (2 * (ρ / (1 - 2 * ρ * Λ)) + τ / 16 * γ) * (1 + 1 / (τ / 16))
        ≤ τ / 16 * γ * γ * (17 / τ) := by
          apply mul_le_mul this h17 (by positivity) (by positivity)
      _ = 17 * (τ / 16) * γ ^ 2 / τ := by field_simp
  have e3 : (τ / 16 * γ) ^ 2 ≤ (τ / 16) * γ ^ 2 / τ := by
    rw [le_div_iff₀ hτ0]
    have : τ / 16 * τ ≤ 1 := by nlinarith
    nlinarith [sq_nonneg γ, mul_pos hτ0 (mul_pos hγ0 hγ0)]
  have : 4 * (τ / 16) * γ ^ 2 / τ + 17 * (τ / 16) * γ ^ 2 / τ + (τ / 16) * γ ^ 2 / τ =
      22 * (τ / 16) * γ ^ 2 / τ := by ring
  linarith

lemma pow_le_exp_bound {q ℓ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (1 - q) ^ ⌈ℓ / q⌉₊ ≤ Real.exp (-ℓ) := by
  have h1 : 0 ≤ 1 - q := by linarith
  have h2 : 1 - q ≤ Real.exp (-q) := by have := Real.add_one_le_exp (-q); linarith
  calc (1 - q) ^ ⌈ℓ / q⌉₊ ≤ Real.exp (-q) ^ ⌈ℓ / q⌉₊ := pow_le_pow_left₀ h1 h2 _
    _ = Real.exp (⌈ℓ / q⌉₊ * (-q)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (-ℓ) := by
        apply Real.exp_le_exp.mpr
        have := Nat.le_ceil (ℓ / q)
        rw [div_le_iff₀ hq] at this
        nlinarith


lemma TuneHyp.δ_pos (h : TuneHyp L ρ R σ ε) (s : ℕ) : 0 < tδ L ρ R ε s := by
  unfold tδ; have := h.ε_pos; have := h.l0_pos
  have : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  positivity

lemma TuneHyp.δ_succ (h : TuneHyp L ρ R σ ε) (s : ℕ) : tδ L ρ R ε s = 2 * tδ L ρ R ε (s + 1) := by
  unfold tδ
  have := h.l0_pos
  have : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  rw [pow_succ 2 (s + 1)]
  field_simp
  try ring

lemma TuneHyp.exp_T (h : TuneHyp L ρ R σ ε) {s : ℕ} (hs : s ≤ tS L ρ R ε) :
    (1 - stageQ (tunedCfg L ρ R σ ε) s) ^ (tunedCfg L ρ R σ ε).T s ≤
      1 / (16 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2) := by
  have hΛ0 := (h.Lam_pos s).le
  have hst := tuned_stepOK h.L_pos h.ρ_nonneg h.ρL hΛ0 (h.Lam_le hs)
  have hK : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  have harg : 0 < 16 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 := by positivity
  have hℓ : 0 ≤ tℓ L ρ R ε := by
    unfold tℓ; apply Real.log_nonneg
    have : 1 ≤ tK0 L ρ := le_trans (by norm_num) h.K0_ge
    have : (1 : ℝ) ≤ (tS L ρ R ε : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (tS L ρ R ε); linarith
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) this 2,
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ‹(1:ℝ) ≤ tK0 L ρ› 2]
  have hq : 0 < stageQ (tunedCfg L ρ R σ ε) s := by
    unfold stageQ; simp only [tunedCfg]
    have := h.τ_pos; have := hst.γ_pos; have := h.Lam_pos s
    unfold tγ at *; positivity
  have hq1 : stageQ (tunedCfg L ρ R σ ε) s ≤ 1 := by
    have := hst.q_le; unfold stageQ; simp only [tunedCfg, tγ, tτ]; linarith
  have hT : (tunedCfg L ρ R σ ε).T s = ⌈tℓ L ρ R ε / stageQ (tunedCfg L ρ R σ ε) s⌉₊ := by
    simp only [tunedCfg, stageQ]
  rw [hT]
  refine (pow_le_exp_bound hq hq1 ).trans (le_of_eq ?_)
  unfold tℓ
  rw [Real.exp_neg, Real.exp_log harg, one_div]

lemma TuneHyp.noise (h : TuneHyp L ρ R σ ε) {s : ℕ} (hs : s ≤ tS L ρ R ε) :
    stageC L ρ σ (tunedCfg L ρ R σ ε) s / stageQ (tunedCfg L ρ R σ ε) s ≤
      tδ L ρ R ε s ^ 2 / 2 := by
  have hΛ0 := (h.Lam_pos s).le
  have hΛ := h.Lam_pos s
  have hKb := h.stepK_le hΛ0 (h.Lam_le hs)
  have hst := tuned_stepOK h.L_pos h.ρ_nonneg h.ρL hΛ0 (h.Lam_le hs)
  have hτ := h.τ_pos
  have hγ : 0 < tγ L ρ := hst.γ_pos
  have hδ := h.δ_pos s
  set Λ := (2 ^ (s + 1) - 1) * tl0 L ρ R ε
  set b := (tunedCfg L ρ R σ ε).b s
  have hb : (44 * tγ L ρ * σ ^ 2 / (tτ L ρ * Λ * tδ L ρ R ε s ^ 2) : ℝ) ≤ b := by
    simp only [b, tunedCfg]; push_cast
    have := Nat.le_ceil (44 * tγ L ρ * σ ^ 2 / (tτ L ρ * Λ * tδ L ρ R ε s ^ 2)); linarith
  have hb0 : (0 : ℝ) < b := by simp only [b, tunedCfg]; positivity
  unfold stageC stageQ
  simp only [tunedCfg]
  set γ := tγ L ρ
  set τ := tτ L ρ
  set K := stepK L ρ γ (τ / 16) Λ
  have hαγΛ : 0 < τ / 16 * γ * Λ := by positivity
  rw [div_le_iff₀ hαγΛ]
  have h1 : (K + (τ / 16 * γ) ^ 2) * (σ ^ 2 / b) ≤ 22 * (τ / 16) * γ ^ 2 / τ * (σ ^ 2 / b) :=
    mul_le_mul_of_nonneg_right hKb (by positivity)
  refine h1.trans ?_
  have hX : 0 < τ * Λ * tδ L ρ R ε s ^ 2 := by positivity
  have hb' : 44 * γ * σ ^ 2 ≤ b * (τ * Λ * tδ L ρ R ε s ^ 2) := (div_le_iff₀ hX).mp hb
  have e1 : 22 * (τ / 16) * γ ^ 2 / τ * (σ ^ 2 / b) = γ / (32 * b) * (44 * γ * σ ^ 2) := by
    field_simp; try ring
  have e2 : tδ L ρ R ε s ^ 2 / 2 * (τ / 16 * γ * Λ) = γ / (32 * b) * (b * (τ * Λ * tδ L ρ R ε s ^ 2)) := by
    field_simp; try ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hb' (by positivity)

theorem tuned_cfgOK (h : TuneHyp L ρ R σ ε) :
    CfgOK (tunedCfg L ρ R σ ε) L ρ R σ ε ((1 - 2 * ρ * L) / (4 * L)) (tδ L ρ R ε) := by
  have hL := h.L_pos
  have hτ := h.τ_pos
  have hl := h.l0_pos
  have hK : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  have hS1 : (1 : ℝ) ≤ (tS L ρ R ε : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (tS L ρ R ε); linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.δ_pos, ?_, ?_, ?_⟩
  · simp only [tunedCfg, tγ]; field_simp; linarith [h.ρL]
  · simp only [tunedCfg, tγ]; rw [le_div_iff₀ (by positivity)]; nlinarith [h.ρL, h.ρ_nonneg]
  · intro s; simp only [tunedCfg]; positivity
  · simp only [tunedCfg]; ring
  · intro s; simp only [tunedCfg]; ring
  · intro s; simp only [tunedCfg]; rw [pow_succ]; nlinarith
  · intro s hs
    have := tuned_stepOK h.L_pos h.ρ_nonneg h.ρL (h.Lam_pos s).le (h.Lam_le hs)
    simpa [tunedCfg, tγ, tτ] using this
  · intro s hs
    have hle := h.Lam_le hs
    simp only [tunedCfg]
    unfold tΛm at hle
    have h3 : tτ L ρ ^ 3 ≤ 1 := pow_le_one₀ hτ.le h.τ_le
    have : 4 * ρ * L ≤ 2 := by linarith [h.ρL]
    nlinarith [h.ρ_nonneg, (h.Lam_pos s).le]
  · intro s; simp only [tunedCfg]; omega
  · simp only [tunedCfg]; omega
  ·
    have hE := h.exp_T (Nat.zero_le _)
    have hN := h.noise (Nat.zero_le _)
    have hδ0 : tδ L ρ R ε 0 = ε / (tK0 L ρ * ((tS L ρ R ε : ℝ) + 1) * (2 * tl0 L ρ R ε)) := by
      unfold tδ; norm_num
    have hR24 := h.l0R
    have hRl : R * tl0 L ρ R ε ≤ ε / 24 := by linarith
    have hfirst : (1 - stageQ (tunedCfg L ρ R σ ε) 0) ^ (tunedCfg L ρ R σ ε).T 0 * (2 * R ^ 2) ≤
        tδ L ρ R ε 0 ^ 2 / 2 := by
      set D := tK0 L ρ * ((tS L ρ R ε : ℝ) + 1) with hD
      have hD0 : 0 < D := by positivity
      have hE' : (1 - stageQ (tunedCfg L ρ R σ ε) 0) ^ (tunedCfg L ρ R σ ε).T 0 ≤ 1 / (16 * D ^ 2) := by
        refine hE.trans (le_of_eq ?_); rw [hD]; ring
      have hRl2 : (R * tl0 L ρ R ε) ^ 2 ≤ ε ^ 2 := by
        have h0 : 0 ≤ R * tl0 L ρ R ε := mul_nonneg h.R_nonneg hl.le
        exact pow_le_pow_left₀ h0 (by linarith) 2
      have hδ0' : tδ L ρ R ε 0 = ε / (D * (2 * tl0 L ρ R ε)) := by rw [hδ0, hD]
      calc (1 - stageQ (tunedCfg L ρ R σ ε) 0) ^ (tunedCfg L ρ R σ ε).T 0 * (2 * R ^ 2)
          ≤ 1 / (16 * D ^ 2) * (2 * R ^ 2) := mul_le_mul_of_nonneg_right hE' (by positivity)
        _ = (R * tl0 L ρ R ε) ^ 2 / (8 * D ^ 2 * tl0 L ρ R ε ^ 2) := by field_simp; try ring
        _ ≤ ε ^ 2 / (8 * D ^ 2 * tl0 L ρ R ε ^ 2) := by gcongr
        _ = tδ L ρ R ε 0 ^ 2 / 2 := by rw [hδ0']; field_simp; try ring
    linarith
  ·
    intro s hs
    have hE := h.exp_T hs
    have hN := h.noise hs
    have hd := h.δ_succ s
    have hq1 : 0 ≤ 1 - stageQ (tunedCfg L ρ R σ ε) (s + 1) := by
      have := (tuned_stepOK h.L_pos h.ρ_nonneg h.ρL (h.Lam_pos (s+1)).le (h.Lam_le hs)).q_le
      unfold stageQ; simp only [tunedCfg, tγ, tτ]; linarith
    have hfirst : (1 - stageQ (tunedCfg L ρ R σ ε) (s + 1)) ^ (tunedCfg L ρ R σ ε).T (s + 1) *
        (2 * tδ L ρ R ε s ^ 2) ≤ tδ L ρ R ε (s + 1) ^ 2 / 2 := by
      rw [hd]
      have hsmall : 1 / (16 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num)
        have : 1 ≤ tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 := by
          have := le_trans (by norm_num : (1:ℝ) ≤ 2 ^ 15) h.K0_ge
          nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) this 2,
            pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hS1 2]
        nlinarith
      have := mul_le_mul_of_nonneg_right (hE.trans hsmall)
        (by positivity : (0:ℝ) ≤ 2 * (2 * tδ L ρ R ε (s + 1)) ^ 2)
      nlinarith
    linarith
  ·
    have hε := h.ε_pos
    have hσ := h.σ_nonneg
    have hterm : ∀ s, (tunedCfg L ρ R σ ε).lam (s + 1) * tδ L ρ R ε s =
        ε / (tK0 L ρ * ((tS L ρ R ε : ℝ) + 1)) := by
      intro s; simp only [tunedCfg]; unfold tδ; field_simp
    have hsum : 3 * ∑ s ∈ Finset.range (tS L ρ R ε), (tunedCfg L ρ R σ ε).lam (s + 1) * tδ L ρ R ε s ≤
        ε / 8 := by
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h1 : ((tS L ρ R ε : ℕ) : ℝ) * (ε / (tK0 L ρ * ((tS L ρ R ε : ℝ) + 1))) ≤ ε / tK0 L ρ := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hK]
        nlinarith [Nat.cast_nonneg (α := ℝ) (tS L ρ R ε), mul_pos hε hK]
      have h2 : ε / tK0 L ρ ≤ ε / 2 ^ 15 := div_le_div_of_nonneg_left hε.le (by norm_num) h.K0_ge
      nlinarith
    have hS2 := h.S_spec.2
    have hγ0 : 1 / (2 * L) ≤ tγ L ρ := by
      unfold tγ; apply div_le_div_of_nonneg_right _ (by positivity)
      have := mul_nonneg h.ρ_nonneg hL.le; linarith
    have hfirst : 8 / (tunedCfg L ρ R σ ε).γ * tδ L ρ R ε (tS L ρ R ε) ≤ ε / 4 := by
      simp only [tunedCfg]
      have hγp : 0 < tγ L ρ := lt_of_lt_of_le (by positivity) hγ0
      have hg : 8 / tγ L ρ ≤ 16 * L := by
        rw [div_le_iff₀ hγp]
        have := mul_le_mul_of_nonneg_left hγ0 (by positivity : (0:ℝ) ≤ 16 * L)
        have e : 16 * L * (1 / (2 * L)) = 8 := by field_simp; try ring
        rw [e] at this; linarith
      have hΛm := h.Λm_pos
      have hd : tδ L ρ R ε (tS L ρ R ε) ≤ 2 * ε / (tK0 L ρ * tΛm L ρ) := by
        unfold tδ
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : tΛm L ρ ≤ 2 * (2 ^ (tS L ρ R ε + 1) * tl0 L ρ R ε) := by
          have : (2 : ℝ) ^ (tS L ρ R ε + 2) = 2 * 2 ^ (tS L ρ R ε + 1) := by rw [pow_succ]; try ring
          rw [this] at hS2; linarith
        have hk2 : tK0 L ρ * tΛm L ρ ≤ tK0 L ρ * (2 * (2 ^ (tS L ρ R ε + 1) * tl0 L ρ R ε)) :=
          mul_le_mul_of_nonneg_left h2 hK.le
        have hk3 : tK0 L ρ * (2 * (2 ^ (tS L ρ R ε + 1) * tl0 L ρ R ε)) ≤
            tK0 L ρ * (2 * (2 ^ (tS L ρ R ε + 1) * tl0 L ρ R ε)) * ((tS L ρ R ε : ℝ) + 1) :=
          le_mul_of_one_le_right (by positivity) hS1
        nlinarith
      have hKΛ : tK0 L ρ * tΛm L ρ = 128 * L := by
        unfold tΛm tK0
        have := hτ.ne'
        field_simp; try ring
      calc 8 / tγ L ρ * tδ L ρ R ε (tS L ρ R ε) ≤ 16 * L * (2 * ε / (tK0 L ρ * tΛm L ρ)) := by
            apply mul_le_mul hg hd (h.δ_pos _).le (by positivity)
        _ = ε / 4 := by rw [hKΛ]; field_simp; try ring
    have hsec : 4 * (σ / Real.sqrt ((tunedCfg L ρ R σ ε).bf : ℝ)) ≤ ε / 4 := by
      simp only [tunedCfg]
      set B : ℝ := ((⌈256 * σ ^ 2 / ε ^ 2⌉₊ + 1 : ℕ) : ℝ) with hB
      have hbf : 256 * σ ^ 2 / ε ^ 2 ≤ B := by
        rw [hB]; push_cast; have := Nat.le_ceil (256 * σ ^ 2 / ε ^ 2); linarith
      have hpos : 0 < B := by rw [hB]; positivity
      have hsq : 0 < Real.sqrt B := Real.sqrt_pos.mpr hpos
      have hbf2 : 256 * σ ^ 2 ≤ ε ^ 2 * B := by
        have := (div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)).mp hbf; linarith
      have h16 : 16 * σ ≤ ε * Real.sqrt B := by
        apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp
        rw [mul_pow, mul_pow, Real.sq_sqrt hpos.le]; nlinarith
      rw [mul_div_assoc', div_le_div_iff₀ hsq (by norm_num)]
      nlinarith
    have hthird : Real.sqrt 2 * (tunedCfg L ρ R σ ε).lam 0 * R ≤ ε / 16 := by
      simp only [tunedCfg, pow_zero, one_mul]
      have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have := h.l0R
      have h0 : 0 ≤ tl0 L ρ R ε * R := mul_nonneg hl.le h.R_nonneg
      nlinarith
    simp only [tunedCfg] at hfirst hsec hthird hsum ⊢
    linarith


lemma stagesLen_eq (cfg : RegCfg) : ∀ n, stagesLen cfg n = ∑ s ∈ Finset.range n, stageLen cfg s
  | 0 => rfl
  | n + 1 => by rw [stagesLen, stagesLen_eq cfg n, Finset.sum_range_succ, add_comm]

noncomputable def tΛg (L ρ R ε : ℝ) : ℝ := 1 + Real.log (2 + L * R / ε) + Real.log (2 / tτ L ρ)

lemma TuneHyp.Λg_ge (h : TuneHyp L ρ R σ ε) : 1 ≤ tΛg L ρ R ε := by
  unfold tΛg
  have h1 : 0 ≤ Real.log (2 + L * R / ε) := by
    apply Real.log_nonneg; have := div_nonneg (mul_nonneg h.L_pos.le h.R_nonneg) h.ε_pos.le; linarith
  have h2 : 0 ≤ Real.log (2 / tτ L ρ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ h.τ_pos]; linarith [h.τ_le]
  linarith

lemma TuneHyp.ratio (h : TuneHyp L ρ R σ ε) :
    tΛm L ρ / tl0 L ρ R ε = 2 + 24 * R * tΛm L ρ / ε := by
  have := h.Λm_pos; have := h.ε_pos
  unfold tl0; field_simp

lemma TuneHyp.S_log (h : TuneHyp L ρ R σ ε) :
    ((tS L ρ R ε : ℝ) + 1) ≤ 2 * Real.log (2 + L * R / ε) := by
  have hS := h.S_spec.1
  have hl := h.l0_pos
  have hpow : (2 : ℝ) ^ (tS L ρ R ε + 1) ≤ 2 + L * R / ε := by
    have h1 : (2 : ℝ) ^ (tS L ρ R ε + 1) ≤ tΛm L ρ / tl0 L ρ R ε := by rw [le_div_iff₀ hl]; exact hS
    rw [h.ratio] at h1
    have h2 : 24 * R * tΛm L ρ / ε ≤ L * R / ε := by
      apply div_le_div_of_nonneg_right _ h.ε_pos.le
      unfold tΛm
      have h3 : tτ L ρ ^ 3 ≤ 1 := pow_le_one₀ h.τ_pos.le h.τ_le
      have := mul_nonneg h.R_nonneg h.L_pos.le
      nlinarith
    linarith
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  push_cast at hlog
  nlinarith [Nat.cast_nonneg (α := ℝ) (tS L ρ R ε)]

lemma TuneHyp.ℓ_le (h : TuneHyp L ρ R σ ε) : tℓ L ρ R ε ≤ 24 * tΛg L ρ R ε := by
  have hK : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  have hS1 : (0 : ℝ) < (tS L ρ R ε : ℝ) + 1 := by positivity
  unfold tℓ
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow]
  have hK0 : Real.log (tK0 L ρ) ≤ 11 + 3 * Real.log (2 / tτ L ρ) := by
    unfold tK0
    rw [Real.log_div (by norm_num) (pow_pos h.τ_pos 3).ne', Real.log_pow, Real.log_pow]
    have : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h2 : Real.log (2 / tτ L ρ) = Real.log 2 - Real.log (tτ L ρ) :=
      Real.log_div (by norm_num) h.τ_pos.ne'
    push_cast
    nlinarith [Real.log_two_gt_d9]
  have hlS : Real.log ((tS L ρ R ε : ℝ) + 1) ≤ (tS L ρ R ε : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos hS1; linarith
  have h16 : Real.log 16 ≤ 3 := by
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [this]; nlinarith [Real.log_two_lt_d9]
  have hSl := h.S_log
  have hΛ := h.Λg_ge
  unfold tΛg at hΛ ⊢
  have h1 : 0 ≤ Real.log (2 + L * R / ε) := by
    apply Real.log_nonneg; have := div_nonneg (mul_nonneg h.L_pos.le h.R_nonneg) h.ε_pos.le; linarith
  have h2 : 0 ≤ Real.log (2 / tτ L ρ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ h.τ_pos]; linarith [h.τ_le]
  push_cast
  nlinarith


lemma TuneHyp.stage_len (h : TuneHyp L ρ R σ ε) {s : ℕ} (hs : s ≤ tS L ρ R ε) :
    (stageLen (tunedCfg L ρ R σ ε) s : ℝ) ≤
      2 * (32 * tℓ L ρ R ε / tτ L ρ) *
          (176 * σ ^ 2 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 / (tτ L ρ * ε ^ 2)) +
        2 * (176 * σ ^ 2 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 / (tτ L ρ * ε ^ 2)) + 5 +
        5 * (32 * tℓ L ρ R ε / tτ L ρ) * (L / (2 ^ s * tl0 L ρ R ε)) := by
  have hL := h.L_pos
  have hτ := h.τ_pos
  have hl := h.l0_pos
  have hε := h.ε_pos
  have hK : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  have hst := tuned_stepOK h.L_pos h.ρ_nonneg h.ρL (h.Lam_pos s).le (h.Lam_le hs)
  set ℓ := tℓ L ρ R ε
  set τ := tτ L ρ
  set A := 32 * ℓ / τ
  set B1 := 176 * σ ^ 2 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 / (τ * ε ^ 2)
  set x := 2 ^ s * tl0 L ρ R ε / L with hxdef
  have hℓ : 0 ≤ ℓ := by
    have := h.ℓ_le
    unfold ℓ tℓ; apply Real.log_nonneg
    have : 1 ≤ tK0 L ρ := le_trans (by norm_num) h.K0_ge
    have hS1 : (1 : ℝ) ≤ (tS L ρ R ε : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) (tS L ρ R ε); linarith
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) this 2,
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hS1 2]
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hΛs : 0 < (2 ^ (s + 1) - 1) * tl0 L ρ R ε := h.Lam_pos s
  have hρ0 := h.ρ_nonneg
  have hγ0 : 0 < tγ L ρ := by unfold tγ; positivity
  have hq0 : 0 < τ / 16 * tγ L ρ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) := by positivity
  have hpowle : (2 : ℝ) ^ s * tl0 L ρ R ε ≤ (2 ^ (s + 1) - 1) * tl0 L ρ R ε := by
    have h1 : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ s ≤ 2 ^ (s + 1) - 1 := by rw [pow_succ]; linarith
    exact mul_le_mul_of_nonneg_right h2 hl.le
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one hL]
    have := h.Lam_le hs
    unfold tΛm at this
    have h3 : τ ^ 3 ≤ 1 := pow_le_one₀ hτ.le h.τ_le
    nlinarith
  have hγ1 : tγ L ρ ≤ 1 / L := by
    unfold tγ; rw [div_le_div_iff₀ (by positivity) hL]; nlinarith [h.ρL]
  have hγ2 : 1 / (2 * L) ≤ tγ L ρ := by
    unfold tγ; apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_nonneg h.ρ_nonneg hL.le; linarith
  have hq : τ * x / 32 ≤ τ / 16 * tγ L ρ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) := by
    have : τ / 16 * (1 / (2 * L)) * (2 ^ s * tl0 L ρ R ε) ≤
        τ / 16 * tγ L ρ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) := by
      gcongr
    rw [hxdef]; refine le_trans (le_of_eq ?_) this; field_simp; try ring
  have hT : ((tunedCfg L ρ R σ ε).T s : ℝ) ≤ A / x + 1 := by
    simp only [tunedCfg]
    refine (Nat.ceil_lt_add_one (div_nonneg hℓ hq0.le)).le.trans ?_
    have : ℓ / (τ / 16 * tγ L ρ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε)) ≤ A / x := by
      rw [show A / x = ℓ / (τ * x / 32) by simp only [A]; field_simp]
      exact div_le_div_of_nonneg_left hℓ (by positivity) hq
    linarith
  have hb : ((tunedCfg L ρ R σ ε).b s : ℝ) ≤ B1 * x + 2 := by
    simp only [tunedCfg]; push_cast
    have hδs := h.δ_pos s
    have hc := (Nat.ceil_lt_add_one (by positivity :
      (0:ℝ) ≤ 44 * tγ L ρ * σ ^ 2 / (τ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) * tδ L ρ R ε s ^ 2))).le
    have hmain : 44 * tγ L ρ * σ ^ 2 / (τ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) * tδ L ρ R ε s ^ 2) ≤
        B1 * x := by
      have hδ : tδ L ρ R ε s = ε / (tK0 L ρ * ((tS L ρ R ε : ℝ) + 1) * (2 ^ (s + 1) * tl0 L ρ R ε)) := rfl
      have hΛpos := h.Lam_pos s
      calc 44 * tγ L ρ * σ ^ 2 / (τ * ((2 ^ (s + 1) - 1) * tl0 L ρ R ε) * tδ L ρ R ε s ^ 2)
          ≤ 44 * (1 / L) * σ ^ 2 / (τ * (2 ^ s * tl0 L ρ R ε) * tδ L ρ R ε s ^ 2) := by
            have := h.δ_pos s
            gcongr
        _ = B1 * x := by
            rw [hδ, hxdef]; simp only [B1]
            rw [pow_succ]
            field_simp
            try ring
    linarith
  have hlen : (stageLen (tunedCfg L ρ R σ ε) s : ℝ) =
      (2 * ((tunedCfg L ρ R σ ε).b s : ℝ) + 1) * ((tunedCfg L ρ R σ ε).T s : ℝ) := by
    unfold stageLen; push_cast; ring
  rw [hlen]
  have hb0 : (0 : ℝ) ≤ 2 * ((tunedCfg L ρ R σ ε).b s : ℝ) + 1 := by positivity
  have hB1 : 0 ≤ B1 := by simp only [B1]; positivity
  have hA : 0 ≤ A := by simp only [A]; positivity
  calc (2 * ((tunedCfg L ρ R σ ε).b s : ℝ) + 1) * ((tunedCfg L ρ R σ ε).T s : ℝ)
      ≤ (2 * (B1 * x + 2) + 1) * (A / x + 1) := by
        apply mul_le_mul (by linarith) hT (by positivity) (by positivity)
    _ = 2 * A * B1 + 2 * B1 * x + 5 + 5 * A * (1 / x) := by field_simp; try ring
    _ ≤ 2 * A * B1 + 2 * B1 + 5 + 5 * A * (L / (2 ^ s * tl0 L ρ R ε)) := by
        have : 1 / x = L / (2 ^ s * tl0 L ρ R ε) := by rw [hxdef]; field_simp
        rw [this]
        nlinarith


lemma budget_arith {τ Λg X Y S1 A B1 bf Ss : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hΛg : 1 ≤ Λg)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B1)
    (hsum : Ss ≤ S1 * (2 * A * B1 + 2 * B1 + 5) + 5 * A * (2 * (512 / τ ^ 3 + 24 * X)))
    (hbf : bf ≤ 256 * Y + 2) (hS : S1 ≤ 2 * Λg) (hA : A ≤ 768 * Λg / τ)
    (hB : B1 ≤ 704 * 2 ^ 30 * Λg ^ 2 * Y / τ ^ 7) :
    1 + bf + Ss ≤ 2 ^ 53 / τ ^ 8 * (1 + X + Y) * Λg ^ 4 := by
  have hΛ0 : 0 ≤ Λg := by linarith
  have hΛ1 : Λg ≤ Λg ^ 4 := by
    calc Λg = Λg ^ 1 := by ring
      _ ≤ Λg ^ 4 := pow_le_pow_right₀ hΛg (by norm_num)
  have hΛ3 : Λg ^ 3 ≤ Λg ^ 4 := pow_le_pow_right₀ hΛg (by norm_num)
  have hΛ4 : 1 ≤ Λg ^ 4 := one_le_pow₀ hΛg
  obtain ⟨u, hu⟩ : ∃ u, u = 1 / τ := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hτ]; linarith
  have hu0 : 0 ≤ u := by linarith
  have hupow : ∀ k : ℕ, 1 ≤ u ^ k := fun k => one_le_pow₀ hu1
  have hmono : ∀ j k : ℕ, j ≤ k → u ^ j ≤ u ^ k := fun j k hjk => pow_le_pow_right₀ hu1 hjk
  have eA : 768 * Λg / τ = 768 * Λg * u := by rw [hu]; field_simp
  have eB : 704 * 2 ^ 30 * Λg ^ 2 * Y / τ ^ 7 = 704 * 2 ^ 30 * Λg ^ 2 * Y * u ^ 7 := by
    rw [hu]; field_simp
  have e512 : 512 / τ ^ 3 = 512 * u ^ 3 := by rw [hu]; field_simp
  have egoal : 2 ^ 53 / τ ^ 8 * (1 + X + Y) * Λg ^ 4 = 2 ^ 53 * u ^ 8 * (1 + X + Y) * Λg ^ 4 := by
    rw [hu]; field_simp
  have hA' : A ≤ 768 * Λg * u := eA ▸ hA
  have hB' : B1 ≤ 704 * 2 ^ 30 * Λg ^ 2 * Y * u ^ 7 := eB ▸ hB
  rw [e512] at hsum
  rw [egoal]
  have hP8 : 1 ≤ Λg ^ 4 * u ^ 8 := by
    have := hupow 8
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Λg ^ 4 * u ^ 8 := mul_le_mul hΛ4 this (by norm_num) (by positivity)
  have t1 : S1 * (2 * A * B1) ≤ 2162688 * 2 ^ 30 * (Λg ^ 4 * Y * u ^ 8) := by
    have h1 : S1 * (2 * A * B1) ≤ 2 * Λg * (2 * (768 * Λg * u) * (704 * 2 ^ 30 * Λg ^ 2 * Y * u ^ 7)) := by
      apply mul_le_mul hS _ (by positivity) (by positivity)
      exact mul_le_mul (by linarith) hB' hB0 (by positivity)
    have h2 : 2 * Λg * (2 * (768 * Λg * u) * (704 * 2 ^ 30 * Λg ^ 2 * Y * u ^ 7)) =
        2162688 * 2 ^ 30 * (Λg ^ 4 * Y * u ^ 8) := by ring
    linarith
  have t2 : S1 * (2 * B1) ≤ 2816 * 2 ^ 30 * (Λg ^ 4 * Y * u ^ 8) := by
    have h1 : S1 * (2 * B1) ≤ 2 * Λg * (2 * (704 * 2 ^ 30 * Λg ^ 2 * Y * u ^ 7)) :=
      mul_le_mul hS (by linarith) (by positivity) (by positivity)
    have h2 : 2 * Λg * (2 * (704 * 2 ^ 30 * Λg ^ 2 * Y * u ^ 7)) = 2816 * 2 ^ 30 * (Λg ^ 3 * Y * u ^ 7) := by
      ring
    have h3 : Λg ^ 3 * Y * u ^ 7 ≤ Λg ^ 4 * Y * u ^ 8 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hΛ3 hY) (hmono 7 8 (by norm_num)) (by positivity)
        (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2816 * 2 ^ 30)
    linarith
  have t3 : S1 * 5 ≤ 10 * (Λg ^ 4 * u ^ 8) := by
    have hh : Λg ≤ Λg ^ 4 * u ^ 8 := hΛ1.trans (le_mul_of_one_le_right (by positivity) (hupow 8))
    linarith
  have t4 : 5 * A * (2 * (512 * u ^ 3)) ≤ 3932160 * (Λg ^ 4 * u ^ 8) := by
    have h1 : 5 * A * (2 * (512 * u ^ 3)) ≤ 5 * (768 * Λg * u) * (2 * (512 * u ^ 3)) := by gcongr
    have h2 : 5 * (768 * Λg * u) * (2 * (512 * u ^ 3)) = 3932160 * (Λg * u ^ 4) := by ring
    have h3 : Λg * u ^ 4 ≤ Λg ^ 4 * u ^ 8 :=
      mul_le_mul hΛ1 (hmono 4 8 (by norm_num)) (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 3932160)
    linarith
  have t5 : 5 * A * (2 * (24 * X)) ≤ 184320 * (Λg ^ 4 * X * u ^ 8) := by
    have h1 : 5 * A * (2 * (24 * X)) ≤ 5 * (768 * Λg * u) * (2 * (24 * X)) := by gcongr
    have h2 : 5 * (768 * Λg * u) * (2 * (24 * X)) = 184320 * (Λg * X * u ^ 1) := by ring
    have h3 : Λg * X * u ^ 1 ≤ Λg ^ 4 * X * u ^ 8 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hΛ1 hX) (hmono 1 8 (by norm_num)) (by positivity)
        (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 184320)
    linarith
  have t6 : Y ≤ Λg ^ 4 * Y * u ^ 8 := by
    have := mul_le_mul_of_nonneg_left hP8 hY
    linarith [show Y * (Λg ^ 4 * u ^ 8) = Λg ^ 4 * Y * u ^ 8 by ring]
  have hsplit : 2 ^ 53 * u ^ 8 * (1 + X + Y) * Λg ^ 4 =
      2 ^ 53 * (Λg ^ 4 * u ^ 8) + 2 ^ 53 * (Λg ^ 4 * X * u ^ 8) + 2 ^ 53 * (Λg ^ 4 * Y * u ^ 8) := by ring
  rw [hsplit]
  have p2 : 0 ≤ Λg ^ 4 * X * u ^ 8 := by positivity
  have p3 : 0 ≤ Λg ^ 4 * Y * u ^ 8 := by positivity
  have hexp : S1 * (2 * A * B1 + 2 * B1 + 5) + 5 * A * (2 * (512 * u ^ 3 + 24 * X)) =
      S1 * (2 * A * B1) + S1 * (2 * B1) + S1 * 5 + 5 * A * (2 * (512 * u ^ 3)) +
        5 * A * (2 * (24 * X)) := by ring
  rw [hexp] at hsum
  linarith

theorem TuneHyp.planLen_le (h : TuneHyp L ρ R σ ε) :
    (planLen (tunedCfg L ρ R σ ε) : ℝ) ≤
      2 ^ 53 / tτ L ρ ^ 8 * (1 + L * R / ε + σ ^ 2 / ε ^ 2) * tΛg L ρ R ε ^ 4 := by
  have hL := h.L_pos
  have hτ := h.τ_pos
  have hτ1 := h.τ_le
  have hl := h.l0_pos
  have hε := h.ε_pos
  have hK : 0 < tK0 L ρ := lt_of_lt_of_le (by norm_num) h.K0_ge
  have hst : ∀ s ∈ Finset.range (tS L ρ R ε + 1), (stageLen (tunedCfg L ρ R σ ε) s : ℝ) ≤
      2 * (32 * tℓ L ρ R ε / tτ L ρ) *
          (176 * σ ^ 2 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 / (tτ L ρ * ε ^ 2)) +
        2 * (176 * σ ^ 2 * tK0 L ρ ^ 2 * ((tS L ρ R ε : ℝ) + 1) ^ 2 / (tτ L ρ * ε ^ 2)) + 5 +
        5 * (32 * tℓ L ρ R ε / tτ L ρ) * ((L / tl0 L ρ R ε) * (1 / 2 : ℝ) ^ s) := by
    intro s hs
    have := h.stage_len (s := s) (by simp at hs; omega)
    have e : L / (2 ^ s * tl0 L ρ R ε) = (L / tl0 L ρ R ε) * (1 / 2 : ℝ) ^ s := by
      rw [one_div_pow]; field_simp
    rw [e] at this; exact this
  have hℓ0 : 0 ≤ tℓ L ρ R ε := by
    unfold tℓ; apply Real.log_nonneg
    have : 1 ≤ tK0 L ρ := le_trans (by norm_num) h.K0_ge
    have hS1 : (1 : ℝ) ≤ (tS L ρ R ε : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) (tS L ρ R ε); linarith
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) this 2,
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hS1 2]
  have hplan : (planLen (tunedCfg L ρ R σ ε) : ℝ) =
      1 + ((tunedCfg L ρ R σ ε).bf : ℝ) +
        ∑ s ∈ Finset.range (tS L ρ R ε + 1), (stageLen (tunedCfg L ρ R σ ε) s : ℝ) := by
    unfold planLen; rw [stagesLen_eq]; push_cast; rfl
  have hgeo := sum_geometric_two_le (tS L ρ R ε + 1)
  set S := tS L ρ R ε
  set τ := tτ L ρ with hτdef
  set ℓ := tℓ L ρ R ε
  set Λg := tΛg L ρ R ε with hΛgdef
  set A := 32 * ℓ / τ with hAdef
  set B1 := 176 * σ ^ 2 * tK0 L ρ ^ 2 * ((S : ℝ) + 1) ^ 2 / (τ * ε ^ 2) with hB1def
  set Lq := L / tl0 L ρ R ε with hLq
  have hΛg := h.Λg_ge
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B1 := by rw [hB1def]; positivity
  have hLq0 : 0 ≤ Lq := by rw [hLq]; positivity
  have hsum : ∑ s ∈ Finset.range (S + 1), (stageLen (tunedCfg L ρ R σ ε) s : ℝ) ≤
      ((S : ℝ) + 1) * (2 * A * B1 + 2 * B1 + 5) + 5 * A * (2 * Lq) := by
    refine (Finset.sum_le_sum hst).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.mul_sum]
    push_cast
    have : 5 * A * (Lq * ∑ i ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ i) ≤ 5 * A * (2 * Lq) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    linarith
  have hLl : Lq = 512 / τ ^ 3 + 24 * (L * R / ε) := by
    rw [hLq]
    unfold tl0 tΛm
    rw [← hτdef]
    have := hτ.ne'
    field_simp
    try ring
  have hbf : ((tunedCfg L ρ R σ ε).bf : ℝ) ≤ 256 * (σ ^ 2 / ε ^ 2) + 2 := by
    simp only [tunedCfg]; push_cast
    have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 256 * σ ^ 2 / ε ^ 2)
    have e : 256 * σ ^ 2 / ε ^ 2 = 256 * (σ ^ 2 / ε ^ 2) := by ring
    linarith
  have hS2 : (S : ℝ) + 1 ≤ 2 * Λg := by
    have := h.S_log
    have h2 : 0 ≤ Real.log (2 / τ) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hτ]; linarith
    have e : Λg = 1 + Real.log (2 + L * R / ε) + Real.log (2 / τ) := rfl
    rw [e]; linarith
  have hℓ : ℓ ≤ 24 * Λg := h.ℓ_le
  have hA : A ≤ 768 * Λg / τ := by
    rw [hAdef, div_le_div_iff_of_pos_right hτ]; linarith
  have hK2 : tK0 L ρ ^ 2 = 2 ^ 30 / τ ^ 6 := by
    have e : tK0 L ρ = 2 ^ 15 / τ ^ 3 := rfl
    rw [e]; have := hτ.ne'; field_simp; try ring
  have hB : B1 ≤ 704 * 2 ^ 30 * Λg ^ 2 * (σ ^ 2 / ε ^ 2) / τ ^ 7 := by
    rw [hB1def, hK2]
    have hS4 : ((S : ℝ) + 1) ^ 2 ≤ 4 * Λg ^ 2 := by
      have h0 : (0 : ℝ) ≤ (S : ℝ) + 1 := by positivity
      nlinarith
    have hτ7 : 0 < τ ^ 7 := by positivity
    rw [div_le_div_iff₀ (by positivity) hτ7]
    have e : 176 * σ ^ 2 * (2 ^ 30 / τ ^ 6) * ((S : ℝ) + 1) ^ 2 * τ ^ 7 =
        176 * σ ^ 2 * 2 ^ 30 * ((S : ℝ) + 1) ^ 2 * τ := by
      have := hτ.ne'; field_simp; try ring
    have e2 : 704 * 2 ^ 30 * Λg ^ 2 * (σ ^ 2 / ε ^ 2) * (τ * ε ^ 2) =
        704 * 2 ^ 30 * Λg ^ 2 * σ ^ 2 * τ := by
      have := hε.ne'; field_simp
    rw [e, e2]
    nlinarith [mul_le_mul_of_nonneg_left hS4 (by positivity : (0:ℝ) ≤ 176 * σ ^ 2 * 2 ^ 30 * τ)]
  rw [hplan]
  rw [hLl] at hsum
  have hX : 0 ≤ L * R / ε := by have := h.R_nonneg; positivity
  exact budget_arith hτ hτ1 hΛg hX (by positivity) hA0 hB0 hsum hbf hS2 hA hB

end Config

end OracleTemplate.StochasticCohypomonotone
