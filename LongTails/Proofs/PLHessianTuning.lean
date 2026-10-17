import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.PLHessian

noncomputable def tH (L μ ρ σ K ε : ℝ) : ℝ :=
  16 * L + 14 * L * Real.sqrt (Real.sqrt (L / μ)) +
    28311552 * K * Real.sqrt (L / μ) * L * σ ^ 2 * ρ ^ 2 / μ ^ 4 + 64 * σ ^ 2 / ε

noncomputable def tΦ0 (L μ ρ K ε : ℝ) : ℝ :=
  1 / (36864 * ρ ^ 2 / μ ^ 3 + μ / (24 * K * Real.sqrt (L / μ) * L * ε))

noncomputable def tTa (L μ ρ σ K Δ ε : ℝ) : ℕ :=
  ⌈32 * tH L μ ρ σ K ε / μ * Real.log (1 + 6 * Real.sqrt (L / μ) * Δ / ε)⌉₊

noncomputable def tTb (L μ ρ σ K ε : ℝ) : ℕ :=
  ⌈512 * σ ^ 2 / (μ * ε) + 32 * tH L μ ρ σ K ε / μ⌉₊

structure Tune (L μ ρ σ K Δ ε : ℝ) : Prop where
  μ_pos : 0 < μ
  μ_le : μ ≤ L
  ρ_nn : 0 ≤ ρ
  σ_nn : 0 ≤ σ
  K_ge : 1 ≤ K
  Δ_nn : 0 ≤ Δ
  ε_pos : 0 < ε

section

variable {L μ ρ σ K Δ ε : ℝ}

lemma Tune.L_pos (h : Tune L μ ρ σ K Δ ε) : 0 < L := lt_of_lt_of_le h.μ_pos h.μ_le

lemma Tune.sk_ge (h : Tune L μ ρ σ K Δ ε) : 1 ≤ Real.sqrt (L / μ) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ h.μ_pos]; linarith [h.μ_le])

lemma Tune.H_pos (h : Tune L μ ρ σ K Δ ε) : 0 < tH L μ ρ σ K ε := by
  have := h.L_pos; have := h.μ_pos; have := h.ε_pos; have := h.K_ge
  unfold tH; positivity

lemma Tune.Φ0_pos (h : Tune L μ ρ σ K Δ ε) : 0 < tΦ0 L μ ρ K ε := by
  have := h.L_pos; have := h.μ_pos; have := h.ε_pos; have := h.K_ge; have := h.sk_ge
  unfold tΦ0; positivity

lemma Tune.Φ0ρ (h : Tune L μ ρ σ K Δ ε) : 36864 * ρ ^ 2 * tΦ0 L μ ρ K ε ≤ μ ^ 3 := by
  have hμ := h.μ_pos
  have := h.L_pos; have := h.ε_pos; have := h.K_ge; have := h.sk_ge
  unfold tΦ0
  have hp : 0 < μ / (24 * K * Real.sqrt (L / μ) * L * ε) := by positivity
  have hq : 0 ≤ 36864 * ρ ^ 2 / μ ^ 3 := by positivity
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  have e : μ ^ 3 * (36864 * ρ ^ 2 / μ ^ 3) = 36864 * ρ ^ 2 := by field_simp
  have hm := mul_pos (pow_pos hμ 3) hp
  rw [mul_add, e]
  linarith

lemma Tune.c1 (h : Tune L μ ρ σ K Δ ε) : 16 * L * (1 / tH L μ ρ σ K ε) ≤ 1 := by
  have hH := h.H_pos
  rw [mul_one_div, div_le_one hH]
  have := h.L_pos; have := h.μ_pos; have := h.ε_pos; have := h.K_ge
  unfold tH
  have : 0 ≤ 14 * L * Real.sqrt (Real.sqrt (L / μ)) := by positivity
  have : 0 ≤ 28311552 * K * Real.sqrt (L / μ) * L * σ ^ 2 * ρ ^ 2 / μ ^ 4 := by positivity
  have : 0 ≤ 64 * σ ^ 2 / ε := by positivity
  linarith

lemma Tune.c3 (h : Tune L μ ρ σ K Δ ε) :
    196 * Real.sqrt (L / μ) * L ^ 2 * (1 / tH L μ ρ σ K ε) ^ 2 ≤ 1 := by
  have hH := h.H_pos
  have := h.L_pos; have := h.μ_pos; have := h.ε_pos; have := h.K_ge
  set q := Real.sqrt (Real.sqrt (L / μ))
  have hq2 : q ^ 2 = Real.sqrt (L / μ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hle : 14 * L * q ≤ tH L μ ρ σ K ε := by
    unfold tH
    have : 0 ≤ 28311552 * K * Real.sqrt (L / μ) * L * σ ^ 2 * ρ ^ 2 / μ ^ 4 := by positivity
    have : 0 ≤ 64 * σ ^ 2 / ε := by positivity
    linarith
  rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity), ← hq2]
  have h0 : 0 ≤ 14 * L * q := by positivity
  nlinarith

lemma Tune.c2 (h : Tune L μ ρ σ K Δ ε) :
    768 * Real.sqrt (L / μ) * K * L * σ ^ 2 * (1 / tH L μ ρ σ K ε) ≤ μ * tΦ0 L μ ρ K ε := by
  have hH := h.H_pos
  have hμ := h.μ_pos
  have := h.L_pos; have := h.ε_pos; have := h.K_ge; have hsk := h.sk_ge
  set sk := Real.sqrt (L / μ)
  have hΦ := h.Φ0_pos
  unfold tΦ0 at hΦ ⊢
  set D := 36864 * ρ ^ 2 / μ ^ 3 + μ / (24 * K * sk * L * ε) with hD
  have hDp : 0 < D := by positivity
  rw [mul_one_div, mul_one_div, div_le_div_iff₀ hH hDp]
  have e : 768 * sk * K * L * σ ^ 2 * D =
      μ * (28311552 * K * sk * L * σ ^ 2 * ρ ^ 2 / μ ^ 4 + 32 * σ ^ 2 / ε) := by
    rw [hD]; field_simp; ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hμ.le
  unfold tH
  have : 0 ≤ 14 * L * Real.sqrt sk := by positivity
  have : 32 * σ ^ 2 / ε ≤ 64 * σ ^ 2 / ε := by
    apply div_le_div_of_nonneg_right _ h.ε_pos.le; nlinarith [sq_nonneg σ]
  linarith

set_option maxHeartbeats 1000000 in
lemma Tune.accuracy (h : Tune L μ ρ σ K Δ ε) {P0 Ea sum : ℝ}
    (hP0 : P0 ≤ 48 * Real.sqrt (L / μ) * Δ / μ) (hP0n : 0 ≤ P0)
    (hEa : Ea ≤ (1 - μ * (1 / tH L μ ρ σ K ε) / 32) ^ tTa L μ ρ σ K Δ ε * P0 +
      64 * (1 / tH L μ ρ σ K ε) * σ ^ 2 / μ)
    (hs : 1 / tH L μ ρ σ K ε / 2 * sum ≤
      Ea + ((tTb L μ ρ σ K ε : ℝ) + 1) * (2 * (1 / tH L μ ρ σ K ε) ^ 2 * σ ^ 2)) :
    sum / ((tTb L μ ρ σ K ε : ℝ) + 1) ≤ ε := by
  have hH := h.H_pos
  have hμ := h.μ_pos
  have hε := h.ε_pos
  have hL := h.L_pos
  have hsk := h.sk_ge
  set H := tH L μ ρ σ K ε with hHdef
  set sk := Real.sqrt (L / μ)
  set A := 6 * sk * Δ / ε with hA
  have hA0 : 0 ≤ A := by have := h.Δ_nn; positivity
  set η := 1 / H with hηdef
  have hη : 0 < η := by positivity
  set q := μ * η / 32 with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    have := h.c1; rw [← hηdef] at this
    simp only [q]; nlinarith [h.μ_le]
  set Ta := tTa L μ ρ σ K Δ ε
  set Tb := tTb L μ ρ σ K ε
  have hTa : 32 * H / μ * Real.log (1 + A) ≤ (Ta : ℝ) := Nat.le_ceil _
  have hTb : 512 * σ ^ 2 / (μ * ε) + 32 * H / μ ≤ (Tb : ℝ) := Nat.le_ceil _
  have hTb1 : (0 : ℝ) < (Tb : ℝ) + 1 := by positivity
  have hpow : (1 - q) ^ Ta ≤ 1 / (1 + A) := by
    have h1 : (1 - q) ^ Ta ≤ Real.exp (-q) ^ Ta :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) _
    rw [← Real.exp_nat_mul] at h1
    have h2 : Real.log (1 + A) ≤ q * Ta := by
      have : q * (32 * H / μ * Real.log (1 + A)) = Real.log (1 + A) := by
        simp only [q, η]; field_simp
      have hlog : 0 ≤ Real.log (1 + A) := Real.log_nonneg (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hTa hq0]
    have h3 : Real.exp (↑Ta * -q) ≤ Real.exp (-Real.log (1 + A)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.exp_neg, Real.exp_log (by linarith)] at h3
    rw [one_div]; linarith
  have hηTb : 32 / μ ≤ η * ((Tb : ℝ) + 1) := by
    have : 32 * H / μ ≤ (Tb : ℝ) + 1 := by
      have : 0 ≤ 512 * σ ^ 2 / (μ * ε) := by positivity
      linarith
    have e : η * (32 * H / μ) = 32 / μ := by simp only [η]; field_simp
    calc 32 / μ = η * (32 * H / μ) := e.symm
      _ ≤ η * ((Tb : ℝ) + 1) := mul_le_mul_of_nonneg_left this hη.le
  have hsum : sum ≤ 2 * Ea / η + ((Tb : ℝ) + 1) * (4 * η * σ ^ 2) := by
    have e : 1 / H / 2 * sum = η / 2 * sum := rfl
    rw [e] at hs
    have : sum = (η / 2 * sum) * (2 / η) := by field_simp
    rw [this]
    have h2η : 0 ≤ 2 / η := by positivity
    have := mul_le_mul_of_nonneg_right hs h2η
    have e2 : (Ea + ((Tb : ℝ) + 1) * (2 * η ^ 2 * σ ^ 2)) * (2 / η) =
        2 * Ea / η + ((Tb : ℝ) + 1) * (4 * η * σ ^ 2) := by field_simp; ring
    linarith
  rw [div_le_iff₀ hTb1]
  have t1 : 2 * ((1 - q) ^ Ta * P0) / η ≤ ε / 2 * ((Tb : ℝ) + 1) := by
    have hp : (1 - q) ^ Ta * P0 ≤ 1 / (1 + A) * (48 * sk * Δ / μ) :=
      mul_le_mul hpow hP0 hP0n (by positivity)
    rw [div_le_iff₀ hη]
    have key : 2 * (1 / (1 + A) * (48 * sk * Δ / μ)) ≤ ε / 2 * (32 / μ) := by
      rw [show 1 / (1 + A) * (48 * sk * Δ / μ) = 48 * sk * Δ / (μ * (1 + A)) by field_simp]
      rw [show ε / 2 * (32 / μ) = 16 * ε / μ by ring]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hμ]
      have : 6 * sk * Δ = A * ε := by simp only [A]; field_simp
      nlinarith
    have : ε / 2 * (32 / μ) ≤ ε / 2 * (η * ((Tb : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hηTb (by positivity)
    nlinarith
  have t2 : 2 * (64 * η * σ ^ 2 / μ) / η ≤ ε / 4 * ((Tb : ℝ) + 1) := by
    have e : 2 * (64 * η * σ ^ 2 / μ) / η = 128 * σ ^ 2 / μ := by field_simp; ring
    rw [e, div_le_iff₀ hμ]
    have : 512 * σ ^ 2 / (μ * ε) * (ε / 4 * μ) = 128 * σ ^ 2 := by field_simp; ring
    have h32 : 0 ≤ 32 * H / μ := by positivity
    have : 512 * σ ^ 2 / (μ * ε) * (ε / 4 * μ) ≤ ((Tb : ℝ) + 1) * (ε / 4 * μ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have t3 : 4 * η * σ ^ 2 ≤ ε / 16 := by
    have : 64 * σ ^ 2 / ε ≤ H := by
      simp only [hHdef, tH]
      have : 0 ≤ 14 * L * Real.sqrt (Real.sqrt (L / μ)) := by positivity
      have : 0 ≤ 28311552 * K * Real.sqrt (L / μ) * L * σ ^ 2 * ρ ^ 2 / μ ^ 4 := by
        have := h.K_ge; positivity
      linarith
    rw [div_le_iff₀ hε] at this
    simp only [η]
    rw [show 4 * (1 / H) * σ ^ 2 = 4 * σ ^ 2 / H by ring, div_le_iff₀ hH]
    linarith
  have hEa2 : 2 * Ea / η ≤ 2 * ((1 - q) ^ Ta * P0) / η + 2 * (64 * η * σ ^ 2 / μ) / η := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hη.le
    simp only [q] at *; linarith
  have : ((Tb : ℝ) + 1) * (4 * η * σ ^ 2) ≤ ((Tb : ℝ) + 1) * (ε / 16) :=
    mul_le_mul_of_nonneg_left t3 hTb1.le
  nlinarith

end

end OracleTemplate.PLHessian
