import LongTails.Proofs.GradientDependentEnergy

namespace LongTails.Proofs.EnergyHessianLedger

lemma moment_update {P Q r n : ℝ} (hn : 0 ≤ n) (hQ : 0 ≤ Q)
    (h : P ^ 2 ≤ n * Q) : (P + r) ^ 2 ≤ (n + 1) * (Q + r ^ 2) := by
  by_cases hz : n = 0
  · subst n
    have hP : P = 0 := by nlinarith [sq_nonneg P]
    rw [hP]
    nlinarith
  · have hn' : 0 < n := lt_of_le_of_ne hn (Ne.symm hz)
    have hh : 2 * P * r ≤ Q + n * r ^ 2 := by
      have hs := sq_nonneg (P - n * r)
      nlinarith
    nlinarith

structure Totals where
  S : ℝ
  C : ℝ
  D : ℝ
  Q : ℝ
  J : ℝ
  E : ℝ

def push (a : Totals) (L₁ σ r μ δ gout : ℝ) : Totals where
  S := a.S + gout
  C := a.C + σ * r ^ 2
  D := a.D + 100 * L₁ * a.E * r
  Q := a.Q + r ^ 2
  J := a.J + 100 * L₁ * a.E
  E := a.E + (σ * r ^ 3 + δ * r ^ 2 + μ * r ^ 2)

structure Valid (a : Totals) (L₀ L₁ m R ρ b ε σstart σend P : ℝ) (j : ℕ) : Prop where
  S_nonneg : 0 ≤ a.S
  C_nonneg : 0 ≤ a.C
  D_nonneg : 0 ≤ a.D
  Q_nonneg : 0 ≤ a.Q
  J_nonneg : 0 ≤ a.J
  E_nonneg : 0 ≤ a.E
  path_nonneg : 0 ≤ P
  balance : a.S ≤ 4 * a.C + 8 * L₀ * P ^ 2 + 4 * a.D + 4 * a.E / ρ
  moment : P ^ 2 ≤ j * a.Q
  floor : 100 * m * L₀ * a.Q ≤ a.C
  history : a.J ≤ 100 * j * L₁ * a.E
  weighted : 20 * R * a.D ≤ 100 * R ^ 2 * a.E + a.J
  zero_noise : L₁ = 0 → a.D = 0
  cubic : a.C ≤ 2 * b ^ 2 * (σstart - σend) + 200 * b ^ 2 * (j + 1) * m * L₀ +
    200 * b ^ 2 * L₁ * a.S + a.E / b
  lower : (j + 1) * ε ≤ a.S

lemma push_valid (a : Totals) {L₀ L₁ m R ρ b ε σstart σ τ P r μ δ gout : ℝ} {j : ℕ}
    (h : Valid a L₀ L₁ m R ρ b ε σstart σ P j)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hb : 0 < b) (_hρ : 0 < ρ)
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hμ : 0 ≤ μ) (hσ : 0 ≤ σ)
    (hδ : δ = 4 * L₀ * P + 100 * L₁ * a.E)
    (hfloor : 100 * m * L₀ ≤ σ)
    (hgrad : gout ≤ 4 * (σ * r ^ 2 + δ * r + μ * r)) (hglower : ε ≤ gout)
    (hcap : μ * r ≤ (σ * r ^ 3 + δ * r ^ 2 + μ * r ^ 2) / ρ)
    (hnext : τ ≤ σ / 2 + 100 * m * L₀ + 100 * L₁ * gout) :
    Valid (push a L₁ σ r μ δ gout) L₀ L₁ m R ρ b ε σstart τ (P + r) (j + 1) := by
  let e := σ * r ^ 3 + δ * r ^ 2 + μ * r ^ 2
  have hδn : 0 ≤ δ := by rw [hδ]; have := h.path_nonneg; have := h.E_nonneg; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hd1 : 0 ≤ 100 * L₁ * a.E := by have := h.E_nonneg; positivity
  have heδ : 100 * L₁ * a.E * r ^ 2 ≤ e := by
    have hp := mul_nonneg hL₀ h.path_nonneg
    have hpr := mul_nonneg hp (sq_nonneg r)
    have hs : 0 ≤ σ * r ^ 3 := by positivity
    have hm : 0 ≤ μ * r ^ 2 := by positivity
    dsimp [e]
    rw [hδ]
    nlinarith
  have hcubic : σ * r ^ 2 ≤ b ^ 2 * σ + e / b := by
    have hh := mul_le_mul_of_nonneg_left (GradientDependentEnergy.quadratic_cubic_interpolation hr hb) hσ
    have hse : σ * r ^ 3 ≤ e := by
      have hd : 0 ≤ δ * r ^ 2 := by positivity
      have hm : 0 ≤ μ * r ^ 2 := by positivity
      dsimp [e]
      linarith
    have he' := div_le_div_of_nonneg_right hse hb.le
    rw [mul_add, ← mul_div_assoc] at hh
    nlinarith
  have hcoef := mul_le_mul_of_nonneg_left hnext (show 0 ≤ 2 * b ^ 2 by positivity)
  constructor
  · dsimp [push]; exact add_nonneg h.S_nonneg (hε.trans hglower)
  · dsimp [push]; exact add_nonneg h.C_nonneg (by positivity)
  · dsimp [push]; exact add_nonneg h.D_nonneg (mul_nonneg hd1 hr)
  · dsimp [push]; exact add_nonneg h.Q_nonneg (sq_nonneg r)
  · dsimp [push]; exact add_nonneg h.J_nonneg hd1
  · exact add_nonneg h.E_nonneg he
  · exact add_nonneg h.path_nonneg hr
  · change a.S + gout ≤ 4 * (a.C + σ * r ^ 2) + 8 * L₀ * (P + r) ^ 2 +
      4 * (a.D + 100 * L₁ * a.E * r) + 4 * (a.E + e) / ρ
    have hh := h.balance
    have hs := mul_nonneg hL₀ (sq_nonneg r)
    have hc : μ * r ≤ e / ρ := hcap
    simp only [mul_add, add_div]
    rw [hδ] at hgrad
    simp only [mul_div_assoc] at hh ⊢
    nlinarith
  · change (P + r) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) * (a.Q + r ^ 2)
    push_cast
    exact moment_update (Nat.cast_nonneg j) h.Q_nonneg h.moment
  · dsimp [push]
    have hh := mul_le_mul_of_nonneg_right hfloor (sq_nonneg r)
    have hf := h.floor
    nlinarith
  · change a.J + 100 * L₁ * a.E ≤ 100 * ((j + 1 : ℕ) : ℝ) * L₁ * (a.E + e)
    push_cast
    have hh := h.history
    have he' : 0 ≤ 100 * ((j : ℝ) + 1) * L₁ * e := by positivity
    nlinarith
  · change 20 * R * (a.D + 100 * L₁ * a.E * r) ≤
      100 * R ^ 2 * (a.E + e) + (a.J + 100 * L₁ * a.E)
    have hs := mul_nonneg hd1 (sq_nonneg (10 * R * r - 1))
    have he' := mul_le_mul_of_nonneg_left heδ (show 0 ≤ 100 * R ^ 2 by positivity)
    have hh := h.weighted
    nlinarith
  · intro hz
    simp [push, hz, h.zero_noise hz]
  · change a.C + σ * r ^ 2 ≤ 2 * b ^ 2 * (σstart - τ) +
      200 * b ^ 2 * (((j + 1 : ℕ) : ℝ) + 1) * m * L₀ +
      200 * b ^ 2 * L₁ * (a.S + gout) + (a.E + e) / b
    push_cast
    rw [add_div]
    have hh := h.cubic
    nlinarith
  · change (((j + 1 : ℕ) : ℝ) + 1) * ε ≤ a.S + gout
    push_cast
    have hh := h.lower
    nlinarith

def initial (σ r μ gout : ℝ) : Totals :=
  ⟨gout, σ * r ^ 2, 0, 0, 0, σ * r ^ 3 + μ * r ^ 2⟩

lemma initial_valid {L₀ L₁ m R ρ b ε σ τ r μ gout : ℝ}
    (hb : 0 < b) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hμ : 0 ≤ μ) (hσ : 0 ≤ σ)
    (hgrad : gout ≤ 4 * (σ * r ^ 2 + μ * r)) (hglower : ε ≤ gout)
    (hcap : μ * r ≤ (σ * r ^ 3 + μ * r ^ 2) / ρ)
    (hnext : τ ≤ σ / 2 + 100 * m * L₀ + 100 * L₁ * gout) :
    Valid (initial σ r μ gout) L₀ L₁ m R ρ b ε σ τ 0 0 := by
  have he : 0 ≤ σ * r ^ 3 + μ * r ^ 2 := by positivity
  have hcubic : σ * r ^ 2 ≤ b ^ 2 * σ + (σ * r ^ 3 + μ * r ^ 2) / b := by
    have hh := mul_le_mul_of_nonneg_left (GradientDependentEnergy.quadratic_cubic_interpolation hr hb) hσ
    have he' := div_le_div_of_nonneg_right
      (show σ * r ^ 3 ≤ σ * r ^ 3 + μ * r ^ 2 from
        le_add_of_nonneg_right (mul_nonneg hμ (sq_nonneg r))) hb.le
    rw [mul_add, ← mul_div_assoc] at hh
    nlinarith
  have hcoef := mul_le_mul_of_nonneg_left hnext (show 0 ≤ 2 * b ^ 2 by positivity)
  constructor
  · exact hε.trans hglower
  · dsimp [initial]; positivity
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact he
  · exact le_rfl
  · dsimp [initial]
    simp only [mul_div_assoc]
    nlinarith
  · simp [initial]
  · simp only [initial, mul_zero]
    positivity
  · simp [initial]
  · dsimp [initial]
    have hh : 0 ≤ 100 * R ^ 2 * (σ * r ^ 3 + μ * r ^ 2) := by positivity
    linarith
  · intro _; rfl
  · dsimp [initial]
    push_cast
    nlinarith
  · simpa [initial] using hglower

lemma final_balance (a : Totals) {L₀ L₁ R ρ b ε σstart σend P : ℝ} {m : ℕ}
    (h : Valid a L₀ L₁ m R ρ b ε σstart σend P m)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hm : 1 ≤ m) (hR : 0 ≤ R)
    (hR2 : R ^ 2 = m * L₁) :
    a.S ≤ 4 * a.C + 4 * (a.C / 25 + 10 * R * a.E) + 4 * a.E / ρ := by
  have hD : a.D ≤ 10 * R * a.E := by
    by_cases hz : R = 0
    · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hLzero : L₁ = 0 := by rw [hz] at hR2; nlinarith
      rw [h.zero_noise hLzero, hz]
      simp
    · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
      have hh := h.weighted
      have hj := h.history
      have hreq : 100 * (m : ℝ) * L₁ * a.E = 100 * R ^ 2 * a.E := by rw [hR2]; ring
      rw [hreq] at hj
      nlinarith
  have hpath := mul_le_mul_of_nonneg_left h.moment (show 0 ≤ 2 * L₀ by positivity)
  have hfloor := h.floor
  have hc := h.C_nonneg
  have hb := h.balance
  nlinarith

end LongTails.Proofs.EnergyHessianLedger
