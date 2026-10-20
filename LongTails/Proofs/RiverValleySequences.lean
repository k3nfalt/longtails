import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.RiverValley

lemma tele_sum {V p : ℕ → ℝ} {c d : ℝ} (hV0 : ∀ n, 0 ≤ V n)
    (h : ∀ n, V (n + 1) ≤ V n - c * p n + d) (M : ℕ) :
    c * ∑ n ∈ Finset.range M, p n ≤ V 0 + M * d := by
  have key : ∀ M, V M + c * ∑ n ∈ Finset.range M, p n ≤ V 0 + M * d := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := h M
        push_cast
        linarith
  have := key M
  have := hV0 M
  linarith

lemma contract_sum {s p : ℕ → ℝ} {k e d : ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (h : ∀ n, s (n + 1) ≤ (1 - k) * s n + e * p n + d) (M : ℕ) :
    k * ∑ n ∈ Finset.range M, s n ≤ s 0 + e * ∑ n ∈ Finset.range M, p n + M * d := by
  have key : ∀ M, s M + k * ∑ n ∈ Finset.range M, s n ≤
      s 0 + e * ∑ n ∈ Finset.range M, p n + M * d := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
        have := h M
        push_cast
        linarith
  have := key M
  have := hs0 M
  linarith

lemma gronwall {Ψ : ℕ → ℝ} {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (h : ∀ k, Ψ (k + 1) ≤ (1 + x) * Ψ k + D) :
    ∀ k, Ψ k ≤ (1 + x) ^ k * (Ψ 0 + k * D) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := h k
      have hp : 1 ≤ (1 + x) ^ k := one_le_pow₀ (by linarith)
      have h2 : (1 + x) * Ψ k ≤ (1 + x) * ((1 + x) ^ k * (Ψ 0 + k * D)) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have h3 : D ≤ (1 + x) ^ (k + 1) * D := by
        have : 1 ≤ (1 + x) ^ (k + 1) := one_le_pow₀ (by linarith)
        nlinarith
      push_cast
      rw [pow_succ] at h3 ⊢
      have e : (1 + x) ^ k * (1 + x) * (Ψ 0 + (k + 1) * D) =
          (1 + x) * ((1 + x) ^ k * (Ψ 0 + k * D)) + (1 + x) ^ k * (1 + x) * D := by ring
      linarith

lemma pow_le_two {x : ℝ} {K : ℕ} (hx : 0 ≤ x) (hK : 2 * K * x ≤ 1) : (1 + x) ^ K ≤ 2 := by
  have h1 : (1 + x) ^ K ≤ Real.exp (K * x) := by
    calc (1 + x) ^ K ≤ Real.exp x ^ K :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) K
      _ = Real.exp (K * x) := by rw [← Real.exp_nat_mul]
  have h2 : Real.exp (K * x) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (1 / 2) ≤ 2 := by
    have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have he : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

lemma geom_bound {q : ℕ → ℝ} {r B : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, q (k + 1) ≤ r * q k + B) (hB : 0 ≤ B) :
    ∀ k, q k ≤ r ^ k * q 0 + B / (1 - r) := by
  intro k
  induction k with
  | zero =>
      simp
      positivity
  | succ k ih =>
      have h1 := h k
      have h2 := mul_le_mul_of_nonneg_left ih hr0
      have hne : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
      have e : r * (B / (1 - r)) + B = B / (1 - r) := by
        field_simp; ring
      rw [pow_succ]
      nlinarith

lemma gronwall_le {Ψ : ℕ → ℝ} {x D : ℝ} {K : ℕ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (h : ∀ k, k < K → Ψ (k + 1) ≤ (1 + x) * Ψ k + D) :
    ∀ k, k ≤ K → Ψ k ≤ (1 + x) ^ k * (Ψ 0 + k * D) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have h1 := h k (by omega)
      have h2 : (1 + x) * Ψ k ≤ (1 + x) * ((1 + x) ^ k * (Ψ 0 + k * D)) :=
        mul_le_mul_of_nonneg_left ih' (by linarith)
      have h3 : D ≤ (1 + x) ^ (k + 1) * D := by
        have : 1 ≤ (1 + x) ^ (k + 1) := one_le_pow₀ (by linarith)
        nlinarith
      push_cast
      rw [pow_succ] at h3 ⊢
      have e : (1 + x) ^ k * (1 + x) * (Ψ 0 + (k + 1) * D) =
          (1 + x) * ((1 + x) ^ k * (Ψ 0 + k * D)) + (1 + x) ^ k * (1 + x) * D := by ring
      linarith

lemma geom_le {q : ℕ → ℝ} {r B : ℝ} {K : ℕ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, k < K → q (k + 1) ≤ r * q k + B) (hB : 0 ≤ B) :
    ∀ k, k ≤ K → q k ≤ r ^ k * q 0 + B / (1 - r) := by
  intro k
  induction k with
  | zero => intro _; simp; positivity
  | succ k ih =>
      intro hk
      have h1 := h k (by omega)
      have h2 := mul_le_mul_of_nonneg_left (ih (by omega)) hr0
      have hne : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
      have e : r * (B / (1 - r)) + B = B / (1 - r) := by
        field_simp; ring
      rw [pow_succ]
      nlinarith

lemma cooldown_bound {p s q : ℕ → ℝ} {η μ Lh Luv Sw SA Ca Hw HA : ℝ} {K : ℕ} (hη : 0 ≤ η)
    (hLh : 0 ≤ Lh) (hμ : 0 < μ) (hημ : η * μ ≤ 1) (hSA : 0 ≤ SA) (hCa : 0 ≤ Ca)
    (hHw : 0 ≤ Hw) (hHA : 0 ≤ HA) (hp0 : ∀ k, 0 ≤ p k) (hs0 : ∀ k, 0 ≤ s k)
    (hp : ∀ k, k < K → p (k + 1) ≤ (1 + 4 * Lh * η) * p k + 2 * Lh * η * Luv ^ 2 * s k +
      η ^ 2 * Ca)
    (hs : ∀ k, k < K → s (k + 1) ≤ (1 - η * μ / 2) * s k + η * Sw * p k + η ^ 2 * Hw)
    (hq : ∀ k, k < K → q (k + 1) ≤ (1 - η * μ / 2) * q k + η * SA * p k + η ^ 2 * HA)
    (hθ : 8 * Luv ^ 2 * Sw ≤ μ) (hK : 10 * Lh * η * K ≤ 1) :
    p K ≤ 2 * (p 0 + 8 * Lh * Luv ^ 2 / μ * s 0 + K * η ^ 2 * (Ca + 8 * Lh * Luv ^ 2 / μ * Hw)) ∧
    q K ≤ (1 - η * μ / 2) ^ K * q 0 + 2 / μ * (SA * (2 * (p 0 + 8 * Lh * Luv ^ 2 / μ * s 0 +
      K * η ^ 2 * (Ca + 8 * Lh * Luv ^ 2 / μ * Hw))) + η * HA) := by
  set θ := 8 * Lh * Luv ^ 2 / μ
  have hθ0 : 0 ≤ θ := by positivity
  set Ψ : ℕ → ℝ := fun k => p k + θ * s k
  have hθSw : θ * Sw ≤ Lh := by
    simp only [θ]
    rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
    have := mul_le_mul_of_nonneg_left hθ hLh
    nlinarith
  have hΨ : ∀ k, k < K → Ψ (k + 1) ≤ (1 + 5 * Lh * η) * Ψ k + η ^ 2 * (Ca + θ * Hw) := by
    intro k hk
    have h1 := hp k hk
    have h2 := mul_le_mul_of_nonneg_left (hs k hk) hθ0
    have h3 : θ * (η * Sw * p k) ≤ Lh * η * p k := by
      have := mul_le_mul_of_nonneg_right hθSw (mul_nonneg hη (hp0 k))
      nlinarith
    have h4 : 2 * Lh * η * Luv ^ 2 * s k + θ * ((1 - η * μ / 2) * s k) ≤ θ * s k := by
      have e : θ * (η * μ / 2) = 4 * Lh * Luv ^ 2 * η := by simp only [θ]; field_simp; ring
      have e2 : θ * ((1 - η * μ / 2) * s k) = θ * s k - 4 * Lh * Luv ^ 2 * η * s k := by
        rw [← e]; ring
      have : 0 ≤ 2 * Lh * η * Luv ^ 2 * s k := by have := hs0 k; positivity
      linarith
    have e3 : θ * ((1 - η * μ / 2) * s k + η * Sw * p k + η ^ 2 * Hw) =
        θ * ((1 - η * μ / 2) * s k) + θ * (η * Sw * p k) + η ^ 2 * (θ * Hw) := by ring
    have e4 : (1 + 5 * Lh * η) * (p k + θ * s k) + η ^ 2 * (Ca + θ * Hw) =
        (1 + 4 * Lh * η) * p k + Lh * η * p k + θ * s k + 5 * Lh * η * (θ * s k) +
          η ^ 2 * Ca + η ^ 2 * (θ * Hw) := by ring
    have e5 : (1 + 4 * Lh * η) * p k + 2 * Lh * η * Luv ^ 2 * s k + η ^ 2 * Ca =
        (1 + 4 * Lh * η) * p k + 2 * Lh * η * Luv ^ 2 * s k + η ^ 2 * Ca := rfl
    have h5 : 0 ≤ 5 * Lh * η * (θ * s k) := by have := hs0 k; positivity
    show p (k + 1) + θ * s (k + 1) ≤ (1 + 5 * Lh * η) * (p k + θ * s k) + η ^ 2 * (Ca + θ * Hw)
    linarith
  have hD : 0 ≤ η ^ 2 * (Ca + θ * Hw) := by positivity
  have hg := gronwall_le (by positivity : (0:ℝ) ≤ 5 * Lh * η) hD hΨ
  have h2 : (1 + 5 * Lh * η) ^ K ≤ 2 := pow_le_two (by positivity) (by nlinarith)
  set P := 2 * (p 0 + θ * s 0 + K * η ^ 2 * (Ca + θ * Hw))
  have hΨP : ∀ k, k ≤ K → Ψ k ≤ P := by
    intro k hk
    have := hg k hk
    have hpow : (1 + 5 * Lh * η) ^ k ≤ 2 :=
      (pow_le_pow_right₀ (by nlinarith) hk).trans h2
    have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
    have hΨ0 : 0 ≤ Ψ 0 + k * (η ^ 2 * (Ca + θ * Hw)) := by
      have := hp0 0; have := hs0 0; simp only [Ψ]; positivity
    have := mul_le_mul_of_nonneg_right hpow hΨ0
    have := mul_le_mul_of_nonneg_left hk' hD
    simp only [P, Ψ] at *
    nlinarith
  have hpP : ∀ k, k ≤ K → p k ≤ P := by
    intro k hk
    have := hΨP k hk
    have := mul_nonneg hθ0 (hs0 k)
    simp only [Ψ] at *
    linarith
  refine ⟨hpP K le_rfl, ?_⟩
  have hr0 : 0 ≤ 1 - η * μ / 2 := by linarith
  have hr1 : 1 - η * μ / 2 < 1 ∨ η * μ = 0 := by
    rcases (mul_nonneg hη hμ.le).lt_or_eq with h | h
    · left; linarith
    · right; linarith
  have hq' : ∀ k, k < K → q (k + 1) ≤ (1 - η * μ / 2) * q k + η * (SA * P + η * HA) := by
    intro k hk
    have := hq k hk
    have := mul_le_mul_of_nonneg_left (hpP k hk.le) (mul_nonneg hη hSA)
    nlinarith
  rcases hr1 with hr1 | hr1
  · have hgeo := geom_le hr0 hr1 hq' (by have : 0 ≤ P := le_trans (by
        have := hp0 0; have := hs0 0; positivity) (hΨP 0 (Nat.zero_le _)); positivity) K le_rfl
    have e : η * (SA * P + η * HA) / (1 - (1 - η * μ / 2)) = 2 / μ * (SA * P + η * HA) := by
      have : η ≠ 0 := by intro h0; rw [h0] at hr1; simp at hr1
      field_simp; ring
    rw [e] at hgeo
    exact hgeo
  · have hη0 : η = 0 := by
      rcases mul_eq_zero.mp hr1 with h | h
      · exact h
      · exact absurd h hμ.ne'
    have hqc : ∀ k, k ≤ K → q k ≤ q 0 := by
      intro k
      induction k with
      | zero => intro _; exact le_rfl
      | succ k ih =>
          intro hk
          have := hq k (by omega)
          rw [hη0] at this
          simp at this
          linarith [ih (by omega)]
    rw [hη0]
    simp
    have hP0 : 0 ≤ SA * P := by
      have : 0 ≤ P := le_trans (by have := hp0 0; have := hs0 0; positivity) (hΨP 0 (Nat.zero_le _))
      positivity
    have := hqc K le_rfl
    have : 0 ≤ 2 / μ * (SA * P) := by positivity
    linarith

end OracleTemplate.RiverValley
