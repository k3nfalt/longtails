import LongTails.Algorithms.MovementQuasar
import LongTails.Proofs.QuasarMovementRecursion

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

lemma movement_absorption {μ γ θ m δ q W : ℝ}
    (hμ : 0 < μ) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hm : 1 ≤ m)
    (hq : 1 / 2 ≤ q) (hgt : γ * θ ≤ 1)
    (hsmall : 16777216 * m ^ 2 * δ ^ 2 * θ ^ 3 ≤ γ * μ ^ 2)
    (hw : W ≤ 32768 * (θ ^ 2 / μ * δ ^ 2) * m) :
    W * (61 * m * θ ^ 2) ≤ q * (γ * μ * θ / 2) -
        20 * (θ ^ 2 / μ * δ ^ 2) * θ ^ 2 ∧
    W * (2 * m * (θ ^ 2 / μ) ^ 2) ≤ q * (θ ^ 2 / (4 * μ)) := by
  have hm0 : 0 ≤ m := by linarith
  have hmsq : 1 ≤ m ^ 2 := by nlinarith
  let Z := m ^ 2 * δ ^ 2 * θ ^ 4 / μ
  have hz : 16777216 * Z ≤ γ * μ * θ := by
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ θ / μ by positivity)
    convert hh using 1 <;> (try dsimp only [Z]) <;> field_simp
  have hw1 : W * (61 * m * θ ^ 2) ≤ 1998848 * Z := by
    have hh := mul_le_mul_of_nonneg_right hw (show 0 ≤ 61 * m * θ ^ 2 by positivity)
    convert hh using 1; (try dsimp only [Z]); ring
  have hn1 : 20 * (θ ^ 2 / μ * δ ^ 2) * θ ^ 2 ≤ 20 * Z := by
    have hh := mul_le_mul_of_nonneg_right hmsq (show 0 ≤ 20 * θ ^ 4 * δ ^ 2 / μ by positivity)
    convert hh using 1 <;> (try dsimp only [Z]) <;> ring
  have hq1 := mul_le_mul_of_nonneg_right hq (show 0 ≤ γ * μ * θ / 2 by positivity)
  constructor
  · nlinarith [show 0 ≤ Z by dsimp [Z]; positivity]
  · let A := θ ^ 2 / μ
    let Zg := m ^ 2 * δ ^ 2 * θ ^ 6 / μ ^ 3
    have hzg : 16777216 * Zg ≤ A := by
      have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ θ ^ 3 / μ ^ 3 by positivity)
      have hh' : 16777216 * Zg ≤ (γ * θ) * A := by
        convert hh using 1 <;> (try dsimp only [Zg, A]) <;> field_simp
      exact hh'.trans (by simpa using mul_le_mul_of_nonneg_right hgt (show 0 ≤ A by dsimp [A]; positivity))
    have hw2 : W * (2 * m * (θ ^ 2 / μ) ^ 2) ≤ 65536 * Zg := by
      have hh := mul_le_mul_of_nonneg_right hw (show 0 ≤ 2 * m * (θ ^ 2 / μ) ^ 2 by positivity)
      convert hh using 1; (try dsimp only [Zg]); ring
    have hq2 := mul_le_mul_of_nonneg_right hq (show 0 ≤ A / 4 by dsimp [A]; positivity)
    have he : θ ^ 2 / (4 * μ) = A / 4 := by dsimp [A]; ring
    rw [he]
    nlinarith [show 0 ≤ Zg by dsimp [Zg]; positivity]

lemma movement_ratio {γ θ : ℝ} {m : ℕ} (hm : 0 < m)
    (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hrt : (m : ℝ) * γ * θ ≤ 1) :
    (1 + 6 / (m : ℝ)) / (4 / (4 + γ * θ)) ≤ 1 + 8 / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgt : γ * θ ≤ 1 := by nlinarith [mul_nonneg hγ hθ]
  have hden : 0 < 4 + γ * θ := by positivity
  apply (div_le_iff₀ (show 0 < 4 / (4 + γ * θ) by positivity)).mpr
  have he : (1 + 8 / (m : ℝ)) * (4 / (4 + γ * θ)) =
      ((1 + 8 / (m : ℝ)) * 4) / (4 + γ * θ) := by ring
  rw [he]
  apply (le_div_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ hmR).mp
  field_simp
  nlinarith

lemma theta_bounds (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hγ : 0 < p.γ) (hδ : 0 ≤ p.δ) :
    0 < theta p ∧ theta p ≤ 1 / 256 ∧ 2 * theta p ^ 2 * p.L ≤ p.μ ∧
      (p.n : ℝ) * p.γ * theta p ≤ 1 ∧
      16777216 * (p.n : ℝ) ^ 2 * p.δ ^ 2 * theta p ^ 3 ≤ p.γ * p.μ ^ 2 := by
  let a := Real.sqrt (p.L / p.μ)
  let b := p.γ * p.n
  let d := (p.n * p.δ / (Real.sqrt p.γ * p.μ)) ^ (2 / 3 : ℝ)
  have hκ : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have ha : 1 ≤ a := by simpa [a] using Real.sqrt_le_sqrt hκ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hZ : 0 < a + b + d := by linarith
  have ht : theta p = 1 / (256 * (a + b + d)) := rfl
  have htpos : 0 < theta p := by rw [ht]; positivity
  have hprod : theta p * (a + b + d) = 1 / 256 := by rw [ht]; field_simp
  have hta : theta p * a ≤ 1 / 256 := by nlinarith [mul_nonneg htpos.le hb, mul_nonneg htpos.le hd]
  have htb : theta p * b ≤ 1 / 256 := by nlinarith [mul_nonneg htpos.le (show 0 ≤ a by linarith), mul_nonneg htpos.le hd]
  have htd : theta p * d ≤ 1 / 256 := by nlinarith [mul_nonneg htpos.le hb, mul_nonneg htpos.le (show 0 ≤ a by linarith)]
  have ht1 : theta p ≤ 1 / 256 := by nlinarith
  have ha2 : a ^ 2 = p.L / p.μ := Real.sq_sqrt (by linarith)
  have hs : theta p ^ 2 * (p.L / p.μ) ≤ 1 / 4 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ theta p * a by positivity)
      (show theta p * a ≤ 1 / 2 by linarith) 2
    nlinarith
  have hstep : 2 * theta p ^ 2 * p.L ≤ p.μ := by
    have hh := mul_le_mul_of_nonneg_right hs hμ.le
    field_simp at hh
    nlinarith
  have hdcube : d ^ 3 = (p.n : ℝ) ^ 2 * p.δ ^ 2 / (p.γ * p.μ ^ 2) := by
    have hx : 0 ≤ p.n * p.δ / (Real.sqrt p.γ * p.μ) := by positivity
    dsimp [d]
    rw [← Real.rpow_mul_natCast hx]
    norm_num
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hγ.le]
  have hcube : theta p ^ 3 * d ^ 3 ≤ 1 / 16777216 := by
    have hh := pow_le_pow_left₀ (mul_nonneg htpos.le hd) htd 3
    norm_num at hh
    simpa only [mul_pow] using hh
  refine ⟨htpos, ht1, hstep, ?_, ?_⟩
  · dsimp [b] at htb
    nlinarith
  · rw [hdcube] at hcube
    have hh := mul_le_mul_of_nonneg_right hcube (show 0 ≤ p.γ * p.μ ^ 2 by positivity)
    field_simp at hh
    nlinarith

lemma noise_prerequisite {m γ μ θ δ : ℝ} (hm : 1 ≤ m) (hμ : 0 < μ)
    (hθ : 0 ≤ θ) (hgt : γ * θ ≤ 1)
    (hsmall : 16777216 * m ^ 2 * δ ^ 2 * θ ^ 3 ≤ γ * μ ^ 2) :
    (θ ^ 2 / μ) ^ 2 * δ ^ 2 ≤ 1 / m := by
  have hm0 : 0 < m := by linarith
  have hh := mul_le_mul_of_nonneg_right hsmall hθ
  have hg := mul_le_mul_of_nonneg_right hgt (sq_nonneg μ)
  have hc : m ≤ 16777216 * m ^ 2 := by nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ δ ^ 2 * θ ^ 4 by positivity)
  apply (le_div_iff₀ hm0).mpr
  have he : (θ ^ 2 / μ) ^ 2 * δ ^ 2 * m = (m * δ ^ 2 * θ ^ 4) / μ ^ 2 := by ring
  rw [he]
  apply (div_le_one (sq_pos_of_pos hμ)).mpr
  nlinarith

lemma logarithmic_accuracy {c A ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hA : 0 ≤ A) (hε : 0 < ε) (N : ℕ)
    (hN : 5 * Real.log (1 + A / ε) ≤ (N : ℝ) * c) :
    (4 / (4 + c)) ^ N * A ≤ ε := by
  have hq0 : 0 ≤ 4 / (4 + c) := by positivity
  have hq : 4 / (4 + c) ≤ Real.exp (-c / 5) := by
    calc
      _ ≤ 1 - c / 5 := by
        apply (div_le_iff₀ (show 0 < 4 + c by positivity)).mpr
        nlinarith
      _ ≤ Real.exp (-c / 5) := by linarith [Real.add_one_le_exp (-c / 5)]
  have hp : (4 / (4 + c)) ^ N ≤ (1 + A / ε)⁻¹ := by
    calc
      _ ≤ (Real.exp (-c / 5)) ^ N := pow_le_pow_left₀ hq0 hq N
      _ = Real.exp ((N : ℝ) * (-c / 5)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-Real.log (1 + A / ε)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (1 + A / ε)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
  calc
    _ ≤ (1 + A / ε)⁻¹ * A := mul_le_mul_of_nonneg_right hp hA
    _ ≤ ε := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ (show 0 < 1 + A / ε by positivity)).mpr
      have he : ε * (1 + A / ε) = ε + A := by field_simp
      rw [he]
      linarith

lemma epochs_accuracy (p : Params) (hp : spec.valid p) :
    (4 / (4 + p.γ * theta p)) ^ (p.n * epochs p) * (2 * p.Δ / p.γ) ≤ p.ε := by
  obtain ⟨hμ, hμL, hγ, hγ1, hδ, hΔ, hε⟩ := hp
  obtain ⟨hθ, hθ1, hstep, hrt, hsmall⟩ := theta_bounds p hμ hμL hγ hδ
  have hc : 0 < p.γ * theta p := mul_pos hγ hθ
  have hc1 : p.γ * theta p ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hγ1 hθ.le
    nlinarith
  apply logarithmic_accuracy hc hc1 (by positivity) hε
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast NeZero.pos p.n
  have hs : 5 * Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) /
      (p.γ * theta p * p.n) ≤ (epochs p : ℝ) := by
    have he : 5 * Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) /
        (p.γ * theta p * p.n) =
        1280 * (Real.sqrt (p.L / p.μ) + p.γ * p.n +
          (p.n * p.δ / (Real.sqrt p.γ * p.μ)) ^ (2 / 3 : ℝ)) *
          Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) / (p.γ * p.n) := by
      unfold theta
      field_simp; ring
    rw [he]
    exact Nat.le_ceil _
  have hh := (div_le_iff₀ (mul_pos hc hn)).mp hs
  have he : (2 * p.Δ / p.γ) / p.ε = 2 * p.Δ / (p.γ * p.ε) := by ring
  rw [he]
  simp only [Nat.cast_mul]
  nlinarith

lemma similarity_term_simplify (p : Params) (hμ : 0 < p.μ) (hγ : 0 < p.γ) (hδ : 0 ≤ p.δ) :
    (p.n * p.δ / (Real.sqrt p.γ * p.μ)) ^ (2 / 3 : ℝ) / p.γ =
      (p.n * p.δ / p.μ) ^ (2 / 3 : ℝ) / p.γ ^ (4 / 3 : ℝ) := by
  have he : (p.n : ℝ) * p.δ / (Real.sqrt p.γ * p.μ) =
      (p.n * p.δ / p.μ) / Real.sqrt p.γ := by ring
  rw [he, Real.div_rpow (by positivity) (Real.sqrt_nonneg _) _, div_div,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hγ.le]
  have hh : p.γ ^ ((1 / 2 : ℝ) * (2 / 3)) * p.γ = p.γ ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_add_one hγ.ne']
    norm_num
  rw [hh]

lemma epochs_calls_le (p : Params) (hp : spec.valid p) :
    (p.n + p.n) * epochs p ≤ 2 * p.n +
      ⌈2560 * (p.n + Real.sqrt (p.L / p.μ) / p.γ +
        (p.n * p.δ / p.μ) ^ (2 / 3 : ℝ) / p.γ ^ (4 / 3 : ℝ)) *
        Real.log (1 + 2 * p.Δ / (p.γ * p.ε))⌉₊ := by
  obtain ⟨hμ, hμL, hγ, hγ1, hδ, hΔ, hε⟩ := hp
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast NeZero.pos p.n
  let t := 1280 * (Real.sqrt (p.L / p.μ) + p.γ * p.n +
    (p.n * p.δ / (Real.sqrt p.γ * p.μ)) ^ (2 / 3 : ℝ)) *
    Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) / (p.γ * p.n)
  have ht : 0 ≤ t := by
    have hl : 0 ≤ Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    dsimp [t]
    positivity
  have hround : (epochs p : ℝ) ≤ t + 1 := by
    exact (Nat.ceil_lt_add_one ht).le
  have he : 2 * p.n * t = 2560 * (p.n + Real.sqrt (p.L / p.μ) / p.γ +
      (p.n * p.δ / p.μ) ^ (2 / 3 : ℝ) / p.γ ^ (4 / 3 : ℝ)) *
      Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) := by
    rw [← similarity_term_simplify p hμ hγ hδ]
    dsimp [t]
    field_simp
    ring
  have hceil := Nat.le_ceil (2560 * (p.n + Real.sqrt (p.L / p.μ) / p.γ +
      (p.n * p.δ / p.μ) ^ (2 / 3 : ℝ) / p.γ ^ (4 / 3 : ℝ)) *
      Real.log (1 + 2 * p.Δ / (p.γ * p.ε)))
  have hb := mul_le_mul_of_nonneg_left hround (show 0 ≤ 2 * (p.n : ℝ) by positivity)
  rw [mul_add, he] at hb
  apply (Nat.cast_le (α := ℝ)).mp
  push_cast
  nlinarith [hceil]

end OracleTemplate.ContinuizedSimilarQuasar.Movement
