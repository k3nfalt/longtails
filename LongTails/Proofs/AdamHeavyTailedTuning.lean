import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.AdamHeavyTailedTuning

lemma noise_scale_of_power_bound {z ρ p : ℝ} (hz : 0 ≤ z) (hρ : 0 < ρ) (hp : 1 < p)
    (hbound : ρ * z ^ (p / (p - 1)) ≤ 1) : (z * ρ) ^ p ≤ ρ := by
  have hp0 : 0 < p - 1 := by linarith
  have he : p / (p - 1) * (p - 1) = p := by field_simp
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ ρ * z ^ (p / (p - 1))) hbound hp0.le
  rw [Real.one_rpow, Real.mul_rpow hρ.le (Real.rpow_nonneg hz _), ← Real.rpow_mul hz, he] at hh
  have hρp : ρ ^ p = ρ * ρ ^ (p - 1) := by
    calc
      ρ ^ p = ρ ^ (1 + (p - 1)) := by congr 1; ring
      _ = ρ * ρ ^ (p - 1) := by rw [Real.rpow_add hρ, Real.rpow_one]
  rw [Real.mul_rpow hz hρ.le, hρp]
  nlinarith [mul_le_mul_of_nonneg_left hh hρ.le]

lemma tuning_parameters {σ ε p : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) :
    let ρ := 1 / (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))
    let τ := ε / (100000 * Real.sqrt ρ)
    0 < ρ ∧ ρ ≤ 1 / 1000000000000 ∧ ε ≤ τ ∧ σ ^ p * (Real.sqrt ρ / τ) ^ p ≤ ρ := by
  dsimp only
  let z := 100000 * σ / ε
  let ρ := 1 / (1000000000000 + z ^ (p / (p - 1)))
  let τ := ε / (100000 * Real.sqrt ρ)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzpow : 0 ≤ z ^ (p / (p - 1)) := Real.rpow_nonneg hz _
  have hden : 0 < 1000000000000 + z ^ (p / (p - 1)) := by positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρle : ρ ≤ 1 / 1000000000000 := by
    dsimp [ρ]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hsqrt : Real.sqrt ρ ≤ 1 / 1000000 := by
    have hs := Real.sq_sqrt hρ.le
    have hn := Real.sqrt_nonneg ρ
    nlinarith
  have hd : 0 < 100000 * Real.sqrt ρ := by positivity
  have hτ : 0 < τ := div_pos hε hd
  have hτε : ε ≤ τ := by
    apply (le_div_iff₀ hd).2
    have hh := mul_le_mul_of_nonneg_left hsqrt hε.le
    nlinarith
  have hb : ρ * z ^ (p / (p - 1)) ≤ 1 := by
    change (1 / (1000000000000 + z ^ (p / (p - 1)))) * z ^ (p / (p - 1)) ≤ 1
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).2
    linarith
  have hn := noise_scale_of_power_bound hz hρ hp hb
  have he : σ * (Real.sqrt ρ / τ) = z * ρ := by
    dsimp [τ, z]
    field_simp
    nlinarith [Real.sq_sqrt hρ.le]
  have hnoise : σ ^ p * (Real.sqrt ρ / τ) ^ p ≤ ρ := by
    rw [← Real.mul_rpow hσ (by positivity), he]
    exact hn
  exact ⟨hρ, hρle, hτε, hnoise⟩

lemma budget_signal_small {Δ L ε ρ S : ℝ} {K : ℕ}
    (hL : 0 < L) (hε : 0 < ε) (hρ : 0 < ρ) (hK : 0 < K)
    (hbudget : 400000000 * Δ * L / (ε ^ 2 * ρ) ≤ (K : ℝ))
    (hS : S ≤ 20 * Δ / ((ε / (100000 * Real.sqrt ρ) * ρ / (100000 * L)) * K) +
      4000000 * (ε / (100000 * Real.sqrt ρ)) * ρ) :
    (ε / (100000 * Real.sqrt ρ)) * S ≤ ε ^ 2 / 100 := by
  let τ := ε / (100000 * Real.sqrt ρ)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hsqrt : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hτeq : τ ^ 2 * ρ = ε ^ 2 / 10000000000 := by
    dsimp [τ]
    field_simp
    nlinarith
  have hcost : 400000000 * Δ * L ≤ (K : ℝ) * (ε ^ 2 * ρ) :=
    (div_le_iff₀ (mul_pos (sq_pos_of_pos hε) hρ)).mp hbudget
  have hfirst : τ * (20 * Δ / ((τ * ρ / (100000 * L)) * K)) ≤ ε ^ 2 / 200 := by
    have he : τ * (20 * Δ / ((τ * ρ / (100000 * L)) * K)) = 2000000 * Δ * L / (ρ * K) := by
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (mul_pos hρ hKr)).2
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hS hτ.le
  change τ * S ≤ _
  change τ * S ≤ τ * (20 * Δ / ((τ * ρ / (100000 * L)) * K) + 4000000 * τ * ρ) at hh
  nlinarith


lemma fixed_momentum_stability {ρ : ℝ} (hρsmall : ρ ≤ 1 / 1000000000000) :
    (9 / 10 : ℝ) / Real.sqrt (1 - ρ) < 1 ∧
    ((1 - (9 / 10 : ℝ)) / (1 - (9 / 10 : ℝ) / Real.sqrt (1 - ρ))) ^ 2 ≤ 4 := by
  have hb : 0 < 1 - ρ := by linarith
  have hs : 99 / 100 ≤ Real.sqrt (1 - ρ) := by
    have hsq := Real.sq_sqrt hb.le
    have hn := Real.sqrt_nonneg (1 - ρ)
    nlinarith
  have ha : (9 / 10 : ℝ) / Real.sqrt (1 - ρ) ≤ 19 / 20 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hb)).2
    linarith
  have ha1 : (9 / 10 : ℝ) / Real.sqrt (1 - ρ) < 1 := by linarith
  refine ⟨ha1, ?_⟩
  have hgap : 0 < 1 - (9 / 10 : ℝ) / Real.sqrt (1 - ρ) := by linarith
  have hc : (1 - (9 / 10 : ℝ)) / (1 - (9 / 10 : ℝ) / Real.sqrt (1 - ρ)) ≤ 2 := by
    apply (div_le_iff₀ hgap).2
    linarith
  nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 9 / 10) hgap.le]


lemma iteration_budget_bound {Δ L σ ε p : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) :
    let ρ := 1 / (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))
    let K := 1 + ⌈400000000 * Δ * L / ε ^ 2 * (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)))⌉₊
    0 < K ∧ 400000000 * Δ * L / (ε ^ 2 * ρ) ≤ (K : ℝ) := by
  dsimp only
  have hpow : 0 ≤ (100000 * σ / ε) ^ (p / (p - 1)) := Real.rpow_nonneg (by positivity) _
  have hden : 0 < 1000000000000 + (100000 * σ / ε) ^ (p / (p - 1)) := by positivity
  have he : 400000000 * Δ * L / (ε ^ 2 * (1 / (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1))))) =
      400000000 * Δ * L / ε ^ 2 * (1000000000000 + (100000 * σ / ε) ^ (p / (p - 1))) := by
    field_simp
  refine ⟨by omega, ?_⟩
  rw [he]
  exact (Nat.le_ceil _).trans (by norm_cast; omega)


lemma descent_signal_absorption {S A τ ρ : ℝ}
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hρsmall : ρ ≤ 1 / 1000000000000)
    (hdescent : (3 / 40 - 200 * ρ) * S ≤
      A + 200000 * τ * ρ + (τ * ρ / 10) * (S / τ + 1)) :
    S ≤ 20 * A + 4000000 * τ * ρ := by
  have he : (τ * ρ / 10) * (S / τ + 1) = (ρ / 10) * S + τ * ρ / 10 := by
    field_simp
  rw [he] at hdescent
  have hs := mul_le_mul_of_nonneg_right hρsmall hS
  nlinarith [mul_pos hτ hρ]

lemma history_transport_absorption {A S U τ : ℝ}
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hτ : 0 < τ)
    (hU : U ≤ 32 * (S / τ + 1))
    (htransport : A ^ 2 ≤ 2 * (τ / 100000) ^ 2 * U) :
    A ≤ τ + Real.sqrt (τ * S) := by
  have hu := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 2 * (τ / 100000) ^ 2)
  have he : 2 * (τ / 100000) ^ 2 * (32 * (S / τ + 1)) =
      (64 / 10000000000 : ℝ) * (τ * S + τ ^ 2) := by field_simp; ring
  rw [he] at hu
  have hs := Real.sq_sqrt (mul_nonneg hτ.le hS)
  have hn := Real.sqrt_nonneg (τ * S)
  nlinarith [mul_nonneg hτ.le hn, mul_nonneg hτ.le hS, sq_nonneg τ]

lemma normalized_history_bound {G S A U τ T : ℝ}
    (hT : 0 < T) (hS : 0 ≤ S) (hA : 0 ≤ A) (hτ : 0 < τ)
    (hU : U ≤ 32 * (S / τ + T))
    (hvariation : A ^ 2 ≤ 2 * (τ / 100000) ^ 2 * T * U)
    (hgradient : G ^ 2 ≤ S * (3 * τ * T + G + A)) :
    (G / T) ^ 2 ≤ (S / T) *
      (4 * τ + G / T + Real.sqrt (τ * (S / T))) := by
  have hu : U / T ≤ 32 * ((S / T) / τ + 1) := by
    apply (div_le_iff₀ hT).2
    calc
      U ≤ 32 * (S / τ + T) := hU
      _ = (32 * ((S / T) / τ + 1)) * T := by field_simp
  have hv : (A / T) ^ 2 ≤ 2 * (τ / 100000) ^ 2 * (U / T) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hT)).2
    calc
      A ^ 2 ≤ 2 * (τ / 100000) ^ 2 * T * U := hvariation
      _ = (2 * (τ / 100000) ^ 2 * (U / T)) * T ^ 2 := by field_simp
  have ha := history_transport_absorption (div_nonneg hA hT.le)
    (div_nonneg hS hT.le) hτ hu hv
  have hg : (G / T) ^ 2 ≤ (S / T) * (3 * τ + G / T + A / T) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hT)).2
    calc
      G ^ 2 ≤ S * (3 * τ * T + G + A) := hgradient
      _ = ((S / T) * (3 * τ + G / T + A / T)) * T ^ 2 := by field_simp
  exact hg.trans (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hS hT.le))

lemma descent_energy_combine {S T U J Δ L η τ ρ : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hL : 0 ≤ L) (hη : 0 < η) (hτ : 0 < τ)
    (hU : U ≤ 32 * (S / τ + T))
    (hJ : (3 / 40 - 200 * ρ) * S - 200000 * τ * ρ * T -
      9800 * (L * η) * (S / τ + T) ≤ J)
    (hdescent : η * J ≤ Δ + L * η ^ 2 / 2 * U) :
    (3 / 40 - 200 * ρ) * S ≤ Δ / η + 200000 * τ * ρ * T +
      10000 * (L * η) * (S / τ + T) := by
  have hU' := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ L * η ^ 2 / 2)
  have hJ' := mul_le_mul_of_nonneg_left hJ hη.le
  have hW : 0 ≤ S / τ + T := by positivity
  have hpos : 0 ≤ L * η ^ 2 * (S / τ + T) := by positivity
  have he : Δ / η * η = Δ := div_mul_cancel₀ Δ hη.ne'
  nlinarith

lemma normalized_signal_bound {S T Δ L τ ρ : ℝ}
    (hS : 0 ≤ S) (hT : 0 < T) (hΔ : 0 ≤ Δ) (hL : 0 < L) (hτ : 0 < τ)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1000000000000)
    (hdescent : (3 / 40 - 200 * ρ) * S ≤
      Δ / (τ * ρ / (100000 * L)) + 200000 * τ * ρ * T +
        10000 * (L * (τ * ρ / (100000 * L))) * (S / τ + T)) :
    S / T ≤ 20 * Δ / ((τ * ρ / (100000 * L)) * T) + 4000000 * τ * ρ := by
  have hA : 0 ≤ Δ / ((τ * ρ / (100000 * L)) * T) := by positivity
  have hh := div_le_div_of_nonneg_right hdescent hT.le
  have he : (Δ / (τ * ρ / (100000 * L)) + 200000 * τ * ρ * T +
      10000 * (L * (τ * ρ / (100000 * L))) * (S / τ + T)) / T =
      Δ / ((τ * ρ / (100000 * L)) * T) + 200000 * τ * ρ +
        (τ * ρ / 10) * ((S / T) / τ + 1) := by field_simp; ring
  rw [he] at hh
  have hh' : (3 / 40 - 200 * ρ) * (S / T) ≤
      Δ / ((τ * ρ / (100000 * L)) * T) + 200000 * τ * ρ +
        (τ * ρ / 10) * ((S / T) / τ + 1) := by
    convert hh using 1
    ring
  have hb := descent_signal_absorption (div_nonneg hS hT.le) hA hτ hρ hρsmall hh'
  convert hb using 1
  ring

end LongTails.Proofs.AdamHeavyTailedTuning
