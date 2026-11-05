import LongTails.Proofs.FiniteSumNondualOuterGeometry
import LongTails.Proofs.KnownValueNondualCounting

open Finset
open scoped BigOperators

namespace LongTails.Proofs.FiniteSumNondualPhaseGeometry

lemma descent_energy (T : ℕ) (value distance : ℕ → ℝ) {μ δ η : ℝ}
    (hstep : ∀ t < T, value (t + 1) ≤ value t + 3 * η / 2 - μ / 2 * distance t ^ 2)
    (hgap : value 0 - value T ≤ 2 * δ) :
    μ * (∑ t ∈ range T, distance t ^ 2) ≤ 4 * δ + 3 * η * T := by
  have hh := sum_le_sum (s := range T) (fun t ht => show
    μ / 2 * distance t ^ 2 ≤ value t - value (t + 1) + 3 * η / 2 by
      have h := hstep t (mem_range.mp ht)
      linarith)
  rw [← mul_sum, sum_add_distrib, sum_range_sub', sum_const, card_range, nsmul_eq_mul] at hh
  linarith

lemma phase_energy {m : ℕ} (hm : 0 < m) (value distance : ℕ → ℝ) {μ δ : ℝ}
    (hstep : ∀ t < 10 * m, value (t + 1) ≤ value t + 3 * (δ / (16 * m)) / 2 - μ / 2 * distance t ^ 2)
    (hgap : value 0 - value (10 * m) ≤ 2 * δ) (hδ : 0 ≤ δ) :
    μ * (∑ t ∈ range (10 * m), distance t ^ 2) ≤ 6 * δ := by
  have hh := descent_energy (10 * m) value distance hstep hgap
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : 4 * δ + 3 * (δ / (16 * m)) * (10 * m : ℕ) = 47 * δ / 8 := by
    push_cast
    field_simp
    ring
  rw [he] at hh
  linarith

lemma phase_count (T : ℕ) (distance movement : ℕ → ℝ) {μ δ B : ℝ}
    (hμ : 0 < μ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hmovement : ∀ t < T, 0 ≤ movement t)
    (hproduct : ∀ t < T, δ / 2 ≤ (μ * distance t) * movement t)
    (henergy : μ * (∑ t ∈ range T, distance t ^ 2) ≤ 6 * δ)
    (htotal : (∑ t ∈ range T, movement t) ≤ B) :
    (T : ℝ) ^ 3 * δ ≤ 24 * μ * B ^ 2 := by
  have he : (∑ t ∈ range T, (μ * distance t) ^ 2 / (δ / 2) ^ 2) ≤ 24 * μ / δ := by
    calc
      _ = (4 * μ / δ ^ 2) * (μ * ∑ t ∈ range T, distance t ^ 2) := by
        rw [← mul_assoc, mul_sum]
        apply sum_congr rfl
        intro t _
        field_simp
        ring
      _ ≤ (4 * μ / δ ^ 2) * (6 * δ) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = 24 * μ / δ := by field_simp; ring
  have hh := KnownValueNondualCounting.weighted_low_count (range T)
    (fun t => μ * distance t) movement (fun _ => δ / 2)
    (fun _ _ => by positivity) (fun t ht => hmovement t (mem_range.mp ht))
    (fun t ht => hproduct t (mem_range.mp ht)) he
  rw [card_range] at hh
  have hs := (sq_le_sq₀ (sum_nonneg (fun t ht => hmovement t (mem_range.mp ht))) hB).mpr htotal
  have hb := hh.trans (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 24 * μ / δ))
  have heq : 24 * μ / δ * B ^ 2 = (24 * μ * B ^ 2) / δ := by ring
  rw [heq] at hb
  exact (le_div_iff₀ hδ).mp hb

lemma phase_impossible {m : ℕ} (hm : 0 < m) (distance movement : ℕ → ℝ)
    {μ δ R kd kt : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (hR : 0 ≤ R) (hkd : 0 ≤ kd) (hkt : 0 ≤ kt)
    (hmovement : ∀ t < 10 * m, 0 ≤ movement t)
    (hproduct : ∀ t < 10 * m, δ / 2 ≤ (μ * distance t) * movement t)
    (henergy : μ * (∑ t ∈ range (10 * m), distance t ^ 2) ≤ 6 * δ)
    (htotal : (∑ t ∈ range (10 * m), movement t) ≤ 12 * R * Real.sqrt (kd * kt))
    (hbudget : 256 * μ * R ^ 2 * kd * kt ≤ (m : ℝ) ^ 3 * δ) : False := by
  have hh := phase_count (10 * m) distance movement hμ hδ (by positivity) hmovement hproduct henergy htotal
  have hs := Real.sq_sqrt (mul_nonneg hkd hkt)
  push_cast at hh
  rw [mul_pow, mul_pow, hs] at hh
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith [mul_pos (pow_pos hm' 3) hδ]

end LongTails.Proofs.FiniteSumNondualPhaseGeometry
