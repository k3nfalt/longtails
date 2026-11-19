import LongTails.Setups.MarkovSmoothNonconvex
import LongTails.Proofs.AbcLowerAssembly

namespace LongTails.Proofs.MarkovParityParameters

open LongTails.Setups.MarkovSmoothNonconvex AbcLowerParameters

noncomputable def geometry (p : Params) : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params :=
  ⟨p.d, p.L, 0, 0, p.τ * p.σ ^ 2 - p.ε ^ 2, p.Δ, p.ε, p.x0⟩

noncomputable def chance (p : Params) : ℝ := 2 ^ 22 * p.ε ^ 2 / p.σ ^ 2

noncomputable def limit (p : Params) : ℕ := ⌊p.τ * p.L * p.Δ * p.σ ^ 2 / (2 ^ 56 * p.ε ^ 4)⌋₊

variable (p : Params) (hv : spec.valid p)
include hv

lemma geometry_valid : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.valid (geometry p) := by
  obtain ⟨hL, hε, hτ, hσ, hreg, hd⟩ := hv
  have hs : p.ε ≤ p.σ := by linarith
  have hs' := mul_le_mul_of_nonneg_right hτ (sq_nonneg p.σ)
  have hc := pow_le_pow_left₀ hε.le hs 2
  refine ⟨hL, le_rfl, le_rfl, by dsimp [geometry]; nlinarith, hε, hreg, ?_⟩
  dsimp [geometry]
  convert hd using 2
  field_simp
  ring

lemma chance_pos : 0 < chance p := by
  obtain ⟨_, hε, _, hσ, _⟩ := hv
  have hs : 0 < p.σ := by linarith
  unfold chance
  positivity

lemma chance_small : 2 * chance p ≤ 1 := by
  obtain ⟨_, hε, _, hσ, _⟩ := hv
  have hs : 0 < p.σ := by linarith
  have hsq := pow_le_pow_left₀ (by positivity) hσ 2
  unfold chance
  rw [← mul_div_assoc, div_le_one (by positivity)]
  nlinarith [sq_nonneg p.ε]

lemma limit_le_geometry : limit p ≤ lowerBudget (geometry p) := by
  obtain ⟨hL, hε, hτ, hσ, hreg, _⟩ := hv
  have hΔ : 0 ≤ p.Δ := by nlinarith [sq_nonneg p.ε]
  have ht : 0 ≤ p.τ := by linarith
  unfold limit lowerBudget
  apply Nat.floor_mono
  dsimp [geometry]
  field_simp
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht hL.le) hΔ) (sq_nonneg p.σ)]

lemma entry_budget (N : ℕ) (hN : N ≤ limit p) :
    1 + (N : ℝ) * (2 * (1 / p.τ) * chance p) ≤ (chainLength (geometry p) : ℝ) / 4 := by
  obtain ⟨hL, hε, hτ, hσ, hreg, hd⟩ := hv
  have hv' : spec.valid p := ⟨hL, hε, hτ, hσ, hreg, hd⟩
  have hs : 0 < p.σ := by linarith
  have ht : 0 < p.τ := by linarith
  have hΔ : 0 ≤ p.Δ := by nlinarith [sq_nonneg p.ε]
  have hB : (N : ℝ) ≤ p.τ * p.L * p.Δ * p.σ ^ 2 / (2 ^ 56 * p.ε ^ 4) :=
    (Nat.cast_le.mpr hN).trans (Nat.floor_le (by positivity))
  have hcnt := mul_le_mul_of_nonneg_right hB (show 0 ≤ 2 * (1 / p.τ) * chance p by
    have := chance_pos p hv'; positivity)
  have he : p.τ * p.L * p.Δ * p.σ ^ 2 / (2 ^ 56 * p.ε ^ 4) * (2 * (1 / p.τ) * chance p)
      = p.L * p.Δ / (2 ^ 33 * p.ε ^ 2) := by
    unfold chance
    field_simp
  rw [he] at hcnt
  have hlow := chainLength_lower (geometry p) (geometry_valid p hv')
  change p.L * p.Δ / (22118400 * p.ε ^ 2) ≤ _ at hlow
  have hlen := chainLength_ge (geometry p) (geometry_valid p hv')
  have hlen' : (6 : ℝ) ≤ chainLength (geometry p) := by exact_mod_cast hlen
  have haux : p.L * p.Δ / (2 ^ 33 * p.ε ^ 2) ≤ (chainLength (geometry p) : ℝ) / 16 := by
    refine le_trans ?_ (div_le_div_of_nonneg_right hlow (by norm_num : (0 : ℝ) ≤ 16))
    field_simp
    nlinarith [mul_nonneg hL.le hΔ]
  linarith

end LongTails.Proofs.MarkovParityParameters
