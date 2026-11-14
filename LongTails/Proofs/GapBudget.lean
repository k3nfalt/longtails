import LongTails.Proofs.GapTransientParameters

namespace LongTails.Proofs.GapBudget

lemma valid_nonempty : ∃ p : LongTails.Setups.GapGeneralizedSmoothConvex.Params,
    LongTails.Setups.GapGeneralizedSmoothConvex.spec.valid p := by
  let d := ⌈1208925819614629174706176 * (1 + Real.sqrt (16 : ℝ)) ^ 10⌉₊
  refine ⟨{ d := d, L0 := 16, L1 := 0, x0 := 0, R := 1, Δ := 16, ε := 1 }, ?_⟩
  norm_num [LongTails.Setups.GapGeneralizedSmoothConvex.spec, d]

lemma rpow_length (M X : ℝ) (hM : 0 < M) (hX : 0 ≤ X)
    (h : 1024 * M ≤ X ^ (2 / 3 : ℝ)) : 32768 * M * Real.sqrt M ≤ X := by
  have hh := Real.rpow_le_rpow (show 0 ≤ 1024 * M by positivity) h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [← Real.rpow_mul hX, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hh
  have he : (1024 * M) ^ (3 / 2 : ℝ) = 32768 * M * Real.sqrt M := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    norm_num
    ring
  rwa [he] at hh

lemma cases (s q h w : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hh : 0 < h) (hw : 1 ≤ w)
    (N : ℕ)
    (hN : N ≤ ⌊(s + min (q / w) ((q * h / w) ^ (2 / 3 : ℝ))) / 16777216⌋₊) :
    N = 0 ∨ 65536 * (N + 1 : ℕ) ≤ s ∨
      (N + 1 : ℕ) ≤ q ∧ 16384 * (N + 1 : ℕ) * w ≤ q ∧
        32768 * (N + 1 : ℕ) * Real.sqrt (N + 1 : ℕ) * w ≤ q * h := by
  by_cases hz : N = 0
  · exact Or.inl hz
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
  have hw0 : 0 < w := by linarith
  let M : ℝ := (N + 1 : ℕ)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMN : M ≤ 2 * (N : ℝ) := by dsimp [M]; push_cast; linarith
  let T := min (q / w) ((q * h / w) ^ (2 / 3 : ℝ))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hreal : (N : ℝ) ≤ (s + T) / 16777216 :=
    (Nat.cast_le.mpr hN).trans (Nat.floor_le (by positivity))
  have hsum := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16777216)).mp hreal
  by_cases hsm : 65536 * M ≤ s
  · exact Or.inr (Or.inl hsm)
  have hbig : 32768 * M ≤ T := by nlinarith only [hsum, hMN, lt_of_not_ge hsm]
  have hlin : 16384 * M * w ≤ q := by
    have hh' : 16384 * M ≤ q / w := by
      have ht := min_le_left (q / w) ((q * h / w) ^ (2 / 3 : ℝ))
      change T ≤ q / w at ht
      nlinarith only [hbig, ht, hM]
    exact (le_div_iff₀ hw0).mp hh'
  have hpow : 1024 * M ≤ (q * h / w) ^ (2 / 3 : ℝ) := by
    have ht := min_le_right (q / w) ((q * h / w) ^ (2 / 3 : ℝ))
    change T ≤ (q * h / w) ^ (2 / 3 : ℝ) at ht
    nlinarith only [hbig, ht, hM]
  have hgap := (le_div_iff₀ hw0).mp (rpow_length M (q * h / w) hM (by positivity) hpow)
  have hmq : M ≤ q := by
    have hh' := mul_le_mul_of_nonneg_left hw hM.le
    nlinarith only [hh', hlin, hM]
  exact Or.inr (Or.inr ⟨hmq, hlin, hgap⟩)

end LongTails.Proofs.GapBudget
