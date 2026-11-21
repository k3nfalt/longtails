import LongTails.Setups.HighDimensionalEllSmoothNonconvex

namespace LongTails.Proofs.EllSmoothExamples

open LongTails.Setups.EllSmoothNonconvex

lemma regular_polynomial (L0 Lρ ρ : ℝ) (hL0 : 0 < L0) (hLρ : 0 ≤ Lρ) (hρ : 0 ≤ ρ) :
    Regular (fun u => L0 + Lρ * u ^ ρ) ρ := by
  refine ⟨fun u v hu huv => ?_, fun u v hu huv => ?_, fun u hu => ?_⟩
  · have := Real.rpow_le_rpow hu huv hρ
    nlinarith
  · have h1 := Real.rpow_le_rpow hu.le huv hρ
    have h2 : 0 ≤ u ^ ρ := Real.rpow_nonneg hu.le ρ
    nlinarith
  · have : 0 ≤ u ^ ρ := Real.rpow_nonneg hu.le ρ
    positivity

lemma regular_weaken (ℓ : ℝ → ℝ) (ρ ρ' : ℝ) (h : Regular ℓ ρ) (hρ : ρ ≤ ρ') : Regular ℓ ρ' := by
  refine ⟨h.1, fun u v hu huv => ?_, h.2.2⟩
  have h1 := h.2.1 u v hu huv
  have hv : 0 < v := hu.trans_le huv
  have hq : 1 ≤ v / u := (one_le_div hu).mpr huv
  have h2 : (1 : ℝ) ≤ (v / u) ^ (ρ' - ρ) := Real.one_le_rpow hq (by linarith)
  have eu : u ^ ρ' = u ^ ρ * u ^ (ρ' - ρ) := by
    rw [← Real.rpow_add hu]; congr 1; ring
  have ev : v ^ ρ' = v ^ ρ * v ^ (ρ' - ρ) := by
    rw [← Real.rpow_add hv]; congr 1; ring
  have hd : v ^ (ρ' - ρ) = (v / u) ^ (ρ' - ρ) * u ^ (ρ' - ρ) := by
    rw [← Real.mul_rpow (by positivity) hu.le]; congr 1; field_simp
  have hup : 0 < u ^ (ρ' - ρ) := Real.rpow_pos_of_pos hu _
  have hlu : 0 < ℓ u := h.2.2 u hu
  have hvp : 0 < v ^ ρ := Real.rpow_pos_of_pos hv _
  rw [eu, ev, hd]
  have h3 : ℓ v * u ^ ρ * u ^ (ρ' - ρ) ≤ ℓ u * v ^ ρ * u ^ (ρ' - ρ) :=
    mul_le_mul_of_nonneg_right h1 hup.le
  have h4 : ℓ u * v ^ ρ * u ^ (ρ' - ρ) ≤ ℓ u * v ^ ρ * u ^ (ρ' - ρ) * (v / u) ^ (ρ' - ρ) :=
    le_mul_of_one_le_right (by positivity) h2
  nlinarith

noncomputable def sampleEll : ℝ → ℝ := fun u => 1 + 1 * u ^ (1 : ℝ)

lemma sampleEll_zero : sampleEll 0 = 1 := by
  unfold sampleEll
  rw [Real.zero_rpow one_ne_zero]
  ring

lemma sampleEll_one : sampleEll 1 = 2 := by
  unfold sampleEll
  rw [Real.one_rpow]
  ring

lemma highDimensional_valid_nonempty :
    ∃ p : Params, LongTails.Setups.HighDimensionalEllSmoothNonconvex.spec.valid p := by
  have hfl : ⌊(2 - (1 : ℝ)) * 2 ^ 27 * 2 / (2 ^ 27 * 1 ^ 2)⌋₊ = 2 := by
    rw [show (2 - (1 : ℝ)) * 2 ^ 27 * 2 / (2 ^ 27 * 1 ^ 2) = ((2 : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast 2
  refine ⟨⟨2 ^ 60 * 729, sampleEll, 1, 2 ^ 27, 1, 0⟩,
    ⟨zero_le_one, one_le_two, regular_polynomial 1 1 1 one_pos zero_le_one zero_le_one,
      (by positivity : (0 : ℝ) ≤ 2 ^ 27), one_pos⟩, one_lt_two, ?_, ?_, ?_⟩
  · dsimp only
    rw [sampleEll_zero]
    exact one_pos
  · dsimp only
    rw [sampleEll_one]
    norm_num
  · dsimp only
    rw [sampleEll_one, sampleEll_zero, hfl]
    norm_num

end LongTails.Proofs.EllSmoothExamples
