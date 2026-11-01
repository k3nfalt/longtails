import LongTails.Algorithms.AdaptiveSilverGd
import LongTails.Proofs.SilverCertificate

namespace LongTails.Proofs.AdaptiveSilverParams

open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.SilverSchedule
open LongTails.Algorithms.AdaptiveSilverGd
open LongTails.Proofs.SilverCertificate

lemma level_ge (p : Params) : 2 ≤ level p := le_max_left _ _

open Classical in
lemma levelRaw_spec (p : Params) (h : levelRaw p ≠ 0) :
    256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * levelRaw p) ≤ p.L ^ 4 :=
  Nat.findGreatest_of_ne_zero rfl h

open Classical in
lemma levelRaw_le (p : Params) : levelRaw p ≤ levelCap p := Nat.findGreatest_le _

open Classical in
lemma le_levelRaw (p : Params) {k : ℕ} (hk : k ≤ levelCap p)
    (h : 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * k) ≤ p.L ^ 4) : k ≤ levelRaw p :=
  Nat.le_findGreatest hk h

lemma lc_level (p : Params) (hgood : good p) :
    256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * level p) ≤ p.L ^ 4 := by
  unfold level
  rcases le_or_gt (levelRaw p) 2 with h | h
  · rw [max_eq_left h]; exact hgood
  · rw [max_eq_right h.le]
    exact levelRaw_spec p (by omega)

lemma blockLength_eq (p : Params) : (blockLength p : ℝ) = 2 ^ level p - 1 := by
  unfold blockLength
  have h := steps_length (level p)
  have : ((steps (level p)).length : ℝ) + 1 = 2 ^ level p := by exact_mod_cast h
  linarith

lemma blockSum_eq (p : Params) : blockSum p = ratio ^ level p - 1 := steps_sum _

lemma blockLength_three (p : Params) : (3 : ℝ) ≤ blockLength p := by
  rw [blockLength_eq]
  have : (2 : ℝ) ^ 2 ≤ 2 ^ level p := pow_le_pow_right₀ (by norm_num) (level_ge p)
  linarith

lemma ratio_pow_ge (p : Params) : ratio ^ 2 ≤ ratio ^ level p :=
  pow_le_pow_right₀ (by linarith [ratio_gt_two]) (level_ge p)

lemma blockSum_ge (p : Params) : 4 ≤ blockSum p := by
  rw [blockSum_eq]
  have h := ratio_pow_ge p
  have := ratio_square
  have := ratio_gt_two
  nlinarith

lemma threshold_cases (p : Params) :
    threshold p = p.ε ∨ (good p ∧ threshold p ^ 2 = p.ε ^ 2 * blockSum p / (25 * blockLength p)) := by
  classical
  unfold threshold
  split_ifs with hg
  · rcases le_total 1 (Real.sqrt (blockSum p / (25 * blockLength p))) with h | h
    · right
      refine ⟨hg, ?_⟩
      rw [max_eq_right h, mul_pow, Real.sq_sqrt]
      · ring
      · have := blockSum_ge p; have := blockLength_three p; positivity
    · left; rw [max_eq_left h, mul_one]
  · left; rfl

lemma threshold_ge (p : Params) (hε : 0 < p.ε) : p.ε ≤ threshold p := by
  classical
  unfold threshold
  split_ifs
  · exact le_mul_of_one_le_right hε.le (le_max_left _ _)
  · exact le_rfl

lemma abort_sq (p : Params) :
    abortThreshold p ^ 2 = (4 * blockLength p + 2) * threshold p ^ 2 := by
  unfold abortThreshold
  rw [mul_pow, Real.sq_sqrt (by positivity)]

section Constraints

variable {σ R n ρ ε L G Mg : ℝ}

lemma from_lc (hL : 0 < L) (hlc : 256 * ρ ^ 2 * ε ^ 2 * R ^ 9 ≤ L ^ 4) {X : ℝ} (hX : 0 ≤ X)
    (h : X ^ 2 ≤ 256 * ρ ^ 2 * ε ^ 2 * R ^ 9) : X ≤ L ^ 2 := by
  have h2 : X ^ 2 ≤ (L ^ 2) ^ 2 := by
    have : (L ^ 2) ^ 2 = L ^ 4 := by ring
    rw [this]; exact h.trans hlc
  exact (pow_le_pow_iff_left₀ hX (by positivity) two_ne_zero).mp h2

lemma mg_bound (hn : 3 ≤ n) (hσ : 0 ≤ σ) (hG2 : G ^ 2 = ε ^ 2 * σ / (25 * n))
    (hM2 : Mg ^ 2 = (4 * n + 2) * G ^ 2) : Mg ^ 2 ≤ 14 / 75 * σ * ε ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hfrac : (4 * n + 2) / (25 * n) ≤ 14 / 75 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have e : Mg ^ 2 = (4 * n + 2) / (25 * n) * (σ * ε ^ 2) := by
    rw [hM2, hG2]; field_simp
  rw [e]
  calc (4 * n + 2) / (25 * n) * (σ * ε ^ 2) ≤ 14 / 75 * (σ * ε ^ 2) :=
        mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = 14 / 75 * σ * ε ^ 2 := by ring

lemma pow_chain (hσ : 0 ≤ σ) (hσR : σ ≤ R) (hR : 5 ≤ R) :
    σ ^ 8 ≤ R ^ 9 ∧ σ ^ 9 ≤ R ^ 9 ∧ 25 * σ ^ 7 ≤ R ^ 9 := by
  have hR1 : 1 ≤ R := by linarith
  have h8 : σ ^ 8 ≤ R ^ 8 := pow_le_pow_left₀ hσ hσR 8
  have h9 : σ ^ 9 ≤ R ^ 9 := pow_le_pow_left₀ hσ hσR 9
  have h7 : σ ^ 7 ≤ R ^ 7 := pow_le_pow_left₀ hσ hσR 7
  have hR89 : R ^ 8 ≤ R ^ 9 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR79 : 25 * R ^ 7 ≤ R ^ 9 := by
    have e : R ^ 9 = R ^ 2 * R ^ 7 := by ring
    rw [e]
    have : (25 : ℝ) ≤ R ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  exact ⟨h8.trans hR89, h9, by linarith⟩

lemma constraints (hσ : 1 ≤ σ) (hσR : σ ≤ R) (hR : 5 ≤ R) (hn : 3 ≤ n) (h4 : 25 ≤ 4 * n * σ)
    (hρ : 0 ≤ ρ) (hε : 0 < ε) (hL : 0 < L) (hG : 0 ≤ G) (hMg : 0 ≤ Mg)
    (hlc : 256 * ρ ^ 2 * ε ^ 2 * R ^ 9 ≤ L ^ 4)
    (hG2 : G ^ 2 = ε ^ 2 * σ / (25 * n)) (hM2 : Mg ^ 2 = (4 * n + 2) * G ^ 2) :
    σ * (ρ * (2 * σ * Mg / L) ^ 2 / 2) ≤ ε / 16 ∧
    G ≤ 2 * σ * ε / 25 ∧
    ρ * (2 * σ * Mg / L) ^ 3 / 6 ≤ σ * ε ^ 2 / (100 * L) ∧
    16 * σ ^ 2 * (ρ * (2 * σ * Mg / L) ^ 2 / 2) ≤ Mg ∧
    2 * G ≤ Mg ∧
    ρ * (2 * σ * Mg / L) ^ 3 / 6 ≤ Mg ^ 2 / (32 * L) := by
  have hσ0 : 0 ≤ σ := by linarith
  have hMb := mg_bound hn hσ0 hG2 hM2
  obtain ⟨hp8, hp9, hp7⟩ := pow_chain hσ0 hσR hR
  have hρε : 0 ≤ ρ ^ 2 * ε ^ 2 := by positivity
  have k1 : 16 * ρ * ε * σ ^ 4 ≤ L ^ 2 := by
    apply from_lc hL hlc (by positivity)
    calc (16 * ρ * ε * σ ^ 4) ^ 2 = 256 * (ρ ^ 2 * ε ^ 2) * σ ^ 8 := by ring
      _ ≤ 256 * (ρ ^ 2 * ε ^ 2) * R ^ 9 := mul_le_mul_of_nonneg_left hp8 (by positivity)
      _ = 256 * ρ ^ 2 * ε ^ 2 * R ^ 9 := by ring
  have k2 : 32 * ρ * σ ^ 4 * Mg ≤ L ^ 2 := by
    apply from_lc hL hlc (by positivity)
    calc (32 * ρ * σ ^ 4 * Mg) ^ 2 = 1024 * ρ ^ 2 * σ ^ 8 * Mg ^ 2 := by ring
      _ ≤ 1024 * ρ ^ 2 * σ ^ 8 * (14 / 75 * σ * ε ^ 2) :=
          mul_le_mul_of_nonneg_left hMb (by positivity)
      _ = 1024 * 14 / 75 * (ρ ^ 2 * ε ^ 2) * σ ^ 9 := by ring
      _ ≤ 1024 * 14 / 75 * (ρ ^ 2 * ε ^ 2) * R ^ 9 :=
          mul_le_mul_of_nonneg_left hp9 (by positivity)
      _ ≤ 256 * ρ ^ 2 * ε ^ 2 * R ^ 9 := by
          have : 0 ≤ (ρ ^ 2 * ε ^ 2) * R ^ 9 := by positivity
          nlinarith
  have k3 : 128 / 3 * ρ * σ ^ 3 * Mg ≤ L ^ 2 := by
    apply from_lc hL hlc (by positivity)
    calc (128 / 3 * ρ * σ ^ 3 * Mg) ^ 2 = 16384 / 9 * ρ ^ 2 * σ ^ 6 * Mg ^ 2 := by ring
      _ ≤ 16384 / 9 * ρ ^ 2 * σ ^ 6 * (14 / 75 * σ * ε ^ 2) :=
          mul_le_mul_of_nonneg_left hMb (by positivity)
      _ = 16384 * 14 / 675 / 25 * (ρ ^ 2 * ε ^ 2) * (25 * σ ^ 7) := by ring
      _ ≤ 16384 * 14 / 675 / 25 * (ρ ^ 2 * ε ^ 2) * R ^ 9 :=
          mul_le_mul_of_nonneg_left hp7 (by positivity)
      _ ≤ 256 * ρ ^ 2 * ε ^ 2 * R ^ 9 := by
          have : 0 ≤ (ρ ^ 2 * ε ^ 2) * R ^ 9 := by positivity
          nlinarith
  have k4 : 400 / 3 * ρ * σ ^ 2 * Mg ^ 3 ≤ ε ^ 2 * L ^ 2 := by
    have hM6 : (Mg ^ 2) ^ 3 ≤ (14 / 75 * σ * ε ^ 2) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hMb 3
    have hsq : (400 / 3 * ρ * σ ^ 2 * Mg ^ 3) ^ 2 ≤ (ε ^ 2 * L ^ 2) ^ 2 := by
      calc (400 / 3 * ρ * σ ^ 2 * Mg ^ 3) ^ 2 = 160000 / 9 * ρ ^ 2 * σ ^ 4 * (Mg ^ 2) ^ 3 := by
            ring
        _ ≤ 160000 / 9 * ρ ^ 2 * σ ^ 4 * (14 / 75 * σ * ε ^ 2) ^ 3 :=
            mul_le_mul_of_nonneg_left hM6 (by positivity)
        _ = 160000 / 9 * (14 / 75) ^ 3 / 25 * (ε ^ 4 * (ρ ^ 2 * ε ^ 2)) * (25 * σ ^ 7) := by ring
        _ ≤ 160000 / 9 * (14 / 75) ^ 3 / 25 * (ε ^ 4 * (ρ ^ 2 * ε ^ 2)) * R ^ 9 :=
            mul_le_mul_of_nonneg_left hp7 (by positivity)
        _ ≤ ε ^ 4 * (256 * ρ ^ 2 * ε ^ 2 * R ^ 9) := by
            have : 0 ≤ ε ^ 4 * (ρ ^ 2 * ε ^ 2) * R ^ 9 := by positivity
            nlinarith
        _ ≤ ε ^ 4 * L ^ 4 := mul_le_mul_of_nonneg_left hlc (by positivity)
        _ = (ε ^ 2 * L ^ 2) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hexp : σ * (ρ * (2 * σ * Mg / L) ^ 2 / 2) = 2 * ρ * σ ^ 3 * Mg ^ 2 / L ^ 2 := by
      field_simp
    rw [hexp, div_le_div_iff₀ (by positivity) (by norm_num)]
    calc 2 * ρ * σ ^ 3 * Mg ^ 2 * 16 ≤ 2 * ρ * σ ^ 3 * (14 / 75 * σ * ε ^ 2) * 16 := by
          gcongr
      _ = 448 / 75 / 16 * ε * (16 * ρ * ε * σ ^ 4) := by ring
      _ ≤ 448 / 75 / 16 * ε * L ^ 2 := by gcongr
      _ ≤ ε * L ^ 2 := by
          have : 0 ≤ ε * L ^ 2 := by positivity
          nlinarith
  · have h1 : G ^ 2 ≤ (2 * σ * ε / 25) ^ 2 := by
      rw [hG2]
      have hn0 : 0 < n := by linarith
      rw [div_le_iff₀ (by positivity)]
      have e : (2 * σ * ε / 25) ^ 2 * (25 * n) = (4 * n * σ) * (σ * ε ^ 2) / 25 := by ring
      rw [e, le_div_iff₀ (by norm_num)]
      have : 25 * (σ * ε ^ 2) ≤ (4 * n * σ) * (σ * ε ^ 2) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    exact (pow_le_pow_iff_left₀ hG (by positivity) two_ne_zero).mp h1
  · have hexp : ρ * (2 * σ * Mg / L) ^ 3 / 6 = 4 / 3 * ρ * σ ^ 3 * Mg ^ 3 / L ^ 3 := by
      field_simp; ring
    rw [hexp, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 4 / 3 * ρ * σ ^ 3 * Mg ^ 3 * (100 * L) = σ * L * (400 / 3 * ρ * σ ^ 2 * Mg ^ 3) := by ring
      _ ≤ σ * L * (ε ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_left k4 (by positivity)
      _ = σ * ε ^ 2 * L ^ 3 := by ring
  · have hexp : 16 * σ ^ 2 * (ρ * (2 * σ * Mg / L) ^ 2 / 2) =
        Mg * (32 * ρ * σ ^ 4 * Mg) / L ^ 2 := by
      field_simp; ring
    rw [hexp, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left k2 hMg
  · have : (2 * G) ^ 2 ≤ Mg ^ 2 := by
      rw [hM2]
      have : (4 : ℝ) ≤ 4 * n + 2 := by linarith
      have h' : 4 * G ^ 2 ≤ (4 * n + 2) * G ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg G)
      calc (2 * G) ^ 2 = 4 * G ^ 2 := by ring
        _ ≤ _ := h'
    exact (pow_le_pow_iff_left₀ (by positivity) hMg two_ne_zero).mp this
  · have hexp : ρ * (2 * σ * Mg / L) ^ 3 / 6 = 4 / 3 * ρ * σ ^ 3 * Mg ^ 3 / L ^ 3 := by
      field_simp; ring
    rw [hexp, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 4 / 3 * ρ * σ ^ 3 * Mg ^ 3 * (32 * L) = Mg ^ 2 * L * (128 / 3 * ρ * σ ^ 3 * Mg) := by ring
      _ ≤ Mg ^ 2 * L * L ^ 2 := mul_le_mul_of_nonneg_left k3 (by positivity)
      _ = Mg ^ 2 * L ^ 3 := by ring

end Constraints

end LongTails.Proofs.AdaptiveSilverParams
