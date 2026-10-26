import LongTails.Proofs.AdamNoiseCoupling
import LongTails.Proofs.AdamSeparationModel

namespace LongTails.Proofs.AdamRademacher

open LongTails.Proofs.AdamSeparationModel

noncomputable def batchNoise (s : ℝ) (B : ℕ) (ω : Fin B → Bool) : ℝ :=
  s / B * ∑ j, sign (ω j)

def flip (B : ℕ) : (Fin B → Bool) ≃ (Fin B → Bool) :=
  ⟨fun ω j => !(ω j), fun ω j => !(ω j), by intro ω; funext j; simp,
    by intro ω; funext j; simp⟩

lemma batchNoise_flip (s : ℝ) (B : ℕ) (ω : Fin B → Bool) :
    batchNoise s B (flip B ω) = -batchNoise s B ω := by
  have hsign (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
  simp only [batchNoise, flip, Equiv.coe_fn_mk, hsign,
    Finset.sum_neg_distrib, mul_neg]

lemma batchNoise_bound {s : ℝ} (hs : 0 ≤ s) {B : ℕ} (hB : 0 < B)
    (ω : Fin B → Bool) : |batchNoise s B ω| ≤ s := by
  have hsum : |∑ j, sign (ω j)| ≤ (B : ℝ) := by
    calc
      _ ≤ ∑ j, |sign (ω j)| := Finset.abs_sum_le_sum_abs _ _
      _ = B := by simp [sign_abs]
  rw [batchNoise, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s / B)]
  calc
    _ ≤ s / B * B := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = s := div_mul_cancel₀ s (by positivity)

lemma batchNoise_absolute_lower {s : ℝ} (hs : 0 ≤ s) {B : ℕ} (hB : 0 < B) :
    (Fintype.card (Fin B → Bool) : ℝ) * s ≤
      B * ∑ ω : Fin B → Bool, |batchNoise s B ω| := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hB.ne'
  have h := LongTails.Proofs.AdamNoiseCoupling.sign_sum_absolute_lower n
  have hm := mul_le_mul_of_nonneg_left h hs
  simp only [batchNoise, abs_mul, abs_of_nonneg (show 0 ≤ s / (n + 1 : ℕ) by positivity),
    ← Finset.mul_sum]
  dsimp only [sign] at *
  convert hm using 1 <;> push_cast <;> field_simp

end LongTails.Proofs.AdamRademacher
