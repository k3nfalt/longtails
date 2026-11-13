import Mathlib.Tactic

namespace OracleTemplate.MixingProfiles

lemma profile_mul_le {φ : ℕ → ℝ} (hφ : ∀ n, 0 ≤ φ n)
    (hzero : φ 0 = 1) (hmul : ∀ m n, φ m * φ n ≤ φ (m + n))
    (H n : ℕ) : φ H ^ n ≤ φ (n * H) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (mul_le_mul_of_nonneg_right ih (hφ H)).trans (hmul (n * H) H)

lemma profile_block_bound {φ : ℕ → ℝ} (hφ : ∀ n, 0 ≤ φ n)
    (hzero : φ 0 = 1) (hanti : Antitone φ)
    (hmul : ∀ m n, φ m * φ n ≤ φ (m + n))
    {b : ℝ} (hb : 0 ≤ b) {H : ℕ} (hH : 0 < H) (hscale : b ≤ φ H)
    (t : ℕ) : b ^ (t / H + 1) ≤ φ t := by
  apply (pow_le_pow_left₀ hb hscale _).trans
  apply (profile_mul_le hφ hzero hmul H (t / H + 1)).trans
  apply hanti
  have ht := Nat.mod_lt t hH
  have he := Nat.mod_add_div t H
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (t / H) H]
  omega

end OracleTemplate.MixingProfiles
