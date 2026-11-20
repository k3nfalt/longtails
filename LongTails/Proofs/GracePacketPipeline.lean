import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace LongTails.Proofs.GracePacketPipeline

lemma lane_count {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    (hw : ∑ t, weight t = 1) :
    Fintype.card ι ≤ ∑ t, ⌊2 * (Fintype.card ι : ℝ) * weight t⌋₊ := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun t _ =>
    (Nat.lt_floor_add_one (2 * (Fintype.card ι : ℝ) * weight t)).le
  rw [← Finset.mul_sum, hw, mul_one, Finset.sum_add_distrib] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have : (Fintype.card ι : ℝ) ≤ ∑ t, (⌊2 * (Fintype.card ι : ℝ) * weight t⌋₊ : ℝ) := by linarith
  exact_mod_cast this

lemma link_load {ι : Type*} [Fintype ι] (weight : ι → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (uses : Finset ι) {b Λ : ℝ} (hc : (∑ t ∈ uses, weight t) ≤ b / Λ) :
    ((∑ t ∈ uses, ⌊2 * (Fintype.card ι : ℝ) * weight t⌋₊ : ℕ) : ℝ) ≤
      2 * Fintype.card ι / Λ * b := by
  push_cast
  calc
    _ ≤ ∑ t ∈ uses, 2 * (Fintype.card ι : ℝ) * weight t :=
      Finset.sum_le_sum fun t _ => Nat.floor_le (mul_nonneg (by positivity) (hw t))
    _ = _ := Finset.mul_sum .. |>.symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring)

lemma striped_time {m P : ℕ} (hm : m ≤ P) (d H : ℕ) (q Λ : ℝ)
    (hq : 0 ≤ q) (hΛ : 0 < Λ) :
    ((d / P + 1 + H : ℕ) : ℝ) * (2 * m * q / Λ) ≤
      2 * q * (d + m * (1 + (H : ℝ))) / Λ := by
  have hn : d / P * m ≤ d := (Nat.mul_le_mul_left _ hm).trans (Nat.div_mul_le_self ..)
  have h : (d / P * m : ℕ) + m + H * m ≤ d + m * (1 + H) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m H]
    omega
  have hc : ((d / P : ℕ) + 1 + (H : ℝ)) * m ≤ d + m * (1 + (H : ℝ)) := by
    exact_mod_cast (show (d / P + 1 + H) * m ≤ d + m * (1 + H) by
      simpa [Nat.add_mul] using h)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hΛ.le
  push_cast
  calc
    _ = 2 * q * (((d / P : ℕ) + 1 + (H : ℝ)) * m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

lemma reduction_precedence (stripe H depth : ℕ) (h : depth < H) :
    stripe + (H - (depth + 1)) + 1 = stripe + (H - depth) := by omega

lemma broadcast_precedence (stripe depth : ℕ) :
    stripe + depth + 1 = stripe + (depth + 1) := Nat.add_assoc ..

end LongTails.Proofs.GracePacketPipeline
