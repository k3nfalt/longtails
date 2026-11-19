import LongTails.Algorithms.MultirateAllocation

namespace LongTails.Proofs.MultirateAllocation

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateAllocation

variable {p : Params}

lemma startup_nonneg (i : Fin p.n) : 0 ≤ startupWeight p i :=
  mul_nonneg (p.h i).coe_nonneg (sq_nonneg _)

lemma refresh_nonneg (hσ : ∀ i, 0 ≤ p.σ i) (i : Fin p.n) : 0 ≤ refreshWeight p i :=
  mul_nonneg (hσ i) (Real.sqrt_nonneg _)

lemma normalized_sum_le_one {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    (∑ i, w i / (∑ j, w j)) ≤ 1 := by
  rw [← Finset.sum_div]
  exact div_self_le_one _

lemma total_share (p : Params) :
    (∑ i, share p i) ≤ ((p.n : ℝ) * precision p) ^ 2 := by
  simp only [share, ← Finset.mul_sum, Finset.sum_add_distrib]
  have h := add_le_add (normalized_sum_le_one (startupWeight p))
    (normalized_sum_le_one (refreshWeight p))
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((p.n : ℝ) * precision p))]

lemma half_pos (hε : 0 < p.ε) : 0 < ((p.n : ℝ) * precision p) ^ 2 / 2 := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  unfold precision
  positivity

lemma share_pos (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε)
    (i : Fin p.n) (hs : p.σ i ≠ 0) : 0 < share p i := by
  have h1 : 0 < startupWeight p i := mul_pos (hh i) (sq_pos_of_ne_zero hs)
  have h2 := Finset.single_le_sum (f := startupWeight p) (fun j _ => startup_nonneg j) (Finset.mem_univ i)
  exact mul_pos (half_pos hε) (add_pos_of_pos_of_nonneg (div_pos h1 (h1.trans_le h2))
    (div_nonneg (refresh_nonneg hσ i) (Finset.sum_nonneg fun j _ => refresh_nonneg hσ j)))

lemma share_nonneg (hσ : ∀ i, 0 ≤ p.σ i) (i : Fin p.n) : 0 ≤ share p i :=
  mul_nonneg (by positivity) (add_nonneg
    (div_nonneg (startup_nonneg i) (Finset.sum_nonneg fun j _ => startup_nonneg j))
    (div_nonneg (refresh_nonneg hσ i) (Finset.sum_nonneg fun j _ => refresh_nonneg hσ j)))

lemma batch_pos (i : Fin p.n) : 0 < batch p i := by unfold batch; omega

lemma batch_variance (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) :
    (∑ i, p.σ i ^ 2 / (batch p i : ℝ)) ≤ ((p.n : ℝ) * precision p) ^ 2 := by
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) (total_share p)
  by_cases hs : p.σ i = 0
  · simpa [hs] using share_nonneg hσ i
  have h := Nat.lt_floor_add_one (p.σ i ^ 2 / share p i)
  have hb : p.σ i ^ 2 / share p i ≤ (batch p i : ℝ) := by simpa [batch, add_comm] using h.le
  apply (div_le_iff₀ (by exact_mod_cast batch_pos (p := p) i)).mpr
  simpa [mul_comm] using (div_le_iff₀ (share_pos hh hσ hε i hs)).mp hb

lemma rounded_batch_le (hσ : ∀ i, 0 ≤ p.σ i) (i : Fin p.n) :
    (batch p i : ℝ) ≤ 1 + p.σ i ^ 2 / share p i := by
  unfold batch
  push_cast
  exact add_le_add_right (Nat.floor_le (div_nonneg (sq_nonneg _) (share_nonneg hσ i))) 1

lemma normalized_ratio {w W s B : ℝ} (hB : 0 < B) (hw : 0 ≤ w) (hW : w ≤ W)
    (hs : B * (w / W) ≤ s) : w / s ≤ W / B := by
  by_cases hz : w = 0
  · simpa [hz] using div_nonneg (hw.trans hW) hB.le
  have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm hz)
  have hWp := hp.trans_le hW
  have hsp := (mul_pos hB (div_pos hp hWp)).trans_le hs
  apply (div_le_div_iff₀ hsp hB).mpr
  have h := mul_le_mul_of_nonneg_right hs hWp.le
  field_simp at h
  linarith

lemma startup_time (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) (i : Fin p.n) :
    p.h i * (batch p i : ℝ) ≤ p.h i + 2 * (∑ j, startupWeight p j) / ((p.n : ℝ) * precision p)^2 := by
  have hi := Finset.single_le_sum (f := startupWeight p) (fun j _ => startup_nonneg j) (Finset.mem_univ i)
  have hc : ((p.n : ℝ) * precision p)^2 / 2 *
      (startupWeight p i / ∑ j, startupWeight p j) ≤ share p i := by
    unfold share
    gcongr
    exact le_add_of_nonneg_right (div_nonneg (refresh_nonneg hσ i) (Finset.sum_nonneg fun j _ => refresh_nonneg hσ j))
  have h := normalized_ratio (half_pos hε) (startup_nonneg i) hi hc
  calc
    _ ≤ (p.h i : ℝ) * (1 + p.σ i ^ 2 / share p i) := by gcongr; exact rounded_batch_le hσ i
    _ = p.h i + startupWeight p i / share p i := by unfold startupWeight; ring
    _ ≤ _ := by refine add_le_add_right ?_ _; convert h using 1; ring

lemma refresh_time (hL : ∀ i, 0 ≤ p.L i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) :
    (∑ i, p.L i * p.h i * (batch p i : ℝ)) ≤
      (∑ i, p.L i * p.h i) + 2 * (∑ i, refreshWeight p i)^2 / ((p.n : ℝ) * precision p)^2 := by
  let W := ∑ i, refreshWeight p i
  let B := ((p.n : ℝ) * precision p)^2 / 2
  have one (i : Fin p.n) : p.L i * p.h i * (batch p i : ℝ) ≤
      p.L i * p.h i + refreshWeight p i * (W / B) := by
    have hi := Finset.single_le_sum (f := refreshWeight p) (fun j _ => refresh_nonneg hσ j) (Finset.mem_univ i)
    have hc : B * (refreshWeight p i / W) ≤ share p i := by
      unfold share
      apply mul_le_mul_of_nonneg_left _ (half_pos hε).le
      exact le_add_of_nonneg_left (div_nonneg (startup_nonneg i) (Finset.sum_nonneg fun j _ => startup_nonneg j))
    have hr := normalized_ratio (half_pos hε) (refresh_nonneg hσ i) hi hc
    have hsq : (refreshWeight p i)^2 = p.σ i ^ 2 * (p.L i * p.h i) := by
      rw [refreshWeight, mul_pow, Real.sq_sqrt (mul_nonneg (hL i) (p.h i).coe_nonneg)]
    calc
      _ ≤ (p.L i * p.h i) * (1 + p.σ i ^ 2 / share p i) :=
        mul_le_mul_of_nonneg_left (rounded_batch_le hσ i) (mul_nonneg (hL i) (p.h i).coe_nonneg)
      _ = p.L i * p.h i + (refreshWeight p i)^2 / share p i := by rw [hsq]; ring
      _ ≤ _ := by rw [sq, mul_div_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_left hr (refresh_nonneg hσ i)) _
  calc
    _ ≤ ∑ i, (p.L i * p.h i + refreshWeight p i * (W / B)) := Finset.sum_le_sum fun i _ => one i
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]; dsimp only [W,B]; ring

end LongTails.Proofs.MultirateAllocation
