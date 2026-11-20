import LongTails.Algorithms.MultirateSchedule
import LongTails.Proofs.MultirateBatchAllocation
import LongTails.Proofs.LeonCalendar

namespace LongTails.Proofs.MultirateService

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms.MultirateSchedule
open LongTails.Algorithms.MultirateBatches

variable {p : Params}

lemma service_pos (hh : ∀ i, 0 < p.h i) (i : Fin p.n) : 0 < service p i := by
  have hc : (0 : Time) < (batch p i : ℕ) := by exact_mod_cast (batch p i).pos
  exact add_pos_of_pos_of_nonneg (mul_pos hc (hh i)) zero_le

lemma sum_L_pos (hL : 0 < smoothness p) : 0 < ∑ i, p.L i :=
  (div_pos_iff_of_pos_right (show (0 : ℝ) < p.n by exact_mod_cast p.n.pos)).mp hL

lemma weighted_pos (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (hpos : 0 < smoothness p) :
    0 < ∑ i, p.L i * (service p i : ℝ) := by
  have hs := sum_L_pos hpos
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hL j)).mp hs
  exact (mul_pos hi (show (0 : ℝ) < service p i by exact_mod_cast service_pos hh i)).trans_le
    (Finset.single_le_sum (fun j _ => mul_nonneg (hL j) (service p j).coe_nonneg) (Finset.mem_univ i))

lemma tick_eq (hL : ∀ i, 0 ≤ p.L i) :
    (tick p : ℝ) = (∑ i, p.L i * (service p i : ℝ)) / ∑ i, p.L i :=
  Real.coe_toNNReal _ (div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hL i) (service p i).coe_nonneg)
    (Finset.sum_nonneg fun i _ => hL i))

lemma tick_pos (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (hpos : 0 < smoothness p) :
    0 < tick p := by
  change 0 < (tick p : ℝ)
  rw [tick_eq hL]
  exact div_pos (weighted_pos hh hL hpos) (sum_L_pos hpos)

lemma period_covers (ht : 0 < tick p) (i : Fin p.n) :
    service p i ≤ (period p i : ℕ) * tick p := by
  change (service p i : ℝ) ≤ ((period p i : ℕ) : ℝ) * (tick p : ℝ)
  apply (div_le_iff₀ (show (0 : ℝ) < tick p from ht)).mp
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

lemma weighted_periods (hL : ∀ i, 0 ≤ p.L i) (ht : 0 < tick p) (hpos : 0 < smoothness p) :
    (∑ i, p.L i * (period p i : ℝ)) ≤ 2 * ∑ i, p.L i := by
  have htr : (0 : ℝ) < tick p := ht
  have he := (eq_div_iff (sum_L_pos hpos).ne').mp (tick_eq hL)
  calc
    _ ≤ ∑ i, p.L i * (1 + (service p i : ℝ) / tick p) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hL i)
      change ((max 1 ⌈(service p i : ℝ) / tick p⌉₊ : ℕ) : ℝ) ≤ _
      rw [Nat.cast_max, Nat.cast_one]
      have hn := div_nonneg (service p i).coe_nonneg htr.le
      exact max_le (le_add_of_nonneg_right hn) ((Nat.ceil_lt_add_one hn).le.trans_eq (add_comm _ _))
    _ = _ := by
      simp only [mul_add, mul_one, ← mul_div_assoc, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [← he, mul_div_cancel_left₀ _ htr.ne']; ring

lemma noise_nonneg (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) (i : Fin p.n) : 0 ≤ noise p i := by
  have hd := LeonBatchTuning.resolution_pos (network p) hε
  exact div_nonneg (mul_nonneg (hσ i) (Real.sqrt_nonneg _)) (mul_nonneg (by positivity) hd.le)

lemma variance (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) :
    (∑ i, p.σ i ^ 2 / ((p.n : ℝ) ^ 2 * (batch p i : ℝ))) ≤ δ p ^ 2 := by
  have hd := LeonBatchTuning.resolution_pos (network p) hε
  have hh' (i) : (0 : ℝ) < p.h i := hh i
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hb := MultirateBatchAllocation.variance_budget (a := noise p) (b := weight p) hh'
    (noise_nonneg hσ hε) (fun _ => Real.sqrt_nonneg _)
  have he (i : Fin p.n) : noise p i ^ 2 / ((batch p i : ℝ) * p.h i) * δ p ^ 2 =
      p.σ i ^ 2 / ((p.n : ℝ) ^ 2 * (batch p i : ℝ)) := by
    simp only [noise, div_pow, mul_pow, Real.sq_sqrt (hh' i).le]
    have hc : (0 : ℝ) < batch p i := by exact_mod_cast (batch p i).pos
    field_simp [ne_of_gt (hh' i), ne_of_gt hn, ne_of_gt hc, show δ p ≠ 0 from hd.ne']
  change (∑ i, noise p i ^ 2 / ((batch p i : ℝ) * p.h i)) ≤ 1 at hb
  simpa only [Finset.sum_mul, he, one_mul] using mul_le_mul_of_nonneg_right hb (sq_nonneg (δ p))

end LongTails.Proofs.MultirateService
