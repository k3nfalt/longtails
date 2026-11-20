import LongTails.Proofs.LeonCalendar
import LongTails.Algorithms.ContaminatedParallelDescent

namespace LongTails.Proofs.ContaminatedCalendarBudget

open LongTails.Algorithms.LeonCalendar
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (height iterations)
open LongTails.Setups.DistributedContaminatedSmoothNonconvex

lemma level_sum (v : ℕ → ℝ) (H : ℕ) :
    ((levels H).map v).sum = ∑ l ∈ Finset.range (H+1), (4:ℝ)^(H-l) * v l := by
  induction H with
  | zero => simp [levels]
  | succ H ih =>
    simp only [levels, List.map_cons, List.map_append, List.sum_cons, List.sum_append]
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    have he : ∀ l ∈ Finset.range (H+1), (4:ℝ)^(H+1-l)*v l = 4*((4:ℝ)^(H-l)*v l) := by
      intro l hl
      rw [show H+1-l=H-l+1 by have := Finset.mem_range.mp hl; omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl he, ← Finset.mul_sum, ← ih]
    ring

lemma levels_length (H : ℕ) : (levels H).length ≤ 2 * 4 ^ H := by
  have he : 3*(levels H).length + 1 = 4 * 4^H := by
    induction H with
    | zero => decide
    | succ H ih => simp only [levels,List.length_cons,List.length_append,pow_succ]; omega
  omega

lemma levels_linear (H : ℕ) : ((levels H).map (fun l => 1+l)).sum ≤ 2*4^H := by
  have he : ∀ l : ℕ, 1+l ≤ 2^l := by
    intro l
    induction l with
    | zero => decide
    | succ l ih => rw [pow_succ]; omega
  have hlist (ls : List ℕ) : (ls.map (fun l => 1+l)).sum ≤ (ls.map (fun l => 2^l)).sum := by
    induction ls with
    | nil => rfl
    | cons l ls ih => exact Nat.add_le_add (he l) ih
  exact (hlist (levels H)).trans ((Nat.le_add_right _ _).trans_eq (LeonCalendar.batch_work H))

def middle (H : ℕ) : ℝ := ∑ l ∈ Finset.range (H+1), min ((4:ℝ)^l) (4^(H-l))

lemma middle_step (H : ℕ) : middle (H+2) = 2 + 4 * middle H := by
  have h4 (j : ℕ) : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  unfold middle
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, Nat.sub_self,
    min_eq_left (h4 _), min_eq_right (h4 _)]
  have he (l : ℕ) (hl : l ∈ Finset.range (H+1)) :
      min ((4:ℝ)^(l+1)) (4^(H+2-(l+1))) = 4 * min (4^l) (4^(H-l)) := by
    rw [show H+2-(l+1)=H-l+1 by have := Finset.mem_range.mp hl; omega, pow_succ, pow_succ,
      mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
    simp [mul_comm]
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum]
  ring

lemma middle_bound (H : ℕ) : middle H ≤ 2 * (2:ℝ)^H - 1 := by
  induction H using Nat.twoStepInduction with
  | zero => norm_num [middle]
  | one => norm_num [middle, Finset.sum_range_succ]
  | more H ih _ =>
    rw [middle_step, pow_add]
    norm_num
    linarith

lemma levels_weight (H : ℕ) :
    ((levels H).map (fun l => min (1:ℝ) (16^l/4^H))).sum ≤ 2*(2:ℝ)^H := by
  rw [level_sum]
  apply le_trans _ ((middle_bound H).trans (sub_le_self _ zero_le_one))
  unfold middle
  apply Finset.sum_le_sum
  intro l hl
  have hle : l ≤ H := by simpa using Finset.mem_range.mp hl
  have hd : (4:ℝ)^H = 4^(H-l)*4^l := by rw [← pow_add,Nat.sub_add_cancel hle]
  have hpow : (16:ℝ)^l = (4^l)^2 := by rw [← pow_mul, Nat.mul_comm l 2, pow_mul]; norm_num
  rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 4^(H-l)), mul_one, hd, hpow, min_comm]
  apply min_le_min_right
  field_simp
  rfl

lemma levels_precision (p : Params) :
    (((levels (height (network p))).map (fun l => (levelConfidence p l : ℝ))).sum) ≤
      32 * ((iterations (network p) : ℝ) + confidence p * min (iterations (network p) : ℝ) (confidence p)) := by
  let H := height (network p)
  let K := (4:ℝ)^H
  let q := (confidence p:ℝ)
  let w (l : ℕ) := min (1:ℝ) (16^l/K)
  have hK : (iterations (network p) : ℝ) = K := by simp [K,H,iterations]
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hsingle (l : ℕ) : (levelConfidence p l : ℝ) ≤ 10*(1+(l:ℝ)) + 2*q*w l := by
    have hw : 0 ≤ q*w l := mul_nonneg hq (le_min zero_le_one (by dsimp [K]; positivity))
    have hc := (Nat.ceil_lt_add_one hw).le
    unfold levelConfidence
    push_cast
    rw [hK]
    change 8*(1+(l:ℝ)) + 2*(⌈q*w l⌉₊:ℝ) ≤ _
    nlinarith [show (0:ℝ) ≤ l by positivity]
  have hlist (ls : List ℕ) :
      (ls.map (fun l => (levelConfidence p l : ℝ))).sum ≤
        10 * ((ls.map (fun (l : ℕ) => (1+(l:ℝ)))).sum) + 2*q*(ls.map w).sum := by
    induction ls with
    | nil => simp
    | cons l ls ih => simp only [List.map_cons, List.sum_cons]; linarith [hsingle l]
  have hlin : ((levels H).map (fun (l : ℕ) => (1+(l:ℝ)))).sum ≤ 2*K := by
    have hc := (Nat.cast_le (α := ℝ)).mpr (levels_linear H)
    simpa [K,Nat.cast_list_sum,List.map_map,Function.comp_def] using hc
  have hweight := levels_weight H
  change ((levels H).map w).sum ≤ 2*(2:ℝ)^H at hweight
  have hsum := hlist (levels H)
  have hw := mul_le_mul_of_nonneg_left hweight (show 0 ≤ 2*q by positivity)
  have he : ((2:ℝ)^H)^2 = K := by dsimp [K]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  rw [hK]
  change _ ≤ 32*(K+q*min K q)
  have hpow : (2:ℝ)^H ≤ K := by dsimp [K]; gcongr; norm_num
  rcases le_total K q with h | h
  · rw [min_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left hpow hq, show 0 ≤ q*K by positivity, show 0 ≤ K by positivity]
  · rw [min_eq_right h]
    nlinarith [sq_nonneg (q-(2:ℝ)^H),sq_nonneg q,show 0 ≤ K by positivity]

end LongTails.Proofs.ContaminatedCalendarBudget
