import LongTails.Proofs.ChiSquareBoundedCentreDroExecution

namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro

variable (q : Params)

lemma tournament_cost_le (hρ : 0 < q.ρ) (r h : ℕ) :
    (tournamentCost q r h : ℝ) ≤ 2^h *
      (4096 * (1+2*q.ρ)*q.B^2 / q.ε^2 * (3/2:ℝ)^r + 2) := by
  let C := (1+2*q.ρ)*q.B^2/q.ε^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  suffices H : (tournamentCost q r h : ℝ) ≤ 2^h * (4096*C*(3/2:ℝ)^r+2) by
    convert H using 1; dsimp [C]; ring
  induction h generalizing r with
  | zero => simp [tournamentCost]; positivity
  | succ h ih =>
    have hsize : (batchSize q r : ℝ) ≤ 1024*C*(3/2:ℝ)^r+1 := by
      unfold batchSize
      convert (Nat.ceil_lt_add_one (by positivity : 0 ≤
        1024*(1+2*q.ρ)*q.B^2*(3/2:ℝ)^r/q.ε^2)).le using 1; dsimp [C]; ring
    rw [tournamentCost]
    push_cast
    calc _ ≤ (2:ℝ)^(h+1)*(1024*C*(3/2:ℝ)^r+1) +
          2^h*(4096*C*(3/2:ℝ)^(r+1)+2) :=
          add_le_add (mul_le_mul_of_nonneg_left hsize (by positivity)) (ih (r+1))
      _ = _ := by rw [pow_succ, pow_succ (3/2:ℝ)]; ring

lemma slots_le : 2^rounds q ≤ 2*bracketCount q := by
  have hK : 0 < bracketCount q := by unfold bracketCount; omega
  by_cases hk : 1 < bracketCount q
  · have hh := Nat.clog_pos (by norm_num : 1 < 2) hk
    have hu := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hk
    unfold rounds
    generalize Nat.clog 2 (bracketCount q) = h at *
    cases h with
    | zero => omega
    | succ h => rw [pow_succ]; simp only [Nat.pred_succ] at hu; omega
  · have hk' : bracketCount q = 1 := by omega
    simp [rounds, hk']

lemma usedCalls_le_budget (hρ : 0 < q.ρ) :
    usedCalls q ≤ if min q.B (q.G*q.R) ≤ q.ε then 0 else
      bracketCount q * (⌈256*(1+2*q.ρ)*(q.G^2*q.R^2+35*q.B^2)/q.ε^2⌉₊ + 5) := by
  unfold usedCalls
  split
  · rfl
  · let C := (1+2*q.ρ)*q.B^2/q.ε^2
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hs : ((2:ℝ)^rounds q) ≤ 2*(bracketCount q:ℝ) := by exact_mod_cast slots_le q
    have htc := tournament_cost_le q hρ 0 (rounds q)
    simp only [pow_zero, mul_one] at htc
    have ht : (tournamentCost q 0 (rounds q):ℝ) ≤ 2*bracketCount q*(4096*C+2) := by
      refine htc.trans ?_
      convert mul_le_mul_of_nonneg_right hs (show 0 ≤ 4096*C+2 by positivity) using 1; dsimp [C]; ring
    have htrain := (Nat.ceil_lt_add_one (by positivity : 0 ≤
      256*(1+2*q.ρ)*(q.G^2*q.R^2+3*q.B^2)/q.ε^2)).le
    have hceil := Nat.le_ceil (256*(1+2*q.ρ)*(q.G^2*q.R^2+35*q.B^2)/q.ε^2)
    change (trainingCount q : ℝ) ≤ _ at htrain
    have hsum := add_le_add (mul_le_mul_of_nonneg_left htrain
      (Nat.cast_nonneg (α := ℝ) (bracketCount q))) ht
    have htop := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg (α := ℝ) (bracketCount q))
    dsimp [C] at hsum
    exact_mod_cast (show (bracketCount q : ℝ)*trainingCount q + tournamentCost q 0 (rounds q) ≤
      bracketCount q * ((⌈256*(1+2*q.ρ)*(q.G^2*q.R^2+35*q.B^2)/q.ε^2⌉₊:ℝ)+5) by
      linear_combination hsum + htop)

end OracleTemplate.ChiSquareBoundedCentreDro
