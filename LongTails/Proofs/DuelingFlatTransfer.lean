import LongTails.Setups.FlatTransferDueling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open LongTails.Setups
open LongTails.Setups.FlatTransferDueling

namespace LongTails.Proofs.DuelingFlatTransfer

noncomputable def link (j : ℕ) (t : ℝ) := Real.arctan (t^(2*j+1)) / 4

noncomputable def gain (j : ℕ) (t : ℝ) := ((2*j+1 : ℕ) : ℝ)*t^(2*j) / (4*(1+(t^(2*j+1))^2))

lemma derivative (j : ℕ) (t : ℝ) : HasDerivAt (link j) (gain j t) t := by
  have h := ((Real.hasDerivAt_arctan _).comp t
    ((hasDerivAt_id t).pow (2*j+1))).div_const 4
  convert h using 1
  · rfl
  · simp [gain, div_eq_mul_inv]
    ring

lemma gain_nonneg (j : ℕ) (t : ℝ) : 0 ≤ gain j t := by
  unfold gain
  rw [pow_mul]
  positivity

lemma gain_le (j : ℕ) (t : ℝ) : gain j t ≤ (2*(j:ℝ)+1)/4 := by
  have ht : t^(2*j) = |t|^(2*j) := by rw [pow_mul, pow_mul, sq_abs]
  have hpow : t^(2*j) ≤ 1 + (t^(2*j+1))^2 := by
    rw [ht, ← sq_abs, abs_pow, ← pow_mul]
    rcases le_total |t| 1 with ha | ha
    · linarith [pow_le_one₀ (abs_nonneg t) ha (n := 2*j), pow_nonneg (abs_nonneg t) ((2*j+1)*2)]
    · linarith [pow_le_pow_right₀ ha (show 2*j ≤ (2*j+1)*2 by omega)]
  unfold gain
  apply (div_le_iff₀ (by positivity)).2
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*(j:ℝ)+1 by positivity)]

lemma gain_lower {j : ℕ} {t : ℝ} (ht : |t| ≤ 1) :
    (2*(j:ℝ)+1)/8 * |t|^(2*j) ≤ gain j t := by
  have he : t^(2*j) = |t|^(2*j) := by rw [pow_mul, pow_mul, sq_abs]
  have hh : (t^(2*j+1))^2 ≤ 1 := by
    rw [← sq_abs, abs_pow, ← pow_mul]
    exact pow_le_one₀ (abs_nonneg _) ht
  unfold gain
  rw [he]
  apply (le_div_iff₀ (by positivity)).2
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (2*(j:ℝ)+1)*|t|^(2*j) by positivity)]

lemma link_bound (j : ℕ) (t : ℝ) : |link j t| ≤ 1/2 := by
  have hl := Real.neg_pi_div_two_lt_arctan (t^(2*j+1))
  have hu := Real.arctan_lt_pi_div_two (t^(2*j+1))
  unfold link
  apply abs_le.mpr
  constructor <;> linarith [Real.pi_lt_four]

lemma transfer (p : Params) : StronglyConvexDueling.Transfer (model p) (link p.j) := by
  have hd : deriv (link p.j) = gain p.j := funext fun t => (derivative p.j t).deriv
  constructor
  · intro t; rw [hd]; exact derivative _ _
  · rw [hd]; unfold gain; fun_prop (disch := intro x; positivity)
  · intro t
    simp [link, pow_succ, pow_mul, neg_div]
  · exact monotone_of_deriv_nonneg (fun t => (derivative _ t).differentiableAt) (by
      intro t; rw [hd]; exact gain_nonneg _ _)
  · intro t; linarith [link_bound p.j t]
  · intro t ht; rw [hd]; exact gain_lower ht
  · intro t _; rw [hd]; exact gain_le _ _

end LongTails.Proofs.DuelingFlatTransfer
