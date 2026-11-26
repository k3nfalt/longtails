import LongTails.Algorithms.FullRangeWeakMintyHalpern
import Mathlib.Tactic

open scoped RealInnerProductSpace
namespace OracleTemplate.FullRangeWeakMintyHalpern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def endpoint (G : E → E) (c : E) : ℕ → E
  | 0 => c
  | j+1 => next c j (G (endpoint G c j))

private noncomputable def energy (j : ℝ) (h v : E) :=
  j / 2 * ‖h + v‖ ^ 2 + ⟪h + v, h⟫

private lemma energy_step {j : ℝ} (hj : 0 ≤ j) (h v v' : E) :
    let h' := -((j+1)/(j+2)) • v
    (j+2) * energy (j+1) h' v' - (j+1) * energy j h v =
      (j+1)*(j+2)/2 * (‖v' - v‖^2 - ‖h' - h‖^2) := by
  dsimp only
  unfold energy
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_right,
    real_inner_comm]
  field_simp [show j + 2 ≠ 0 by linarith]
  ring

lemma relative_error (G : E → E) (lip : ∀ x y, ‖G x - G y‖ ≤ ‖x - y‖)
    (c : E) {δ : ℝ} (hd : 0 < δ) :
    let y := endpoint G c (count δ)
    ‖y - c + G y‖ ≤ Real.sqrt δ / 16 * ‖G y‖ := by
  let u := endpoint G c
  have hp (j : ℕ) : energy j (u j - c) (G (u j)) ≤ 0 := by
    induction j with
    | zero => simp [u, endpoint, energy]
    | succ j ih =>
      have he : u (j+1) - c = -(((j:ℝ)+1)/(j+2)) • G (u j) := by
        dsimp [u, endpoint, next]
        module
      have hl := pow_le_pow_left₀ (norm_nonneg _) (lip (u (j+1)) (u j)) 2
      rw [show u (j+1) - u j = (u (j+1) - c) - (u j - c) by abel, he] at hl
      have hi := energy_step (Nat.cast_nonneg j) (u j - c) (G (u j)) (G (u (j+1)))
      dsimp only at hi
      have hh := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ ((j:ℝ)+1)*(j+2)/2 by positivity) (sub_nonpos.mpr hl)
      push_cast
      rw [he]
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (j:ℝ)+1 by positivity) ih
      exact nonpos_of_mul_nonpos_right (by linarith only [hi, hh, hn]) (by positivity : 0 < (j:ℝ)+2)
  let k := count δ
  let y := u k
  let r := y - c + G y
  change ‖r‖ ≤ _
  have hpot : (k : ℝ) / 2 * ‖r‖ ^ 2 + ⟪r, y-c⟫ ≤ 0 := hp k
  have hcs := real_inner_le_norm r (-(y-c))
  rw [inner_neg_right, norm_neg] at hcs
  have hdisp : ‖y-c‖ ≤ ‖r‖ + ‖G y‖ := by
    rw [show y-c = r - G y by dsimp [r]; abel]
    exact norm_sub_le _ _
  by_cases hr : ‖r‖ = 0
  · rw [hr]; positivity
  have hres : (k:ℝ) * ‖r‖ ≤ 2 * ‖y-c‖ := by
    exact le_of_mul_le_mul_right (by nlinarith only [hpot, hcs]) (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr))
  have hs := Real.sqrt_pos.2 hd
  have hk : 2 + 32 / Real.sqrt δ ≤ (k:ℝ) := Nat.le_ceil _
  have hscale := mul_le_mul_of_nonneg_right hk (norm_nonneg r)
  have h32 : 32 / Real.sqrt δ * ‖r‖ ≤ 2 * ‖G y‖ := by linarith
  have hh := mul_le_mul_of_nonneg_left h32 hs.le
  field_simp [hs.ne'] at hh
  change ‖r‖ ≤ Real.sqrt δ / 16 * ‖G y‖
  linarith

end OracleTemplate.FullRangeWeakMintyHalpern
