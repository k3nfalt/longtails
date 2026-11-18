import LongTails.Proofs.MultiscaleAggregateCodec
import LongTails.Proofs.MultiscaleAggregateSchedule
import LongTails.Proofs.MultiscaleAggregateTracking
import LongTails.Proofs.NormalizedStormMoments

namespace LongTails.Proofs.MultiscaleAggregateTrajectory

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateCodec MultiscaleAggregateSchedule MultiscaleAggregateTracking

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

noncomputable abbrev point (k : ℕ) : Point p := (trajectory p g s k).point

noncomputable def raw (k : ℕ) : Point p :=
  unpack p (∑ i, localCode p (batchMean p g s k i (point g s k)))

noncomputable def estimate (k : ℕ) : Point p :=
  (trajectory p g s (k + 1)).estimates k

noncomputable def anchor (k : ℕ) : Point p :=
  if k = 0 then 0 else (trajectory p g s k).estimates ((schedule p).pred k)

lemma estimate_eq (k : ℕ) :
    estimate g s k = recover p k (anchor g s k)
      (readPacket p k (rootMessage p g s k (point g s k))) := by
  simp only [estimate, trajectory, advance, Function.update_self, anchor, point]

lemma history_eq {i k : ℕ} (h : i < k) :
    (trajectory p g s k).estimates i = estimate g s i := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i = k
    · subst i
      rfl
    · simpa only [trajectory, advance, Function.update_of_ne he] using ih (by omega)

lemma point_succ (k : ℕ) :
    point g s (k + 1) = OracleTemplate.NormalizedStorm.stormStep
      (precision p / p.L) (point g s k) (estimate g s k) := by
  rw [estimate_eq]
  rfl

lemma point_drift (hL : 0 < p.L) (hε : 0 < p.ε) {i k : ℕ} (h : i ≤ k) :
    ‖point g s k - point g s i‖ ≤ (k - i : ℕ) * (precision p / p.L) := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have hstep := OracleTemplate.NormalizedStorm.stormStep_dist
      (div_nonneg (precision_pos hε).le hL.le) (point g s k) (estimate g s k)
    rw [← point_succ] at hstep
    have htri := norm_sub_le_norm_sub_add_norm_sub (point g s (k + 1)) (point g s k) (point g s i)
    rw [show k + 1 - i = (k - i) + 1 by omega, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith

lemma estimate_near_anchor (hε : 0 < p.ε) (k : ℕ) :
    ‖estimate g s k - anchor g s k‖ ≤ 3 * radius p k := by
  rw [estimate_eq]
  exact recover_move hε _ _ _

lemma estimate_exact (hε : 0 < p.ε) (k : ℕ)
    (hd : ‖raw g s k - anchor g s k‖ ≤ 3 * radius p k) :
    estimate g s k = raw g s k := by
  rw [estimate_eq]
  apply recover_exact hε _ hd
  exact congruent_aggregate p k _

lemma parent_drift (F : Point p → ℝ)
    (hlip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 < p.L) (hε : 0 < p.ε) {k : ℕ} (hk : k < rounds p) (hk₀ : k ≠ 0) :
    ‖gradient F (point g s k) - gradient F (point g s ((schedule p).pred k))‖ ≤ radius p k := by
  have hpos : (schedule p).pos k = k := Nat.mod_eq_of_lt hk
  have hn : (schedule p).pos k ≠ 0 := by rwa [hpos]
  have hd := point_drift g s hL hε ((schedule p).pred_lt hn).le
  have h := (hlip _ _).trans (mul_le_mul_of_nonneg_left hd hL.le)
  rw [(schedule p).sub_pred hn, Nat.cast_pow, Nat.cast_ofNat] at h
  unfold radius exponent
  rw [ite_eq_right hk₀]
  convert h using 1
  field_simp

lemma parent_anchor {k : ℕ} (hk : k < rounds p) (hk₀ : k ≠ 0) :
    anchor g s k = estimate g s ((schedule p).pred k) := by
  have hpos : (schedule p).pos k = k := Nat.mod_eq_of_lt hk
  have hn : (schedule p).pos k ≠ 0 := by rwa [hpos]
  simp only [anchor, ite_eq_right hk₀]
  exact history_eq g s ((schedule p).pred_lt hn)

end LongTails.Proofs.MultiscaleAggregateTrajectory
