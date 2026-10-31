import LongTails.Algorithms.SilverSchedule
import LongTails.Setups.SmoothWeaklyConvex

namespace LongTails.Algorithms.WeaklyConvexSilver

open OracleTemplate
open LongTails.Setups.SmoothWeaklyConvex
open LongTails.Algorithms.SilverSchedule

lemma levelCap_exists (y : ℝ) : ∃ k : ℕ, y ≤ ratio ^ k := by
  have h : 1 < ratio := by
    unfold ratio
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt y h
  exact ⟨k, hk.le⟩

open Classical in
noncomputable def levelCap (p : Params) : ℕ :=
  Nat.find (levelCap_exists (4 * p.L * p.Δ / p.ε ^ 2))

open Classical in
noncomputable def levelRaw (p : Params) : ℕ :=
  Nat.findGreatest (fun k => 250000 * p.ρ * (7 / 2) ^ k ≤ p.L) (levelCap p)

noncomputable def level (p : Params) : ℕ :=
  max 1 (levelRaw p)

noncomputable def stepSize (p : Params) (t : ℕ) : ℝ :=
  (steps (level p)).getD (t % (steps (level p)).length) 1 / p.L

structure State (E : Type*) where
  point : E
  count : ℕ
  best : E
  bestNorm : ℝ

noncomputable def method (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := ⟨p.x0, 0, p.x0, 0⟩
  query s := (0, s.point)
  update s reply :=
    ⟨s.point - stepSize p s.count • reply, s.count + 1,
      if s.count = 0 ∨ ‖reply‖ ^ 2 ≤ s.bestNorm then s.point else s.best,
      if s.count = 0 ∨ ‖reply‖ ^ 2 ≤ s.bestNorm then ‖reply‖ ^ 2 else s.bestNorm⟩
  output s := s.best

end LongTails.Algorithms.WeaklyConvexSilver
