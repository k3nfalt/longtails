import LongTails.Algorithms.SilverSchedule
import LongTails.Setups.SmoothHessianLipschitzGd

namespace LongTails.Algorithms.AdaptiveSilverGd

open OracleTemplate
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.SilverSchedule

def good (p : Params) : Prop := 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * 2) ≤ p.L ^ 4

lemma levelCap_exists (y : ℝ) : ∃ k : ℕ, y ≤ ratio ^ k := by
  have h : 1 < ratio := by
    unfold ratio
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt y h
  exact ⟨k, hk.le⟩

open Classical in
noncomputable def levelCap (p : Params) : ℕ :=
  Nat.find (levelCap_exists (50 * p.L * p.Δ / p.ε ^ 2))

open Classical in
noncomputable def levelRaw (p : Params) : ℕ :=
  Nat.findGreatest (fun k => 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * k) ≤ p.L ^ 4) (levelCap p)

noncomputable def level (p : Params) : ℕ := max 2 (levelRaw p)

noncomputable def blockLength (p : Params) : ℕ := (steps (level p)).length

noncomputable def blockSum (p : Params) : ℝ := (steps (level p)).sum

open Classical in
noncomputable def threshold (p : Params) : ℝ :=
  if good p then p.ε * max 1 (Real.sqrt (blockSum p / (25 * blockLength p))) else p.ε

noncomputable def abortThreshold (p : Params) : ℝ :=
  Real.sqrt (4 * blockLength p + 2) * threshold p

noncomputable def silverStep (p : Params) (i : ℕ) : ℝ :=
  (steps (level p)).getD (i % blockLength p) 1 / p.L

open Classical in
noncomputable def rule (p : Params) (phase : ℕ) (r : p.E) : ℝ × ℕ :=
  if phase = 0 then
    if threshold p < ‖r‖ then (1 / p.L, 0) else (silverStep p 0, 1)
  else if abortThreshold p < ‖r‖ then (1 / p.L, 0)
  else (silverStep p phase, if phase + 1 < 2 * blockLength p then phase + 1 else 0)

structure State (E : Type*) where
  point : E
  phase : ℕ
  count : ℕ
  best : E
  bestNorm : ℝ

noncomputable def method (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := ⟨p.x0, 0, 0, p.x0, 0⟩
  query s := (0, s.point)
  update s reply :=
    ⟨s.point - (rule p s.phase reply).1 • reply, (rule p s.phase reply).2, s.count + 1,
      if s.count = 0 ∨ ‖reply‖ ^ 2 ≤ s.bestNorm then s.point else s.best,
      if s.count = 0 ∨ ‖reply‖ ^ 2 ≤ s.bestNorm then ‖reply‖ ^ 2 else s.bestNorm⟩
  output s := s.best

end LongTails.Algorithms.AdaptiveSilverGd
