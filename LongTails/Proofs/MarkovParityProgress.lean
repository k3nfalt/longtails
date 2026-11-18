import Mathlib.Tactic

namespace LongTails.Proofs.MarkovParityProgress

abbrev Color := Option Bool

def accepts (r : Nat) (z : Color) : Bool := z == some (decide (r % 2 = 1))

def progress (z : Nat → Color) : Nat → Nat
  | 0 => 0
  | t + 1 => progress z t + if accepts (progress z t) (z t) then 1 else 0

def entries (z : Nat → Color) : Nat → Nat
  | 0 => 0
  | t + 1 => entries z t +
      if (z t).isSome && (t == 0 || z t != z (t - 1)) then 1 else 0

lemma matches_succ {r : Nat} {z : Color} (h : accepts r z = true) :
    accepts (r + 1) z = false := by
  simp only [accepts, beq_iff_eq] at h
  subst z
  simp only [accepts, Option.some_beq_some]
  by_cases hr : r % 2 = 1
  · simp [hr, show (r + 1) % 2 ≠ 1 by omega]
  · simp [hr, show (r + 1) % 2 = 1 by omega]

lemma progress_mono (z : Nat → Color) {s t : Nat} (h : s ≤ t) : progress z s ≤ progress z t := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

lemma consumed (z : Nat → Color) (t : Nat) :
    accepts (progress z (t + 1)) (z t) = false := by
  by_cases h : accepts (progress z t) (z t) = true
  · simpa only [progress, h, ↓reduceIte] using matches_succ h
  · simp [progress, h]

lemma progress_le_entries (z : Nat → Color) (t : Nat) :
    progress z t ≤ entries z t := by
  induction t with
  | zero => exact Nat.le_refl 0
  | succ t ih =>
    rw [progress, entries]
    apply Nat.add_le_add ih
    by_cases h : accepts (progress z t) (z t) = true
    · have hs : (z t).isSome = true := by
        cases hz : z t <;> simp_all [accepts]
      cases t with
      | zero => simp [h, hs]
      | succ t =>
        have hd : z (t + 1) ≠ z t := by
          intro he
          rw [he, consumed] at h
          contradiction
        simp [h, hs, hd]
    · simp [h]

end LongTails.Proofs.MarkovParityProgress
