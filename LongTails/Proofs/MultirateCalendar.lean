import LongTails.Proofs.MultirateTrajectory
import LongTails.Proofs.MultirateService
import LongTails.Proofs.LeonConfiguredSchedule

namespace LongTails.Proofs.MultirateCalendar

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms.MultirateSchedule
open MultirateTrajectory
open LeonReservations (Frame posted consumed usedCount)

variable {p : Params}

noncomputable def stamp (p : Params) (k : ℕ) : Time :=
  Finset.univ.sup (service p) + k * tick p

noncomputable def countBefore (p : Params) (i : Fin p.n) (k : ℕ) : ℕ :=
  if k = 0 then 0 else block p i (k-1) + 1

noncomputable def issued (p : Params) (i : Fin p.n) (k : ℕ) : ℕ :=
  min (countBefore p i (K p)) (countBefore p i k + 1)

noncomputable def enter (p : Params) (i : Fin p.n) (k : ℕ) : Time :=
  stamp p (min (K p) (countBefore p i k * (period p i : ℕ)))

lemma K_pos (p : Params) : 0 < K p := by change 0 < 4 ^ _; positivity

lemma stamp_mono : Monotone (stamp p) := by intro a b h; unfold stamp; gcongr
lemma stamp_strict (ht : 0 < tick p) : StrictMono (stamp p) := by
  intro a b h
  unfold stamp
  exact add_lt_add_right (mul_lt_mul_of_pos_right (by exact_mod_cast h) ht) _

lemma before_succ (i : Fin p.n) (k : ℕ) : countBefore p i (k+1) = block p i k + 1 := by
  simp [countBefore]

lemma before_eq (i : Fin p.n) (k : ℕ) :
    countBefore p i k = block p i k + if k % (period p i : ℕ) = 0 then 0 else 1 := by
  cases k with
  | zero => simp [block,countBefore]
  | succ k =>
    rw [before_succ]
    dsimp [block]
    by_cases h : (k+1) % (period p i : ℕ) = 0
    · simp [h,Nat.succ_div_of_mod_eq_zero h]
    · simp [h,Nat.succ_div_of_mod_ne_zero h]

lemma before_bounds (i : Fin p.n) (k : ℕ) :
    k ≤ countBefore p i k * (period p i : ℕ) ∧
      countBefore p i k * (period p i : ℕ) < k + (period p i : ℕ) := by
  rw [before_eq]
  have ht := Nat.div_add_mod' k (period p i)
  have hm := Nat.mod_lt k (period p i).pos
  unfold block
  split_ifs <;> simp_all only [Nat.add_zero, Nat.add_one_mul] <;> omega

lemma before_mono (i : Fin p.n) : Monotone (countBefore p i) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [before_eq i k,before_succ]
  split_ifs <;> omega

lemma issued_zero (i : Fin p.n) : issued p i 0 = 1 := by
  simp [issued,countBefore,(K_pos p).ne']

lemma due_mul (i : Fin p.n) (k : ℕ) (h : k % (period p i : ℕ) = 0) :
    block p i k * (period p i : ℕ) = k := by
  simpa [block,h] using Nat.div_add_mod' k (period p i)

lemma next_count (i : Fin p.n) (k : ℕ) : countBefore p i (k+1) = countBefore p i k +
    if k % (period p i : ℕ) = 0 then 1 else 0 := by
  rw [before_eq i k,before_succ]
  split_ifs <;> omega

lemma next_issued (i : Fin p.n) (k : ℕ) :
    issued p i (k+1) = issued p i k +
      if k % (period p i : ℕ) = 0 ∧ k + period p i < K p then 1 else 0 := by
  rw [issued,issued,next_count]
  by_cases h : k % (period p i : ℕ) = 0
  · rw [ite_eq_left h]
    have he := due_mul (p := p) i k h
    have hn : countBefore p i k = block p i k := by simp [before_eq i k,h]
    rw [hn]
    have hlt : block p i k + 1 < countBefore p i (K p) ↔ k + period p i < K p := by
      have hb := before_bounds (p := p) i (K p)
      have hp := (period p i).pos
      have hx : (block p i k + 1) * (period p i : ℕ) = k + period p i := by rw [Nat.add_one_mul,he]
      constructor
      · intro hle
        have hl := Nat.mul_le_mul_right (period p i : ℕ) hle
        rw [Nat.succ_mul,hx] at hl
        omega
      · intro hk
        by_contra hn
        have hl := Nat.mul_le_mul_right (period p i : ℕ) (Nat.le_of_not_gt hn)
        omega
    split_ifs <;> omega
  · simp [h]

lemma issued_launch (i : Fin p.n) (k : ℕ) (hk : k % (period p i : ℕ) = 0 ∧ k + period p i < K p) :
    issued p i k = block p i k + 1 := by
  have hh := next_issued (p := p) i k
  rw [ite_eq_left hk] at hh
  have hb := Nat.min_le_left (countBefore p i (K p)) (countBefore p i (k+1)+1)
  change issued p i (k+1) ≤ _ at hb
  unfold issued at hh ⊢
  rw [before_eq i k, ite_eq_left hk.1, Nat.add_zero] at *
  omega

end LongTails.Proofs.MultirateCalendar
