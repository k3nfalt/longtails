import LongTails.Algorithms.MultirateSchedule
import LongTails.Proofs.LeonCalendar
import LongTails.Proofs.LeonRoundTrace

namespace LongTails.Proofs.MultirateTrajectory

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms
open MultirateSchedule

def wire (bits : List Bool) := bits ++ List.replicate clockBits false

structure Snapshot (p : Params) where
  model : Model p
  past : ℕ → Point p

noncomputable def values (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (i : Fin p.n) (j : ℕ) (x : Point p) : List (Point p) :=
  (List.range (batch p i)).map (fun u => g i x (s i (j * (batch p i : ℕ) + u)))

noncomputable def source (p : Params) (v : Snapshot p) (i : Fin p.n) (j : ℕ) : Point p :=
  if j = 0 then p.x0 else v.past (anchor p i j)

noncomputable def data (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (v : Snapshot p) (k : ℕ) : Table p := fun i =>
  let j := block p i k
  wire (packet p (values p g s i j (source p v i j)))

noncomputable def trajectory (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) : ℕ → Snapshot p
  | 0 => ⟨LeonTrajectory.initial (network p), fun _ => p.x0⟩
  | k+1 =>
    let v := trajectory p g s k
    ⟨update p v.model (data p g s v k), Function.update v.past k v.model.point⟩

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

noncomputable abbrev modelAt (k : ℕ) := (trajectory p g s k).model
noncomputable abbrev x (k : ℕ) := (modelAt g s k).point
noncomputable abbrev packets (k : ℕ) := data p g s (trajectory p g s k) k
noncomputable abbrev v (k : ℕ) := estimate p (packets g s k)

lemma past_eq {t k : ℕ} (hk : k < t) : (trajectory p g s t).past k = x g s k := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases he : k = t
    · subst k; simp [trajectory]
    · simpa [trajectory, Function.update_of_ne he] using ih (by omega)

lemma anchor_bounds (i : Fin p.n) (k : ℕ) :
    anchor p i (block p i k) ≤ k ∧ k < anchor p i (block p i k) + 2 * (period p i : ℕ) := by
  let m : ℕ := period p i
  have hm : 0 < m := (period p i).pos
  have hr := Nat.mod_lt k hm
  have he := Nat.mod_add_div k m
  change (k / m - 1) * m ≤ k ∧ k < (k / m - 1) * m + 2 * m
  rw [Nat.mul_comm m] at he
  cases hj : k / m with
  | zero => simp [hj] at he ⊢; omega
  | succ j => simp [hj, Nat.succ_mul] at he ⊢; omega

lemma anchor_lt (i : Fin p.n) (k : ℕ) (hk : block p i k ≠ 0) :
    anchor p i (block p i k) < k := by
  let m : ℕ := period p i
  have hm : 0 < m := (period p i).pos
  have hb : (k / m - 1) < k / m := Nat.sub_lt (Nat.pos_of_ne_zero hk) Nat.zero_lt_one
  exact (Nat.mul_lt_mul_of_pos_right hb hm).trans_le (Nat.div_mul_le_self k m)

lemma source_eq (i : Fin p.n) (k : ℕ) :
    source p (trajectory p g s k) i (block p i k) = x g s (anchor p i (block p i k)) := by
  by_cases he : block p i k = 0
  · simp [he,source,anchor,x,modelAt,trajectory,LeonTrajectory.initial]
  · simp [source,he,past_eq g s (anchor_lt i k he)]

lemma x_step (k : ℕ) :
    x g s (k+1) = x g s k - (δ p / smoothness p / ‖v g s k‖) • v g s k := by
  simp [x,modelAt,trajectory,update,LeonTrajectory.applyEstimate,v,packets]

lemma source_age (i : Fin p.n) (k : ℕ) :
    k - anchor p i (block p i k) ≤ 2 * (period p i : ℕ) := by
  obtain ⟨_,hu⟩ := anchor_bounds (p := p) i k
  omega

end LongTails.Proofs.MultirateTrajectory
