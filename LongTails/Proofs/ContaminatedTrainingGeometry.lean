import LongTails.Proofs.ContaminatedParallelFailures
import LongTails.Proofs.ContaminatedTreeMass
import LongTails.Proofs.LeonTreeError

namespace LongTails.Proofs.ContaminatedTrainingGeometry

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (resolution radius height spacing iterations)
open LongTails.Algorithms
open ContaminatedParallelHistory ContaminatedParallelTrajectory ContaminatedParallelObservations
open ContaminatedParallelFailures ContaminatedTreeTracking LeonBlocks LeonBlockCover
open scoped Classical

variable {p : Params}
noncomputable abbrev level (p : Params) (t : ℕ) := (levels (height (network p)))[t]?.getD 0
noncomputable abbrev model (D : Data p) (s : Samples p) (t : ℕ) := state p D.g (trainOp p) s t
noncomputable abbrev x (D : Data p) (s : Samples p) (t : ℕ) := (model D s t).training.point
noncomputable def v (D : Data p) (s : Samples p) (t : ℕ) :=
  decoded (ContaminatedParallelTrajectory.read p D.g s (used p (trainOp p) t) (model D s t) (trainOp p t))
noncomputable abbrev err (D : Data p) (s : Samples p) (t : ℕ) := ‖v D s t - D.G (x D s t)‖
noncomputable def failed (D : Data p) (s : Samples p) (t : ℕ) := decide (s ∈ bad D (trainOp p) t)

lemma step (D : Data p) (s : Samples p) (t : ℕ) :
    (model D s (t+1)).training = LeonTrajectory.applyEstimate (network p)
      (model D s t).training (level p t) (v D s t) := rfl

lemma one_move (D : Data p) (s : Samples p) (t : ℕ) :
    ‖x D s (t+1) - x D s t‖ ≤ if level p t = 0 then resolution (network p)/p.L else 0 := by
  unfold x
  rw [step]
  unfold LeonTrajectory.applyEstimate
  split_ifs
  · exact ParameterFreeNsgdmRun.normalized_move_norm _ (div_nonneg
      (LeonBatchTuning.resolution_pos _ D.valid.2.2.2.1).le D.valid.2.1.le) _ _
  · simp

lemma slot_step (D : Data p) (s : Samples p) (t j : ℕ) (hne : j ≠ level p t) :
    (model D s (t+1)).training.anchors j = (model D s t).training.anchors j := by
  rw [step]
  unfold LeonTrajectory.applyEstimate
  split_ifs <;> simp [Function.update_of_ne hne]

lemma child_geometry (D : Data p) (s : Samples p) (t j : ℕ) (i : Fin 4)
    (ha : Aligned (level p) t (levels (j+1))) :
    (model D s (child j t i)).training.anchors (j+1) = v D s t ∧
      ‖D.G (x D s (child j t i)) - D.G (x D s t)‖ ≤ 3*4^j*resolution (network p) := by
  let pre := copies (levels j) i.val
  have hp : Aligned (level p) (t+1) pre := (child_alignment ha i.isLt).1
  have hset : (model D s (t+1)).training.anchors (j+1) = v D s t ∧ x D s (t+1) = x D s t := by
    unfold x
    rw [step]
    simp [LeonTrajectory.applyEstimate,(children ha).1]
  have hne : j+1 ∉ pre := fun h => Nat.not_succ_le_self j (level_le j _ (copies_mem _ _ _ h))
  have hanch := slot_constant (fun t => (model D s t).training.anchors) (level p)
    (slot_step D s) (j+1) pre (t+1) hp hne
  have hmove (i : ℕ) : ‖D.G (x D s (i+1)) - D.G (x D s i)‖ ≤
      if level p i = 0 then resolution (network p) else 0 := by
    apply (D.smooth _ _).trans
    have hh := mul_le_mul_of_nonneg_left (one_move D s i) D.valid.2.1.le
    split_ifs at hh ⊢ <;> simpa [D.valid.2.1.ne', mul_comm p.L] using hh
  have hd := leaf_drift (fun i => D.G (x D s i)) (level p) hmove pre (t+1) hp
  dsimp only [pre] at hanch hd
  rw [copies_len] at hanch hd
  rw [copies_count,LeonCalendar.leaf_count,hset.2] at hd
  refine ⟨hanch.trans hset.1,hd.trans ?_⟩
  push_cast
  gcongr
  · exact (LeonBatchTuning.resolution_pos _ D.valid.2.2.2.1).le
  exact_mod_cast (show i.val ≤ 3 by omega)

lemma decode_accurate (D : Data p) (o : ℕ → Operation) (s : Samples p) (t : ℕ)
    (hb : s ∉ bad D o t)
    (ha : ‖reference p (state p D.g o s t) (o t) - D.G (location p (state p D.g o s t) (o t))‖ +
      2 * resolution (network p) ≤ radius (network p) (o t).level) :
    ‖decoded (ContaminatedParallelTrajectory.read p D.g s (used p o t) (state p D.g o s t) (o t)) -
      D.G (location p (state p D.g o s t) (o t))‖ ≤ 2 * resolution (network p) := by
  let r := ContaminatedParallelTrajectory.read p D.g s (used p o t) (state p D.g o s t) (o t)
  let a := reference p (state p D.g o s t) (o t)
  let g := D.G (location p (state p D.g o s t) (o t))
  let y := Algorithms.LeonAggregate.displacement p.n (spacing (network p)) (rawCodes r)
  have hr : ‖a+y-g‖ ≤ 2*resolution (network p) := by
    have h := rounding_error p D.valid.2.2.2.1 D.g D.f (used p o t) (state p D.g o s t) (o t) s
    change ¬ resolution (network p) < noise p D.g D.f (used p o t) (state p D.g o s t) (o t) s at hb
    have hn := le_of_not_gt hb
    change noise p D.g D.f (used p o t) (state p D.g o s t) (o t) s ≤ resolution (network p) at hn
    exact h.trans (by linarith only [hn])
  have hy : ‖y‖ ≤ radius (network p) (o t).level := by
    have he : y = (a+y-g) - (a-g) := by abel
    calc
      ‖y‖ = ‖(a+y-g)-(a-g)‖ := congrArg norm he
      _ ≤ ‖a+y-g‖ + ‖a-g‖ := norm_sub_le _ _
      _ ≤ _ := by change ‖a-g‖ + _ ≤ _ at ha; linarith only [ha,hr]
  have hd := LeonPrecision.exact_small (network p) D.valid.2.2.2.1 (o t).level a
    (rawCodes r) (rawCodes r) (fun _ => rfl) hy
  change ‖decoded r-g‖ ≤ _
  change decoded r = a+y at hd
  rwa [hd]

end LongTails.Proofs.ContaminatedTrainingGeometry
