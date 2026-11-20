import LongTails.Algorithms.GraceSgd
import LongTails.Proofs.GraceBatchTuning
import LongTails.Proofs.GracePacket

namespace LongTails.Proofs.GraceSgdTrajectory

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceBatch GracePacket GraceSgd
open DistributedQuantization (Grid)

variable {p : Params} {S : Finset (Fin p.n)}

noncomputable def familyTuning (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (hL : 0 < p.L)
    (hε : 0 < p.ε) : SgdTuning p where
  K := (tuning p S).iterations
  batch := batches p S
  positiveBatch := by
    change 0 < DistributedBatchedSgd.totalBatch (statistical p) (tuning p S)
    rw [(GraceBatchTuning.total_and_worker_time hS hh).1]
    exact Nat.zero_lt_one.trans_le (le_max_left 1 _)
  η := 1 / (2 * p.L)
  positiveStep := by positivity
  width := (tuning p S).width
  radius := DistributedBatchedSgd.radius (statistical p)
  positiveRadius := DistributedBatchedSgd.radius_pos (p := statistical p) (mul_nonneg (by norm_num) hL.le) hε

lemma quantized_map (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (hL : 0 < p.L) (hε : 0 < p.ε)
    (x v : Point p) :
    (familyTuning hS hh hL hε).quantize x v = DistributedBatchedSgd.decode (statistical p)
      (tuning p S) x (DistributedBatchedSgd.encode (statistical p) (tuning p S) x v) := by
  rw [DistributedBatchedSgd.decode_encode]
  unfold Algorithms.DistributedBatchedSgd.encode
  rw [DistributedQuantization.receive_message]
  rfl

lemma family_iterate (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (hL : 0 < p.L) (hε : 0 < p.ε)
    (g : Point p → p.Ω → Point p) (s : Samples p) (k : ℕ) :
    (familyTuning hS hh hL hε).iterate g s k =
      DistributedBatchedSgd.trajectory (statistical p) (tuning p S) (fun _ => g) s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [SgdTuning.iterate, DistributedBatchedSgd.trajectory, ih]
    simp only [quantized_map, DistributedBatchedSgd.estimate]
    rfl

lemma indices_at {d w : ℕ} (t : ℕ) (z : Grid d w) (j : Fin d) (l : ℕ)
    (hl : l < limbCount w t) :
    indices t z (j.val * limbCount w t + l) = (limb t (z j).val l).val := by
  have hF : 0 < limbCount w t := by simp [limbCount]
  have hdiv : (j.val * limbCount w t + l) / limbCount w t = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hF, Nat.div_eq_of_lt hl, Nat.zero_add]
  have hmod : (j.val * limbCount w t + l) % limbCount w t = l := by simp [Nat.add_mod, Nat.mod_eq_of_lt hl]
  simp [indices, hdiv, hmod, j.isLt]

lemma assembled_indices {d w : ℕ} (t : ℕ) (ht : 0 < t) (z : Grid d w) (j : Fin d) :
    assembled t w (indices t z) j = (z j).val := by
  unfold assembled
  have h := GracePacket.assemble_exact t (z j).val (limbCount w t)
    ((z j).isLt.trans_le (by rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) (GracePacket.limb_capacity w t ht).1))
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro l hl
  exact congrArg (_ * ·) (indices_at t z j l (Finset.mem_range.mp hl))

lemma assembled_total {d w : ℕ} (t : ℕ) (ht : 0 < t) {ι : Type*} (s : Finset ι)
    (b : ι → ℕ) (z : ι → Grid d w) (j : Fin d) :
    assembled t w (fun x => ∑ i ∈ s, b i * indices t (z i) x) j =
      partialIndex s b z j := by
  refine Eq.trans ?_ (GracePacket.assemble_partial s b z t ht j)
  unfold assembled assemble partialIndex
  apply Finset.sum_congr rfl
  intro l hl
  apply congrArg ((2 ^ t) ^ l * ·)
  dsimp only
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (b i * ·) (indices_at t (z i) j l (Finset.mem_range.mp hl))

end LongTails.Proofs.GraceSgdTrajectory
