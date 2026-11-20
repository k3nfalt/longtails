import LongTails.Algorithms.GracePacket
import LongTails.Proofs.DistributedQuantization

namespace LongTails.Proofs.GracePacket

open LongTails.Algorithms.DistributedQuantization
open LongTails.Algorithms.GracePacket

lemma word_length (q z : ℕ) : (word q z).length = q := by
  simp [word, DistributedQuantization.encode_length]

lemma read_word (q z : ℕ) (hz : z < 2 ^ q) (suffix : List Bool) :
    readWord q (word q z ++ suffix) = z := by
  have ht : (word q z ++ suffix).take q = word q z := by
    conv_lhs => arg 1; rw [← word_length q z]
    exact List.take_left
  rw [readWord, ht, word, DistributedQuantization.decode_encode]
  exact Nat.mod_eq_of_lt hz

lemma partial_index_lt {ι : Type*} {d w B : ℕ} (S : Finset ι) (batch : ι → ℕ)
    (grid : ι → Grid d w) (hB : ∑ i ∈ S, batch i ≤ B) (j : Fin d) :
    partialIndex S batch grid j < 2 ^ wordWidth w B := by
  have hcap : partialIndex S batch grid j ≤ B * 2 ^ w := by
    calc
      _ ≤ ∑ i ∈ S, batch i * 2 ^ w :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (grid i j).isLt.le
      _ ≤ B * 2 ^ w := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ hB
  rw [wordWidth, pow_add, Nat.mul_comm]
  exact lt_of_le_of_lt hcap (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self B) (by positivity))

lemma limb_capacity (w t : ℕ) (ht : 0 < t) :
    w ≤ t * limbCount w t ∧ t * limbCount w t ≤ w + t := by
  rw [limbCount, Nat.mul_add_one, Nat.mul_comm t (w / t)]
  have h := Nat.mod_add_div w t
  rw [Nat.mul_comm t (w / t)] at h
  have hr := Nat.mod_lt w ht
  omega

lemma assemble_exact (t z F : ℕ) (hz : z < (2 ^ t) ^ F) :
    assemble t F (fun l => (limb t z l).val) = z := by
  have h (k : ℕ) : assemble t k (fun l => (limb t z l).val) +
      (2 ^ t) ^ k * (z / (2 ^ t) ^ k) = z := by
    induction k with
    | zero => simp [assemble]
    | succ k ih =>
      unfold assemble at ih ⊢
      simp only [Finset.sum_range_succ, limb, pow_succ, ← Nat.div_div_eq_div_mul]
      rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]
      exact ih
  simpa [Nat.div_eq_of_lt hz] using h F

lemma assemble_partial {ι : Type*} {d w : ℕ} (S : Finset ι) (batch : ι → ℕ)
    (grid : ι → Grid d w) (t : ℕ) (ht : 0 < t) (j : Fin d) :
    assemble t (limbCount w t) (fun l =>
      partialIndex S batch (fun i k => limb t (grid i k).val l) j) =
        partialIndex S batch grid j := by
  unfold assemble partialIndex
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_left_comm _ (batch i), ← Finset.mul_sum]
  congr 1
  apply assemble_exact
  rw [← pow_mul]
  exact (grid i j).isLt.trans_le (Nat.pow_le_pow_right (by decide) (limb_capacity w t ht).1)

lemma reconstruct_mean {ι : Type*} {d w : ℕ} (S : Finset ι) (batch : ι → ℕ)
    (grid : ι → Grid d w) (spacing : ℝ) {B : ℕ} (hpos : 0 < B)
    (htotal : ∑ i ∈ S, batch i = B) :
    meanFromIndices w B spacing (partialIndex S batch grid) =
      ∑ i ∈ S, ((batch i : ℝ) / B) • reconstruct spacing (grid i) := by
  ext j
  let ev := EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin d) j
  change spacing * ((_ : ℝ) / B - _) = ev (∑ i ∈ S, _)
  rw [map_sum]
  have weight : (∑ i ∈ S, (batch i : ℝ)) = B := by exact_mod_cast htotal
  simp only [partialIndex, Nat.cast_sum, Nat.cast_mul, map_smul, smul_eq_mul]
  change spacing * ((∑ i ∈ S, (batch i : ℝ) * (grid i j).val) / B -
    ((2 ^ w - 1 : ℕ) : ℝ) / 2) =
    ∑ i ∈ S, ((batch i : ℝ) / B) * (spacing * (((grid i j).val : ℝ) - _))
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp_rw [show ∀ a z : ℝ, a / B * (spacing * (z - ((2 ^ w - 1 : ℕ) : ℝ) / 2)) =
    (a * z) * (spacing / B) - a * (spacing * ((2 ^ w - 1 : ℕ) : ℝ) / (2 * B))
    by intros; ring]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, weight]
  field_simp

end LongTails.Proofs.GracePacket
