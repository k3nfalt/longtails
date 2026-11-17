import LongTails.Algorithms.DashaPackets
import LongTails.Proofs.DashaCyclic
import LongTails.Proofs.DashaFloat
import LongTails.Proofs.DistributedQuantization

namespace LongTails.Proofs.DashaPackets

open LongTails.Algorithms.DashaCyclic
open LongTails.Algorithms.DashaPackets

lemma coordinate_inverse {d : ℕ+} (k shift j : Fin d) (h : selected k shift j) :
    coordinate k shift ⟨(j - shift).val, h⟩ = j := by
  have he : Fin.castLE (Nat.succ_le_of_lt k.isLt) (⟨(j - shift).val, h⟩ : Fin (k.val + 1)) = j - shift := by
    apply Fin.ext
    rfl
  rw [coordinate, he]
  simp [sub_eq_add_neg, ← add_assoc]

lemma message_length {d : ℕ+} (k : Fin d) (r w : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (seed : Seed d) :
    (message k r w ρ x seed).length = (k.val + 1) * (r + w + 3) :=
  DistributedQuantization.encode_length _

lemma receive_message {d : ℕ+} (k : Fin d) (r w : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (seed : Seed d) (suffix : List Bool)
    (he : ∀ j, LongTails.Algorithms.DashaFloat.exponent r (multiplier k * x j / ρ) < 2 ^ w) :
    receive k seed.1 r w (message k r w ρ x seed ++ suffix) = compressedIndex k seed.1 r ρ x seed.2 := by
  funext j
  unfold receive
  rw [← message_length k r w ρ x seed, List.take_left]
  unfold message
  rw [DistributedQuantization.decode_encode]
  by_cases h : selected k seed.1 j
  · simp only [h, dite_true, compressedIndex, ite_true, Equiv.symm_apply_apply]
    rw [coordinate_inverse k seed.1 j h]
    exact DashaFloat.value_packet r w _ _ (he j)
  · simp [h, compressedIndex]

end LongTails.Proofs.DashaPackets
