import LongTails.Algorithms.DashaModular
import LongTails.Proofs.DistributedQuantization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LongTails.Proofs.DashaModular

open LongTails.Algorithms.DashaModular
open LongTails.Algorithms.DashaQuantization

lemma residue_val (width : ℕ) (z : ℤ) :
    ((residue width z).val : ℤ) = z % modulus width := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by unfold modulus; positivity))

lemma restore_mod (width : ℕ) (z : ℤ) :
    restore width (z % modulus width) = restore width z := by
  simp only [restore, Int.add_emod, Int.emod_emod]

lemma restore_exact (width : ℕ) (z : ℤ)
    (hlo : -(center width : ℤ) ≤ z)
    (hhi : z + center width < modulus width) :
    restore width z = z := by
  unfold restore
  rw [Int.emod_eq_of_lt (by omega) hhi]
  omega

lemma encode_length (d width : ℕ) (z : Fin d → ℤ) :
    (LongTails.Algorithms.DashaModular.encode d width z).length = d * width :=
  LongTails.Proofs.DistributedQuantization.encode_length _

lemma decode_encode (d width : ℕ) (z : Fin d → ℤ) (suffix : List Bool) :
    LongTails.Algorithms.DashaModular.decode d width
      (LongTails.Algorithms.DashaModular.encode d width z ++ suffix) =
      fun i => z i % modulus width := by
  have hlen := encode_length d width z
  funext i
  simp only [LongTails.Algorithms.DashaModular.decode, ← hlen, List.take_left,
    LongTails.Algorithms.DashaModular.encode,
    LongTails.Proofs.DistributedQuantization.decode_encode]
  exact residue_val width (z i)

lemma sum_residue_mod {ι : Type*} (s : Finset ι) (width : ℕ) (z : ι → ℤ) :
    (∑ i ∈ s, z i % modulus width) % modulus width = (∑ i ∈ s, z i) % modulus width := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Int.add_emod, Int.emod_emod, ih]

lemma restore_sum_residues {ι : Type*} (s : Finset ι) (width : ℕ) (z : ι → ℤ)
    (hlo : -(center width : ℤ) ≤ ∑ i ∈ s, z i)
    (hhi : (∑ i ∈ s, z i) + center width < modulus width) :
    restore width (∑ i ∈ s, z i % modulus width) = ∑ i ∈ s, z i := by
  rw [← restore_mod, sum_residue_mod, restore_mod]
  exact restore_exact width _ hlo hhi

lemma decoded_sum_exact {ι : Type*} (s : Finset ι) (d width : ℕ)
    (z : ι → Fin d → ℤ) (suffix : ι → List Bool)
    (hlo : ∀ j, -(center width : ℤ) ≤ ∑ i ∈ s, z i j)
    (hhi : ∀ j, (∑ i ∈ s, z i j) + center width < modulus width) :
    (fun j => restore width (∑ i ∈ s, LongTails.Algorithms.DashaModular.decode d width
      (LongTails.Algorithms.DashaModular.encode d width (z i) ++ suffix i) j)) =
      fun j => ∑ i ∈ s, z i j := by
  funext j
  simp only [decode_encode]
  exact restore_sum_residues s width (fun i => z i j) (hlo j) (hhi j)

end LongTails.Proofs.DashaModular
