import LongTails.Algorithms.MultiscaleAggregateProtocol
import LongTails.Proofs.DashaModular
import LongTails.Proofs.DashaQuantization
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Size

namespace LongTails.Proofs.MultiscaleAggregateCodec

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate
open LongTails.Algorithms.DashaModular (modulus)

lemma precision_pos {p : Params} (h : 0 < p.ε) : 0 < precision p := by
  unfold precision
  positivity

lemma aggregateSpacing_pos {p : Params} (h : 0 < p.ε) : 0 < aggregateSpacing p := by
  have := precision_pos h
  unfold aggregateSpacing spacing
  positivity

lemma period_large {p : Params} (h : 0 < p.ε) (k : ℕ) :
    6 * radius p k < aggregateSpacing p * (modulus (width p k) : ℝ) := by
  have hd := precision_pos h
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hs : ((p.n : ℕ) * (p.d + 1) : ℕ) < 2 ^ Nat.size ((p.n : ℕ) * (p.d + 1)) :=
    Nat.lt_size_self _
  have hs' : (p.n : ℝ) * (p.d + 1) < (2 : ℝ) ^ Nat.size ((p.n : ℕ) * (p.d + 1)) := by
    exact_mod_cast hs
  have he : 0 < (2 : ℝ) ^ exponent p k := by positivity
  unfold aggregateSpacing spacing modulus width radius
  push_cast
  rw [pow_add, pow_add]
  have hd' : (0 : ℝ) < p.d + 1 := by positivity
  field_simp
  nlinarith [mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hs' he) hd,
    mul_pos (mul_pos (mul_pos hn hd') he) hd]

lemma recover_move {p : Params} (h : 0 < p.ε) (k : ℕ) (anchor : Point p) (z : Code p) :
    ‖recover p k anchor z - anchor‖ ≤ 3 * radius p k := by
  simp only [recover]
  split
  · rename_i hx
    exact (Classical.choose_spec hx).2
  · have := precision_pos h
    simp only [sub_self, norm_zero, radius]
    positivity

lemma unique_code {p : Params} (h : 0 < p.ε) {k : ℕ} {a b : Code p}
    (hc : congruent (width p k) a b) (hd : ‖unpack p a - unpack p b‖ ≤ 6 * radius p k) :
    a = b := by
  have hs := aggregateSpacing_pos h
  have hsep := period_large h k
  funext j
  have hj := (PiLp.norm_apply_le (unpack p a - unpack p b) j).trans hd
  change |aggregateSpacing p * (a j : ℝ) - aggregateSpacing p * (b j : ℝ)| ≤ _ at hj
  rw [← mul_sub, abs_mul, abs_of_pos hs] at hj
  have hsmall : |(a j : ℝ) - (b j : ℝ)| < (modulus (width p k) : ℝ) :=
    lt_of_mul_lt_mul_left (hj.trans_lt hsep) hs.le
  have hint : |a j - b j| < modulus (width p k) := by exact_mod_cast hsmall
  have hmod : b j ≡ a j [ZMOD modulus (width p k)] := (hc j).symm
  have hdvd := Int.modEq_iff_dvd.mp hmod
  by_contra hne
  have hpos : 0 < |a j - b j| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hdvd' : modulus (width p k) ∣ |a j - b j| := (dvd_abs _ _).mpr hdvd
  exact (not_le_of_gt hint) (Int.le_of_dvd hpos hdvd')

lemma recover_exact {p : Params} (h : 0 < p.ε) {k : ℕ} {a z : Code p} {anchor : Point p}
    (hc : congruent (width p k) a z) (hd : ‖unpack p a - anchor‖ ≤ 3 * radius p k) :
    recover p k anchor z = unpack p a := by
  classical
  have hex : ∃ q, congruent (width p k) q z ∧ ‖unpack p q - anchor‖ ≤ 3 * radius p k :=
    ⟨a, hc, hd⟩
  simp only [recover]
  rw [dite_eq_left hex]
  apply congrArg (unpack p)
  apply unique_code h (fun j => ((Classical.choose_spec hex).1 j).trans (hc j).symm)
  have htri := norm_sub_le_norm_sub_add_norm_sub (unpack p (Classical.choose hex)) anchor (unpack p a)
  rw [norm_sub_rev anchor] at htri
  linarith [(Classical.choose_spec hex).2]

lemma packet_length (p : Params) (k : ℕ) (z : Code p) :
    (packet p k z).length = p.d * width p k := DashaModular.encode_length _ _ _

lemma read_packet (p : Params) (k : ℕ) (z : Code p) (suffix : List Bool) :
    readPacket p k (packet p k z ++ suffix) = fun j => z j % modulus (width p k) :=
  DashaModular.decode_encode _ _ _ _

lemma read_packet_self (p : Params) (k : ℕ) (z : Code p) :
    readPacket p k (packet p k z) = fun j => z j % modulus (width p k) := by
  simpa using read_packet p k z []

lemma congruent_aggregate (p : Params) (k : ℕ) (z : Fin p.n → Code p) :
    congruent (width p k) (∑ i, z i)
      (readPacket p k (packet p k (∑ i, readPacket p k (packet p k (z i))))) := by
  intro j
  simp only [read_packet_self, Finset.sum_apply, Int.emod_emod]
  exact (DashaModular.sum_residue_mod Finset.univ _ (fun i => z i j)).symm

end LongTails.Proofs.MultiscaleAggregateCodec
