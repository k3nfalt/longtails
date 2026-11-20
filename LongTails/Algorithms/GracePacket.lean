import LongTails.Algorithms.DistributedBatchedSgd

namespace LongTails.Algorithms.GracePacket

open DistributedQuantization

def wordWidth (w B : ℕ) := w + Nat.size B

noncomputable def word (q z : ℕ) : List Bool :=
  encode (d := 1) (width := q) (fun _ => Fin.ofNat (2 ^ q) z)

noncomputable def readWord (q : ℕ) (bits : List Bool) : ℕ :=
  (decode 1 q (bits.take q) 0).val

def partialIndex {ι : Type*} {d w : ℕ} (S : Finset ι) (batch : ι → ℕ)
    (grid : ι → Grid d w) (j : Fin d) : ℕ :=
  ∑ i ∈ S, batch i * (grid i j).val

def limbWidth (B : ℕ) := DistributedTemplate.clockBits + Nat.size B

def limbCount (w t : ℕ) := w / t + 1

def limb (t z l : ℕ) : Fin (2 ^ t) :=
  ⟨z / (2 ^ t) ^ l % (2 ^ t), Nat.mod_lt _ (by positivity)⟩

def assemble (t F : ℕ) (digits : ℕ → ℕ) :=
  ∑ l ∈ Finset.range F, (2 ^ t) ^ l * digits l

noncomputable def meanFromIndices {d : ℕ} (w B : ℕ) (spacing : ℝ) (z : Fin d → ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => spacing * ((z j : ℝ) / B - ((2 ^ w - 1 : ℕ) : ℝ) / 2))

end LongTails.Algorithms.GracePacket
