import LongTails.Algorithms.DashaQuantization

namespace LongTails.Algorithms.DashaModular

def modulus (width : ℕ) : ℤ := (2 ^ width : ℕ)

def residue (width : ℕ) (z : ℤ) : Fin (2 ^ width) :=
  ⟨(z % modulus width).toNat, by
    have hp : 0 < modulus width := by unfold modulus; positivity
    have hl := Int.emod_nonneg z (ne_of_gt hp)
    have hu := Int.emod_lt_of_pos z hp
    unfold modulus at *
    omega⟩

def restore (width : ℕ) (z : ℤ) : ℤ :=
  (z + DashaQuantization.center width) % modulus width - DashaQuantization.center width

noncomputable def encode (d width : ℕ) (z : Fin d → ℤ) : List Bool :=
  DistributedQuantization.encode (fun i => residue width (z i))

noncomputable def decode (d width : ℕ) (bits : List Bool) : Fin d → ℤ :=
  fun i => (DistributedQuantization.decode d width (bits.take (d * width)) i).val

end LongTails.Algorithms.DashaModular
