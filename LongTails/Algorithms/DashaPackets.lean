import LongTails.Algorithms.DashaCyclic

namespace LongTails.Algorithms.DashaPackets

open DashaCyclic

noncomputable def packetEquiv (precision exponentWidth : ℕ) :
    DashaFloat.Packet precision exponentWidth ≃ Fin (2 ^ (precision + exponentWidth + 3)) :=
  Fintype.equivOfCardEq (by simp [DashaFloat.Packet, pow_add]; ring)

noncomputable def message {d : ℕ+} (k : Fin d) (precision exponentWidth : ℕ) (ρ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (seed : Seed d) : List Bool :=
  DistributedQuantization.encode (fun j : Fin (k.val + 1) =>
    packetEquiv precision exponentWidth (DashaFloat.packet precision exponentWidth
      (multiplier k * x (coordinate k seed.1 j) / ρ) (seed.2 (coordinate k seed.1 j))))

noncomputable def receive {d : ℕ+} (k shift : Fin d) (precision exponentWidth : ℕ)
    (bits : List Bool) : Fin d → ℤ := fun j =>
  if h : selected k shift j then
    DashaFloat.value ((packetEquiv precision exponentWidth).symm
      (DistributedQuantization.decode (k.val + 1) (precision + exponentWidth + 3)
        (bits.take ((k.val + 1) * (precision + exponentWidth + 3))) ⟨(j - shift).val, h⟩))
  else 0

end LongTails.Algorithms.DashaPackets
