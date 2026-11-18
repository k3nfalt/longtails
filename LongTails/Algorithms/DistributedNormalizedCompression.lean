import LongTails.Algorithms.DistributedRandomRounding

namespace LongTails.Algorithms.DistributedNormalizedCompression

open DistributedQuantization

noncomputable def sparseSample {d : ℕ} (width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) (u : ℝ) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single j (spacing *
    (((DistributedRandomRounding.gridIndex width spacing (d * x j) u).val : ℝ) -
      ((2 ^ width - 1 : ℕ) : ℝ) / 2))

noncomputable def sparseGrid {d : ℕ} (width m : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin m → Fin d) (u : Fin m → ℝ) : Grid m width :=
  fun q => DistributedRandomRounding.gridIndex width spacing (d * x (j q)) (u q)

noncomputable def sparseMessage {d : ℕ} (width m : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin m → Fin d) (u : Fin m → ℝ) : List Bool :=
  encode (sparseGrid width m spacing x j u)

noncomputable def sparseReceive {d : ℕ} (width m : ℕ) (spacing : ℝ)
    (j : Fin m → Fin d) (bits : List Bool) : EuclideanSpace ℝ (Fin d) :=
  let values := reconstruct spacing (decode m width (bits.take (m * width)))
  (m : ℝ)⁻¹ • ∑ q, EuclideanSpace.single (j q) (values q)

noncomputable def fullReceive (d width : ℕ) (spacing : ℝ)
    (bits : List Bool) : EuclideanSpace ℝ (Fin d) :=
  receive d width spacing (bits.take (d * width))

end LongTails.Algorithms.DistributedNormalizedCompression
