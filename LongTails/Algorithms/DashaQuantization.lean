import LongTails.Algorithms.DistributedQuantization
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace LongTails.Algorithms.DashaQuantization

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def stride (coarse : Bool) (x : ℝ) : ℕ :=
  if coarse then 2 ^ (Nat.log2 ⌊|x|⌋₊ - 2) else 1

noncomputable def scalarIndex (coarse : Bool) (x u : ℝ) : ℤ :=
  let s := stride coarse x
  let y := |x| / s
  let k := ⌊y⌋₊
  let magnitude := (k + if u < y - k then 1 else 0) * s
  if x < 0 then -(magnitude : ℤ) else (magnitude : ℤ)

noncomputable def indices (d : ℕ) (coarse : Bool) (spacing : ℝ)
    (x : Vector d) (u : Fin d → ℝ) : Fin d → ℤ :=
  fun i => scalarIndex coarse (x i / spacing) (u i)

noncomputable def reconstruct {d : ℕ} (spacing : ℝ) (z : Fin d → ℤ) : Vector d :=
  WithLp.toLp 2 (fun i => spacing * (z i : ℝ))

noncomputable def rounded (d : ℕ) (coarse : Bool) (spacing : ℝ)
    (x : Vector d) (u : Fin d → ℝ) : Vector d :=
  reconstruct spacing (indices d coarse spacing x u)

def center (width : ℕ) : ℕ := 2 ^ width / 2

def packScalar (width : ℕ) (z : ℤ) : Fin (2 ^ width) :=
  ⟨min (z + (center width : ℤ)).toNat (2 ^ width - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩

def unpackScalar {width : ℕ} (code : Fin (2 ^ width)) : ℤ :=
  (code.val : ℤ) - center width

noncomputable def encode (d width : ℕ) (z : Fin d → ℤ) : List Bool :=
  DistributedQuantization.encode (fun i => packScalar width (z i))

noncomputable def decode (d width : ℕ) (bits : List Bool) : Fin d → ℤ :=
  fun i => unpackScalar (DistributedQuantization.decode d width (bits.take (d * width)) i)

noncomputable def message (d width : ℕ) (coarse : Bool) (spacing : ℝ)
    (x : Vector d) (u : Fin d → ℝ) : List Bool :=
  encode d width (indices d coarse spacing x u)

noncomputable def receive (d width : ℕ) (spacing : ℝ) (bits : List Bool) : Vector d :=
  reconstruct spacing (decode d width bits)

noncomputable def unitLaw : MeasureTheory.ProbabilityMeasure ℝ :=
  ⟨MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1), ⟨by simp⟩⟩

end LongTails.Algorithms.DashaQuantization
