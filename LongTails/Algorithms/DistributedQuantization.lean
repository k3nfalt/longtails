import LongTails.Setups.DistributedSmoothNonconvex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.Floor.Ring

namespace LongTails.Algorithms.DistributedQuantization

abbrev Grid (d width : ℕ) := Fin d → Fin (2 ^ width)

noncomputable def bitEquiv (d width : ℕ) : Grid d width ≃ (Fin (d * width) → Bool) :=
  Fintype.equivOfCardEq (by simp [Grid, ← pow_mul, Nat.mul_comm])

noncomputable def encode {d width : ℕ} (x : Grid d width) : List Bool :=
  List.ofFn (bitEquiv d width x)

noncomputable def decode (d width : ℕ) (bits : List Bool) : Grid d width :=
  if h : bits.length = d * width then
    (bitEquiv d width).symm (fun i => bits.get ⟨i.val, h.symm ▸ i.isLt⟩)
  else fun _ => 0

noncomputable def quantize (d width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Grid d width :=
  fun i => ⟨min ⌊x i / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2⌋₊ (2 ^ width - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩

noncomputable def reconstruct {d width : ℕ} (spacing : ℝ) (x : Grid d width) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => spacing * (((x i).val : ℝ) - ((2 ^ width - 1 : ℕ) : ℝ) / 2))

noncomputable def message (d width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : List Bool :=
  encode (quantize d width spacing x)

noncomputable def receive (d width : ℕ) (spacing : ℝ) (bits : List Bool) :
    EuclideanSpace ℝ (Fin d) :=
  reconstruct spacing (decode d width bits)

end LongTails.Algorithms.DistributedQuantization
