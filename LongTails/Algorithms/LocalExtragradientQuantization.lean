import LongTails.Algorithms.DistributedQuantization

namespace LongTails.Algorithms.LocalExtragradientQuantization

open LongTails.Algorithms.DistributedQuantization

def aggregateCodes {n d width : ℕ} (codes : Fin n → Grid d width) : Fin d → ℕ :=
  fun j => ∑ i, (codes i j).val

noncomputable def decodeAverage {d : ℕ} (n width : ℕ) (spacing : ℝ)
    (codes : Fin d → ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => spacing *
    ((codes j : ℝ) - (n : ℝ) * ((2 ^ width - 1 : ℕ) : ℝ) / 2) / n)

noncomputable def quantizedAverage (n d width : ℕ) (spacing : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  decodeAverage n width spacing (aggregateCodes (fun i => quantize d width spacing (x i)))

def packAggregate {n d width : ℕ} (extra : ℕ) (codes : Fin n → Grid d width) :
    Grid d (width + extra) :=
  fun j => ⟨aggregateCodes codes j % 2 ^ (width + extra), Nat.mod_lt _ (by positivity)⟩

noncomputable def aggregateMessage {n d width : ℕ} (extra : ℕ)
    (codes : Fin n → Grid d width) : List Bool :=
  encode (packAggregate extra codes)

noncomputable def receiveAggregate (d width extra : ℕ) (bits : List Bool) : Fin d → ℕ :=
  fun j => (decode d (width + extra) (bits.take (d * (width + extra))) j).val

def packNaturals {d : ℕ} (width : ℕ) (values : Fin d → ℕ) : Grid d width :=
  fun j => ⟨values j % 2 ^ width, Nat.mod_lt _ (by positivity)⟩

noncomputable def naturalMessage {d : ℕ} (width : ℕ) (values : Fin d → ℕ) : List Bool :=
  encode (packNaturals width values)

noncomputable def receiveNaturals (d width : ℕ) (bits : List Bool) : Fin d → ℕ :=
  fun j => (decode d width (bits.take (d * width)) j).val

end LongTails.Algorithms.LocalExtragradientQuantization
