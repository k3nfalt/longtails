import LongTails.Algorithms.DashaQuantization

namespace LongTails.Algorithms.DashaFloat

noncomputable def exponent (precision : ℕ) (x : ℝ) : ℕ := Nat.log2 ⌊|x|⌋₊ - precision

noncomputable def stride (precision : ℕ) (x : ℝ) : ℕ := 2 ^ exponent precision x

noncomputable def mantissa (precision : ℕ) (x u : ℝ) : ℕ :=
  let y := |x| / stride precision x
  ⌊y⌋₊ + if u < y - ⌊y⌋₊ then 1 else 0

noncomputable def scalarIndex (precision : ℕ) (x u : ℝ) : ℤ :=
  if x < 0 then -((mantissa precision x u * stride precision x : ℕ) : ℤ)
  else ((mantissa precision x u * stride precision x : ℕ) : ℤ)

noncomputable def rounded (precision : ℕ) (spacing x u : ℝ) : ℝ :=
  spacing * (scalarIndex precision (x / spacing) u : ℝ)

abbrev Packet (precision exponentWidth : ℕ) :=
  Bool × Fin (2 ^ (precision + 2)) × Fin (2 ^ exponentWidth)

noncomputable def bitEquiv (precision exponentWidth : ℕ) :
    Packet precision exponentWidth ≃ (Fin (precision + exponentWidth + 3) → Bool) :=
  Fintype.equivOfCardEq (by simp [Packet, pow_add]; ring)

noncomputable def encode {precision exponentWidth : ℕ} (packet : Packet precision exponentWidth) :
    List Bool := List.ofFn (bitEquiv precision exponentWidth packet)

noncomputable def decode (precision exponentWidth : ℕ) (bits : List Bool) :
    Packet precision exponentWidth :=
  if h : bits.length = precision + exponentWidth + 3 then
    (bitEquiv precision exponentWidth).symm (fun i => bits.get ⟨i.val, h.symm ▸ i.isLt⟩)
  else (false, 0, 0)

noncomputable def packet (precision exponentWidth : ℕ) (x u : ℝ) : Packet precision exponentWidth :=
  (decide (x < 0),
    ⟨mantissa precision x u % 2 ^ (precision + 2), Nat.mod_lt _ (by positivity)⟩,
    ⟨exponent precision x % 2 ^ exponentWidth, Nat.mod_lt _ (by positivity)⟩)

noncomputable def value {precision exponentWidth : ℕ} (p : Packet precision exponentWidth) : ℤ :=
  if p.1 then -((p.2.1.val * 2 ^ p.2.2.val : ℕ) : ℤ)
  else ((p.2.1.val * 2 ^ p.2.2.val : ℕ) : ℤ)

end LongTails.Algorithms.DashaFloat
