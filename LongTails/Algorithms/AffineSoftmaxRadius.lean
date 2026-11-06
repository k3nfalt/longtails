import LongTails.Algorithms.AffineSoftmaxOuter

namespace LongTails.Algorithms.AffineSoftmaxRadius

noncomputable def radiusFactor (m a b ell : ℝ) : ℝ :=
  max 1 (max (Real.sqrt (8 * b * ell)) (max ((64 * b ^ 2 / m) ^ (3 / 8 : ℝ))
    ((1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) ^ (3 / 14 : ℝ))))

noncomputable def publicRadius (m : ℕ) (G L R ε : ℝ) : ℝ :=
  2 * R / radiusFactor m (G * R / ε) (L * R ^ 2 / ε) (Real.log m)

noncomputable def publicDepth (m : ℕ) (G L R ε : ℝ) : ℕ :=
  1 + Nat.clog 2 (Nat.ceil (2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε))

noncomputable def meanCostBound (m : ℕ) (G L R ε : ℝ) : ℝ :=
  let r := publicRadius m G L R ε
  let τ := ε / (2 * Real.log m)
  let H := LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G (2 * R) r (ε / 2)
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  50000000000000 * (H : ℝ) ^ 6 * ((m : ℝ) * LongTails.Algorithms.AffineSoftmaxOuter.compilerScale (2 * R) r +
    (2 * R) * Real.sqrt ((L + 2 * G ^ 2 / τ) / (ε / 2)) + V * (2 * R) ^ 2 / (ε / 2) ^ 2)

end LongTails.Algorithms.AffineSoftmaxRadius
