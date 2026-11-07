import LongTails.Setups.ChiSquareConstrainedDro

namespace OracleTemplate.ChiSquareDro

open LongTails.Setups.ChiSquareConstrainedDro

noncomputable def radius (q : Params) : ℝ := Real.sqrt (1 + 2 * q.ρ)

noncomputable def etaLow (q : Params) : ℝ := -(q.B / Real.sqrt q.ρ)

noncomputable def tailBound (q : Params) : ℝ := q.B + q.B / Real.sqrt q.ρ

noncomputable def numBrackets (q : Params) : ℕ :=
  Nat.clog 2 ⌈8 * radius q * tailBound q / q.ε⌉₊ + 1

noncomputable def sgdSteps (q : Params) : ℕ :=
  ⌈2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2⌉₊ + 144

noncomputable def selectionSamples (q : Params) : ℕ := numBrackets q * sgdSteps q

noncomputable def bracketLength (q : Params) : ℕ := sgdSteps q + selectionSamples q

noncomputable def scaleLow (q : Params) (j : ℕ) : ℝ := 2 ^ j * q.ε / (8 * radius q)

noncomputable def stepX (q : Params) : ℝ := q.ε / (128 * radius q ^ 2 * q.G ^ 2)

noncomputable def stepEta (q : Params) : ℝ := q.ε / (128 * (2 + 4 * radius q ^ 2))

noncomputable def stepScale (q : Params) (j : ℕ) : ℝ :=
  q.ε * scaleLow q j ^ 2 / (128 * radius q ^ 2 * (scaleLow q j ^ 2 / 2 + tailBound q ^ 2))

structure BracketState (E : Type*) where
  j : ℕ
  t : ℕ
  x : E
  η : ℝ
  s : ℝ
  sx : E
  se : ℝ
  ss : ℝ
  acc : ℝ
  bx : E
  bv : ℝ

noncomputable def bracketStart (q : Params) (j : ℕ) (bx : q.E) (bv : ℝ) : BracketState q.E :=
  ⟨j, 0, q.x0, 0, scaleLow q j, 0, 0, 0, 0, bx, bv⟩

noncomputable def sgdUpdate (q : Params) (st : BracketState q.E) (r : q.E × ℝ × q.E) :
    BracketState q.E :=
  let u := max (r.2.1 - st.η) 0
  ⟨st.j, st.t + 1,
    r.1 - stepX q • ((radius q * u / st.s) • r.2.2),
    max (etaLow q) (min q.B (st.η - stepEta q * (1 - radius q * u / st.s))),
    max (scaleLow q st.j) (min (4 * scaleLow q st.j)
      (st.s - stepScale q st.j * (radius q / 2 - radius q * u ^ 2 / (2 * st.s ^ 2)))),
    st.sx + r.1, st.se + st.η, st.ss + st.s, st.acc, st.bx, st.bv⟩

noncomputable def selectUpdate (q : Params) (st : BracketState q.E) (r : q.E × ℝ × q.E) :
    BracketState q.E :=
  let acc := st.acc + max (r.2.1 - (sgdSteps q : ℝ)⁻¹ * st.se) 0 ^ 2
  if st.t + 1 < bracketLength q then
    ⟨st.j, st.t + 1, st.x, st.η, st.s, st.sx, st.se, st.ss, acc, st.bx, st.bv⟩
  else
    let value := (sgdSteps q : ℝ)⁻¹ * st.se +
      radius q * Real.sqrt (acc / selectionSamples q)
    if st.j = 0 ∨ value < st.bv then
      bracketStart q (st.j + 1) ((sgdSteps q : ℝ)⁻¹ • st.sx) value
    else bracketStart q (st.j + 1) st.bx st.bv

noncomputable def bracketUpdate (q : Params) (st : BracketState q.E) (r : q.E × ℝ × q.E) :
    BracketState q.E :=
  if numBrackets q ≤ st.j then st
  else if st.t < sgdSteps q then sgdUpdate q st r else selectUpdate q st r

noncomputable def bracketQuery (q : Params) (st : BracketState q.E) : q.E :=
  if st.t < sgdSteps q then st.x else (sgdSteps q : ℝ)⁻¹ • st.sx

noncomputable def bracketAlgorithm (q : Params) : Algorithm q.E (q.E × ℝ × q.E) q.E where
  State := BracketState q.E
  initial := fun _ => bracketStart q 0 q.x0 0
  query := fun st => (0, bracketQuery q st)
  update := bracketUpdate q
  output := fun st => st.bx

end OracleTemplate.ChiSquareDro
