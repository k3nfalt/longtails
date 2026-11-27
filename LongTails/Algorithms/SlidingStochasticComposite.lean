import LongTails.Algorithms.AcceleratedStochastic
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.SlidingStochasticComposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[ext]
structure State (E : Type*) where
  t : ℕ
  c : E
  v : E
  k : ℕ
  x : E
  z : E
  index : ℕ
  out : E

noncomputable def method (ℓ D : ℝ) (N K : ℕ) (x0 : E) : Algorithm E E E 2 where
  Seed := Fin (K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (K + 1))).toMeasure, inferInstance⟩
  State := State E
  initial j := ⟨0, x0, 0, 0, x0, x0, j.val, x0⟩
  query s := if s.t % (N + 1) = 0 then (0, s.c) else (1, Gradient.acceleratedQuery (s.k, s.x, s.z))
  update s reply :=
    if s.t % (N + 1) = 0 then
      ⟨s.t + 1, s.c, reply, 0, s.c, s.c, s.index, if s.t / (N + 1) = s.index then s.c else s.out⟩
    else
      let y := Gradient.acceleratedQuery (s.k, s.x, s.z)
      let G := s.v + reply + ℓ • (y - s.c)
      let a := ((s.k : ℝ) + 1) / 2
      let x' := y - (1 / D) • G
      let z' := s.z - (a / D) • G
      ⟨s.t + 1, if s.t % (N + 1) = N then x' else s.c, s.v, s.k + 1, x', z', s.index, s.out⟩
  output s := s.out

noncomputable def innerRun {Ω : Type*} (ℓ D : ℝ) (N : ℕ) (g : E → Ω → E) (c v : E)
    (η : Fin N → Ω) : E :=
  (StochasticGradient.acceleratedRun (fun y ω => v + g y ω + ℓ • (y - c)) D N 0 c c η).1

noncomputable def centers {Ω : Type*} (ℓ D : ℝ) (N : ℕ) (gf : E → E) (g : E → Ω → E) (x0 : E)
    (blocks : ℕ → Fin N → Ω) : ℕ → E
  | 0 => x0
  | k + 1 =>
      let c := centers ℓ D N gf g x0 blocks k
      innerRun ℓ D N g c (gf c) (blocks k)

end OracleTemplate.SlidingStochasticComposite
