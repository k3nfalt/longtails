import LongTails.Algorithms.AcceleratedBiasedStochastic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.HiddenPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

inductive Program (E : Type*) where
  | done : E → Program E
  | ask : E → (E → Program E) → Program E

def programQuery (fallback : E) : Program E → E
  | .done _ => fallback
  | .ask x _ => x

def programUpdate : Program E → E → Program E
  | .done x, _ => .done x
  | .ask _ next, reply => next reply

def programOutput (fallback : E) : Program E → E
  | .done x => x
  | .ask _ _ => fallback

noncomputable def innerProgram (β D R : ℝ) (anchor center : E)
    (next : E → Program E) : ℕ → ℕ → E × E → Program E
  | 0, _, state => next state.1
  | N + 1, k, state =>
      let y := Gradient.acceleratedQuery (k, state.1, state.2)
      .ask y fun reply =>
        innerProgram β D R anchor center next N (k + 1)
          (BiasedStochasticGradient.projectedUpdate D R center k state
            (reply + β • (y - anchor)))

noncomputable def stageProgram (β D : ℝ) (T : ℕ) (anchor : E)
    (next : E → Program E) : ℕ → ℝ → E → Program E
  | 0, _, center => next center
  | H + 1, R, center =>
      innerProgram β D R anchor center
        (fun out => stageProgram β D T anchor next H (R / 2) out)
        T 0 (center, center)

noncomputable def outerProgram (β D q : ℝ) (T H : ℕ) : ℕ → ℝ → E → Program E
  | 0, _, anchor => .done anchor
  | N + 1, R, anchor =>
      stageProgram β D T anchor
        (fun out => outerProgram β D q T H N (q * R) out)
        H R anchor

noncomputable def innerRun (F : E → E) (β D R : ℝ) (anchor center : E) :
    ℕ → ℕ → E × E → E × E
  | 0, _, state => state
  | N + 1, k, state =>
      let y := Gradient.acceleratedQuery (k, state.1, state.2)
      innerRun F β D R anchor center N (k + 1)
        (BiasedStochasticGradient.projectedUpdate D R center k state
          (F y + β • (y - anchor)))

noncomputable def stageRun (F : E → E) (β D : ℝ) (T : ℕ) (anchor : E) :
    ℕ → ℝ → E → E
  | 0, _, center => center
  | H + 1, R, center =>
      stageRun F β D T anchor H (R / 2)
        (innerRun F β D R anchor center T 0 (center, center)).1

noncomputable def outerRun (F : E → E) (β D q : ℝ) (T H : ℕ) : ℕ → ℝ → E → E
  | 0, _, anchor => anchor
  | N + 1, R, anchor =>
      outerRun F β D q T H N (q * R) (stageRun F β D T anchor H R anchor)

noncomputable def nestedAcceleration (β D q R : ℝ) (T H N : ℕ) (x0 : E) :
    Algorithm E E E where
  State := Program E
  initial _ := outerProgram β D q T H N R x0
  query p := (0, programQuery x0 p)
  update := programUpdate
  output := programOutput x0

noncomputable def hiddenPotentialOutput (μ L s R ε : ℝ) (x0 : E) : Algorithm E E E :=
  let β := 512 * s
  let m := μ + 511 * s
  let ℓ := L + μ + 512 * s
  let T := ⌈16 * Real.sqrt (ℓ / m)⌉₊
  let H := ⌈Real.log (2 * (μ + β) / μ) / Real.log 2⌉₊
  let N := ⌈2 * (μ + β) / μ * Real.log (2 + R / ε)⌉₊
  nestedAcceleration β (2 * ℓ) (1 - μ / (2 * (μ + β))) R T H N x0

end OracleTemplate.HiddenPotential
