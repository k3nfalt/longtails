import LongTails.Algorithms.Accelerated
import LongTails.Algorithms.Clipping

namespace OracleTemplate.HeavyTailedMarkovGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def projectedClippedUpdate (D R C : ℝ) (x0 : E)
    (state : ℕ × E × E) (reply : E) : ℕ × E × E :=
  let k := state.1
  let a := ((k : ℝ) + 1) / 2
  let z := x0 + clip R (state.2.2 - (a / D) • clip C reply - x0)
  (k + 1, Gradient.acceleratedQuery (k, state.2.1, z), z)

noncomputable def acceleratedClipped (D R C : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, x0)
  query := fun s => (0, (Gradient.acceleratedQuery) s)
  update := projectedClippedUpdate D R C x0
  output state := state.2.1

noncomputable def spaced {Query Reply Output : Type*} (m : ℕ)
    (A : Algorithm Query Reply Output) : Algorithm Query Reply Output where
  Seed := A.Seed
  law := A.law
  State := ℕ × A.State
  initial seed := (0, A.initial seed)
  query state := A.query state.2
  update state reply :=
    (state.1 + 1, if state.1 % m = 0 then A.update state.2 reply else state.2)
  output state := A.output state.2

noncomputable def acceleratedMarkov (D R C : ℝ) (m : ℕ) (x0 : E) : Algorithm E E E :=
  spaced m (acceleratedClipped D R C x0)

noncomputable def clippedRun {Ω : Type*} (g : E → Ω → E) (D R C : ℝ)
    (m : ℕ) (x0 : E) (ξ : ℕ → Ω) : ℕ → ℕ × E × E
  | 0 => (0, x0, x0)
  | k + 1 =>
    let state := clippedRun g D R C m x0 ξ k
    projectedClippedUpdate D R C x0 state (g (Gradient.acceleratedQuery state) (ξ (k * m)))

end OracleTemplate.HeavyTailedMarkovGradient
