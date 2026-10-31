import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.InertialMonotone

open QueryPlan

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def horizon (L R ε : ℝ) : ℕ := ⌈4096 + 2048 * L * R / ε⌉₊

def remainingScale (N k : ℕ) : ℝ := (N : ℝ) + 128 - k

noncomputable def regularization (L : ℝ) (N k : ℕ) : ℝ :=
  128 * L * N / remainingScale N k ^ 2

noncomputable def growth (N k : ℕ) : ℝ :=
  2 * ((remainingScale N k / (remainingScale N k - 1)) ^ 2 - 1)

noncomputable def stepSize (L : ℝ) (N k : ℕ) : ℝ :=
  2 * growth N k / regularization L N k

noncomputable def batchSize (σ ε : ℝ) (N k : ℕ) : ℕ :=
  max 1 ⌈4096 * σ ^ 2 * (1 + Real.log (N + 128)) /
    (ε ^ 2 * (remainingScale N k - 1))⌉₊

def batchPlan (x : E) : (b : ℕ) → QueryPlan E E E b
  | 0 => .done 0
  | b + 1 => .ask x (fun v => (batchPlan x b).map (v + ·))

noncomputable def extrapolated (μ η : ℝ) (b : ℕ) (x z s : E) : E :=
  z - η • ((1 / (b : ℝ)) • s + μ • (z - x))

noncomputable def transported (r : ℝ) (x w : E) : E × E :=
  (x + (3 * r / (2 * (2 + r))) • (w - x),
    x + ((4 + 3 * r) / (2 * (2 + r))) • (w - x))

noncomputable def batchTrial {Ω : Type*} (g : E → Ω → E) (μ η : ℝ) (b : ℕ)
    (state : E × E) (u v : Fin b → Ω) : E :=
  let y := extrapolated μ η b state.1 state.2 (∑ i, g state.2 (u i))
  state.2 - η • ((1 / (b : ℝ)) • (∑ i, g y (v i)) + μ • (y - state.1))

noncomputable def stepPlan (μ η r : ℝ) (b : ℕ) (state : E × E) :
    QueryPlan E E (E × E) (b + b) :=
  (batchPlan state.2 b).bind fun s1 =>
    let y := extrapolated μ η b state.1 state.2 s1
    (batchPlan y b).map fun s2 =>
      transported r state.1
        (state.2 - η • ((1 / (b : ℝ)) • s2 + μ • (y - state.1)))

def calls (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (b k + b k) + calls b k

noncomputable def runPlan (μ η r : ℕ → ℝ) (b : ℕ → ℕ) :
    (k : ℕ) → E × E → QueryPlan E E (E × E) (calls b k)
  | 0, state => .done state
  | k + 1, state =>
      (runPlan μ η r b k state).bind (stepPlan (μ k) (η k) (r k) (b k))

noncomputable def finiteRun {Ω : Type} (g : E → Ω → E)
    (μ η r : ℕ → ℝ) (b : ℕ → ℕ) (state : E × E) :
    (k : ℕ) → (Fin (calls b k) → Ω) → E × E
  | 0, _ => state
  | k + 1, ξ =>
      let previous := finiteRun g μ η r b state k
        (fun i => ξ ⟨i, by simp only [calls]; omega⟩)
      transported (r k) previous.1 (batchTrial g (μ k) (η k) (b k) previous
        (fun i => ξ ⟨calls b k + i, by simp only [calls]; have hi := i.isLt; omega⟩)
        (fun i => ξ ⟨calls b k + (b k + i), by simp only [calls]; have hi := i.isLt; omega⟩))

noncomputable def inertialExtragradient (L R σ ε : ℝ) (x0 : E) : Algorithm E E E :=
  let N := horizon L R ε
  let b := batchSize σ ε N
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    x0 x0 (calls b N) (fun _ =>
      (runPlan (regularization L N) (stepSize L N) (growth N) b N (x0, x0)).map Prod.snd)

noncomputable def terminalPoint (L R σ ε : ℝ) (x0 : E) (O : Oracle E E) (K : ℕ)
    (seed : Unit × ((k : ℕ) → O.Seed k)) : E :=
  execute O (inertialExtragradient L R σ ε x0) (fun _ => K) seed.1 seed.2

end OracleTemplate.InertialMonotone
