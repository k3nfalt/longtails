import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.List.OfFn

namespace OracleTemplate.FiniteSum

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def fullGradient (oracle : Fin n × E → E) (x : E) : E :=
  (n : ℝ)⁻¹ • ∑ i, oracle (i, x)

noncomputable def estimator (oracle : Fin n × E → E) (snapshot x : E) (i : Fin n) : E :=
  oracle (i, x) - oracle (i, snapshot) + fullGradient oracle snapshot

def EpochSeeds (n m : ℕ) : ℕ → Type
  | 0 => Unit
  | S + 1 => (Fin m → Fin n) × EpochSeeds n (2 * m) S

instance epochSeedsFintype (n m S : ℕ) : Fintype (EpochSeeds n m S) := by
  induction S generalizing m with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ S ih =>
    letI := ih (2 * m)
    exact inferInstanceAs (Fintype ((Fin m → Fin n) × EpochSeeds n (2 * m) S))

instance epochSeedsNonempty (n m S : ℕ) [NeZero n] : Nonempty (EpochSeeds n m S) := by
  induction S generalizing m with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ S ih =>
    let := ih (2 * m)
    exact inferInstanceAs (Nonempty ((Fin m → Fin n) × EpochSeeds n (2 * m) S))

instance (n m S : ℕ) : MeasurableSpace (EpochSeeds n m S) := ⊤
instance (n m S : ℕ) : MeasurableSingletonClass (EpochSeeds n m S) := ⟨fun _ => trivial⟩

def flattenSeeds {n m : ℕ} : (S : ℕ) → EpochSeeds n m S → List (Fin n)
  | 0, _ => []
  | S + 1, seed => List.ofFn seed.1 ++ flattenSeeds S seed.2

noncomputable def innerRun (oracle : Fin n × E → E) (L : ℝ) (snapshot : E) :
    E → List (Fin n) → E × List E
  | x, [] => (x, [])
  | x, i :: tail =>
    let result := innerRun oracle L snapshot (x - (1 / (8 * L)) • estimator oracle snapshot x i) tail
    (result.1, x :: result.2)

noncomputable def epochRun (oracle : Fin n × E → E) (L : ℝ) (m : ℕ) :
    (S : ℕ) → E → E → EpochSeeds n m S → E × E
  | 0, x, snapshot, _ => (x, snapshot)
  | S + 1, x, snapshot, seed =>
    let result := innerRun oracle L snapshot x (List.ofFn seed.1)
    epochRun oracle L (2 * m) S result.1 ((m : ℝ)⁻¹ • result.2.sum) seed.2

def queryCount (n m : ℕ) : ℕ → ℕ
  | 0 => 0
  | S + 1 => n + 2 * m + queryCount n (2 * m) S

structure SvrgState (n : ℕ) (E : Type*) where
  samples : List (Fin n)
  phase : Nat
  index : Nat
  length : Nat
  remaining : Nat
  point : E
  snapshot : E
  accumulated : E
  gradient : E
  reply : E

noncomputable def svrgQuery [NeZero n] (state : SvrgState n E) : Fin n × E :=
  if state.phase = 0 then (⟨state.index % n, Nat.mod_lt _ (NeZero.pos n)⟩, state.snapshot)
  else (state.samples.headD 0, if state.phase = 1 then state.point else state.snapshot)

noncomputable def svrgUpdate (L : ℝ) (state : SvrgState n E) (reply : E) : SvrgState n E :=
  if state.samples.isEmpty then state
  else if state.phase = 0 then
    if state.index + 1 < n then
      { state with index := state.index + 1, gradient := state.gradient + reply }
    else
      { state with
        phase := 1
        index := 0
        gradient := (n : ℝ)⁻¹ • (state.gradient + reply) }
  else if state.phase = 1 then
    { state with phase := 2, reply := reply }
  else
    let point := state.point - (1 / (8 * L)) • (state.reply - reply + state.gradient)
    let accumulated := state.accumulated + state.point
    if state.remaining = 1 then
      { state with
        reply := 0
        samples := state.samples.tail
        phase := 0
        length := 2 * state.length
        remaining := 2 * state.length
        point := point
        snapshot := (state.length : ℝ)⁻¹ • accumulated
        accumulated := 0
        gradient := 0 }
    else
      { state with
        reply := 0
        samples := state.samples.tail
        phase := 1
        remaining := state.remaining - 1
        point := point
        accumulated := accumulated }

noncomputable def svrg [NeZero n] (L : ℝ) (x0 : E) (epochs : ℕ) :
    Algorithm (Fin n × E) E E where
  Seed := EpochSeeds n 2 epochs
  law := ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  State := SvrgState n E
  initial seed := ⟨flattenSeeds epochs seed, 0, 0, 2, 2, x0, x0, 0, 0, 0⟩
  query := fun s => (0, (svrgQuery) s)
  update := svrgUpdate L
  output state := state.snapshot

end OracleTemplate.FiniteSum
