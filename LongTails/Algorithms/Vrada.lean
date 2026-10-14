import LongTails.Algorithms.Svrg
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.FiniteSum

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def vradaWeight (m : ℕ) (L : ℝ) : ℕ → ℝ
  | 0 => 1 / L
  | k + 1 => vradaWeight m L k + Real.sqrt ((m : ℝ) * vradaWeight m L k / (2 * L))

noncomputable def vradaIncrement (m : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * vradaWeight m L k / (2 * L))

noncomputable def vradaMix (A a : ℝ) (snapshot z : E) : E :=
  (A / (A + a)) • snapshot + (a / (A + a)) • z

noncomputable def vradaInner (g : Fin n × E → E) (A a m : ℝ) (snapshot : E) :
    E → List (Fin n) → E × List E
  | z, [] => (z, [])
  | z, i :: tail =>
      let y := vradaMix A a snapshot z
      let next := z - (a / m) • estimator g snapshot y i
      let result := vradaInner g A a m snapshot next tail
      (result.1, vradaMix A a snapshot next :: result.2)

def VradaSeeds (n m : ℕ) : ℕ → Type
  | 0 => Unit
  | S + 1 => (Fin m → Fin n) × VradaSeeds n m S

instance vradaSeedsFintype (n m S : ℕ) : Fintype (VradaSeeds n m S) := by
  induction S with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ S ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Fin m → Fin n) × VradaSeeds n m S))

instance vradaSeedsNonempty (n m S : ℕ) [NeZero n] : Nonempty (VradaSeeds n m S) := by
  induction S with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ S ih =>
    let := ih
    exact inferInstanceAs (Nonempty ((Fin m → Fin n) × VradaSeeds n m S))

instance (n m S : ℕ) : MeasurableSpace (VradaSeeds n m S) := ⊤
instance (n m S : ℕ) : MeasurableSingletonClass (VradaSeeds n m S) := ⟨fun _ => trivial⟩

noncomputable def vradaRun (g : Fin n × E → E) (L : ℝ) (m : ℕ) :
    (S : ℕ) → ℕ → E → E → VradaSeeds n m S → E × E
  | 0, _, z, snapshot, _ => (z, snapshot)
  | S + 1, k, z, snapshot, seed =>
      let result := vradaInner g (vradaWeight m L k) (vradaIncrement m L k) m snapshot z (List.ofFn seed.1)
      vradaRun g L m S (k + 1) result.1 ((m : ℝ)⁻¹ • result.2.sum) seed.2

def vradaFlatten {n m : ℕ} : (S : ℕ) → VradaSeeds n m S → List (Fin n)
  | 0, _ => []
  | S + 1, seed => List.ofFn seed.1 ++ vradaFlatten S seed.2

structure VradaState (n : ℕ) (E : Type*) extends SvrgState n E where
  epoch : ℕ

noncomputable def vradaQuery [NeZero n] (L : ℝ) (state : VradaState n E) : Fin n × E :=
  if state.phase = 0 then (⟨state.index % n, Nat.mod_lt _ (NeZero.pos n)⟩, state.snapshot)
  else (state.samples.headD 0, if state.phase = 1 then
    vradaMix (vradaWeight state.length L state.epoch) (vradaIncrement state.length L state.epoch)
      state.snapshot state.point else state.snapshot)

noncomputable def vradaUpdate (L : ℝ) (state : VradaState n E) (reply : E) : VradaState n E :=
  if state.samples.isEmpty then state
  else if state.phase = 0 then
    if state.index + 1 < n then
      { state with index := state.index + 1, gradient := state.gradient + reply }
    else
      { state with phase := 1, index := 0, gradient := (n : ℝ)⁻¹ • (state.gradient + reply) }
  else if state.phase = 1 then
    { state with phase := 2, reply := reply }
  else
    let a := vradaIncrement state.length L state.epoch
    let point := state.point - (a / state.length) • (state.reply - reply + state.gradient)
    let accumulated := state.accumulated +
      vradaMix (vradaWeight state.length L state.epoch) a state.snapshot point
    if state.remaining = 1 then
      { state with
        reply := 0
        samples := state.samples.tail
        phase := 0
        remaining := state.length
        epoch := state.epoch + 1
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

noncomputable def vrada [NeZero n] (L : ℝ) (x0 : E) (m epochs : ℕ) :
    Algorithm (Fin n × E) E E where
  Seed := VradaSeeds n m epochs
  law := ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  State := VradaState n E
  initial seed := ⟨⟨vradaFlatten epochs seed, 0, 0, m, m, x0, x0, 0, 0, 0⟩, 0⟩
  query := fun s => (0, (vradaQuery L) s)
  update := vradaUpdate L
  output state := state.snapshot

end OracleTemplate.FiniteSum
