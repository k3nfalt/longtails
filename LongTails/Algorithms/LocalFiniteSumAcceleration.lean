import LongTails.Setups.GeneralizedSmoothFiniteSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.GeneralizedFiniteSum

open LongTails.Setups.GeneralizedSmoothFiniteSum

noncomputable def slotCount {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℕ :=
  ⌊(n : ℝ) * max 0 (w i) / (∑ j, max 0 (w j))⌋₊ + 1

noncomputable def slotTotal {n : ℕ} (w : Fin n → ℝ) : ℕ :=
  ∑ i, slotCount w i

noncomputable def drawIndex {n : ℕ} [NeZero n] (w : Fin n → ℝ)
    (seed : Fin (Nat.factorial (2 * n))) : Fin n := by
  classical
  let D := slotTotal w
  let M := Nat.factorial (2 * n)
  exact if h : 0 < D ∧ D ∣ M then
    let e : Fin D × Fin (M / D) ≃ Fin M :=
      finProdFinEquiv.trans (finCongr (Nat.mul_div_cancel' h.2))
    ((finSigmaFinEquiv (n := slotCount w)).symm (e.symm seed).1).1
  else 0

noncomputable def snapshotWeights {n : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (L0 L1 : ℝ) (cached : Fin n → E) : Fin n → ℝ :=
  fun i => L0 + L1 * ‖cached i‖

noncomputable def direction {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : Fin n → ℝ) (cached : Fin n → E)
    (i : Fin n) (reply : E) : E :=
  (n : ℝ)⁻¹ • ∑ j, cached j +
    ((slotTotal w : ℝ) / ((n : ℝ) * slotCount w i)) • (reply - cached i)

noncomputable def epochIncrement (p : Params) (A : ℝ) : ℝ :=
  min (A / (1024 * (1 + p.L1 * p.R)))
    (Real.sqrt ((p.n : ℝ) * A / (1048576 * (p.L0 + p.L1 * p.G))))

noncomputable def epochWeight (p : Params) : ℕ → ℝ
  | 0 => p.R ^ 2 / p.Δ
  | k + 1 => epochWeight p k + epochIncrement p (epochWeight p k)

noncomputable def epochCount (p : Params) : ℕ :=
  ⌈65536 * (1 + p.L1 * p.R) * Real.log (2 + p.Δ / p.ε) +
    65536 * Real.sqrt ((p.L0 + p.L1 * p.G) * p.R ^ 2 / ((p.n : ℝ) * p.ε))⌉₊

noncomputable def trialCount (p : Params) : ℕ :=
  ⌈Real.log (2 * max 1 (p.Δ / p.ε)) / Real.log 4⌉₊

noncomputable def mix {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A a : ℝ) (s z : E) : E := (A / (A + a)) • s + (a / (A + a)) • z

structure LocalCore (p : Params) where
  epoch : ℕ
  index : ℕ
  snapshot : p.E
  dual : p.E
  outputs : List p.E

noncomputable def coreStep (p : Params) (g : Fin p.n → p.E → p.E)
    (s : LocalCore p) (seed : Fin ((2 * p.n).factorial)) : LocalCore p :=
  let A := epochWeight p s.epoch
  let a := epochIncrement p A
  let cache := fun i => g i s.snapshot
  let w := snapshotWeights p.L0 p.L1 cache
  let i := drawIndex w seed
  let y := mix A a s.snapshot s.dual
  let z := s.dual - (a / p.n) • direction w cache i (g i y)
  let outs := mix A a s.snapshot z :: s.outputs
  if s.index + 1 < p.n then {s with index := s.index + 1, dual := z, outputs := outs}
  else {
    epoch := s.epoch + 1, index := 0, snapshot := (p.n : ℝ)⁻¹ • outs.sum
    dual := z, outputs := []}


def initialCore (p : Params) : LocalCore p :=
  ⟨0, 0, p.x0, p.x0, []⟩

noncomputable def coreRun (p : Params) (g : Fin p.n → p.E → p.E) :
    (k : ℕ) → LocalCore p → (Fin k → Fin ((2 * p.n).factorial)) → LocalCore p
  | 0, s, _ => s
  | k + 1, s, ξ => coreRun p g k (coreStep p g s (ξ 0)) (fun j => ξ j.succ)

noncomputable def trialOutput (p : Params) (g : Fin p.n → p.E → p.E)
    (ξ : Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial)) : p.E :=
  (coreRun p g (epochCount p * p.n) (initialCore p) ξ).snapshot

structure LocalState (p : Params) where
  phase : ℕ
  index : ℕ
  epoch : ℕ
  trials : List (List (Fin ((2 * p.n).factorial)))
  samples : List (Fin ((2 * p.n).factorial))
  snapshot : p.E
  dual : p.E
  cached : Fin p.n → p.E
  accumulated : p.E
  values : ℝ
  best : p.E
  bestValue : ℝ

noncomputable def beginTrial (p : Params) (s : LocalState p) : LocalState p :=
  match s.trials with
  | [] => {s with phase := 4}
  | row :: tail => {s with
      phase := if epochCount p = 0 then 3 else 1
      index := 0, epoch := 0, trials := tail, samples := row,
      snapshot := p.x0, dual := p.x0, cached := fun _ => 0, accumulated := 0, values := 0}

noncomputable def localQuery (p : Params) (s : LocalState p) : spec.Query p :=
  if s.phase = 2 then
    let w := snapshotWeights p.L0 p.L1 s.cached
    (drawIndex w (s.samples.headD ⟨0, Nat.factorial_pos _⟩),
      mix (epochWeight p s.epoch) (epochIncrement p (epochWeight p s.epoch)) s.snapshot s.dual)
  else (⟨s.index % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩,
    if s.phase = 0 then p.x0 else s.snapshot)

noncomputable def localUpdate (p : Params) (s : LocalState p) (reply : spec.Reply p) : LocalState p := by
  classical
  exact if s.phase = 4 then s
  else if s.phase = 0 then
    if s.index + 1 < p.n then {s with index := s.index + 1, values := s.values + reply.1}
    else beginTrial p {s with bestValue := (s.values + reply.1) / p.n, values := 0}
  else if s.phase = 1 then
    let cache := Function.update s.cached ⟨s.index % p.n, Nat.mod_lt _ (NeZero.pos p.n)⟩ reply.2
    if s.index + 1 < p.n then {s with index := s.index + 1, cached := cache}
    else {s with index := 0, cached := cache, phase := 2}
  else if s.phase = 2 then
    let A := epochWeight p s.epoch
    let a := epochIncrement p A
    let w := snapshotWeights p.L0 p.L1 s.cached
    let i := drawIndex w (s.samples.headD ⟨0, Nat.factorial_pos _⟩)
    let z := s.dual - (a / p.n) • direction w s.cached i reply.2
    let acc := s.accumulated + mix A a s.snapshot z
    if s.index + 1 < p.n then
      {s with index := s.index + 1, samples := s.samples.tail, dual := z, accumulated := acc}
    else {s with
      index := 0, epoch := s.epoch + 1, samples := s.samples.tail
      dual := z, snapshot := (p.n : ℝ)⁻¹ • acc, accumulated := 0,
      phase := if s.epoch + 1 < epochCount p then 1 else 3}
  else
    if s.index + 1 < p.n then {s with index := s.index + 1, values := s.values + reply.1}
    else
      let value := (s.values + reply.1) / p.n
      let s' := if value < s.bestValue then {s with best := s.snapshot, bestValue := value} else s
      beginTrial p s'

abbrev LocalSeeds (p : Params) :=
  Fin (trialCount p) → Fin (epochCount p * p.n) → Fin ((2 * p.n).factorial)

instance (p : Params) : Nonempty (LocalSeeds p) :=
  ⟨fun _ _ => ⟨0, Nat.factorial_pos _⟩⟩

noncomputable def selectBest {E : Type*} (f : E → ℝ) : E → List E → E
  | best, [] => best
  | best, x :: tail => selectBest f (if f x < f best then x else best) tail

noncomputable def amplifiedOutput (p : Params) (f : Fin p.n → p.E → ℝ)
    (g : Fin p.n → p.E → p.E) (ξ : LocalSeeds p) : p.E :=
  if p.Δ ≤ p.ε then p.x0 else
    selectBest (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) p.x0
      (List.ofFn (fun j => trialOutput p g (ξ j)))

noncomputable def localInitial (p : Params) (seed : LocalSeeds p) : LocalState p := {
    phase := if p.Δ ≤ p.ε then 4 else 0
    index := 0, epoch := 0
    trials := List.ofFn (fun j => List.ofFn (seed j)), samples := [], snapshot := p.x0,
    dual := p.x0, cached := fun _ => 0, accumulated := 0, values := 0, best := p.x0, bestValue := 0}

noncomputable def localAcceleration (p : Params) : Algorithm (spec.Query p) (spec.Reply p) (spec.Output p) where
  Seed := LocalSeeds p
  law := ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  State := LocalState p
  initial := localInitial p
  query s := (0, localQuery p s)
  update := localUpdate p
  output s := s.best

end OracleTemplate.GeneralizedFiniteSum
