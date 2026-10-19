import LongTails.Template
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OracleTemplate.MixedNoise

structure Config where
  η : ℝ
  T : ℕ
  m : ℕ
  batch : ℕ → ℕ → ℕ

structure RepresentativeSeed (cfg : Config) where
  outputIndex : Fin (max 1 cfg.T)
  representatives : (i : Fin (cfg.m + 1) × Fin (cfg.T + 1)) → Fin (4 ^ i.1.val)
  deriving Fintype

instance (cfg : Config) : MeasurableSpace (RepresentativeSeed cfg) := ⊤

instance (cfg : Config) : MeasurableSingletonClass (RepresentativeSeed cfg) :=
  ⟨fun _ => trivial⟩

instance (cfg : Config) : Nonempty (RepresentativeSeed cfg) :=
  ⟨⟨⟨0, by omega⟩, fun _ => ⟨0, by positivity⟩⟩⟩

structure BatchTask where
  t : ℕ := 0
  level : ℕ := 0
  size : ℕ := 1
  finish : Bool := true
  deriving Inhabited

def Config.levels (cfg : Config) (t : ℕ) : List ℕ :=
  if t = 0 then [cfg.m] else (List.range (cfg.m + 1)).filter (fun l => t % 4 ^ l = 0)

def Config.iterationTasks (cfg : Config) (t : ℕ) : List BatchTask :=
  (cfg.levels t).mapIdx fun i l =>
    { t := t, level := l, size := max 1 (cfg.batch t l),
      finish := i + 1 = (cfg.levels t).length }

def Config.prefixTasks (cfg : Config) (t : ℕ) : List BatchTask :=
  (List.range t).flatMap cfg.iterationTasks

def Config.tasks (cfg : Config) : List BatchTask := cfg.prefixTasks cfg.T

def Config.eventOffset (cfg : Config) (t : ℕ) : ℕ := (cfg.prefixTasks t).length

def Config.calls (cfg : Config) : ℕ := 2 * (cfg.tasks.map BatchTask.size).sum

structure RepresentativeState (cfg : Config) (E : Type) where
  seed : RepresentativeSeed cfg
  taskIndex : ℕ
  sampleIndex : ℕ
  second : Bool
  firstReply : E
  secondPoint : E
  accumulator : E
  xs : ℕ → E
  estimates : ℕ → E

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def anchorIndex (cfg : Config) (seed : RepresentativeSeed cfg) (t l : ℕ) : ℕ :=
  if l = 0 then t else
    let h := 4 ^ l
    let boundary := t / h * h
    if boundary = 0 then 0 else
      if hl : l ≤ cfg.m then
        if ht : boundary ≤ cfg.T then
          boundary - h + (seed.representatives (⟨l, by omega⟩, ⟨boundary, by omega⟩)).val
        else 0
      else 0

def taskPoints (cfg : Config) (s : RepresentativeState cfg E) : E × E :=
  let task := cfg.tasks[s.taskIndex]!
  let left := s.xs (anchorIndex cfg s.seed task.t task.level)
  if task.level = cfg.m then (left, left)
  else (left, s.xs (anchorIndex cfg s.seed task.t (task.level + 1)))

noncomputable def representativeQuery (cfg : Config) (s : RepresentativeState cfg E) : E :=
  if s.second then s.secondPoint else (taskPoints cfg s).1

noncomputable def representativeCommit (cfg : Config) (s : RepresentativeState cfg E) (acc : E) :
    RepresentativeState cfg E :=
  let task := cfg.tasks[s.taskIndex]!
  let estimates := Function.update s.estimates task.level ((task.size : ℝ)⁻¹ • acc)
  let xs := if task.finish then
    Function.update s.xs (task.t + 1)
      (s.xs task.t - cfg.η • ∑ l ∈ Finset.range (cfg.m + 1), estimates l)
    else s.xs
  { s with
    taskIndex := s.taskIndex + 1
    sampleIndex := 0
    second := false
    accumulator := 0
    firstReply := 0
    secondPoint := 0
    estimates := estimates
    xs := xs }

noncomputable def representativeUpdate (cfg : Config) (s : RepresentativeState cfg E) (reply : E) :
    RepresentativeState cfg E :=
  if cfg.tasks.length ≤ s.taskIndex then s else
    if s.second then
      let task := cfg.tasks[s.taskIndex]!
      let acc := s.accumulator + (if task.level = cfg.m then s.firstReply else s.firstReply - reply)
      if s.sampleIndex + 1 < task.size then
        { s with
          sampleIndex := s.sampleIndex + 1
          second := false
          accumulator := acc
          firstReply := 0
          secondPoint := 0 }
      else representativeCommit cfg s acc
    else
      { s with second := true, firstReply := reply, secondPoint := (taskPoints cfg s).2 }

noncomputable def representativeOutput (s : RepresentativeState cfg E) : E :=
  s.xs s.seed.outputIndex.val

noncomputable def multiscaleRepresentatives (cfg : Config) (x0 : E) : Algorithm E E E where
  Seed := RepresentativeSeed cfg
  law := ⟨(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure, inferInstance⟩
  State := RepresentativeState cfg E
  initial seed := {
    seed := seed
    taskIndex := 0
    sampleIndex := 0
    second := false
    firstReply := 0
    secondPoint := 0
    accumulator := 0
    xs := fun _ => x0
    estimates := fun _ => 0 }
  query s := (0, representativeQuery cfg s)
  update := representativeUpdate cfg
  output := representativeOutput

noncomputable def iterationTarget (L Δ ε : ℝ) : ℕ := ⌈16 * L * Δ / ε ^ 2⌉₊

noncomputable def hierarchyDepth (L M σ Δ ε : ℝ) : ℕ :=
  if σ = 0 then 0 else
    if M = 0 then Nat.log 4 (iterationTarget L Δ ε)
    else Nat.log 4 (min (iterationTarget L Δ ε) (max 1 ⌊2 * L * σ / (M * ε)⌋₊))

noncomputable def tunedConfig (L r M σ Δ ε : ℝ) : Config :=
  let η := 1 / (2 * L)
  let m := hierarchyDepth L M σ Δ ε
  let q : ℕ := 4 ^ m
  let N := iterationTarget L Δ ε
  let T : ℕ := if 2 * L * Δ ≤ ε ^ 2 then 0 else q * ⌈(N : ℝ) / q⌉₊
  let B := max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊
  let B0 := max B ⌈4096 * (r * q + σ ^ 2 / ε ^ 2)⌉₊
  { η := η
    T := T
    m := m
    batch := fun t l =>
      if l = m then (if t = 0 then B0 else B)
      else max 1 ⌈4096 * (r * 2 ^ l + M ^ 2 * η ^ 2 * 2 ^ m * ((2 : ℝ) ^ l) ^ 3)⌉₊ +
        if t < 4 ^ (l + 1) then ⌈4096 * r * 2 ^ m * (2 : ℝ) ^ l⌉₊ else 0 }

end OracleTemplate.MixedNoise
