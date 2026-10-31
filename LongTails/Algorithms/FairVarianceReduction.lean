import LongTails.Algorithms.RadialFairLocation
import LongTails.Algorithms.NormalizedStorm
import LongTails.Proofs.Clipping

namespace OracleTemplate.FairVarianceReduction

structure Config where
  η : ℝ
  R : ℝ
  G : ℝ
  B : ℝ
  T : ℕ
  q : ℕ
  m : ℕ
  b0 : ℕ
  b : ℕ

def Config.isRefresh (cfg : Config) (t : ℕ) : Bool := t % cfg.q == 0

def Config.batch (cfg : Config) (t : ℕ) : ℕ :=
  if cfg.isRefresh t then cfg.b0 else cfg.b

def Config.calls (cfg : Config) : ℕ :=
  ∑ t ∈ Finset.range cfg.T, 2 * cfg.m * cfg.batch t

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def refresh {m : ℕ} (R G : ℝ) (a : Fin m → E) : E :=
  clip (G + 3 * R) (RadialFairLocation.location R a)

noncomputable def increment {m : ℕ} (R B : ℝ) (a b : Fin m → E) : E :=
  clip B (RadialFairLocation.location R a - RadialFairLocation.location R b)

structure State (cfg : Config) (E : Type) where
  outputIndex : Fin (max 1 cfg.T)
  t : ℕ
  blockIndex : ℕ
  sampleIndex : ℕ
  second : Bool
  secondPoint : E
  left : ℕ → E
  right : ℕ → E
  accumulator : E
  point : E
  previous : E
  estimate : E
  selected : E

def points (cfg : Config) (s : State cfg E) : E × E :=
  (s.point, if cfg.isRefresh s.t then s.point else s.previous)

def query (cfg : Config) (s : State cfg E) : E :=
  if s.second then s.secondPoint else (points cfg s).1

noncomputable def commitObservation (cfg : Config) (s : State cfg E) (v : E) : State cfg E :=
  let acc := s.accumulator + v
  if s.blockIndex + 1 < cfg.batch s.t then
    { s with
      blockIndex := s.blockIndex + 1
      sampleIndex := 0
      second := false
      secondPoint := 0
      left := fun _ => 0
      right := fun _ => 0
      accumulator := acc }
  else
    let estimate := (cfg.batch s.t : ℝ)⁻¹ • acc +
      if cfg.isRefresh s.t then 0 else s.estimate
    { s with
      t := s.t + 1
      blockIndex := 0
      sampleIndex := 0
      second := false
      secondPoint := 0
      left := fun _ => 0
      right := fun _ => 0
      accumulator := 0
      point := NormalizedStorm.stormStep cfg.η s.point estimate
      previous := s.point
      estimate := estimate
      selected := if s.t = s.outputIndex.val then s.point else s.selected }

noncomputable def finishBlock (cfg : Config) (s : State cfg E) (right : ℕ → E) : State cfg E :=
  let v := if cfg.isRefresh s.t then
      refresh cfg.R cfg.G (fun i : Fin cfg.m => s.left i)
    else increment cfg.R cfg.B (fun i : Fin cfg.m => s.left i) (fun i : Fin cfg.m => right i)
  commitObservation cfg s v

noncomputable def update (cfg : Config) (s : State cfg E) (reply : E) : State cfg E :=
  if cfg.T ≤ s.t then s else
    if s.second then
      let right := Function.update s.right s.sampleIndex reply
      if s.sampleIndex + 1 < cfg.m then
        { s with
          sampleIndex := s.sampleIndex + 1
          second := false
          secondPoint := 0
          right := right }
      else finishBlock cfg s right
    else
      { s with
        second := true
        secondPoint := (points cfg s).2
        left := Function.update s.left s.sampleIndex reply }

def output (cfg : Config) (s : State cfg E) : E := s.selected

noncomputable def algorithm (cfg : Config) (x0 : E) : Algorithm E E E := by
  letI : Nonempty (Fin (max 1 cfg.T)) := ⟨⟨0, by omega⟩⟩
  exact {
    Seed := Fin (max 1 cfg.T)
    law := ⟨(PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure, inferInstance⟩
    State := State cfg E
    initial := fun τ => {
      outputIndex := τ
      t := 0
      blockIndex := 0
      sampleIndex := 0
      second := false
      secondPoint := 0
      left := fun _ => 0
      right := fun _ => 0
      accumulator := 0
      point := x0
      previous := x0
      estimate := 0
      selected := x0 }
    query := fun s => (0, query cfg s)
    update := update cfg
    output := output cfg }

def Config.blockOffset (cfg : Config) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, cfg.batch j

noncomputable def blockObservation {Ω : Type} (cfg : Config) (g : E → Ω → E)
    (t : ℕ) (x y : E) (ω : Fin cfg.m → Ω) : E :=
  if cfg.isRefresh t then refresh cfg.R cfg.G (fun i => g x (ω i))
  else increment cfg.R cfg.B (fun i => g x (ω i)) (fun i => g y (ω i))

noncomputable def batchObservation {Ω : Type} (cfg : Config) (g : E → Ω → E)
    (t : ℕ) (x y : E) (ξ : ℕ → Fin cfg.m → Ω) : E :=
  (cfg.batch t : ℝ)⁻¹ • ∑ j ∈ Finset.range (cfg.batch t),
    blockObservation cfg g t x y (ξ (cfg.blockOffset t + j))

noncomputable def trajectory {Ω : Type} (cfg : Config) (g : E → Ω → E)
    (x0 : E) (ξ : ℕ → Fin cfg.m → Ω) : ℕ → E × E × E
  | 0 => (x0, x0, 0)
  | t + 1 =>
    let s := trajectory cfg g x0 ξ t
    let v := batchObservation cfg g t s.1 s.2.1 ξ + if cfg.isRefresh t then 0 else s.2.2
    (NormalizedStorm.stormStep cfg.η s.1 v, s.1, v)

noncomputable def direction {Ω : Type} (cfg : Config) (g : E → Ω → E)
    (x0 : E) (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) : E :=
  (trajectory cfg g x0 ξ (t + 1)).2.2

end OracleTemplate.FairVarianceReduction
