import LongTails.Setups.DistributedComponentSmoothNonconvex
import LongTails.Algorithms.MultirateBatches
import LongTails.Algorithms.LeonTrajectory
import LongTails.Algorithms.LeonProtocol

namespace LongTails.Algorithms.MultirateSchedule

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex

noncomputable abbrev δ (p : Params) := LeonTuning.resolution (network p)
noncomputable abbrev K (p : Params) := LeonTuning.iterations (network p)
noncomputable def level (p : Params) := LeonTuning.height (network p) + 1

noncomputable def noise (p : Params) (i : Fin p.n) : ℝ :=
  p.σ i * √(p.h i : ℝ) / (p.n * δ p)

noncomputable def weight (p : Params) (i : Fin p.n) : ℝ := √(p.L i / p.n)

noncomputable def batch (p : Params) (i : Fin p.n) : ℕ+ :=
  MultirateBatches.count (fun j => (p.h j : ℝ)) (noise p) (weight p) i

noncomputable def width (p : Params) := LeonTuning.width (network p) (level p)

noncomputable def transmission (p : Params) : Time :=
  p.l + p.b * (p.d * width p + clockBits : ℕ)

noncomputable def service (p : Params) (i : Fin p.n) : Time :=
  (batch p i : ℕ) * p.h i + transmission p

noncomputable def tick (p : Params) : Time :=
  Real.toNNReal ((∑ i, p.L i * (service p i : ℝ)) / ∑ i, p.L i)

noncomputable def period (p : Params) (i : Fin p.n) : ℕ+ :=
  ⟨max 1 ⌈(service p i : ℝ) / (tick p : ℝ)⌉₊, by omega⟩

noncomputable def due (p : Params) (k : ℕ) : List (Fin p.n) :=
  (List.finRange p.n).filter fun i => k % (period p i : ℕ) = 0

noncomputable def block (p : Params) (i : Fin p.n) (k : ℕ) := k / (period p i : ℕ)

noncomputable def anchor (p : Params) (i : Fin p.n) (j : ℕ) := (j - 1) * (period p i : ℕ)

abbrev Code (p : Params) := Fin p.d → ℤ
abbrev Table (p : Params) := Fin p.n → List Bool
abbrev Model (p : Params) := LeonTrajectory.Model (network p)

noncomputable def packet (p : Params) (values : List (Point p)) : List Bool :=
  DashaModular.encode p.d (width p) (LeonAggregate.localCodes (LeonTuning.spacing (network p)) 0
    (LeonTrajectory.mean (network p) values))

noncomputable def estimate (p : Params) (bs : Table p) : Point p :=
  LeonAggregate.decode p.n (width p) (LeonTuning.spacing (network p))
    (LeonTuning.radius (network p) (level p)) 0 (fun j => ∑ i, DashaModular.decode p.d (width p) (bs i) j)

noncomputable def update (p : Params) (model : Model p) (bs : Table p) : Model p :=
  LeonTrajectory.applyEstimate (network p) model 0 (estimate p bs)

noncomputable def publish (p : Params) (i : Fin p.n) (x : Point p)
    (next : LeonProtocol.Program (network p)) : LeonProtocol.Program (network p) :=
  .sample (x, batch p i) fun vs => LeonProtocol.post (fun _ => packet p vs) next (List.finRange p.n)

noncomputable def program (p : Params) (i : Fin p.n) (a b : ℕ) :
    List ℕ → Model p → Table p → LeonProtocol.Program (network p)
  | [], model, _ => .finish (LeonTrajectory.output (network p) model a b)
  | k :: ks, model, table =>
    let next := LeonProtocol.collect (fun data => program p i a b ks (update p model data) data)
      (due p k) table
    if k % (period p i : ℕ) = 0 ∧ k + period p i < K p then publish p i model.point next else next

noncomputable def initialProgram (p : Params) (i : Fin p.n) (a b : ℕ) :
    LeonProtocol.Program (network p) :=
  if smoothness p = 0 then .finish p.x0
  else publish p i p.x0 (program p i a b (List.range (K p)) (LeonTrajectory.initial (network p)) (fun _ => []))

noncomputable def algorithm (p : Params) (limit : Time) :=
  { LeonProtocol.algorithm (network p) limit with
    initial := fun i ab => ⟨initialProgram p i ab.1 ab.2, fun _ => [], false⟩ }

noncomputable def output (p : Params) (model : Model p) (ab : Fin (K p) × Fin (K p)) : Point p :=
  LeonTrajectory.output (network p) model ab.1 ab.2

end LongTails.Algorithms.MultirateSchedule
