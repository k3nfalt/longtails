import LongTails.Setups.DistributedHessianLipschitzNonconvex
import LongTails.Algorithms.DistributedNormalizedCompression
import LongTails.Algorithms.Clipping
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

namespace LongTails.Algorithms.DistributedNormalizedDownlink

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open DistributedNormalizedCompression

structure Config where
  iterations : ℕ+
  batch : ℕ+
  uplinkWidth : ℕ
  downlinkWidth : ℕ
  uplinkCount : ℕ+
  downlinkCount : ℕ+
  refreshPeriod : ℕ+
  fullUplink : Bool
  stepSize : ℝ
  clipRadius : ℝ
  uplinkSpacing : ℝ
  incrementSpacing : ℝ
  refreshSpacing : ℝ

abbrev Draws (p : Params) := ℕ → Fin p.n → ℕ → Fin p.d × ℝ

abbrev Seed (p : Params) (cfg : Config) := Fin cfg.iterations × Draws p

noncomputable def drawLaw (p : Params) [Nonempty (Fin p.d)] :
    MeasureTheory.ProbabilityMeasure (Fin p.d × ℝ) :=
  ⟨(PMF.uniformOfFintype (Fin p.d)).toMeasure.prod
    (DistributedRandomRounding.uniform : MeasureTheory.Measure ℝ), inferInstance⟩

noncomputable def drawsLaw (p : Params) [Nonempty (Fin p.d)] :
    MeasureTheory.ProbabilityMeasure (Draws p) :=
  ⟨MeasureTheory.Measure.infinitePi (fun _ : ℕ =>
    MeasureTheory.Measure.pi (fun _ : Fin p.n =>
      MeasureTheory.Measure.infinitePi (fun _ : ℕ => (drawLaw p : MeasureTheory.Measure _)))),
    inferInstance⟩

noncomputable def seedLaw (p : Params) (cfg : Config) [Nonempty (Fin p.d)] :
    MeasureTheory.ProbabilityMeasure (Seed p cfg) :=
  ⟨(PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod
    (drawsLaw p : MeasureTheory.Measure _), inferInstance⟩

structure Iterate (p : Params) where
  root : Point p
  workers : Fin p.n → Point p

noncomputable def initial (p : Params) : Iterate p := ⟨p.x0, fun _ => p.x0⟩

noncomputable def batchMean (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (i : Fin p.n) (x : Point p) : Point p :=
  (cfg.batch : ℝ)⁻¹ • ∑ j ∈ Finset.range cfg.batch,
    g i x (samples i (k * cfg.batch + j))

noncomputable def uplinkMessage (p : Params) (cfg : Config) (draws : Draws p)
    (k : ℕ) (i : Fin p.n) (v : Point p) : List Bool :=
  let c := OracleTemplate.clip cfg.clipRadius v
  if cfg.fullUplink then
    DistributedRandomRounding.message p.d cfg.uplinkWidth cfg.uplinkSpacing c
      (fun j => (draws (2 * k) i j.val).2)
  else
    sparseMessage cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing c
      (fun q => (draws (2 * k) i q.val).1) (fun q => (draws (2 * k) i q.val).2)

noncomputable def uplinkReceive (p : Params) (cfg : Config) (draws : Draws p)
    (k : ℕ) (i : Fin p.n) (bits : List Bool) : Point p :=
  if cfg.fullUplink then fullReceive p.d cfg.uplinkWidth cfg.uplinkSpacing bits
  else sparseReceive cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing
    (fun q => (draws (2 * k) i q.val).1) bits

noncomputable def estimator (p : Params) (cfg : Config) (draws : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (s : Iterate p) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, uplinkReceive p cfg draws k i
    (uplinkMessage p cfg draws k i (batchMean p cfg g samples k i (s.workers i)))

noncomputable def increment (cfg : Config) {p : Params} (v : Point p) : Point p :=
  -(cfg.stepSize / ‖v‖) • v

def refresh (cfg : Config) (k : ℕ) : Bool := (k + 1) % cfg.refreshPeriod = 0

noncomputable def downlinkMessage (p : Params) (cfg : Config) (draws : Draws p)
    (k : ℕ) (i : Fin p.n) (x u : Point p) : List Bool :=
  if refresh cfg k then
    DistributedRandomRounding.message p.d cfg.downlinkWidth cfg.refreshSpacing (x - p.x0)
      (fun j => (draws (2 * k + 1) i j.val).2)
  else
    sparseMessage cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing u
      (fun q => (draws (2 * k + 1) i q.val).1) (fun q => (draws (2 * k + 1) i q.val).2)

noncomputable def downlinkReceive (p : Params) (cfg : Config) (draws : Draws p)
    (k : ℕ) (i : Fin p.n) (previous : Point p) (bits : List Bool) : Point p :=
  if refresh cfg k then p.x0 + fullReceive p.d cfg.downlinkWidth cfg.refreshSpacing bits
  else previous + sparseReceive cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing
    (fun q => (draws (2 * k + 1) i q.val).1) bits

noncomputable def next (p : Params) (cfg : Config) (draws : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (s : Iterate p) : Iterate p :=
  let u := increment cfg (estimator p cfg draws g samples k s)
  let x := s.root + u
  ⟨x, fun i => downlinkReceive p cfg draws k i (s.workers i) (downlinkMessage p cfg draws k i x u)⟩

noncomputable def trajectory (p : Params) (cfg : Config) (draws : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
    ℕ → Iterate p
  | 0 => initial p
  | k + 1 => next p cfg draws g samples k (trajectory p cfg draws g samples k)

noncomputable def output (p : Params) (cfg : Config) (draws : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (index : Fin cfg.iterations) : Point p :=
  (trajectory p cfg draws g samples index.val).root

end LongTails.Algorithms.DistributedNormalizedDownlink
