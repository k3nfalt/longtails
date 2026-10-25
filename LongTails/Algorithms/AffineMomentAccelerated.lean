import LongTails.Algorithms.Batched
import LongTails.Proofs.Clipping
import LongTails.Setups.AffineMomentConvex
import LongTails.Algorithms.AffineGradientEstimator
import LongTails.Algorithms.RobustGeneralizedAccelerated

namespace LongTails.Algorithms.AffineMomentAccelerated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def couplingPoint (A a : ℝ) (x z : E) : E :=
  (a / (A + a)) • z + (1 - a / (A + a)) • x

noncomputable def primalVertex (h : E) : E := (-4 / ‖h‖) • h

noncomputable def primalFraction (h : E) : ℝ := min 1 (‖h‖ / 128)

noncomputable def primalStep (y h : E) : E :=
  (1 - primalFraction h) • y + primalFraction h • primalVertex h

noncomputable def mirrorStep (a : ℝ) (z g : E) : E := OracleTemplate.clip 1 (z - a • g)

structure Tuning where
  p : ℝ
  ε : ℝ
  δ : ℝ
  σ : ℝ
  σ0 : ℝ

noncomputable def tuning (p : LongTails.Setups.AffineMomentConvex.Params) : Tuning :=
  ⟨p.α, min (p.ε / (p.L * p.R ^ 2)) (1 / 4), p.δ, p.σ, p.σ0 / (p.L * p.R)⟩

noncomputable def conjugate (t : Tuning) : ℝ := t.p / (t.p - 1)

noncomputable def confidence (t : Tuning) : ℝ := Real.log (16 + conjugate t + 1 / t.ε + 1 / t.δ)

noncomputable def iterations (t : Tuning) : ℕ :=
  ⌈((2 : ℝ) ^ 48 * confidence t / t.ε) ^ (t.p / (3 * t.p - 2))⌉₊

noncomputable def weightScale (t : Tuning) : ℝ :=
  (2 : ℝ) ^ 40 * (iterations t : ℝ) ^ ((2 - t.p) / t.p)

noncomputable def weight (t : Tuning) (k : ℕ) : ℝ := ((k : ℝ) + 1) / weightScale t

noncomputable def accumulatedWeight (t : Tuning) (k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) + 1) / (2 * weightScale t)

noncomputable def pilotGroups (t : Tuning) : ℕ := ⌈1024 * conjugate t * confidence t⌉₊

noncomputable def pilotRadius (t : Tuning) : ℝ :=
  (iterations t : ℝ) ^ (-(2 * t.p - 1) / t.p)

noncomputable def noiseScale (t : Tuning) : ℝ := t.σ + t.σ0 / pilotRadius t

noncomputable def batchSize (t : Tuning) : ℕ := ⌈(65536 * (1 + noiseScale t)) ^ conjugate t⌉₊

noncomputable def sampleSize (t : Tuning) : ℕ := batchSize t * pilotGroups t

noncomputable def blockSize (t : Tuning) : ℕ := 2 * sampleSize t

noncomputable def point (t : Tuning) (k : ℕ) (s : E × E) : E :=
  couplingPoint (accumulatedWeight t k) (weight t k) s.1 s.2

noncomputable def advance (t : Tuning) (k : ℕ) (s : E × E) (pilot raw : E) : E × E :=
  (primalStep (point t k s) pilot, mirrorStep (weight t k) s.2 raw)

noncomputable def pilotEstimate (t : Tuning) (replies : ℕ → E) : E :=
  OracleTemplate.AffineGradient.center (1 / 24) (pilotRadius t)
    (fun i : Fin (pilotGroups t) => OracleTemplate.RobustGeneralized.meanBlock
      (i * batchSize t) (batchSize t) replies)

noncomputable def blockAdvance (t : Tuning) (k : ℕ) (s : E × E) (replies : ℕ → E) : E × E :=
  advance t k s (pilotEstimate t replies)
    (OracleTemplate.RobustGeneralized.meanBlock (sampleSize t) (sampleSize t) replies)

noncomputable def sampledIterate {Ω : Type*} (t : Tuning) (oracle : E → Ω → E) (ξ : ℕ → Ω) : ℕ → E × E
  | 0 => (0, 0)
  | k + 1 =>
    let s := sampledIterate t oracle ξ k
    blockAdvance t k s (fun i => oracle (point t k s) (ξ (blockSize t * k + i)))

noncomputable def baseAlgorithm (p : LongTails.Setups.AffineMomentConvex.Params) :
    OracleTemplate.Algorithm p.E (ℕ → p.E) p.E where
  State := ℕ × (p.E × p.E)
  initial _ := (0, (0, 0))
  query state := (0, p.x0 + p.R •
    (if iterations (tuning p) ≤ state.1 then state.2.1 else point (tuning p) state.1 state.2))
  update state replies := if iterations (tuning p) ≤ state.1 then state
    else (state.1 + 1, blockAdvance (tuning p) state.1 state.2 replies)
  output state := p.x0 + p.R • state.2.1

noncomputable def algorithm (p : LongTails.Setups.AffineMomentConvex.Params) :
    OracleTemplate.Algorithm p.E p.E p.E :=
  OracleTemplate.batched (n := max 1 (blockSize (tuning p))) (by omega) (baseAlgorithm p)
    (fun state _ => ((baseAlgorithm p).query state).2)
    (fun _ replies i => if hi : i < max 1 (blockSize (tuning p)) then
      (1 / (p.L * p.R)) • replies ⟨i, hi⟩ else 0) 0

noncomputable def runOutput (p : LongTails.Setups.AffineMomentConvex.Params)
    (O : OracleTemplate.Oracle p.E p.E) (K : ℕ) (ξ : (k : ℕ) → O.Seed k) : p.E :=
  OracleTemplate.execute O (algorithm p) (fun _ => K) () ξ

end LongTails.Algorithms.AffineMomentAccelerated
