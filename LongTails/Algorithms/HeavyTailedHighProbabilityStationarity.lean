import LongTails.Setups.HeavyTailedHighProbabilityStationarity
import LongTails.Algorithms.HighProbabilityStationarity

namespace LongTails.Algorithms.HeavyTailedHighProbabilityStationarity

open OracleTemplate RobustGradient
open LongTails.Algorithms.HighProbabilityStationarity LongTails.Algorithms.StochasticEnvelopeProgram

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def blockEstimate (r B : ℝ) (m0 mc : ℕ) (v : Fin (m0 + mc) → E) : E :=
  let c := gradedPilot r 0 (fun i : Fin m0 => v (Fin.castAdd mc i)) 0
  c + (1 / (mc : ℝ)) • ∑ i : Fin mc, clip B (v (Fin.natAdd m0 i) - c)

def blockAggregate {k r : ℕ} (hk : 0 < k) (α : ℝ) (est : (Fin r → E) → E)
    (v : Fin (k * r) → E) : E :=
  OracleTemplate.SublevelRobustGradient.robustCenter hk (2 * α)
    (fun i => est (fun l => v (finProdFinEquiv (i, l))))

def testPassesH {β : Type*} (α τ : ℝ) {r : ℕ} (est : (Fin r → E) → E) {k : ℕ} (hk : 0 < k)
    (entry : Option β) (v : Fin (k * r) → E) : Bool := by
  classical
  exact entry.isSome && decide (‖blockAggregate hk α est v‖ ≤ τ)

def testPlanH {J : ℕ} (α τ : ℝ) {r : ℕ} (est : (Fin r → E) → E) {k : ℕ} (hk : 0 < k) (x0 : E)
    (Y : Fin J → E) (entry : Option (Fin J)) : QueryPlan E E Bool (k * r) :=
  (samplePlan ((entry.map Y).getD x0) (k * r)).map (testPassesH α τ est hk entry)

def roundPlanH (ε α : ℝ) (Λ k0 r : ℕ) (est : (Fin r → E) → E) (hk0 : 0 < k0) (x0 : E)
    (Y : Fin (2 ^ Λ) → E) (s : Ladder (2 ^ Λ)) : QueryPlan E E (Ladder (2 ^ Λ)) (k0 * r * 2 ^ Λ) :=
  castPlan (round_calls Λ k0 r (min s.1 Λ) (min_le_right _ _))
    ((collectPlans (2 ^ (Λ - min s.1 Λ)) (fun i =>
      testPlanH α (threshold ε α (min s.1 Λ)) est
        (Nat.mul_pos hk0 (Nat.two_pow_pos (min s.1 Λ))) x0 Y (slots s.2 i))).map
      (fun pass => (s.1 + 1, nextSlots s.2 pass)))

def phaseTwoH (ε α : ℝ) (Λ k0 r : ℕ) (est : (Fin r → E) → E) (hk0 : 0 < k0) (x0 : E)
    (Y : Fin (2 ^ Λ) → E) : QueryPlan E E E ((k0 * r * 2 ^ Λ) * (Λ + 1)) :=
  (stepRepeat (Λ + 1) (roundPlanH ε α Λ k0 r est hk0 x0 Y) (0, fun j => some j)).map
    (fun s => ((s.2 ⟨0, Nat.two_pow_pos Λ⟩).map Y).getD x0)

def methodH (B η ε α : ℝ) (K mp mc T Λ k0 r : ℕ) (est : (Fin r → E) → E) (hk0 : 0 < k0)
    (x0 : E) (τ : Fin (2 ^ Λ) → Fin T) :
    QueryPlan E E E ((k0 * r * 2 ^ Λ) * (Λ + 1) + (mp + mc) * T) :=
  (phaseOne B η K mp mc T x0).bind
    (fun s => phaseTwoH ε α Λ k0 r est hk0 x0 (fun j => s.path (τ j)))

end

section Tuning

open LongTails.Setups.HeavyTailedHighProbabilityStationarity

variable (q : Params)

noncomputable def tailFactor : ℝ := 2 ^ 45 * (q.σ / q.ε) ^ q.p

noncomputable def effectiveSigma : ℝ :=
  q.ε * max (Real.sqrt (tailFactor q)) (tailFactor q ^ (1 / (2 * (q.p - 1))))

noncomputable def varianceParams : LongTails.Setups.HighProbabilityStationarity.Params where
  E := q.E
  Ω := q.Ω
  L := q.L
  σ := effectiveSigma q
  Δ := q.Δ
  ε := q.ε
  δ := q.δ
  x0 := q.x0

noncomputable def pilotSamples : ℕ := 2 * pilotSize (varianceParams q)

noncomputable def ladderTolerance : ℝ := q.ε + q.ε / 2 ^ 18

noncomputable def testRadius : ℝ := 2 ^ 10 * (q.σ + q.ε)

noncomputable def testClip : ℝ :=
  radius (varianceParams q) * ((rounds (varianceParams q) : ℝ) + 1) ^ (1 / q.p)

noncomputable def testSize : ℕ :=
  ⌈2 ^ 14 * noiseScale (varianceParams q) ^ 2 *
    ((rounds (varianceParams q) : ℝ) + 1) ^ ((2 - q.p) / q.p) /
      accuracy (varianceParams q) ^ 2⌉₊

noncomputable def seedLawH :
    MeasureTheory.ProbabilityMeasure
      (Fin (2 ^ rounds (varianceParams q)) → Fin (steps (varianceParams q))) :=
  seedLaw (varianceParams q)

noncomputable def testEstimate : (Fin (4 + testSize q) → q.E) → q.E :=
  blockEstimate (testRadius q) (testClip q) 4 (testSize q)

noncomputable def algorithm : Algorithm q.E q.E q.E :=
  QueryPlan.algorithm (seedLawH q) q.x0 q.x0 _ (fun τ =>
    methodH (radius (varianceParams q)) (stepSize (varianceParams q)) (ladderTolerance q)
      (accuracy (varianceParams q)) (levels (varianceParams q)) (pilotSamples q)
      (clipSize (varianceParams q)) (steps (varianceParams q)) (rounds (varianceParams q)) 8
      (4 + testSize q) (testEstimate q) (by norm_num) q.x0 τ)

end Tuning

end LongTails.Algorithms.HeavyTailedHighProbabilityStationarity
