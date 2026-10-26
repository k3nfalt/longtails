import LongTails.Setups.AffineMomentConvex
import LongTails.Algorithms.StochasticEnvelopeProgram

namespace LongTails.Algorithms.StochasticEnvelope
open OracleTemplate MeasureTheory
open StochasticEnvelopeProgram

structure Parameters where
  smoothness : ℕ → ℝ
  moment : ℕ → ℝ
  additive : ℕ → ℝ
  relative : ℕ → ℝ
  baseWork : ℝ
  levelProbability : unitInterval
  batchSize : ℕ
  recoveryRadius : ℕ → ℝ
  recoveryDistance : ℕ → ℝ
  recoveryFailure : ℝ

def Seed : ℕ → Type
  | 0 => Unit
  | i + 1 => ℕ × (ℕ → Seed i)

instance seedMeasurable : (i : ℕ) → MeasurableSpace (Seed i)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | i + 1 => by
    letI := seedMeasurable i
    exact inferInstanceAs (MeasurableSpace (ℕ × (ℕ → Seed i)))

noncomputable def seedLaw (v : unitInterval) : (i : ℕ) → ProbabilityMeasure (Seed i)
  | 0 => by
    change ProbabilityMeasure Unit
    exact ⟨Measure.dirac (), inferInstance⟩
  | i + 1 => by
    change ProbabilityMeasure (ℕ × (ℕ → Seed i))
    exact ⟨(ProbabilityTheory.geometricMeasure v).prod
      (Measure.infinitePi fun _ : ℕ => (seedLaw v i : Measure (Seed i))), inferInstance⟩

noncomputable def levelCalls (c : Parameters) (i n : ℕ) : ℕ :=
  let κ := (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)
  let C := fun ell => (approximationTuning κ (c.moment i) (c.relative i)
    (c.baseWork * (2 : ℝ) ^ ell)).calls
  C 0 + C (n + 1) + C n

noncomputable def calls (c : Parameters) : (i : ℕ) → Seed i → ℕ
  | 0, _ => c.batchSize
  | i + 1, seed => slotCalls (fun j => calls c i (seed.2 j)) (levelCalls c i seed.1) 0

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def batchPlan (B : ℕ) (point : E) : QueryPlan E E E B :=
  (castPlan (Nat.one_mul B) (collectPlans B (fun _ => .ask point fun reply => .done reply))).map
    (fun values => (B : ℝ)⁻¹ • ∑ i, values i)

noncomputable def gradientPlan (c : Parameters) : (i : ℕ) → (seed : Seed i) →
    E → QueryPlan E E E (calls c i seed)
  | 0, _, point => batchPlan c.batchSize point
  | i + 1, seed, point =>
      substitutePlan (fun j => calls c i (seed.2 j))
        (fun j => gradientPlan c i (seed.2 j))
        (tunedEnvelopePlan (c.smoothness i) (c.smoothness (i + 1)) (c.moment i)
          (c.additive i) (c.relative i) c.baseWork c.levelProbability point seed.1) 0

def RecoverySeed : ℕ → Type
  | 0 => Unit
  | i + 1 => (ℕ → Seed i) × RecoverySeed i

instance recoverySeedMeasurable : (i : ℕ) → MeasurableSpace (RecoverySeed i)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | i + 1 => by
    letI := recoverySeedMeasurable i
    exact inferInstanceAs (MeasurableSpace ((ℕ → Seed i) × RecoverySeed i))

noncomputable def recoverySeedLaw (v : unitInterval) : (i : ℕ) → ProbabilityMeasure (RecoverySeed i)
  | 0 => by
    change ProbabilityMeasure Unit
    exact ⟨Measure.dirac (), inferInstance⟩
  | i + 1 => by
    change ProbabilityMeasure ((ℕ → Seed i) × RecoverySeed i)
    exact ⟨(Measure.infinitePi fun _ : ℕ => (seedLaw v i : Measure (Seed i))).prod
      (recoverySeedLaw v i : Measure (RecoverySeed i)), inferInstance⟩

noncomputable def recoveryLevelTuning (c : Parameters) (i : ℕ) : RecoveryTuning :=
  recoveryTuning (c.smoothness i) (c.smoothness (i + 1)) (c.moment i)
    (c.additive i) (c.relative i) (c.recoveryRadius i) (c.recoveryDistance i) c.recoveryFailure

noncomputable def recoveryCalls (c : Parameters) : (i : ℕ) → RecoverySeed i → ℕ
  | 0, _ => 0
  | i + 1, seed => recoveryCalls c i seed.2 +
      slotCalls (fun j => calls c i (seed.1 j)) (recoveryLevelTuning c i).calls 0

noncomputable def recoverPlan (c : Parameters) : (i : ℕ) → (seed : RecoverySeed i) →
    E → QueryPlan E E E (recoveryCalls c i seed)
  | 0, _, point => .done point
  | i + 1, seed, point =>
      (substitutePlan (fun j => calls c i (seed.1 j))
        (fun j => gradientPlan c i (seed.1 j))
        (StochasticEnvelopeProgram.recoveryPlan (c.smoothness i) (c.smoothness (i + 1))
          (c.moment i) (c.additive i) (c.relative i) (c.recoveryRadius i)
          (c.recoveryDistance i) c.recoveryFailure point) 0).bind
        (recoverPlan c i seed.2)

noncomputable def output (c : Parameters) (d : ℕ) (x0 : E) : Algorithm E E E :=
  StochasticEnvelopeProgram.algorithm (recoverySeedLaw c.levelProbability d) x0 x0
    (fun seed => ⟨recoveryCalls c d seed, recoverPlan c d seed x0⟩)

noncomputable def parameters (L R ε δ σ0 σ p : ℝ) (d : ℕ) (hd : 1 ≤ d) : Parameters :=
  let q := p / (p - 1)
  let T := L * R ^ 2 / ε
  let V := (σ0 * R / ε) ^ q
  let M := 4 + T + V + 1 / δ
  let W := 2 + q + Real.log M
  let H := W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ (3 : ℕ))
  let k := (2 * T) ^ (1 / (d : ℝ))
  let κ := k + 1
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun i : ℕ => q * (1 + t) ^ i
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  let B := ⌈(4 * (1 + σ) * κ ^ 2 * H) ^ q⌉₊
  let s := 4 * σ0 * (B : ℝ) ^ (-(1 / q))
  let a := κ ^ (-2 : ℝ) / H
  let μ := fun i : ℕ => L / k ^ i
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have ht : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity : 0 < (d : ℝ) ^ 2)).2
    nlinarith
  { smoothness := μ
    moment := fun i => Q i / (Q i - 1)
    additive := fun i => s * ρ ^ i
    relative := fun i => a * ρ ^ i
    baseWork := m
    levelProbability := StochasticEnvelopeProgram.levelProbability t ht ht1
    batchSize := B
    recoveryRadius := fun i => Real.sqrt (2 * ε / μ (i + 1))
    recoveryDistance := fun i => Real.sqrt (ε / (2 * (d : ℝ) * μ (i + 1) * κ))
    recoveryFailure := δ / (4 * (d : ℝ)) }

noncomputable def depth (L R ε δ σ0 p : ℝ) : ℕ :=
  max 1 ⌈Real.sqrt (Real.log (4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ (p / (p - 1)) + 1 / δ))⌉₊

noncomputable def algorithm (p : LongTails.Setups.AffineMomentConvex.Params) : Algorithm p.E p.E p.E :=
  if p.L * p.R ^ 2 / p.ε ≤ 1 then
    StochasticEnvelopeProgram.algorithm (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit)
      p.x0 p.x0 (fun _ => ⟨0, QueryPlan.done p.x0⟩)
  else
    output (parameters p.L p.R p.ε p.δ p.σ0 p.σ p.α
      (depth p.L p.R p.ε p.δ p.σ0 p.α) (Nat.le_max_left _ _))
      (depth p.L p.R p.ε p.δ p.σ0 p.α) p.x0

end LongTails.Algorithms.StochasticEnvelope
