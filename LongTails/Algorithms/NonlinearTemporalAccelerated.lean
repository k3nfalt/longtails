import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.TemporalAccelerated
import LongTails.Setups.HessianLipschitzTemporalDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

open TemporalDiscrepancy

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def acceleratedFrom (g : ℕ → E → E) (θ μ : ℝ) (s : E × E) : ℕ → E × E
  | 0 => s
  | k + 1 => acceleratedUpdate θ μ (acceleratedFrom g θ μ s k)
      (g k (acceleratedQuery θ (acceleratedFrom g θ μ s k)))

def frozenQuery (x : E) : (b : ℕ) → QueryPlan E E E b
  | 0 => .done 0
  | b + 1 => .ask x (fun g => (frozenQuery x b).map (g + ·))

def warmupPlan (θ μ : ℝ) (b : ℕ) : (n : ℕ) → E × E → QueryPlan E E (E × E) (b * n)
  | 0, s => .done s
  | n + 1, s => by
      simpa only [Nat.mul_succ] using
        (frozenQuery (acceleratedQuery θ s) b).bind
          (fun g => warmupPlan θ μ b n (acceleratedUpdate θ μ s ((b : ℝ)⁻¹ • g)))

def finalPlan (θ μ : ℝ) : (n : ℕ) → E × E → QueryPlan E E (List E) n
  | 0, _ => .done []
  | n + 1, s => .ask (acceleratedQuery θ s) (fun g =>
      let next := acceleratedUpdate θ μ s g
      (finalPlan θ μ n next).map (next.1 :: ·))

def twoPhasePlan (θ₀ θ μ : ℝ) (x0 : E) (b n₀ n : ℕ) :
    QueryPlan E E E (2 * n + b * n₀) :=
  (warmupPlan θ₀ μ b n₀ (x0, x0)).bind (fun s =>
    (finalPlan θ μ (2 * n) s).map (fun xs => (n : ℝ)⁻¹ • (xs.drop n).sum))

def twoPhaseAccelerated (θ₀ θ μ : ℝ) (x0 : E) (b n₀ n : ℕ) : Algorithm E E E :=
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ x0 x0
    (2 * n + b * n₀) (fun _ => twoPhasePlan θ₀ θ μ x0 b n₀ n)

def warmupMomentum (p : Params) : ℝ := 1 / (2 * Real.sqrt (p.L / p.μ))

def finalMomentum (p : Params) : ℝ :=
  1 / (4096 * (1 + Real.sqrt (p.L / p.μ) + p.M * p.D / p.μ ^ 2 +
    p.D / Real.sqrt (p.μ * p.ε)))

def warmupBatch (p : Params) : ℕ := ⌈65536 * (1 + p.M * p.D / p.μ ^ 2)⌉₊

def warmupLength (p : Params) : ℕ :=
  if 4096 * p.M ^ 2 * p.Δ ≤ p.μ ^ 3 then 0
  else ⌈16 / warmupMomentum p * Real.log (2 + 4096 * p.M ^ 2 * p.Δ / p.μ ^ 3)⌉₊

def finalLength (p : Params) : ℕ :=
  ⌈64 / finalMomentum p * Real.log (2 + p.Δ / p.ε)⌉₊

def nonlinearTemporalAccelerated (p : Params) : Algorithm p.E p.E p.E :=
  if p.Δ ≤ p.ε then
    QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
      p.x0 p.x0 0 (fun _ => .done p.x0)
  else twoPhaseAccelerated (warmupMomentum p) (finalMomentum p) p.μ p.x0
    (warmupBatch p) (warmupLength p) (finalLength p)

end OracleTemplate.NonlinearTemporalDiscrepancy
