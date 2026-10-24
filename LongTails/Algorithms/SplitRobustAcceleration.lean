import LongTails.Setups.HeavyTailedStrongGrowthConvex
import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Algorithms.Accelerated
import LongTails.Algorithms.Batched
import Mathlib.Logic.Equiv.Fin.Basic

namespace OracleTemplate.SplitRobustAcceleration

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def core (L V : ℝ) (x0 : E) : Algorithm E (E × E) E where
  State := ℕ × E × E
  initial _ := (0, x0, x0)
  query s := (0, Gradient.acceleratedQuery s)
  update s reply :=
    (s.1 + 1, Gradient.acceleratedQuery s - (1 / L) • reply.1,
      s.2.2 - (((s.1 : ℝ) + 1) / (32 * L * V)) • reply.2)
  output s := s.2.1

noncomputable def method (L V Λ : ℝ) (k b : ℕ) (x0 : E) : Algorithm E E E :=
  batched (by positivity : 0 < (k + 2) * (b + 1)) (core L V x0)
    (fun s _ => Gradient.acceleratedQuery s)
    (fun _ replies => MultiplicativeRobustEstimator.estimate Λ
      (fun i j => replies (finProdFinEquiv (i, j)))) 0

noncomputable def output (O : Oracle E E)
    (L V Λ : ℝ) (k b N : ℕ) (x0 : E) (ξ : (t : ℕ) → O.Seed t) : E :=
  execute O (method L V Λ k b x0) (fun _ => (k + 2) * (b + 1) * N) () ξ

noncomputable def run {Ω : Type*} (g : E → Ω → E × E) (L V : ℝ) :
    (K : ℕ) → ℕ → E → E → (Fin K → Ω) → E × E
  | 0, _, x, z, _ => (x, z)
  | K + 1, k, x, z, ξ =>
      let y := Gradient.acceleratedQuery (k, x, z)
      let reply := g y (ξ 0)
      run g L V K (k + 1) (y - (1/L) • reply.1)
        (z - (((k : ℝ)+1)/(32*L*V)) • reply.2) (fun i => ξ i.succ)

noncomputable def capped {Q R U : Type} (A : Algorithm Q R U) (K : ℕ) : Algorithm Q R U where
  Seed := A.Seed
  law := A.law
  State := ℕ × A.State
  initial seed := (K,A.initial seed)
  query s := A.query s.2
  update s reply := if s.1 = 0 then s else (s.1-1,A.update s.2 reply)
  output s := A.output s.2

open LongTails.Setups.HeavyTailedStrongGrowthConvex

noncomputable def scale (q : Params) : ℝ := max 1 (q.L*q.R^2/q.ε)
noncomputable def clippingScale (q : Params) : ℝ :=
  if q.ρ = 0 then 1 else (scale q)^(1/(3*q.p-2))
noncomputable def variance (q : Params) : ℝ := 32*(clippingScale q)^(2-q.p)
noncomputable def pilotCount (q : Params) : ℕ :=
  if q.ρ = 0 then 128 else 128+⌈2*Real.log (scale q)⌉₊
noncomputable def batchExtra (q : Params) : ℕ := ⌈(17179869184*q.ρ)^(1/(q.p-1))⌉₊
noncomputable def iterations (q : Params) : ℕ :=
  if q.ρ = 0 then ⌈128*Real.sqrt (scale q)⌉₊ else ⌈128*(scale q)^(q.p/(3*q.p-2))⌉₊
noncomputable def calls (q : Params) : ℕ := (pilotCount q+2)*(batchExtra q+1)*iterations q
noncomputable def algorithm (q : Params) : Algorithm q.E q.E q.E :=
  capped (method q.L (variance q) (clippingScale q) (pilotCount q) (batchExtra q) q.x0) (calls q)
noncomputable def lastIterate (q : Params) (O : Oracle q.E q.E)
    (ξ : (t : ℕ) → O.Seed t) : q.E :=
  output O q.L (variance q) (clippingScale q) (pilotCount q) (batchExtra q) (iterations q) q.x0 ξ

end OracleTemplate.SplitRobustAcceleration
