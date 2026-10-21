import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import LongTails.Algorithms.DampedGeneralizedAccelerated
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling)

noncomputable def batchReply {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (oracle : E → Ω → E) (x : E) {m : ℕ} (ξ : Fin m → Ω) : E :=
  (1/(m : ℝ)) • ∑ i, oracle x (ξ i)

noncomputable def target (R ε : ℝ) : ℝ := 16*R^2/ε

noncomputable def initialIterate {E : Type*} (L0 R Δ ε : ℝ) (x0 : E) : Iterate E :=
  ⟨R^2/(2*Δ), x0, x0, max L0 (1/target R ε)⟩

noncomputable def batchSize {E : Type*} (σ ε δ : ℝ) (s : Iterate E) : ℕ :=
  max 1 ⌈1048576*σ^2*tentativeWeight s*Real.log (Real.exp 1/δ)/ε⌉₊

noncomputable def prepare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (s : Iterate E) (v : E) : Pending E :=
  let y := coupling s
  let M := max s.guess (16*(L0+L1*‖v‖))
  ⟨s, tentativeWeight s, y, M, y-(1/M) • v⟩

noncomputable def finish {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Pending E) (h : E) : Iterate E := by
  classical
  exact
    let γ := p.previous.guess/p.curvature
    let b := γ*p.weight
    let A := p.previous.A+b
    ⟨A, ((1-γ)*p.previous.A/A) • p.previous.x +
      (γ*(p.previous.A+p.weight)/A) • p.point,
      p.previous.z-b • h,
      if p.curvature ≤ p.previous.guess then p.previous.guess/16 else 16*p.previous.guess⟩

noncomputable def step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (v h : E → E) (s : Iterate E) : Iterate E :=
  let p := prepare L0 L1 s (v (coupling s))
  finish p (h p.point)

noncomputable def run {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (v h : ℕ → E → E) (s : Iterate E) : ℕ → Iterate E
  | 0 => s
  | n+1 => step L0 L1 (v n) (h n) (run L0 L1 v h s n)

def firstHalf {Ω : Type*} {n : ℕ} (ξ : Fin n → Ω) : Fin (n/2) → Ω :=
  fun i => ξ ⟨i, by have hi := i.isLt; omega⟩

def secondHalf {Ω : Type*} {n : ℕ} (ξ : Fin n → Ω) : Fin (n/2) → Ω :=
  fun i => ξ ⟨n/2+i, by have hi := i.isLt; omega⟩

noncomputable def prefixStep {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (oracle : E → Ω → E) (s : Iterate E) {n : ℕ} (ξ : Fin n → Ω) : Iterate E :=
  let p := prepare L0 L1 s (batchReply oracle (coupling s) (firstHalf ξ))
  finish p (batchReply oracle p.point (secondHalf ξ))

noncomputable def blockAdvance {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (w : S × (ℕ → Ω)) : S × (ℕ → Ω) :=
  (next (cost w.1) w.1 (fun i => w.2 i), fun i => w.2 (cost w.1+i))

noncomputable def blockTrace {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (n : ℕ) : S × (ℕ → Ω) :=
  (blockAdvance cost next)^[n] (s, ξ)

noncomputable def blockCalls {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, cost (blockTrace cost next s ξ i).1

inductive State (E : Type*) where
  | first (s : Iterate E) (size received : ℕ) (total : E)
  | second (s : Pending E) (size received : ℕ) (total : E)
  | done (s : Iterate E)

noncomputable def resume (p : Params) (s : Iterate p.E) : State p.E := by
  classical
  exact if target p.R p.ε ≤ s.A then .done s
    else .first s (batchSize p.σ p.ε p.δ s) 0 0

noncomputable def algorithm (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := by
    classical
    exact if p.Δ ≤ p.ε then .done (initialIterate p.L0 p.R p.Δ p.ε p.x0)
      else resume p (initialIterate p.L0 p.R p.Δ p.ε p.x0)
  query := fun state => (0, match state with
    | .first s _ _ _ => coupling s
    | .second s _ _ _ => s.point
    | .done s => s.x)
  update := by
    classical
    exact fun s reply => match s with
      | .first s m n total =>
        if n+1 < m then .first s m (n+1) (total+reply)
        else .second (prepare p.L0 p.L1 s ((1/(m : ℝ)) • (total+reply))) m 0 0
      | .second s m n total =>
        if n+1 < m then .second s m (n+1) (total+reply)
        else resume p (finish s ((1/(m : ℝ)) • (total+reply)))
      | .done s => .done s
  output
    | .first s _ _ _ => s.x
    | .second s _ _ _ => s.previous.x
    | .done s => s.x

end OracleTemplate.StochasticGeneralized
