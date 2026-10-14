import LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
import LongTails.Algorithms.StochasticGeneralizedAccelerated
import LongTails.Algorithms.RobustGradientEstimator

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling)
open StochasticGeneralized (target initialIterate prepare finish)
open RobustGradient (centeredClip pilotCenter)

noncomputable def confidence (p : Params) : ℝ := Real.log (Real.exp 1/p.δ)

noncomputable def pilotGroups (p : Params) : ℕ :=
  max 1 ⌈64*Real.log (Real.exp 1*(1+p.L0*p.R^2/p.ε+p.L1*p.R+Real.log (4+4*p.Δ/p.ε))/p.δ)⌉₊

noncomputable def radius (p : Params) (a : ℝ) : ℝ := p.R/(64*a*confidence p)

noncomputable def pilotSize (p : Params) (a : ℝ) : ℕ :=
  max 1 ⌈576*p.σ^2/(radius p a)^2⌉₊

noncomputable def correctionSize (p : Params) (a : ℝ) : ℕ :=
  max 1 ⌈1073741824*p.σ^2*a*(confidence p)^2/p.ε⌉₊

noncomputable def estimatorCost (p : Params) (a : ℝ) : ℕ :=
  pilotGroups p*pilotSize p a+correctionSize p a

noncomputable def meanBlock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (offset size : ℕ) (v : ℕ → E) : E :=
  (1/(size : ℝ)) • ∑ i : Fin size, v (offset+i)

noncomputable def estimate (p : Params) (a : ℝ) (v : ℕ → p.E) : p.E :=
  let k := pilotGroups p
  let r := pilotSize p a
  let m := correctionSize p a
  let c := pilotCenter (radius p a) (fun i : Fin k => meanBlock (i*r) r v)
  centeredClip (radius p a) c (meanBlock (k*r) m v)

inductive State (E : Type*) where
  | first (s : Iterate E) (received : ℕ) (replies : ℕ → E)
  | second (s : Pending E) (received : ℕ) (replies : ℕ → E)
  | done (s : Iterate E)

noncomputable def resume (p : Params) (s : Iterate p.E) : State p.E := by
  classical
  exact if target p.R p.ε ≤ s.A then .done s else .first s 0 (fun _ => 0)

noncomputable def algorithm (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := by
    classical
    exact if p.Δ ≤ p.ε then .done (initialIterate p.L0 p.R p.Δ p.ε p.x0)
      else resume p (initialIterate p.L0 p.R p.Δ p.ε p.x0)
  query := fun state => (0, match state with
    | .first s _ _ => coupling s
    | .second s _ _ => s.point
    | .done s => s.x)
  update := by
    classical
    exact fun s reply => match s with
      | .first s n v =>
        let v' := Function.update v n reply
        if n+1 < estimatorCost p (tentativeWeight s) then .first s (n+1) v'
        else .second (prepare p.L0 p.L1 s (estimate p (tentativeWeight s) v')) 0 (fun _ => 0)
      | .second s n v =>
        let v' := Function.update v n reply
        if n+1 < estimatorCost p s.weight then .second s (n+1) v'
        else resume p (finish s (estimate p s.weight v'))
      | .done s => .done s
  output
    | .first s _ _ => s.x
    | .second s _ _ => s.previous.x
    | .done s => s.x

noncomputable def sampleReplies {E Ω : Type*} [Zero E] (oracle : E → Ω → E)
    (x : E) {n : ℕ} (ξ : Fin n → Ω) : ℕ → E :=
  fun i => if h : i < n then oracle x (ξ ⟨i, h⟩) else 0

noncomputable def pilotReply (p : Params) (a : ℝ) (v : ℕ → p.E) : p.E :=
  pilotCenter (radius p a)
    (fun i : Fin (pilotGroups p) => meanBlock (i*pilotSize p a) (pilotSize p a) v)

noncomputable def correctionReply (p : Params) (a : ℝ) (v : ℕ → p.E) : p.E :=
  meanBlock (pilotGroups p*pilotSize p a) (correctionSize p a) v

noncomputable def sampleEstimate (p : Params) (a : ℝ) (oracle : p.E → p.Ω → p.E)
    (x : p.E) {n : ℕ} (ξ : Fin n → p.Ω) : p.E := estimate p a (sampleReplies oracle x ξ)

noncomputable def sampleStep (p : Params) (oracle : p.E → p.Ω → p.E)
    (s : Iterate p.E) {n : ℕ} (ξ : Fin n → p.Ω) : Iterate p.E :=
  StochasticGeneralized.step p.L0 p.L1
    (fun x => sampleEstimate p (tentativeWeight s) oracle x (StochasticGeneralized.firstHalf ξ))
    (fun x => sampleEstimate p (tentativeWeight s) oracle x (StochasticGeneralized.secondHalf ξ)) s

end OracleTemplate.RobustGeneralized
