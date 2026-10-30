import LongTails.Algorithms.GeneralizedLipschitzPilot
import LongTails.Algorithms.GeneralizedLipschitzWarmStart
import LongTails.Algorithms.SplitRobustAcceleration
namespace LongTails.Algorithms.GeneralizedLipschitzConvex
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
open LongTails.Algorithms.GeneralizedLipschitzPilot

noncomputable def twoPhase (A : OracleTemplate.Algorithm E E E) (seed : A.Seed)
    (B : ℕ) (D G0 α : ℝ) : OracleTemplate.Algorithm E E E where
  State := (ℕ × A.State) ⊕ (E × State E)
  initial _ := if B = 0 then .inr (A.output (A.initial seed), initial (A.output (A.initial seed)) G0)
    else .inl (0, A.initial seed)
  query s := match s with
    | .inl (_, state) => A.query state
    | .inr (_, state) => (0, point α state)
  update s reply := match s with
    | .inl (n, state) =>
      let next := A.update state reply
      if n + 1 < B then .inl (n + 1, next)
      else .inr (A.output next, initial (A.output next) G0)
    | .inr (center, state) => .inr (center, update center D α state reply)
  output s := match s with
    | .inl (_, state) => A.output state
    | .inr (_, state) => state.2.1
noncomputable def algorithm (c : Config) (hc : 0 < c.calls) (center : E)
    (R G G0 κ α : ℝ) (T K : ℕ) : OracleTemplate.Algorithm E E E :=
  OracleTemplate.SplitRobustAcceleration.capped
    (twoPhase (burninAlgorithm c hc center R G G0 κ) () (T * c.calls) (2 * R) G0 α)
    (T * c.calls + K)
noncomputable def output (c : Config) (hc : 0 < c.calls) (center : E)
    (R G G0 κ α : ℝ) (T K budget : ℕ) (O : OracleTemplate.Oracle E E)
    (ξ : (k : ℕ) → O.Seed k) : E :=
  OracleTemplate.execute O (algorithm c hc center R G G0 κ α T K) (fun _ => budget) () ξ
noncomputable def tunedAlgorithm (center : E) (R G0 G1 ε : ℝ) : OracleTemplate.Algorithm E E E :=
  let G := max G1 (1 / R)
  let T := ⌈204800 * (R * G) ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  let c := tuning (R * G) δ
  let D := 2 * R
  let e := ε / 20
  let τ := ⌈(96 * D * G) ^ 2⌉₊
  let α := min (1 / (16 * τ * (D * G))) (min ((e / (24 * D * G0)) ^ 2) (e / (1536 * τ * D * G0)))
  let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * G0 / e))⌉₊
  algorithm c (by dsimp [c, Config.calls, tuning]; omega) center R G G0 (R * G) α T K
end LongTails.Algorithms.GeneralizedLipschitzConvex
