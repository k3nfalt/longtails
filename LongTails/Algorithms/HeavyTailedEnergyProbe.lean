import LongTails.Setups.HeavyTailedHessianVector
import LongTails.Algorithms.MatrixGeneralizedZO
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.HeavyTailedEnergyProbe

open LongTails.Setups.HeavyTailedHessianVector

noncomputable def initialVector {d : ℕ} (s : Fin d → Bool) : EuclideanSpace ℝ (Fin d) :=
  (Real.sqrt d)⁻¹ • OracleTemplate.MatrixGeneralizedZO.signVec s

noncomputable def normalize {d : ℕ} (fallback w : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  if w = 0 then fallback else ‖w‖⁻¹ • w

structure State (d : ℕ) where
  index : ℕ
  target : ℕ
  fallback : EuclideanSpace ℝ (Fin d)
  vector : EuclideanSpace ℝ (Fin d)
  selected : EuclideanSpace ℝ (Fin d)
  alive : Bool

noncomputable def step {d : ℕ} (L η : ℝ) (s : State d)
    (reply : EuclideanSpace ℝ (Fin d)) : State d :=
  let w := (1 + η * L) • s.vector - η • reply
  { index := s.index + 1
    target := s.target
    fallback := s.fallback
    vector := normalize s.fallback w
    selected := if s.index = s.target then s.vector else s.selected
    alive := s.alive && decide (w ≠ 0) }

noncomputable def initialState {d : ℕ} (signs : Fin d → Bool) (target : ℕ) : State d :=
  { index := 0
    target := target
    fallback := initialVector signs
    vector := initialVector signs
    selected := initialVector signs
    alive := true }

noncomputable def run {d : ℕ} (shift η : ℝ)
    (response : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℕ) (s : State d) : State d :=
  (fun state => step shift η state (response state.index state.vector))^[K] s

noncomputable def algorithm (p : Params) (x : Space p) (shift η : ℝ) (T : ℕ) :
    OracleTemplate.Algorithm (Space p × Option (Space p)) (Space p) (Space p) where
  Seed := (Fin p.d → Bool) × Fin (max 1 T)
  law := by
    letI : NeZero (max 1 T) := ⟨by omega⟩
    exact ⟨(PMF.uniformOfFintype (Fin p.d → Bool)).toMeasure.prod
      (PMF.uniformOfFintype (Fin (max 1 T))).toMeasure, inferInstance⟩
  State := State p.d
  initial seed := initialState seed.1 seed.2.val
  query s := (0, x, some s.vector)
  update := step shift η
  output s := s.selected

end LongTails.Algorithms.HeavyTailedEnergyProbe
