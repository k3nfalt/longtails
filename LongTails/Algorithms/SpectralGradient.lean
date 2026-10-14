import LongTails.Setups.MinimizerRegularHessian
import Mathlib.Analysis.InnerProductSpace.Spectrum

open scoped RealInnerProductSpace

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

noncomputable def gradientSteps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E) : List ℝ → E → E
  | [], x => x
  | η :: rs, x => gradientSteps g rs (x - η • g x)

structure Model (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  map : E →L[ℝ] E
  symmetric : map.toLinearMap.IsSymmetric

noncomputable def scalarModel (p : Params) : Model p.E where
  map := p.μ • ContinuousLinearMap.id ℝ p.E
  symmetric := by
    intro x y
    simp only [ContinuousLinearMap.coe_coe, smul_apply,
      ContinuousLinearMap.id_apply, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]

def Fits (p : Params) (history : List p.E) (B : Model p.E) : Prop :=
  (∀ x, p.μ * ‖x‖ ^ 2 ≤ ⟪B.map x, x⟫ ∧ ⟪B.map x, x⟫ ≤ p.L * ‖x‖ ^ 2) ∧
  ∀ j < Module.finrank ℝ p.E,
    ‖history.getD (j + 1) 0 -
      (history.getD j 0 - (1 / (2 * p.L)) • B.map (history.getD j 0))‖ ≤
        p.M * ‖history.getD 0 0‖ ^ 2 / (2 * p.μ * p.L)

noncomputable def fit (p : Params) (history : List p.E) : Model p.E := by
  classical
  exact if h : ∃ B, Fits p history B then Classical.choose h else scalarModel p

noncomputable def spectralSteps (p : Params) (history : List p.E) : List ℝ :=
  List.ofFn (fun i : Fin (Module.finrank ℝ p.E) =>
    1 / (fit p history).symmetric.eigenvalues rfl i)

noncomputable def probePoint (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ) : p.E :=
  (fun y => y - (1 / (2 * p.L)) • g y)^[n] x

noncomputable def probeHistory (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ) : List p.E :=
  List.ofFn (fun i : Fin n => g (probePoint p g x i))

noncomputable def window (p : Params) (g : p.E → p.E) (x : p.E) : p.E :=
  gradientSteps g (spectralSteps p (probeHistory p g x (Module.finrank ℝ p.E + 1)))
    (probePoint p g x (Module.finrank ℝ p.E))

structure State (p : Params) where
  point : p.E
  warmup : ℕ
  history : List p.E
  remaining : List ℝ

noncomputable def update (p : Params) (s : State p) (g : p.E) : State p :=
  if s.warmup > 0 then
    { s with point := s.point - (1 / (2 * p.L)) • g, warmup := s.warmup - 1 }
  else match s.remaining with
    | η :: rest => { s with point := s.point - η • g, remaining := rest }
    | [] =>
      if s.history.length < Module.finrank ℝ p.E then
        { s with
          point := s.point - (1 / (2 * p.L)) • g
          history := s.history ++ [g] }
      else
        let steps := spectralSteps p (s.history ++ [g])
        { point := s.point - steps.headD (1 / (2 * p.L)) • g
          warmup := 0
          history := []
          remaining := steps.tail }

noncomputable def spectralGradient (p : Params) (warmup : ℕ) :
    Algorithm p.E p.E p.E where
  State := State p
  initial _ := ⟨p.x0, warmup, [], []⟩
  query s := (0, s.point)
  update := update p
  output s := s.point

end OracleTemplate.SpectralGradient
