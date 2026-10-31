import LongTails.Algorithms.QuarticMetricStage

namespace LongTails.Algorithms.MonotoneCurvatureStage

open OracleTemplate GuardedMetricAcceleration QuarticMetricStage
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

def horizon (t : ℝ) : ℕ := ⌈2 ^ 13 * t * Real.log (2 + t)⌉₊

def parameters (S : E ≃L[ℝ] E) (c : Point E) (H γ t : ℝ) : Parameters E where
  S := S
  center := c
  α := γ
  μ := 1 / (512 * t ^ 2)
  L := 8
  a := 1 / (64 * t)
  r := 256 * t * Real.sqrt γ * (γ / (2 ^ 30 * H))
  q := γ * (γ / (2 ^ 30 * H)) ^ 2
  η := γ / (1024 * H)
  ε := -1

def correctedPoint (S : E ≃L[ℝ] E) (x : Point E) : E :=
  x.x - S.symm (transformedGradient S x.gradient)

def signedDirection (g v : E) : E :=
  if ⟪g, v⟫ ≤ 0 then ‖v‖⁻¹ • v else -(‖v‖⁻¹ • v)

def witnessPoint (p : Parameters E) (w : Witness E) : E :=
  p.center.x + p.η • signedDirection p.center.gradient (w.point.x - w.plane.point.x)

def finish (p : Parameters E) : Status E → Plan E (Point E) 1 := by
  classical
  intro status
  exact match status with
  | .witness w => .ask (0, witnessPoint p w) fun reply =>
      .done (readPoint (witnessPoint p w) reply)
  | .finished x =>
      if successful p x then .ask (0, p.center.x) fun _ => .done x
      else .ask (0, correctedPoint p.S x) fun reply =>
        .done (readPoint (correctedPoint p.S x) reply)
  | .running st => .ask (0, correctedPoint p.S st.accepted) fun reply =>
      .done (readPoint (correctedPoint p.S st.accepted) reply)

def plan (p : Parameters E) (n : ℕ) : Plan E (Point E) (2 * n + 2) :=
  let initial := Status.running (State.mk p.center p.center (p.S p.center.x) [])
  (show 1 + 1 + 2 * n = 2 * n + 2 by omega) ▸
    (loop p n initial).bind (fun status => (certificate p status).bind (finish p))

end

end LongTails.Algorithms.MonotoneCurvatureStage
