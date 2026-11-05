import LongTails.Algorithms.TaylorCorrectedNewton

namespace LongTails.Algorithms.TensorFreeModel

open OracleTemplate OracleTemplate.QueryPlan TaylorCorrectedNewton
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def kernelValue (H : E →L[ℝ] E) (L : ℝ) (s : E) : ℝ :=
  ⟪s, H s⟫ / 2 + L * ‖s‖ ^ 4 / 4

noncomputable def kernelGradient (H : E →L[ℝ] E) (L : ℝ) (s : E) : E :=
  H s + (L * ‖s‖ ^ 2) • s

noncomputable def kernelBregman (H : E →L[ℝ] E) (L : ℝ) (x y : E) : ℝ :=
  kernelValue H L y - kernelValue H L x - ⟪kernelGradient H L x, y - x⟫

noncomputable def stepObjective (H : E →L[ℝ] E) (L : ℝ) (x e y : E) : ℝ :=
  ⟪e, y⟫ + 2 * (1 + 1 / Real.sqrt 2) * kernelBregman H L x y

noncomputable def stepPoint (H : E →L[ℝ] E) (L ρ : ℝ) (x e : E) : E := by
  classical
  exact if h : ∃ y ∈ Metric.closedBall (0 : E) ρ,
      IsMinOn (stepObjective H L x e) (Metric.closedBall (0 : E) ρ) y
    then Classical.choose h else 0

noncomputable def modelValue (g : E) (H : E →L[ℝ] E)
    (T : E →L[ℝ] E →L[ℝ] E) (L : ℝ) (s : E) : ℝ :=
  ⟪g, s⟫ + kernelValue H L s + ⟪T s s, s⟫ / 6

noncomputable def exactGradient (g : E) (H : E →L[ℝ] E)
    (T : E →L[ℝ] E →L[ℝ] E) (L : ℝ) (s : E) : E :=
  g + H s + (1 / 2 : ℝ) • T s s + (L * ‖s‖ ^ 2) • s

noncomputable def estimateGradient (g : E) (H : E →L[ℝ] E)
    (gplus gminus : E) (L τ : ℝ) (s : E) : E :=
  g + H s + (1 / (2 * τ ^ 2)) • (gplus + gminus - (2 : ℝ) • g) + (L * ‖s‖ ^ 2) • s

noncomputable def probes {n : ℕ} (g : E) (H : E →L[ℝ] E)
    (L τ : ℝ) (z s : E) : QueryPlan (Fin n × E) (Reply E) E (n + n) :=
  QueryPlan.bind (snapshot (z + τ • s)) (fun plus =>
    QueryPlan.map (fun minus => estimateGradient g H (meanGradient plus) (meanGradient minus) L τ s)
      (snapshot (z - τ • s)))

structure ModelState (E : Type*) where
  displacement : E
  trueGradient : E
  accepted : Bool

noncomputable def modelRound {n : ℕ} (g : E) (H : E →L[ℝ] E)
    (L τ ρ δ tol : ℝ) (z : E) (st : ModelState E) :
    QueryPlan (Fin n × E) (Reply E) (ModelState E) (n + (n + n)) := by
  classical
  exact QueryPlan.bind (probes g H L τ z st.displacement) (fun estimate =>
    QueryPlan.map (fun fresh =>
      if st.accepted then st
      else if ‖meanGradient fresh‖ ≤ tol ∨ ‖estimate‖ ≤ ‖meanGradient fresh‖ / 6 - δ
      then ⟨st.displacement, meanGradient fresh, true⟩
      else ⟨stepPoint H L ρ st.displacement estimate, 0, false⟩)
      (snapshot (z + st.displacement)))

noncomputable def modelRounds {n : ℕ} (g : E) (H : E →L[ℝ] E)
    (L τ ρ δ tol : ℝ) (z : E) : (k : ℕ) → ModelState E →
    QueryPlan (Fin n × E) (Reply E) (ModelState E) ((n + (n + n)) * k)
  | 0, st => .done st
  | k + 1, st => QueryPlan.bind (modelRound g H L τ ρ δ tol z st)
      (fun next => modelRounds g H L τ ρ δ tol z k next)

noncomputable def solveModel {n : ℕ} (L τ ρ δ tol : ℝ) (z : E) (K : ℕ) :
    QueryPlan (Fin n × E) (Reply E) (ModelState E) ((n + (n + n)) * (K + 1) + n) :=
  QueryPlan.bind (snapshot z) (fun cache =>
    modelRounds (meanGradient cache) (meanHessian cache) L τ ρ δ tol z (K + 1) ⟨0, 0, false⟩)

end LongTails.Algorithms.TensorFreeModel
