import LongTails.Algorithms.QuarticMetricStage
import LongTails.Algorithms.HeavyTailedEnergyProbe

namespace LongTails.Algorithms.RelativeCurvatureSearch

open OracleTemplate LongTails.Algorithms.QuarticMetricStage
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

def seed (s : Fin (Module.finrank ℝ E) → Bool) : E :=
  (stdOrthonormalBasis ℝ E).repr.symm (HeavyTailedEnergyProbe.initialVector s)

def differenceStep (D : E →L[ℝ] E) (H τ : ℝ) (v : E) : ℝ :=
  τ / (4 * H * (1 + ‖D‖ ^ 3) * (1 + ‖v‖))

def product (D : E →L[ℝ] E) (x : Point E) (H τ : ℝ) (v : E) : Plan E E 1 :=
  let h := differenceStep D H τ v
  let u := ‖v‖⁻¹ • v
  let y := x.x + h • D u
  .ask (0, y) fun reply =>
    let gy := (readPoint y reply).gradient
    .done (‖v‖ • D.adjoint (h⁻¹ • (gy - x.gradient)))

def transformedProduct (D : E →L[ℝ] E) (x : Point E) (H a τ : ℝ) (v : E) : Plan E E 1 :=
  (product D x H τ v).map (fun w => (1 + a)⁻¹ • ((1 - a) • v - (2 : ℝ) • w))

def filter (D : E →L[ℝ] E) (x : Point E) (H a τ : ℝ) (u : E) :
    (n : ℕ) → Plan E (E × E) n
  | 0 => .done (0, u)
  | n + 1 => (show 1 + n = n + 1 by omega) ▸
      (filter D x H a τ u n).bind (fun state =>
        (transformedProduct D x H a τ state.2).map (fun w =>
          (state.2, if n = 0 then w else (2 : ℝ) • w - state.1)))

def search (D : E →L[ℝ] E) (x : Point E) (H a : ℝ) (u : E) (n : ℕ) :
    Plan E (Option E) (n + 1) := by
  classical
  let τ := a / (128 * (12 : ℝ) ^ n)
  exact (show 1 + n = n + 1 by omega) ▸
    (filter D x H a τ (‖u‖⁻¹ • u) n).bind (fun state =>
      let v := ‖state.2‖⁻¹ • state.2
      (product D x H (a / 4) v).map (fun w =>
        if state.2 ≠ 0 ∧ ⟪v, w⟫ ≤ -a / 2 then some (D v) else none))

end

end LongTails.Algorithms.RelativeCurvatureSearch
