import LongTails.Algorithms.Clipping
import LongTails.Setups.TerminalClippingConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Setups.TerminalClippingConvex.Public

noncomputable def T (q : Public) : ℕ :=
  max 1 ⌈2 ^ 40 * (q.B * q.R ^ 2 + q.G ^ 2 / q.B) ^ 2 * Real.log (8 / q.δ) ^ 2 / q.ε ^ 2⌉₊


end LongTails.Setups.TerminalClippingConvex.Public

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

noncomputable def stepSize (B δ : ℝ) (T t : ℕ) : ℝ :=
  (T - t : ℕ) / (4096 * B * Real.sqrt T * Real.log (8 / δ) * T)

noncomputable def weight (T t : ℕ) : ℝ := 1 - (t + 1 : ℕ) / (2 * (T : ℝ))

noncomputable def tailWeight (B δ : ℝ) (T t : ℕ) : ℝ :=
  let m : ℝ := (T - t : ℕ)
  m * (m + 1) * (3 * T + 2 * m - 2) /
    (12 * (T : ℝ) ^ 2 * (4096 * B * Real.sqrt T * Real.log (8 / δ)))

noncomputable def influenceScale (B δ : ℝ) (T t : ℕ) : ℝ :=
  weight T t * stepSize B δ T t / tailWeight B δ T (t - 1)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def threshold (B G : ℝ) (T : ℕ) (x U : E) : ℝ := by
  classical
  exact
    let M := Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2)
    if U = 0 then M * Real.sqrt T
    else min (M * Real.sqrt T) (M ^ 2 / (B * Real.sqrt T * ‖U‖))

noncomputable def nextAuxiliary (B δ : ℝ) (T t : ℕ) (x p : E) : E :=
  let a := tailWeight B δ T t / tailWeight B δ T (t - 1)
  a • p + (1 - a) • x

noncomputable def nextPoint (projection : E → E) (B G δ : ℝ) (T t : ℕ)
    (x p g : E) : E :=
  let U := influenceScale B δ T t • (x - p)
  projection (x - stepSize B δ T t • clip (threshold B G T x U) g)

structure State (q : Public) where
  t : ℕ
  x : Vector q.d
  auxiliary : Vector q.d
  pending : Bool
  proposal : Vector q.d

noncomputable def algorithm (q : Public) : Algorithm (Query q) (Vector q.d) (Vector q.d) where
  State := State q
  initial _ := ⟨0, q.x0, 0, false, q.x0⟩
  query s := (0, if s.pending then .projection s.proposal else .subgradient s.x)
  update s reply :=
    if s.pending then ⟨s.t + 1, reply, s.auxiliary, false, s.proposal⟩
    else
      let x := s.x - q.x0
      let proposal := q.x0 + nextPoint id q.B q.G q.δ q.T s.t x s.auxiliary reply
      let auxiliary := nextAuxiliary q.B q.δ q.T s.t x s.auxiliary
      ⟨s.t, s.x, auxiliary, true, proposal⟩
  output s := s.x

noncomputable def transition {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (s : ℕ × (Vector q.d × Vector q.d)) (ω : Ω) : ℕ × (Vector q.d × Vector q.d) :=
  let u := s.2.1 - q.x0
  let y := projection (q.x0 + nextPoint id q.B q.G q.δ q.T s.1 u s.2.2 (g s.2.1 ω))
  let p := nextAuxiliary q.B q.δ q.T s.1 u s.2.2
  (s.1 + 1, y, p)

noncomputable def trajectory {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) : ℕ → ℕ × (Vector q.d × Vector q.d)
  | 0 => (0, q.x0, 0)
  | n + 1 => transition q g projection (trajectory q g projection ξ n) (ξ n)

noncomputable def run {Ω : Type*} (q : Public) (g : Vector q.d → Ω → Vector q.d)
    (projection : Vector q.d → Vector q.d) :
    ℕ → ℕ → Vector q.d → Vector q.d → (ℕ → Ω) → Vector q.d
  | 0, _, x, _, _ => x
  | n + 1, t, x, p, ξ =>
      let u := x - q.x0
      let y := projection (q.x0 + nextPoint id q.B q.G q.δ q.T t u p (g x (ξ 0)))
      let p' := nextAuxiliary q.B q.δ q.T t u p
      run q g projection n (t + 1) y p' (fun k => ξ (k + 2))

noncomputable def terminal {Ω : Type*} (q : Public) (g : Vector q.d → Ω → Vector q.d)
    (projection : Vector q.d → Vector q.d) (ξ : ℕ → Ω) : Vector q.d :=
  run q g projection q.T 0 q.x0 0 ξ

end OracleTemplate.TerminalClipping
