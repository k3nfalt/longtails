import LongTails.Setups.CompositeGeneralizedParameterFree
import LongTails.Algorithms.CompositeGeneralizedAccelerated

open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

structure BtState (E : Type u) where
  A : ℝ
  x : E
  z : E
  h : ℝ
  phase : ℕ
  gy : E
  p : E

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stepWeight (h A : ℝ) : ℝ := (h + Real.sqrt (h ^ 2 + 4 * h * A)) / 2

open Classical in
noncomputable def backtrackingComposite (p : Public) : Algorithm (Query p) p.E p.E where
  State := BtState p.E
  initial := fun _ => ⟨0, p.x0, p.x0, p.h0, 0, 0, p.x0⟩
  query :=  fun s => (0,
    if s.phase = 0 then
      .gradient (CompositeGeneralized.mixPoint s.A (stepWeight s.h s.A) s.x s.z)
    else if s.phase = 1 then .prox (stepWeight s.h s.A) s.z s.gy
    else .gradient (CompositeGeneralized.mixPoint s.A (stepWeight s.h s.A) s.x s.p))
  update := fun s r =>
    if s.phase = 0 then { s with phase := 1, gy := r }
    else if s.phase = 1 then { s with phase := 2, p := r }
    else
      let a := stepWeight s.h s.A
      let y := CompositeGeneralized.mixPoint s.A a s.x s.z
      let x' := CompositeGeneralized.mixPoint s.A a s.x s.p
      if 2 * s.h * ⟪r - s.gy, x' - y⟫ ≤ ‖x' - y‖ ^ 2 then
        ⟨s.A + a, x', s.p, 2 * s.h, 0, s.gy, s.p⟩
      else ⟨s.A, s.x, s.z, s.h / 2, 0, s.gy, s.p⟩
  output := fun s => s.x

end OracleTemplate.CompositeParameterFree
