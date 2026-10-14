import LongTails.Setups.SlidingGeneralizedSmooth
import LongTails.Algorithms.CompositeGeneralizedAccelerated

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

open CompositeGeneralized (mixPoint)

structure SlideState (E : Type u) where
  stage : ℕ
  k : ℕ
  A : ℝ
  x : E
  z : E
  a : ℝ
  g : E
  T : ℕ
  t : ℕ
  u : E
  ub : E
  w : E

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def slideWeight (L1 R A M : ℝ) : ℝ :=
  min ((1 + Real.sqrt (1 + 64 * M * A)) / (32 * M)) (A / (1 + 80 * L1 * R))

noncomputable def innerLength (M ε a : ℝ) : ℕ := ⌈192 * M ^ 2 * a / ε⌉₊ + 2

noncomputable def wsum (t : ℕ) : ℝ := (t : ℝ) * (t + 3) / 2

noncomputable def innerTarget (β p : ℝ) (z u' v : E) : E :=
  (1 / (1 + p)) • (z + p • u' - (1 / β) • v)

noncomputable def outerCap (p : Public) : ℕ :=
  ⌈20 * Real.sqrt ((p.L0 + p.L1 * p.G) * p.R ^ 2 / p.ε) + (6 + 320 * p.L1 * p.R) *
    Real.log (2 + (3 + 240 * p.L1 * p.R) * Real.sqrt (p.Δ / (p.L0 * p.R ^ 2)))⌉₊

noncomputable def sliding (p : Public) : Algorithm p.E p.E p.E 3 where
  State := SlideState p.E
  initial := fun _ => ⟨0, 0, p.R ^ 2 / (4 * p.Δ), p.x0, p.x0, 0, 0, 0, 0, p.x0, p.x0, p.x0⟩
  query := fun s =>
    if s.stage = 0 then
      (if p.R ^ 2 / p.ε ≤ s.A ∨ outerCap p ≤ s.k then Query.project s.x else Query.gradient s.x)
    else if s.stage = 1 then Query.gradient (mixPoint s.A s.a s.x s.z)
    else if s.stage = 2 then Query.subgradient s.u
    else Query.project s.w
  update := fun s r =>
    if s.stage = 0 then
      (if p.R ^ 2 / p.ε ≤ s.A ∨ outerCap p ≤ s.k then s
        else { s with stage := 1, a := slideWeight p.L1 p.R s.A (p.L0 + p.L1 * ‖r‖) })
    else if s.stage = 1 then
      { s with stage := 2, g := r, T := innerLength p.M p.ε s.a, t := 0, u := s.z, ub := s.z }
    else if s.stage = 2 then
      { s with
        stage := 3
        w := innerTarget (wsum s.T / (s.a * (wsum s.T + 1))) (((s.t : ℝ) + 1) / 2) s.z s.u
          (s.g + r) }
    else if s.t + 1 = s.T then
      { s with
        stage := 0
        k := s.k + 1
        A := s.A + s.a
        x := mixPoint s.A s.a s.x
          ((wsum s.t / wsum (s.t + 1)) • s.ub + (((s.t : ℝ) + 2) / wsum (s.t + 1)) • r)
        z := r }
    else
      { s with
        stage := 2
        t := s.t + 1
        u := r
        ub := (wsum s.t / wsum (s.t + 1)) • s.ub + (((s.t : ℝ) + 2) / wsum (s.t + 1)) • r }
  output := fun s => s.x

end OracleTemplate.GeneralizedSliding
