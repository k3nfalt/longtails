import LongTails.Setups.CompositeGeneralizedSmooth

namespace OracleTemplate.CompositeGeneralized

open LongTails.Setups.CompositeGeneralizedSmooth

structure AccState (E : Type u) where
  stage : ℕ
  A : ℝ
  x : E
  z : E
  M : ℝ
  gy : E

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def weight (L1 R A M : ℝ) : ℝ :=
  min ((1 + Real.sqrt (1 + 16 * M * A)) / (8 * M)) (A / (1 + 32 * L1 * R))

noncomputable def mixPoint (A a : ℝ) (x z : E) : E :=
  (A / (A + a)) • x + (a / (A + a)) • z

noncomputable def accelerated (p : Public) : Algorithm (Query p) p.E p.E 1 where
  State := AccState p.E
  initial := fun _ => ⟨0, p.R ^ 2 / (2 * p.Δ), p.x0, p.x0, 0, 0⟩
  query := fun s => (0,
    if s.stage = 0 then .gradient s.x
    else if s.stage = 1 then .gradient (mixPoint s.A (weight p.L1 p.R s.A s.M) s.x s.z)
    else .prox (weight p.L1 p.R s.A s.M) s.z s.gy)
  update := fun s r =>
    if s.stage = 0 then ⟨1, s.A, s.x, s.z, p.L0 + p.L1 * ‖r‖, 0⟩
    else if s.stage = 1 then ⟨2, s.A, s.x, s.z, s.M, r⟩
    else ⟨0, s.A + weight p.L1 p.R s.A s.M,
      mixPoint s.A (weight p.L1 p.R s.A s.M) s.x r, r, 0, 0⟩
  output := fun s => s.x

end OracleTemplate.CompositeGeneralized
