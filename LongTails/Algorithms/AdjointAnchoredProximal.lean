import LongTails.Template
import LongTails.Algorithms.MultiStepAnchoredForwardBackward
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.CohypomonotoneAdjoint

structure AdjState (E : Type u) where
  k : ℕ
  rem : ℕ
  fresh : Bool
  back : Bool
  a : E
  t : E
  v : E
  r : E
  last : E

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stepSize (L L₂ ρ : ℝ) (r : E) : ℝ :=
  1 / (2 + 2 * ρ * L) ^ 2 / max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖r‖)

noncomputable def innerLen (L L₂ ρ x : ℝ) : ℕ :=
  ⌈16 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 * x⌉₊ +
    ⌈4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)⌉₊

noncomputable def finish (L ρ : ℝ) (st : AdjState E) (f : E) : AdjState E :=
  let y := st.v + (2 * ρ + 1 / L) • f
  let a := if st.k = 0 then y else st.a
  let t := CohypomonotoneInclusion.target (ρ + 1 / L) st.k a y f
  ⟨st.k + 1, 0, true, false, a, t,
    t - ((2 * ρ + 1 / L) * (1 - 1 / ((st.k : ℝ) + 2))) • f, 0, st.v⟩

noncomputable def adjointAnchored (L L₂ ρ : ℝ) (x0 : E) :
    Algorithm (E ⊕ (E × E)) E E where
  State := AdjState E
  initial := fun _ => ⟨0, 0, true, false, x0, x0, x0, 0, x0⟩
  query :=  fun st => (0, if st.back then Sum.inr (st.v, st.r) else Sum.inl st.v)
  update := fun st reply =>
    if st.back then
      { st with
        rem := st.rem - 1, back := false,
        v := st.v - stepSize L L₂ ρ st.r • (st.r + (2 * ρ + 1 / L) • reply) }
    else
      let r := st.v + (2 * ρ + 1 / L) • reply - st.t
      let n := if st.fresh then innerLen L L₂ ρ ‖r‖ else st.rem
      if n = 0 then finish L ρ st reply
      else { st with rem := n, fresh := false, back := true, r := r }
  output := fun st => st.last

end OracleTemplate.CohypomonotoneAdjoint
