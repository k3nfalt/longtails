import LongTails.Algorithms.AdjointAnchoredProximal

namespace OracleTemplate.CohypomonotoneAdjoint

structure AgdState (E : Type u) where
  x : E
  z : E
  y : E

structure AccState (E : Type u) where
  k : ℕ
  rem : ℕ
  fresh : Bool
  back : Bool
  agd : Bool
  fin : Bool
  a : E
  t : E
  v : E
  r : E
  x : E
  z : E
  last : E

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def agdq (L ρ : ℝ) : ℝ := 1 / (2 * (2 + 2 * ρ * L))

noncomputable def agdL (L ρ : ℝ) : ℝ := 2 * (2 + 2 * ρ * L) ^ 2

noncomputable def agdLen (L ρ : ℝ) : ℕ := ⌈4 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L)⌉₊

noncomputable def agdUpdate (L ρ : ℝ) (s : AgdState E) (g : E) : AgdState E :=
  ⟨s.y - (1 / agdL L ρ) • g,
    (1 - agdq L ρ) • s.z + agdq L ρ • s.y - (2 * agdq L ρ) • g,
    (1 / (1 + agdq L ρ)) • ((s.y - (1 / agdL L ρ) • g) +
      agdq L ρ • ((1 - agdq L ρ) • s.z + agdq L ρ • s.y - (2 * agdq L ρ) • g))⟩

noncomputable def useAgd (L L₂ ρ x : ℝ) : Bool :=
  decide (7 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) * x ≤ 1)

noncomputable def accLen (L L₂ ρ x : ℝ) : ℕ :=
  if useAgd L L₂ ρ x then agdLen L ρ else innerLen L L₂ ρ x

noncomputable def accFinish (L ρ : ℝ) (st : AccState E) (u f : E) : AccState E :=
  let y := u + (2 * ρ + 1 / L) • f
  let a := if st.k = 0 then y else st.a
  let t := CohypomonotoneInclusion.target (ρ + 1 / L) st.k a y f
  ⟨st.k + 1, 0, true, false, false, false, a, t,
    t - ((2 * ρ + 1 / L) * (1 - 1 / ((st.k : ℝ) + 2))) • f, 0, 0, 0, u⟩

noncomputable def adjointAccelerated (L L₂ ρ : ℝ) (x0 : E) :
    Algorithm (E ⊕ (E × E)) E E where
  State := AccState E
  initial := fun _ => ⟨0, 0, true, false, false, false, x0, x0, x0, 0, 0, 0, x0⟩
  query := fun st =>
    (0, if st.back then Sum.inr (st.v, st.r) else if st.fin then Sum.inl st.x else Sum.inl st.v)
  update := fun st reply =>
    if st.back then
      if st.agd then
        { st with
          rem := st.rem - 1, back := false, fin := decide (st.rem - 1 = 0),
          x := (agdUpdate L ρ ⟨st.x, st.z, st.v⟩ (st.r + (2 * ρ + 1 / L) • reply)).x,
          z := (agdUpdate L ρ ⟨st.x, st.z, st.v⟩ (st.r + (2 * ρ + 1 / L) • reply)).z,
          v := (agdUpdate L ρ ⟨st.x, st.z, st.v⟩ (st.r + (2 * ρ + 1 / L) • reply)).y }
      else
        { st with
          rem := st.rem - 1, back := false,
          v := st.v - stepSize L L₂ ρ st.r • (st.r + (2 * ρ + 1 / L) • reply) }
    else if st.fin then accFinish L ρ st st.x reply
    else
      let r := st.v + (2 * ρ + 1 / L) • reply - st.t
      let n := if st.fresh then accLen L L₂ ρ ‖r‖ else st.rem
      if n = 0 then accFinish L ρ st st.v reply
      else
        { st with
          rem := n, fresh := false, back := true,
          agd := if st.fresh then useAgd L L₂ ρ ‖r‖ else st.agd, r := r,
          x := if st.fresh then st.v else st.x, z := if st.fresh then st.v else st.z }
  output := fun st => st.last

end OracleTemplate.CohypomonotoneAdjoint
