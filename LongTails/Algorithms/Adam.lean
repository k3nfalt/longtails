import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.Adam

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure State (d : ℕ) where
  selected : ℕ
  time : ℕ
  point : Point d
  momentum : Point d
  secondMoment : Point d
  saved : Point d

noncomputable def secondMomentStep {d : ℕ} (ρ : ℝ) (v g : Point d) : Point d :=
  WithLp.toLp 2 fun i => (1 - ρ) * v i + ρ * (g i) ^ 2

noncomputable def direction {d : ℕ} (τ : ℝ) (m v : Point d) : Point d :=
  WithLp.toLp 2 fun i => m i / (Real.sqrt (v i) + τ)

noncomputable def update {d : ℕ} (q ρ η τ : ℝ) (s : State d) (g : Point d) : State d :=
  let m := q • s.momentum + (1 - q) • g
  let v := secondMomentStep ρ s.secondMoment g
  { selected := s.selected
    time := s.time + 1
    point := s.point - η • direction τ m v
    momentum := m
    secondMoment := v
    saved := if s.time = s.selected then s.point else s.saved }

noncomputable def method {d : ℕ} (q ρ η τ : ℝ) (n : ℕ) (x0 : Point d) :
    Algorithm (Point d) (Point d) (Point d) where
  Seed := Fin (n + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (n + 1))).toMeasure, inferInstance⟩
  State := State d
  initial k := ⟨k.val, 0, x0, 0, 0, x0⟩
  query s := (0, s.point)
  update := update q ρ η τ
  output s := s.saved

noncomputable def output {d : ℕ} (O : Oracle (Point d) (Point d))
    (q ρ η τ : ℝ) (n : ℕ) (x0 : Point d) (selected : Fin (n + 1))
    (ξ : (k : ℕ) → O.Seed k) : Point d :=
  execute O (method q ρ η τ n x0) (fun _ => n + 1) selected ξ

end OracleTemplate.Adam
