import LongTails.Proofs.SingleOracleCounted
import LongTails.Proofs.BatchIterations
import LongTails.Setups.ClassicalSgd
import LongTails.Setups.RennalaIterations

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ClassicalSgd

lemma execution_success (p : Params) (hp : LongTails.Setups.ClassicalSgd.spec.valid p) (I : Rennala.Instance p.d)
    (O : Oracle (Rennala.Point p.d) (Rennala.Point p.d))
    (hO : LongTails.Setups.ClassicalSgd.spec.admissible p I O) :
    let A := BatchIterations.algorithm (publicInput p)
    let Q : ProbabilityMeasure (A.Seed × ((k : ℕ) → O.Seed k)) :=
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩
    LongTails.Setups.ClassicalSgd.spec.successful p I (fun z =>
      (executeCounted O A (max 1 ⌈4 * p.Delta * p.L / p.eps + 8 * p.Delta * p.L * p.v / p.eps ^ 2⌉₊ + p.extra) z.1 z.2).1) Q := by
  classical
  rcases hO with ⟨hf, Ω, m, μ, P, g, hiid, hg, rfl⟩
  let := m
  let q := publicInput p
  let rate : ℝ := 4 * p.Delta * p.L / p.eps + 8 * p.Delta * p.L * p.v / p.eps ^ 2
  let K := max 1 ⌈rate⌉₊ + p.extra
  have hK : 0 < K := by
    have := le_max_left (1 : ℕ) ⌈rate⌉₊
    dsimp only [K]
    omega
  have hNK : q.N + 1 = K := by
    change K - 1 + 1 = K
    omega
  have hrate : rate ≤ ((q.N + 1 : ℕ) : ℝ) := by
    rw [hNK]
    exact ((BatchIterations.horizon_coverage rate K).mpr ⟨p.extra, rfl⟩).2
  have hS : 0 < q.S := by
    exact Nat.zero_lt_one
  have ha : (1 / ((q.N+1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range (q.N+1),
      (∫ ξ, ‖gradient I.f (Rennala.iterate g q.gamma q.S q.x0 ξ k)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps := by
    exact (Rennala.classical_sgd I.f g μ P (fun k ξ => ξ k) p.L p.v p.eps p.Delta I.lower p.x0
      hp.1 hp.2.1 hp.2.2.1 hf.hasGradient hf.lipschitz hf.lower hf.gap hg hiid).2
      (q.N+1) (Nat.succ_pos _) hrate
  have hh := BatchIterations.uniform_success q I.f g μ P p.L p.v p.eps hS
    hp.1 hp.2.1 hf.hasGradient hf.lipschitz hg hiid ha
  have hexe (j : Fin (q.N+1)) (ξ : ℕ → Fin q.S → Ω) :
      executeCounted (BatchIterations.oracle q P g) (BatchIterations.algorithm q) K j ξ =
      executeCounted (BatchIterations.oracle q P g) (BatchIterations.algorithm q) (q.N+1) j ξ := by
    rw [hNK]
  let R := fun (B : ℕ) (z : Fin (q.N+1) × (ℕ → Fin q.S → Ω)) =>
    (executeCounted (BatchIterations.oracle q P g) (BatchIterations.algorithm q) B z.1 z.2).1
  let Q := (PMF.uniformOfFintype (Fin (q.N+1))).toMeasure.prod
    (P.map (BatchIterations.blocks q.S) : Measure (ℕ → Fin q.S → Ω))
  change Measurable (R K) ∧ Integrable (fun z => ‖gradient I.f (R K z)‖ ^ 2) Q ∧
    (∫ z, ‖gradient I.f (R K z)‖ ^ 2 ∂Q) ≤ p.eps
  dsimp only [R]
  simp only [hexe]
  exact hh

end OracleTemplate.ClassicalSgd

namespace OracleTemplate.RennalaIterations

lemma execution_success (p : Params) (hp : LongTails.Setups.RennalaIterations.spec.valid p) (I : Rennala.Instance p.d)
    (O : Oracle (Rennala.Point p.d) (Rennala.Point p.d))
    (hO : LongTails.Setups.RennalaIterations.spec.admissible p I O) :
    let A := BatchIterations.algorithm (publicInput p)
    let Q : ProbabilityMeasure (A.Seed × ((k : ℕ) → O.Seed k)) :=
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩
    LongTails.Setups.RennalaIterations.spec.successful p I (fun z =>
      (executeCounted O A (max 1 ⌈24 * p.Delta * p.L / p.eps⌉₊ + p.extra) z.1 z.2).1) Q := by
  classical
  rcases hO with ⟨hf, Ω, m, μ, P, g, hiid, hg, rfl⟩
  let := m
  let q := publicInput p
  let rate : ℝ := 24 * p.Delta * p.L / p.eps
  let K := max 1 ⌈rate⌉₊ + p.extra
  have hK : 0 < K := by
    have := le_max_left (1 : ℕ) ⌈rate⌉₊
    dsimp only [K]
    omega
  have hNK : q.N + 1 = K := by
    change K - 1 + 1 = K
    omega
  have hrate : rate ≤ ((q.N + 1 : ℕ) : ℝ) := by
    rw [hNK]
    exact ((BatchIterations.horizon_coverage rate K).mpr ⟨p.extra, rfl⟩).2
  have hS : 0 < q.S := by
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have ha : (1 / ((q.N+1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range (q.N+1),
      (∫ ξ, ‖gradient I.f (Rennala.iterate g q.gamma q.S q.x0 ξ k)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps := by
    exact Rennala.iteration_accuracy I.f g μ P (fun k ξ => ξ k) p.L p.v p.eps p.Delta I.lower p.x0
      hp.1 hp.2.1 hp.2.2.1 hf.hasGradient hf.lipschitz hf.lower hf.gap hg hiid
      (q.N+1) (Nat.succ_pos _) hrate
  have hh := BatchIterations.uniform_success q I.f g μ P p.L p.v p.eps hS
    hp.1 hp.2.1 hf.hasGradient hf.lipschitz hg hiid ha
  have hexe (j : Fin (q.N+1)) (ξ : ℕ → Fin q.S → Ω) :
      executeCounted (BatchIterations.oracle q P g) (BatchIterations.algorithm q) K j ξ =
      executeCounted (BatchIterations.oracle q P g) (BatchIterations.algorithm q) (q.N+1) j ξ := by
    rw [hNK]
  let R := fun (B : ℕ) (z : Fin (q.N+1) × (ℕ → Fin q.S → Ω)) =>
    (executeCounted (BatchIterations.oracle q P g) (BatchIterations.algorithm q) B z.1 z.2).1
  let Q := (PMF.uniformOfFintype (Fin (q.N+1))).toMeasure.prod
    (P.map (BatchIterations.blocks q.S) : Measure (ℕ → Fin q.S → Ω))
  change Measurable (R K) ∧ Integrable (fun z => ‖gradient I.f (R K z)‖ ^ 2) Q ∧
    (∫ z, ‖gradient I.f (R K z)‖ ^ 2 ∂Q) ≤ p.eps
  dsimp only [R]
  simp only [hexe]
  exact hh

end OracleTemplate.RennalaIterations
