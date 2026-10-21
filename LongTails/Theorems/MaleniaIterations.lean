import LongTails.Setups.MaleniaIterations
import LongTails.Proofs.SingleOracleCounted
import LongTails.Proofs.MaleniaStochastic
import LongTails.Proofs.BatchIterations
import LongTails.Proofs.RennalaConvergence

open MeasureTheory

namespace OracleTemplate.MaleniaIterations

open Rennala MaleniaUniform

noncomputable def budget : (let S := LongTails.Setups.MaleniaIterations.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈24 * p.L * p.Delta / p.eps⌉₊ + p.extra

theorem result : Convergence LongTails.Setups.MaleniaIterations.spec budget := by
  classical
  refine ⟨BatchIterations.algorithm, ?_, ?_⟩
  · intro p hp I O hO
    rcases hO with ⟨hf, fs, hfs, hgi, Ω, m, μ, Pst, g, B, hst, ho, hB, rfl⟩
    let := m
    let q := publicInput p
    let rate : ℝ := 24 * p.L * p.Delta / p.eps
    let K := max 1 ⌈rate⌉₊ + p.extra
    have hK : 0 < K := by
      have := le_max_left (1 : ℕ) ⌈rate⌉₊
      omega
    have hNK : q.N + 1 = K := by
      change K - 1 + 1 = K
      omega
    have hrate : rate ≤ ((q.N + 1 : ℕ) : ℝ) := by
      rw [hNK]
      exact ((BatchIterations.horizon_coverage rate K).mpr ⟨p.extra, rfl⟩).2
    let P : ProbabilityMeasure (ℕ → ℕ → Ω) :=
      ⟨Measure.map arrays (Pst : Measure (ℕ → Ω)), inferInstance⟩
    let μ' : ProbabilityMeasure (ℕ → Ω) :=
      ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)), inferInstance⟩
    have hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun r (ω : ℕ → ℕ → Ω) => ω r) (μ' : Measure (ℕ → Ω))
        (P : Measure (ℕ → ℕ → Ω)) := by
      change LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID _ _ (Measure.map arrays (Pst : Measure (ℕ → Ω)))
      rw [arrays_law μ Pst hst]
      exact StochasticGeneralized.infinitePi_iid _
    have hS : 0 < q.S := lt_of_lt_of_le hp.1 (le_max_right _ _)
    have hoG (r : ℕ) : StochasticOracle (ℕ → Ω) μ' I.f (estimator (B r) g) (p.v / q.S) :=
      estimator_moments fs I.f hfs hgi μ g p.v hp.2.2.1 ho hp.1 q.S hS (B r) (hB r)
    let x : Fin (q.N + 1) → (ℕ → ℕ → Ω) → Point p.d := fun j ω => iterate g q.gamma B q.x0 ω j.val
    have hm (j : Fin (q.N + 1)) : Measurable (x j) :=
      (sgd_moments I.f (fun r => estimator (B r) g) μ' P (fun r ω => ω r) p.L (p.v / q.S) q.gamma
        q.x0 hp.2.1 (div_nonneg hp.2.2.1 (Nat.cast_nonneg _)) hf.hasGradient hf.lipschitz hoG hiid j.val).1
    have hi (j : Fin (q.N + 1)) : Integrable (fun ω => ‖gradient I.f (x j ω)‖ ^ 2) (P : Measure _) :=
      (sgd_moments I.f (fun r => estimator (B r) g) μ' P (fun r ω => ω r) p.L (p.v / q.S) q.gamma
        q.x0 hp.2.1 (div_nonneg hp.2.2.1 (Nat.cast_nonneg _)) hf.hasGradient hf.lipschitz hoG hiid j.val).2.2.2
    have ha : (1 / ((q.N + 1 : ℕ) : ℝ)) * ∑ j : Fin (q.N + 1),
        (∫ ω, ‖gradient I.f (x j ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps := by
      have hh := malenia_accuracy fs I.f hfs hgi μ Pst hst g p.L p.v p.eps p.Delta I.lower p.x0 hp.1 hp.2.1
        hp.2.2.1 hp.2.2.2 hf.hasGradient hf.lipschitz hf.lower hf.gap ho B hB (q.N + 1)
        (Nat.succ_pos _) hrate
      erw [← Fin.sum_univ_eq_sum_range (fun k => ∫ ω, ‖gradient I.f (iterate g
        (MaleniaIterations.stepSize p.L p.v p.eps (MaleniaIterations.batchSize p.n p.v p.eps)) B p.x0 ω k)‖ ^ 2
          ∂(Measure.map arrays (Pst : Measure (ℕ → Ω)))) (q.N + 1)] at hh
      exact hh
    have hu := uniform_prefix_accuracy P I.f q.N x p.eps hm hi ha
    have hexFun : (fun z : Fin (q.N + 1) × (ℕ → ℕ → Ω) =>
        (executeCounted (iterOracle q p.n B Pst g) (BatchIterations.algorithm q) (budget p 0) z.1 z.2).1) =
        (fun z => x z.1 z.2) := by
      funext z
      rw [show budget p 0 = q.N + 1 from hNK.symm, execute_iter q p.n B Pst g z.1 z.2]
      rfl
    let Q : ProbabilityMeasure (Fin (q.N + 1) × (ℕ → ℕ → Ω)) :=
      ⟨(PMF.uniformOfFintype (Fin (q.N + 1))).toMeasure.prod (P : Measure (ℕ → ℕ → Ω)), inferInstance⟩
    change LongTails.Setups.MaleniaIterations.spec.successful p I (fun z : Fin (q.N + 1) × (ℕ → ℕ → Ω) =>
      (executeCounted (iterOracle q p.n B Pst g) (BatchIterations.algorithm q) (budget p 0) z.1 z.2).1) Q
    rw [hexFun]
    exact ⟨hu.1, hu.2.1, hu.2.2.2⟩
  · intro p hp
    rfl


end OracleTemplate.MaleniaIterations
