import LongTails.Setups.FiniteSumSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.VradaRate
import LongTails.Proofs.VradaExecution
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace OracleTemplate.FiniteSum.AcceleratedFiniteSumConvex

open LongTails.Setups.FiniteSumSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 3 * q.n * (Nat.clog 2 (Nat.clog 2 q.n) + ⌈Real.sqrt (32 * q.L * q.R ^ 2 / ((q.n : ℝ) * q.ε))⌉₊)

theorem result :
    Convergence LongTails.Setups.FiniteSumSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => vrada q.L q.x0 q.n (Nat.clog 2 (Nat.clog 2 q.n) + ⌈Real.sqrt (32 * q.L * q.R ^ 2 / ((q.n : ℝ) * q.ε))⌉₊), ?_, fun _ _ => trivial⟩
  intro q hp f oracle h
  rcases hp with ⟨hn, hL, hR, hε⟩
  rcases h with ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun z => oracle.answer [] (0, z) seed0
  have hanswer : ∀ k z seed, oracle.answer k (0, z) seed = g z :=
    fun k z seed => (hg k seed z.1 z.2).unique (hg [] seed0 z.1 z.2)
  let s := Nat.clog 2 (Nat.clog 2 q.n)
  let t := ⌈Real.sqrt (32 * q.L * q.R ^ 2 / ((q.n : ℝ) * q.ε))⌉₊
  let S := s + t
  let K := 3 * q.n * S
  have hK : K = (q.n + 2 * q.n) * S := by dsimp [K]; ring
  have hrate := vradaRun_rate (g := g) hL hR (NeZero.pos q.n) hc
    (hg [] seed0) (hlip [] seed0) hmin hdist S
  have heps := vradaWeight_tuning (m := q.n) (R := q.R) hL (NeZero.pos q.n) hε
  have hexec (seed : VradaSeeds q.n q.n S) (oracleSeed : (k : ℕ) → oracle.Seed k) :
      execute oracle (vrada q.L q.x0 q.n S) (fun _ => K) seed oracleSeed =
        (vradaRun g q.L q.n S 0 q.x0 q.x0 seed).2 := by
    erw [execute_eq_of_answer_eq oracle g hanswer, hK, execute_vrada g q.L q.x0 q.n S (NeZero.pos q.n)]
  change spec.successful q f
      (fun seed => (execute oracle (vrada q.L q.x0 q.n S) (fun _ => K) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (VradaSeeds q.n q.n S)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : VradaSeeds q.n q.n S × ((k : ℕ) → oracle.Seed k) =>
    (vradaRun g q.L q.n S 0 q.x0 q.x0 seed.1).2) ∧ _
  refine ⟨(measurable_from_top : Measurable (fun seed : VradaSeeds q.n q.n S =>
    (vradaRun g q.L q.n S 0 q.x0 q.x0 seed).2)).comp measurable_fst, xstar, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : VradaSeeds q.n q.n S =>
        objective f (vradaRun g q.L q.n S 0 q.x0 q.x0 seed).2 - objective f xstar)
        (μ := (PMF.uniformOfFintype (VradaSeeds q.n q.n S)).toMeasure))
  · change (∫ seed : VradaSeeds q.n q.n S × ((k : ℕ) → oracle.Seed k),
      objective f (vradaRun g q.L q.n S 0 q.x0 q.x0 seed.1).2 - objective f xstar
      ∂(PMF.uniformOfFintype (VradaSeeds q.n q.n S)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ q.ε
    rw [integral_fun_fst (fun seed =>
      objective f (vradaRun g q.L q.n S 0 q.x0 q.x0 seed).2 - objective f xstar)]
    simp only [probReal_univ, one_smul]
    rw [uniform_integral]
    exact hrate.trans heps

end OracleTemplate.FiniteSum.AcceleratedFiniteSumConvex
