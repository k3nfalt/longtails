import LongTails.Setups.FiniteSumSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.SvrgConvex
import LongTails.Proofs.SvrgExecution
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace OracleTemplate.FiniteSum.SvrgConvex

open LongTails.Setups.FiniteSumSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => q.n * Nat.clog 2 ⌈17 * q.L * q.R ^ 2 / (2 * q.ε)⌉₊ + ⌈68 * q.L * q.R ^ 2 / q.ε⌉₊

theorem result :
    Convergence LongTails.Setups.FiniteSumSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => svrg q.L q.x0 (Nat.clog 2 ⌈17 * q.L * q.R ^ 2 / (2 * q.ε)⌉₊), ?_, fun _ _ => trivial⟩
  intro q hp f oracle h
  rcases hp with ⟨hn, hL, hR, hε⟩
  rcases h with ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun z => oracle.answer [] (0, z) seed0
  have hanswer : ∀ k z seed, oracle.answer k (0, z) seed = g z :=
    fun k z seed => (hg k seed z.1 z.2).unique (hg [] seed0 z.1 z.2)
  let S := Nat.clog 2 ⌈17 * q.L * q.R ^ 2 / (2 * q.ε)⌉₊
  let K := q.n * S + ⌈68 * q.L * q.R ^ 2 / q.ε⌉₊
  have hK : queryCount q.n 2 S ≤ K := by
    rw [queryCount_eq]
    change q.n * S + 4 * (2 ^ S - 1) ≤ q.n * S + ⌈68 * q.L * q.R ^ 2 / q.ε⌉₊
    apply Nat.add_le_add_left
    by_cases hS : S = 0
    · simp [hS]
    have hp : 2 ^ (S - 1) < ⌈17 * q.L * q.R ^ 2 / (2 * q.ε)⌉₊ :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mp (show S - 1 < S by omega)
    have hp' := (Nat.lt_ceil.mp hp)
    have hpow : (2 : ℝ) ^ S = 2 * (2 : ℝ) ^ (S - 1) := by
      conv_lhs => rw [show S = (S - 1) + 1 by omega]
      rw [pow_succ, mul_comm]
    have hreal : (4 : ℝ) * (2 : ℝ) ^ S ≤ 68 * q.L * q.R ^ 2 / q.ε := by
      rw [hpow]
      have heq : 8 * (17 * q.L * q.R ^ 2 / (2 * q.ε)) = 68 * q.L * q.R ^ 2 / q.ε := by ring
      push_cast at hp'
      nlinarith
    have hnat : 4 * 2 ^ S ≤ ⌈68 * q.L * q.R ^ 2 / q.ε⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    exact (Nat.mul_le_mul_left 4 (Nat.sub_le _ _)).trans hnat
  have hrate := epochRun_rate (oracle := g) hL hR hc (hg [] seed0) (hlip [] seed0) hmin hdist S
  have hceil : 17 * q.L * q.R ^ 2 / (2 * q.ε) ≤ (2 : ℝ) ^ S := by
    calc
      _ ≤ (⌈17 * q.L * q.R ^ 2 / (2 * q.ε)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ S : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_pow_clog (by decide) _)
      _ = _ := by norm_cast
  have heps : 17 * q.L * q.R ^ 2 / (2 * 2 ^ S) ≤ q.ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ S)).mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q.ε)).mp hceil
    nlinarith
  have hexec (seed : EpochSeeds q.n 2 S) (oracleSeed : (k : ℕ) → oracle.Seed k) :
      execute oracle (svrg q.L q.x0 S) (fun _ => K) seed oracleSeed =
        (epochRun g q.L 2 S q.x0 q.x0 seed).2 := by
    erw [execute_eq_of_answer_eq oracle g hanswer, execute_svrg_of_le g q.L q.x0 S K hK]
  change spec.successful q f
      (fun seed => (execute oracle (svrg q.L q.x0 S) (fun _ => K) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (EpochSeeds q.n 2 S)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k)), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : EpochSeeds q.n 2 S × ((k : ℕ) → oracle.Seed k) =>
    (epochRun g q.L 2 S q.x0 q.x0 seed.1).2) ∧ _
  refine ⟨(measurable_from_top : Measurable (fun seed : EpochSeeds q.n 2 S =>
    (epochRun g q.L 2 S q.x0 q.x0 seed).2)).comp measurable_fst, xstar, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : EpochSeeds q.n 2 S =>
        objective f (epochRun g q.L 2 S q.x0 q.x0 seed).2 - objective f xstar)
        (μ := (PMF.uniformOfFintype (EpochSeeds q.n 2 S)).toMeasure))
  · change (∫ seed : EpochSeeds q.n 2 S × ((k : ℕ) → oracle.Seed k),
      objective f (epochRun g q.L 2 S q.x0 q.x0 seed.1).2 - objective f xstar
      ∂(PMF.uniformOfFintype (EpochSeeds q.n 2 S)).toMeasure.prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k))) ≤ q.ε
    rw [integral_fun_fst (fun seed =>
      objective f (epochRun g q.L 2 S q.x0 q.x0 seed).2 - objective f xstar)]
    simp only [probReal_univ, one_smul]
    rw [uniform_integral]
    exact hrate.trans heps

end OracleTemplate.FiniteSum.SvrgConvex
