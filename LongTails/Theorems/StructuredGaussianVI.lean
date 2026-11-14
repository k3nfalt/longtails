import LongTails.Setups.StructuredGaussianVariationalInference
import LongTails.Algorithms.StructuredReparameterizedSgd
import LongTails.Proofs.StructuredGaussianVariationalConvergence
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.StructuredGaussianVariational.StructuredGaussianVI

open LongTails.Setups.GaussianVariationalInference hiding spec
open LongTails.Setups.StructuredGaussianVariationalInference
open OracleTemplate.GaussianVariational

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈(2 + 3 * q.w + 8 * Real.log (48 * q.d * q.L / q.μ)) * (26 * q.L * q.R / Real.sqrt (q.μ * q.ε) + 32 * q.d * q.L / (q.μ * q.ε))⌉₊

theorem result :
    Convergence LongTails.Setups.StructuredGaussianVariationalInference.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => structuredProxSgd q.S q.μ (patternOffset q.L q.μ q.d q.w) q.m0 q.C0, ?_,
    fun _ _ => trivial⟩
  intro q hq V O hadm
  obtain ⟨hμ, hμL, hR, hε, hS, hC0⟩ := hq
  obtain ⟨rfl, hg, hlip, hstrong, ms, Cs, hCs, hmin, hdist⟩ := hadm
  let K := budget q 0
  have hpot : Potential q.L q.μ V := ⟨hg, hlip, hstrong, hμ, hμL⟩
  have hopt : IsPatternOptimal V q.S ms Cs := ⟨hCs, hmin⟩
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : (2 + patternTau q.d q.w (q.L / q.μ)) * (26 * q.L * q.R / Real.sqrt (q.μ * q.ε) +
      32 * q.d * q.L / (q.μ * q.ε)) ≤ K := by
    have he : patternTau q.d q.w (q.L / q.μ) =
        3 * q.w + 8 * Real.log (48 * q.d * q.L / q.μ) := by
      unfold patternTau
      rw [mul_div_assoc]
    rw [he, ← add_assoc]
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hmain := pattern_main_guarantee hpot hS hopt hR hε hC0 hdist hK1 hK
  intro A
  have hexec : (fun seed : A.Seed × ((k : ℕ) → Unit) =>
      execute { answer := fun _ (_, x) _ => gradient V x } A (fun _ => K) seed.1 seed.2) =
      fun seed => patternOutput V q.S q.μ (patternOffset q.L q.μ q.d q.w) q.m0 q.C0 K seed.1 := by
    funext seed
    have hseed : seed.2 = fun _ => () := funext fun _ => rfl
    rw [hseed]
    exact execute_iterate (gradient V) A K seed.1
  change Measurable (fun seed : A.Seed × ((k : ℕ) → Unit) =>
      execute { answer := fun _ (_, x) _ => gradient V x } A (fun _ => K) seed.1 seed.2) ∧ _
  rw [hexec]
  refine ⟨hmain.1.comp measurable_fst, fun seed => hmain.2.1 seed.1, fun m' C' hC' hmin' => ?_⟩
  have hobj : objective V m' C' = objective V ms Cs :=
    le_antisymm (hmin' ms Cs hCs) (hmin m' C' hC')
  rw [hobj]
  refine ⟨?_, ?_⟩
  · exact (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => noiseLaw q.d)
      (ν := Measure.dirac fun _ : ℕ => ())).integrable_comp_of_integrable hmain.2.2.1
  · change (∫ seed : (ℕ → Fin q.d → ℝ) × ((k : ℕ) → Unit),
      objective V (patternOutput V q.S q.μ (patternOffset q.L q.μ q.d q.w) q.m0 q.C0 K seed.1).1
        (patternOutput V q.S q.μ (patternOffset q.L q.μ q.d q.w) q.m0 q.C0 K seed.1).2 -
          objective V ms Cs
      ∂(Measure.infinitePi fun _ : ℕ => noiseLaw q.d).prod (Measure.dirac fun _ : ℕ => ())) ≤ q.ε
    rw [integral_fun_fst (fun ω : ℕ → Fin q.d → ℝ =>
      objective V (patternOutput V q.S q.μ (patternOffset q.L q.μ q.d q.w) q.m0 q.C0 K ω).1
        (patternOutput V q.S q.μ (patternOffset q.L q.μ q.d q.w) q.m0 q.C0 K ω).2 -
          objective V ms Cs)]
    simpa using hmain.2.2.2

end OracleTemplate.StructuredGaussianVariational.StructuredGaussianVI
