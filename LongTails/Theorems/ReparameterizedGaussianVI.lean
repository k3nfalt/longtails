import LongTails.Setups.GaussianVariationalInference
import LongTails.Algorithms.ReparameterizedProxSgd
import LongTails.Proofs.GaussianVariationalGuarantee
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.GaussianVariational.ReparameterizedGaussianVI

open LongTails.Setups.GaussianVariationalInference

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈(2 + 3 * q.d + 8 * Real.log (48 * q.L / q.μ)) * (26 * q.L * q.R / Real.sqrt (q.μ * q.ε) + 32 * q.d * q.L / (q.μ * q.ε))⌉₊

theorem result :
    Convergence LongTails.Setups.GaussianVariationalInference.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => reparameterizedProxSgd q.μ (offset q.L q.μ q.d) q.m0 q.C0, ?_,
    fun _ _ => trivial⟩
  intro q hq V O hadm
  obtain ⟨hμ, hμL, hR, hε, hC0⟩ := hq
  obtain ⟨rfl, hg, hlip, hstrong, ms, Cs, hCs, hmin, hdist⟩ := hadm
  let K := budget q 0
  have hpot : Potential q.L q.μ V := ⟨hg, hlip, hstrong, hμ, hμL⟩
  have hopt : IsOptimal V ms Cs := ⟨hCs, hmin⟩
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : (2 + tau q.d (q.L / q.μ)) * (26 * q.L * q.R / Real.sqrt (q.μ * q.ε) +
      32 * q.d * q.L / (q.μ * q.ε)) ≤ K := by
    have he : tau q.d (q.L / q.μ) = 3 * q.d + 8 * Real.log (48 * q.L / q.μ) := by
      unfold tau
      rw [mul_div_assoc]
    rw [he, ← add_assoc]
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hmain := main_guarantee hpot hopt hR hε hC0 hdist hK1 hK
  intro A
  have hexec : (fun seed : A.Seed × ((k : ℕ) → Unit) =>
      execute { answer := fun _ (_, x) _ => gradient V x } A (fun _ => K) seed.1 seed.2) =
      fun seed => sgdOutput V q.μ (offset q.L q.μ q.d) q.m0 q.C0 K seed.1 := by
    funext seed
    have hseed : seed.2 = fun _ => () := funext fun _ => rfl
    rw [hseed]
    exact execute_iterate (gradient V) A K seed.1
  change Measurable (fun seed : A.Seed × ((k : ℕ) → Unit) =>
      execute { answer := fun _ (_, x) _ => gradient V x } A (fun _ => K) seed.1 seed.2) ∧ _
  rw [hexec]
  refine ⟨hmain.1.comp measurable_fst, fun seed => hmain.2.1 seed.1, ms, Cs, hCs, hmin, ?_, ?_⟩
  · exact (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => noiseLaw q.d)
      (ν := Measure.dirac fun _ : ℕ => ())).integrable_comp_of_integrable hmain.2.2.1
  · change (∫ seed : (ℕ → Fin q.d → ℝ) × ((k : ℕ) → Unit),
      objective V (sgdOutput V q.μ (offset q.L q.μ q.d) q.m0 q.C0 K seed.1).1
        (sgdOutput V q.μ (offset q.L q.μ q.d) q.m0 q.C0 K seed.1).2 - objective V ms Cs
      ∂(Measure.infinitePi fun _ : ℕ => noiseLaw q.d).prod (Measure.dirac fun _ : ℕ => ())) ≤ q.ε
    rw [integral_fun_fst (fun ω : ℕ → Fin q.d → ℝ =>
      objective V (sgdOutput V q.μ (offset q.L q.μ q.d) q.m0 q.C0 K ω).1
        (sgdOutput V q.μ (offset q.L q.μ q.d) q.m0 q.C0 K ω).2 - objective V ms Cs)]
    simpa using hmain.2.2.2

end OracleTemplate.GaussianVariational.ReparameterizedGaussianVI
