import LongTails.Setups.GaussianVariationalInference
import LongTails.Theorems.ReparameterizedGaussianVI
import LongTails.Proofs.TwoPhaseGaussianVIExecution

namespace OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
open LongTails.Setups.GaussianVariationalInference

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let τ := 3 * q.d + 8 * Real.log (48*q.L/q.μ)
  let u := (2+τ) * (q.L/q.μ)
  let a := 16*u+2
  let x := q.μ*q.R^2/q.ε
  min (⌈a/2 * Real.log (max 1 x)⌉₊ + ⌈2*a*(1+q.d/q.ε)⌉₊)
    (max 1 ⌈u*(26*Real.sqrt x + 32*q.d/q.ε)⌉₊)

theorem result : Convergence LongTails.Setups.GaussianVariationalInference.spec budget := by
  obtain ⟨warm, hw, _⟩ := twoPhase_convergence
  obtain ⟨base, hb, _⟩ := ReparameterizedGaussianVI.result
  let N := fun q => warmCount q + suffixCount q
  let B := fun q => ReparameterizedGaussianVI.budget q 0
  have eqb (q : Params) (hq : spec.valid q) : budget q = fun _ => min (N q) (B q) := by
    funext i
    have ht : tau q.d (q.L/q.μ) = 3*q.d+8*Real.log (48*q.L/q.μ) := by
      unfold tau; rw [mul_div_assoc]
    have ha : offset q.L q.μ q.d =
        16*((2+(3*q.d+8*Real.log (48*q.L/q.μ)))*(q.L/q.μ))+2 := by
      unfold offset smoothConst; rw [ht]; ring
    obtain ⟨hm, _, hR, he, _⟩ := hq
    have sm := Real.sq_sqrt hm.le
    have hm' := Real.sqrt_pos.mpr hm
    have he' := Real.sqrt_pos.mpr he
    have eqn : (q.L/q.μ)*(26*Real.sqrt (q.μ*q.R^2/q.ε) + 32*q.d/q.ε) =
        26*q.L*q.R/Real.sqrt (q.μ*q.ε) + 32*q.d*q.L/(q.μ*q.ε) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul hm.le, Real.sqrt_sq hR, Real.sqrt_mul hm.le]
      field_simp
      linear_combination (26*q.L*q.R*q.ε) * sm
    simp only [budget,N,B,warmCount,suffixCount,ha,ReparameterizedGaussianVI.budget,add_assoc,
      mul_assoc,eqn]
  refine ⟨fun q => if N q ≤ B q then warm q else base q, ?_, fun _ _ => trivial⟩
  intro q hq I O ho
  let succeeds := fun (A : Algorithm (Point q.d) (Point q.d) (Location q.d × Scale q.d))
      (b : Fin 1 → ℕ) => spec.successful q I (fun s : A.Seed × ((k : ℕ) → O.Seed k) =>
        execute O A b s.1 s.2) ⟨(A.law : MeasureTheory.Measure _).prod
          (O.law : MeasureTheory.Measure _), inferInstance⟩
  change succeeds (if N q ≤ B q then warm q else base q) (budget q)
  rw [eqb q hq]
  by_cases h : N q ≤ B q
  · rw [ite_eq_left h, min_eq_left h]
    exact hw q hq I O ho
  · rw [ite_eq_right h, min_eq_right (le_of_not_ge h)]
    exact hb q hq I O ho

end OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
