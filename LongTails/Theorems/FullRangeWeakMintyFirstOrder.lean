import LongTails.Setups.WeakMintySecondOrder
import LongTails.Proofs.FullRangeWeakMintyFirstOrder

namespace OracleTemplate.FullRangeWeakMintyFirstOrder

open LongTails.Setups.WeakMintySecondOrder
open WeakMintyHybrid

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let δ := 1 - q.ρ * q.L₁ / 2
  let H := 1048576 * Real.log (2 / δ) / δ ^ 5
  if 8 * q.L₁ ^ 2 / (δ ^ 2 * q.ε ^ 2) ≤ H * q.L₂ / q.ε then
    ⌊8 * q.L₁ ^ 2 * q.R ^ 2 / (δ ^ 2 * q.ε ^ 2)⌋₊ + 1
  else
    ⌈H * (1 + q.L₂ * q.R ^ 2 / q.ε)⌉₊

theorem result : Convergence LongTails.Setups.WeakMintySecondOrder.spec budget := by
  classical
  refine ⟨fun p => select p.L₁ p.L₂ p.ρ p.ε p.x0, ?_, fun _ _ => trivial⟩
  intro q hq F oracle hadm
  obtain ⟨hL, hM, hρ, hρL, _, hε⟩ := hq
  obtain ⟨J, hF, hJ, hder, hjlip, hlip, z, hz, hdist, hm⟩ := hadm
  let succeeds (A : Algorithm (q.E ⊕ q.E) (q.E × (q.E →L[ℝ] q.E)) q.E) : Prop :=
    spec.successful q F (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
      execute oracle A (budget q) seed.1 seed.2)
      ⟨(A.law : MeasureTheory.Measure _).prod (oracle.law : MeasureTheory.Measure _), inferInstance⟩
  change succeeds (select q.L₁ q.L₂ q.ρ q.ε q.x0)
  by_cases hs : useValues q.L₁ q.L₂ q.ρ q.ε
  · rw [select, ite_eq_left hs]
    have hK : ⌊8 * q.L₁ ^ 2 * q.R ^ 2 / ((margin q.L₁ q.ρ) ^ 2 * q.ε ^ 2)⌋₊ + 1 ≤ budget q 0 := by
      unfold useValues margin at hs
      simp only [budget, hs, ite_true, margin, le_refl]
    exact Filter.Eventually.of_forall (fun seed =>
      value_execute_accurate hL hρ hρL hε hlip hm hz q.x0 hdist hK oracle J hF hJ seed.1 seed.2)
  · rw [select, ite_eq_right hs]
    let δ := margin q.L₁ q.ρ
    have hd : 0 < δ := margin_pos hρL
    have hd' : δ ≤ 1 := margin_le_one hL.le hρ
    have hN := iteration_sufficient hd hM hε (norm_nonneg _) hdist
    have hK := total_budget hd hd' (show 0 ≤ q.L₂ * q.R ^ 2 / q.ε by positivity)
    have hb : budget q 0 = ⌈1048576 * (1 + q.L₂ * q.R ^ 2 / q.ε) * Real.log (2 / δ) / δ ^ 5⌉₊ := by
      unfold useValues margin at hs
      simp only [budget, hs, ite_false]
      congr 1
      dsimp [δ, margin]
      ring
    rw [← hb] at hK
    exact Filter.Eventually.of_forall (fun seed =>
      execute_accurate ⟨hder, hjlip, hlip, hm⟩ hL hM hρ hρL hε q.x0 hN hK
        oracle hF hJ seed.1 seed.2)

end OracleTemplate.FullRangeWeakMintyFirstOrder
