import LongTails.Setups.MarkovQuadraticInterpolation
import LongTails.Proofs.MarkovQuadraticWeightedAverage
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.MarkovQuadraticWeightedAverage

open LongTails.Setups.MarkovQuadraticInterpolation

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let B := q.L * q.R ^ 2 / 2
  if B ≤ q.ε then 0 else 1 + ⌈(B / q.ε - 1) / q.α⌉₊

theorem result : Convergence LongTails.Setups.MarkovQuadraticInterpolation.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => algorithm q.L q.α q.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hR, hα, _, hε⟩ K hK f O ⟨m, π, μ, κ, hκ, H, u, model, rfl⟩
  have := hκ
  let P := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ
  let y := fun ξ => output q.α q.x0 (point q H u ξ) K
  let B := q.L * q.R^2 / 2
  have hi : Integrable (fun ξ => f (y ξ) - f u) (P : Measure (ℕ → Fin m)) :=
    integrable_output_gap _ _
  have ha : (∫ ξ, f (y ξ) - f u ∂(P : Measure (ℕ → Fin m))) ≤ q.ε := by
    change (if B ≤ q.ε then 0 else 1 + ⌈(B / q.ε - 1) / q.α⌉₊) ≤ K at hK
    cases K with
    | zero =>
      have hb : B ≤ q.ε := by by_contra! hn; simp [hn.not_ge] at hK
      have hr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) model.radius 2) hL.le
      have hx := model.objective_upper q.x0
      change (∫ _ : ℕ → Fin m, f q.x0 - f u ∂(P : Measure _)) ≤ _
      simp only [integral_const, probReal_univ, one_smul]
      dsimp [B] at hb
      linarith
    | succ n =>
      apply (output_risk model μ hL hα n).trans
      apply (div_le_iff₀ (by positivity)).mpr
      change B ≤ _
      by_cases hb : B ≤ q.ε
      · nlinarith [mul_nonneg (mul_nonneg hε.le hα.le) (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      · simp only [hb, ite_false] at hK
        have hc : ⌈(B / q.ε - 1) / q.α⌉₊ ≤ n := by omega
        have hd := (div_le_iff₀ hα).mp ((Nat.le_ceil _).trans (Nat.cast_le.mpr hc))
        have hh : B / q.ε ≤ 1 + q.α * n := by linarith
        linarith only [(div_le_iff₀ hε).mp hh]
  let actual := fun seed : Unit × (ℕ → Fin m) =>
    execute { Seed := fun _ => Fin m, law := P, answer := fun _ (_, x) i => H i (x-u) }
      (algorithm q.L q.α q.x0) (fun _ => K) seed.1 seed.2
  change Measurable actual ∧ ∃ u, IsMinOn f Set.univ u ∧
    Integrable (fun seed => f (actual seed) - f u) ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ seed, f (actual seed) - f u ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε
  have he : actual = fun seed => y seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact execute_output P (fun x i => H i (x-u)) q.L q.α q.x0 K ξ
  rw [he]
  refine ⟨(measurable_output H u K).comp measurable_snd, u, model.minimizer, ?_, ?_⟩
  · change Integrable (fun seed : Unit × (ℕ → Fin m) => f (y seed.2) - f u)
      ((Measure.dirac ()).prod (P : Measure (ℕ → Fin m)))
    exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → Fin m)))).integrable_comp_of_integrable hi
  · rw [integral_fun_snd (fun ξ => f (y ξ) - f u)]
    simpa using ha

end OracleTemplate.MarkovQuadraticWeightedAverage
