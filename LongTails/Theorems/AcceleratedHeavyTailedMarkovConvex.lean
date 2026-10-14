import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.AcceleratedMarkovConvergence
import LongTails.Proofs.AcceleratedMarkovTuning

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈Real.sqrt (32 * q.L * q.R ^ 2 / q.ε) + (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))⌉₊ * max 1 ⌈q.τ * (256 * q.L * q.R ^ 2 / q.ε + 64 * (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) ^ (1 / q.β)⌉₊

theorem result :
    Convergence LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q =>
    let N := max 1 ⌈Real.sqrt (32 * q.L * q.R ^ 2 / q.ε) + (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))⌉₊
    let m := max 1 ⌈q.τ * (256 * q.L * q.R ^ 2 / q.ε + 64 * (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) ^ (1 / q.β)⌉₊
    acceleratedMarkov (2 * q.L + q.ε * (N : ℝ) ^ 2 / (16 * q.R ^ 2))
      q.R (4 * q.L * q.R + q.ε / q.R * (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) m q.x0, ?_, fun _ _ => trivial⟩
  intro q hp f O h
  rcases hp with ⟨hL, hR, hσ, hα, hα2, hτ, hβ, hε⟩
  rcases h with ⟨g, κ, hκ, π, hO, hπ, hd, hmix, hc, hg, hlip, ⟨u, hm, hdist⟩,
    hG, hGi, hmean, hmi, hmoment⟩
  let : IsMarkovKernel κ := hκ
  subst O
  let N := max 1 ⌈Real.sqrt (32 * q.L * q.R ^ 2 / q.ε) + (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))⌉₊
  let m := max 1 ⌈q.τ * (256 * q.L * q.R ^ 2 / q.ε + 64 * (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) ^ (1 / q.β)⌉₊
  let D := 2 * q.L + q.ε * (N : ℝ) ^ 2 / (16 * q.R ^ 2)
  let C := 4 * q.L * q.R + q.ε / q.R * (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))
  let P : Measure (ℕ → q.Ω) := pathLaw κ π
  let output := fun ξ : ℕ → q.Ω => (clippedRun g D q.R C m q.x0 ξ N).2.1
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hD : 0 < D := by dsimp [D]; positivity
  have hLD : 2 * q.L ≤ D := le_add_of_nonneg_right (by positivity)
  have hu : ‖u - q.x0‖ ≤ q.R := by simpa only [norm_sub_rev] using hdist
  have hout : Measurable output := (measurable_clippedRun hG D q.R C m q.x0 N).fst
  have hacc : Integrable (fun ξ => f (output ξ) - f u) P ∧ (∫ ξ, f (output ξ) - f u ∂P) ≤ q.ε := by
    by_cases hz : q.R = 0
    · have hzero : ∀ ξ, output ξ = u := by
        intro ξ
        have hh := (clippedRun_ball g D C hR m q.x0 ξ N).1
        change ‖output ξ - q.x0‖ ≤ q.R at hh
        rw [hz] at hh hdist
        have hx : output ξ = q.x0 := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
        have hu' : q.x0 = u := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hdist (norm_nonneg _)))
        exact hx.trans hu'
      simp only [hzero, sub_self, integral_zero]
      exact ⟨integrable_const 0, hε.le⟩
    · have hRpos : 0 < q.R := lt_of_le_of_ne hR (Ne.symm hz)
      have hC : 0 < C := by dsimp [C]; positivity
      have hLC : 4 * q.L * q.R ≤ C := le_add_of_nonneg_right (by positivity)
      have hceil : Real.sqrt (32 * q.L * q.R ^ 2 / q.ε) + (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1)) ≤ (N : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
      have hdet : Real.sqrt (32 * q.L * q.R ^ 2 / q.ε) ≤ (N : ℝ) := by
        have hh : 0 ≤ (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1)) := by positivity
        linarith
      have hnoise : (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1)) ≤ (N : ℝ) := by
        linarith [Real.sqrt_nonneg (32 * q.L * q.R ^ 2 / q.ε)]
      have hmceil : q.τ * (256 * q.L * q.R ^ 2 / q.ε + 64 * (256 * q.σ * q.R / q.ε) ^ (q.α / (q.α - 1))) ^ (1 / q.β) ≤ (m : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
      have htune := accelerated_markov_tuning hL hσ hRpos hε hτ hβ hα hα2
        (Nat.cast_pos.mpr hN) hdet hnoise m hmceil
      have hr := clippedRun_rate κ π hπ hG hGi hmean hL hD hLD hR hσ hC hLC hα.le hα2 hc hg hlip
        hmi hmoment m (hd m) (hmix m) q.x0 u hm hu N hN
      exact ⟨hr.1, hr.2.trans htune⟩
  let result := fun seed : Unit × (ℕ → q.Ω) => (execute
      { Seed := fun _ => q.Ω, law := pathLaw κ π, answer := fun _ (_, x) y => g x y }
      (acceleratedMarkov D q.R C m q.x0) (fun _ => (N * m)) seed.1 seed.2)
  change Measurable result ∧ ∃ u, IsMinOn f Set.univ u ∧
    Integrable (fun seed => f (result seed) - f u) ((Measure.dirac ()).prod P) ∧
    (∫ seed, f (result seed) - f u ∂(Measure.dirac ()).prod P) ≤ q.ε
  have hexec : result = fun seed => output seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact (execute_acceleratedMarkov (pathLaw κ π) g D q.R C hmpos q.x0 ξ N)
  rw [hexec]
  refine ⟨hout.comp measurable_snd, u, hm, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hacc.1
  · rw [integral_fun_snd (fun ξ : ℕ → q.Ω => f (output ξ) - f u)]
    simpa using hacc.2

end OracleTemplate.HeavyTailedMarkovGradient
