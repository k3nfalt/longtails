import LongTails.Setups.GapGeneralizedSmoothConvex
import LongTails.Proofs.GeneralizedSelfNormalizedConvergence
import LongTails.Proofs.DampedGeneralizedExecution
import LongTails.Proofs.FullGeneralizedSmoothUpper

namespace LongTails.Proofs.GapGeneralizedSmoothUpper

open OracleTemplate MeasureTheory
open LongTails.Setups.GapGeneralizedSmoothConvex

lemma gap_expected_success (p : Params) (hp : spec.valid p) (K : ℕ)
    (hK : 4096 * (1 + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) +
      min ((⌈(p.L1 * p.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * p.Δ / p.ε))
        (Real.log (4 + 4 * p.Δ / p.ε) + (p.L1 * p.R * Real.log (4 + 4 * p.Δ / p.ε)) ^ (2 / 3 : ℝ))) ≤ K)
    (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (oracle : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) 1)
    (hf : spec.admissible p f oracle)
    (P : ProbabilityMeasure ((GeneralizedAccelerated.algorithm p.toGeneralized.toPublic).Seed ×
      ((k : ℕ) → oracle.Seed k))) :
    spec.successful p f
      (fun seed => execute oracle (GeneralizedAccelerated.algorithm p.toGeneralized.toPublic)
        (fun _ => 2 * K) seed.1 seed.2) P := by
  rcases hp with ⟨h0, h1, hR, hε, hεu, hΔu, hdim⟩
  rcases hf with ⟨hc, hg, hgd, hH, u, hmin, hdist, hgap⟩
  have hΔ : 0 < p.Δ := by linarith
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  let x := (GeneralizedAccelerated.run p.L0 p.L1 g
    (GeneralizedAccelerated.initialIterate p.L0 p.L1 p.R p.Δ p.x0 g) K).x
  have hacc : f x - f u ≤ p.ε := GeneralizedAccelerated.run_accuracy_min h0 h1 hR hΔ hε
    hc (hg [] seed0) (hgd [] seed0) (hH [] seed0) p.x0 u hmin hdist hgap K hK
  have hexec (seed : (GeneralizedAccelerated.algorithm p.toGeneralized.toPublic).Seed ×
      ((k : ℕ) → oracle.Seed k)) :
      execute oracle (GeneralizedAccelerated.algorithm p.toGeneralized.toPublic)
        (fun _ => 2 * K) seed.1 seed.2 = x :=
    GeneralizedAccelerated.execute_gradient_oracle p.toGeneralized.toPublic f g oracle
      (hg [] seed0) hg h0 h1 hΔ K seed.1 seed.2
  refine ⟨u, hmin, ?_, ?_⟩
  · simpa only [hexec] using (integrable_const (f x - f u) : Integrable
      (fun _ : (GeneralizedAccelerated.algorithm p.toGeneralized.toPublic).Seed ×
        ((k : ℕ) → oracle.Seed k) => f x - f u) (P : Measure _))
  · simpa only [hexec, integral_const, probReal_univ, one_smul] using hacc

noncomputable def radiusParams (p : Params) : LongTails.Setups.GeneralizedSmoothConvexFull.Params :=
  { d := p.d, L0 := p.L0, L1 := p.L1, x0 := p.x0, R := p.R, ε := p.ε }

lemma radius_valid (p : Params) (hp : spec.valid p) :
    LongTails.Setups.GeneralizedSmoothConvexFull.spec.valid (radiusParams p) := by
  rcases hp with ⟨h0, h1, hR, hε, he, hΔ, hd⟩
  refine ⟨h0, h1, hR, hε, he, ?_⟩
  apply le_trans _ hd
  apply Nat.ceil_mono
  have hU : 1 ≤ 1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := by
    linarith [mul_nonneg h1 hR.le, Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)]
  have hh := pow_le_pow_right₀ hU (show 5 ≤ 10 by norm_num)
  change 17592186044416 * (1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 5 ≤ _
  nlinarith [pow_nonneg (show 0 ≤ 1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) by positivity) 10]

lemma radius_expected_success (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : 64 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) +
      65536 * (1 + p.L1 * p.R) * Real.log (3 + p.L1 * p.R) ≤ N)
    (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (oracle : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) 1)
    (hf : spec.admissible p f oracle)
    (P : ProbabilityMeasure
      ((RadiusFreeSherpa.algorithm (FullGeneralizedSmoothUpper.effectiveParams (radiusParams p)).toRadiusOnly.toPublic).Seed ×
        ((k : ℕ) → oracle.Seed k))) :
    spec.successful p f
      (fun seed => execute oracle
        (RadiusFreeSherpa.algorithm (FullGeneralizedSmoothUpper.effectiveParams (radiusParams p)).toRadiusOnly.toPublic)
        (fun _ => N) seed.1 seed.2) P := by
  have hf' : LongTails.Setups.GeneralizedSmoothConvexFull.spec.admissible (radiusParams p) f oracle := by
    rcases hf with ⟨hc, hg, hgd, hH, u, hu, hR, hΔ⟩
    exact ⟨hc, hg, hgd, hH, u, hu, hR⟩
  exact FullGeneralizedSmoothUpper.expected_success (radiusParams p) (radius_valid p hp) N hN f oracle hf' P

end LongTails.Proofs.GapGeneralizedSmoothUpper
