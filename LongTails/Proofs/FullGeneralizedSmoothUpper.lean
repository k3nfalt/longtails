import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.RadiusFreeSherpaExpected

namespace LongTails.Proofs.FullGeneralizedSmoothUpper

open OracleTemplate OracleTemplate.RadiusFreeSherpa MeasureTheory
open LongTails.Setups.GeneralizedSmoothConvexFull

noncomputable def effectiveParams (p : Params) : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params :=
  { d := p.d, L0 := p.L0, L1 := max p.L1 (1 / p.R), x0 := p.x0, R := p.R, ε := p.ε }

lemma expected_success (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : 64 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) +
      65536 * (1 + p.L1 * p.R) * Real.log (3 + p.L1 * p.R) ≤ N)
    (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
    (oracle : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) 1)
    (hf : spec.admissible p f oracle)
    (P : ProbabilityMeasure ((algorithm (effectiveParams p).toRadiusOnly.toPublic).Seed × ((k : ℕ) → oracle.Seed k))) :
    spec.successful p f
      (fun seed => execute oracle (algorithm (effectiveParams p).toRadiusOnly.toPublic)
        (fun _ => N) seed.1 seed.2) P := by
  rcases hp with ⟨h0, h1, hR, hε, hupper, hdim⟩
  have heff : 0 < (effectiveParams p).L1 :=
    lt_of_lt_of_le (one_div_pos.mpr hR) (le_max_right _ _)
  have hadm : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.admissible
      (effectiveParams p) f oracle := by
    rcases hf with ⟨hc, hg, hd, hH, hm⟩
    refine ⟨hc, hg, hd, ?_, hm⟩
    intro history seed x
    exact (hH history seed x).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  have hq : 0 ≤ p.L1 * p.R := mul_nonneg h1 hR.le
  have hqe : (effectiveParams p).L1 * p.R ≤ 1 + p.L1 * p.R := by
    change max p.L1 (1 / p.R) * p.R ≤ _
    rw [max_mul_of_nonneg _ _ hR.le]
    apply max_le
    · linarith
    · rw [one_div_mul_cancel hR.ne']
      linarith
  have hqen : 0 ≤ (effectiveParams p).L1 * p.R := mul_nonneg heff.le hR.le
  have hlog : Real.log (2 + (effectiveParams p).L1 * p.R) ≤ Real.log (3 + p.L1 * p.R) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogn : 0 ≤ Real.log (2 + (effectiveParams p).L1 * p.R) :=
    Real.log_nonneg (by linarith)
  have hcoef : 32768 * (1 + (effectiveParams p).L1 * p.R) ≤ 65536 * (1 + p.L1 * p.R) := by
    linarith
  have hm := mul_le_mul hcoef hlog hlogn (by positivity : 0 ≤ 65536 * (1 + p.L1 * p.R))
  have hN' : 64 * Real.sqrt ((effectiveParams p).L0 * (effectiveParams p).R ^ 2 / (effectiveParams p).ε) +
      32768 * (1 + (effectiveParams p).L1 * (effectiveParams p).R) *
        Real.log (2 + (effectiveParams p).L1 * (effectiveParams p).R) ≤ N := by
    change 64 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) +
      32768 * (1 + (effectiveParams p).L1 * p.R) *
        Real.log (2 + (effectiveParams p).L1 * p.R) ≤ N
    linarith
  exact RadiusFreeSherpaExpected.expected_success (effectiveParams p) h0 heff hR hε N hN' f oracle hadm P

end LongTails.Proofs.FullGeneralizedSmoothUpper
