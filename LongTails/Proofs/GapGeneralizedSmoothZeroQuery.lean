import LongTails.Setups.GapGeneralizedSmoothConvex
import LongTails.Proofs.GapGeneralizedSmoothUpper
import LongTails.Proofs.FullGeneralizedSmoothZeroQuery

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate Set

namespace LongTails.Proofs.GapGeneralizedSmoothZeroQuery

open LongTails.Setups.GapGeneralizedSmoothConvex
open FullGeneralizedSmoothZeroQuery

lemma admissible (p : Params) (hp : spec.valid p) (u : EuclideanSpace ℝ (Fin p.d))
    (hu : ‖u‖ ≤ p.R) (hgap : p.L0 / 2 * ‖u‖ ^ 2 ≤ p.Δ) :
    spec.admissible p (fun x : EuclideanSpace ℝ (Fin p.d) => quadratic p.L0 u (x - p.x0))
      (SmoothConvexFiniteLowerBound.oracle p.x0 (field p.L0 u)) := by
  have hadm := FullGeneralizedSmoothZeroQuery.admissible (GapGeneralizedSmoothUpper.radiusParams p)
    (GapGeneralizedSmoothUpper.radius_valid p hp) u hu
  rcases hadm with ⟨hc, hg, hd, hH, v, hm, hr⟩
  change EuclideanSpace ℝ (Fin p.d) at v
  refine ⟨hc, hg, hd, hH, v, hm, hr, ?_⟩
  have hz : quadratic p.L0 u (v - p.x0) = 0 := by
    apply le_antisymm
    · have hh := hm (mem_univ (p.x0 + u))
      change quadratic p.L0 u (v - p.x0) ≤ quadratic p.L0 u (p.x0 + u - p.x0) at hh
      simpa only [add_sub_cancel_left, quadratic_zero] using hh
    · exact quadratic_nonneg p.L0 hp.1.le u _
  change quadratic p.L0 u (p.x0 - p.x0) - quadratic p.L0 u (v - p.x0) ≤ p.Δ
  rw [hz, sub_zero]
  simpa only [sub_self, quadratic, zero_sub, norm_neg] using hgap

lemma exists_failure (p : Params) (hp : spec.valid p) (hd : 0 < p.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => 0) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  by_contra h
  push Not at h
  let u : EuclideanSpace ℝ (Fin p.d) := PiLp.single 2 ⟨0, hd⟩ (Real.sqrt (4 * p.ε / p.L0))
  have hu : ‖u‖ = Real.sqrt (4 * p.ε / p.L0) := by
    simp only [u, PiLp.norm_single, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h0 := hp.1
  have hε := hp.2.2.2.1
  have hR := hp.2.2.1
  have hs := Real.sq_sqrt (show 0 ≤ 4 * p.ε / p.L0 by positivity)
  have hnorm : p.L0 * ‖u‖ ^ 2 = 4 * p.ε := by rw [hu, hs]; field_simp
  have huR : ‖u‖ ≤ p.R := by
    have hh := hp.2.2.2.2.1
    have hs' : ‖u‖ ^ 2 ≤ p.R ^ 2 := (mul_le_mul_iff_of_pos_left h0).mp (by
      nlinarith only [hh, hnorm, hε])
    nlinarith [norm_nonneg u]
  have hgap : p.L0 / 2 * ‖u‖ ^ 2 ≤ p.Δ := by
    have hh := hp.2.2.2.2.2.1
    nlinarith only [hnorm, hh, hε]
  have hp' := h _ _ (admissible p hp u huR hgap)
  have hm' := h _ _ (admissible p hp (-u) (by simpa only [norm_neg] using huR) (by simpa only [norm_neg] using hgap))
  obtain ⟨hip, hep⟩ := zero_success (GapGeneralizedSmoothUpper.radiusParams p) (GapGeneralizedSmoothUpper.radius_valid p hp) u A hp'
  obtain ⟨him, hem⟩ := zero_success (GapGeneralizedSmoothUpper.radiusParams p) (GapGeneralizedSmoothUpper.radius_valid p hp) (-u) A hm'
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  have hpair (w : A.Seed × (ℕ → Unit)) : p.L0 * ‖u‖ ^ 2 ≤
      quadratic p.L0 u (A.output (A.initial w.1) - p.x0) +
      quadratic p.L0 (-u) (A.output (A.initial w.1) - p.x0) := by
    exact quadratic_pair p.L0 hp.1.le u (A.output (A.initial w.1) - p.x0)
  have hh := integral_mono (μ := (P : Measure _)) (integrable_const (p.L0 * ‖u‖ ^ 2))
    (hip.add him) hpair
  have hipP : Integrable (fun w : A.Seed × (ℕ → Unit) => quadratic p.L0 u (A.output (A.initial w.1) - p.x0))
      (P : Measure (A.Seed × (ℕ → Unit))) := hip
  have himP : Integrable (fun w : A.Seed × (ℕ → Unit) => quadratic p.L0 (-u) (A.output (A.initial w.1) - p.x0))
      (P : Measure (A.Seed × (ℕ → Unit))) := him
  rw [integral_add hipP himP] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  change _ ≤ (∫ w : A.Seed × (ℕ → Unit), quadratic p.L0 u (A.output (A.initial w.1) - p.x0)
    ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) +
    (∫ w : A.Seed × (ℕ → Unit), quadratic p.L0 (-u) (A.output (A.initial w.1) - p.x0)
    ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) at hh
  dsimp [GapGeneralizedSmoothUpper.radiusParams] at hep hem
  linarith

end LongTails.Proofs.GapGeneralizedSmoothZeroQuery
