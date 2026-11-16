import LongTails.Proofs.AsgoFixedRadiusBatch
import LongTails.Proofs.AsgoFixedRadiusMeasurability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open MeasureTheory Matrix OracleTemplate.Muon
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma trajectory_memLp (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (t : ℕ) (ht : t < T) :
    MemLp (fun ω => Core.point p I.g (fun j => ξ j ω) t) 2 P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    have hm := (trajectory_measurable p I.g hS.gradientMeasurable ξ hξ.measurable t).fst
    apply MemLp.of_bound hm.aestronglyMeasurable (F + ‖Wstar‖)
    filter_upwards [hRad.2] with ω hω
    have hb := (hω t ht).2
    have hn := norm_add_le (Core.point p I.g (fun j => ξ j ω) t - Wstar) Wstar
    rw [sub_add_cancel] at hn
    change ‖Core.point p I.g (fun j => ξ j ω) t‖ ≤ F + ‖Wstar‖
    linarith
  )

lemma gradient_memLp (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (t : ℕ) (ht : t < T) :
    MemLp (fun ω => I.H (Core.point p I.g (fun j => ξ j ω) t)) 2 P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    have hm := (trajectory_measurable p I.g hS.gradientMeasurable ξ hξ.measurable t).fst
    have hg := (gradient_continuous I Wstar hS).measurable.comp hm
    have hL : 0 ≤ spectralNorm (ofMatrix I.L) := norm_nonneg _
    apply MemLp.of_bound hg.aestronglyMeasurable (spectralNorm (ofMatrix I.L) * F)
    filter_upwards [hRad.2] with ω hω
    exact (gradient_norm_bound I Wstar hS _).trans
      (mul_le_mul_of_nonneg_left (hω t ht).2 hL)
  )

lemma estimator_memLp (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (hM : 1 ≤ p.M)
    (t : ℕ) (ht : t < T) :
    MemLp (fun ω => Core.batchGradient p I.g (fun j => ξ j ω) t (Core.point p I.g (fun j => ξ j ω) t)) 2 P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    exact (batch_noise_memLp p I Wstar hS P ξ hξ hM t
      (fun ω => Core.point p I.g (fun j => ξ j ω) t)
      (trajectory_adapted p I.g hS.gradientMeasurable ξ t)
      F hRad.1 (hRad.2.mono (fun ω hω => (hω t ht).2))).1
  )

lemma noise_memLp (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (hM : 1 ≤ p.M)
    (t : ℕ) (ht : t < T) :
    MemLp (fun ω => Core.batchGradient p I.g (fun j => ξ j ω) t (Core.point p I.g (fun j => ξ j ω) t) - I.H (Core.point p I.g (fun j => ξ j ω) t)) 2 P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    exact (batch_noise_memLp p I Wstar hS P ξ hξ hM t
      (fun ω => Core.point p I.g (fun j => ξ j ω) t)
      (trajectory_adapted p I.g hS.gradientMeasurable ξ t)
      F hRad.1 (hRad.2.mono (fun ω hω => (hω t ht).2))).2
  )

lemma gap_integrable (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (t : ℕ) (ht : t < T) :
    Integrable (fun ω => I.f (Core.point p I.g (fun j => ξ j ω) t) - I.f Wstar) P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    let Y : Ω → Mat p.m p.n := fun ω => Core.point p I.g (fun j => ξ j ω) t
    have hm : Measurable Y :=
      (trajectory_measurable p I.g hS.gradientMeasurable ξ hξ.measurable t).fst
    have hy : MemLp Y 2 P.toMeasure := trajectory_memLp p I Wstar hS P ξ hξ T F hRad t ht
    have hd : MemLp (fun ω => Y ω - Wstar) 2 P.toMeasure :=
      hy.sub (memLp_const Wstar)
    have hg : MemLp (fun ω => I.H (Y ω)) 2 P.toMeasure :=
      gradient_memLp p I Wstar hS P ξ hξ T F hRad t ht
    have hi : Integrable (fun ω => ‖I.H (Y ω)‖ * ‖Y ω - Wstar‖) P.toMeasure :=
      hg.norm.integrable_mul hd.norm
    have hgm : AEStronglyMeasurable (fun ω => I.f (Y ω) - I.f Wstar) P.toMeasure :=
      ((objective_continuous I Wstar hS).measurable.comp hm).sub measurable_const
        |>.aestronglyMeasurable
    apply hi.mono' hgm
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hS.minimizer _))]
    have hc := OracleTemplate.Gradient.convex_support hS.convex hS.objectiveGradient (Y ω) Wstar
    have he : Wstar - Y ω = -(Y ω - Wstar) := (neg_sub (Y ω) Wstar).symm
    rw [he, inner_neg_right] at hc
    have hh := real_inner_le_norm (I.H (Y ω)) (Y ω - Wstar)
    linarith
  )

lemma weighted_terms_integrable (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (hM : 1 ≤ p.M)
    (t : ℕ) (ht : t < T) :
    Integrable (fun ω => Core.weightedQuadratic I.L⁻¹ (I.H (Core.point p I.g (fun j => ξ j ω) t))) P.toMeasure ∧
      Integrable (fun ω => Core.weightedQuadratic I.V⁻¹ (Core.batchGradient p I.g (fun j => ξ j ω) t (Core.point p I.g (fun j => ξ j ω) t) - I.H (Core.point p I.g (fun j => ξ j ω) t))) P.toMeasure ∧
      Integrable (fun ω => inner ℝ (Core.batchGradient p I.g (fun j => ξ j ω) t (Core.point p I.g (fun j => ξ j ω) t)) (Core.point p I.g (fun j => ξ j ω) t - Wstar)) P.toMeasure ∧
      Integrable (fun ω => inner ℝ (I.H (Core.point p I.g (fun j => ξ j ω) t)) (Core.point p I.g (fun j => ξ j ω) t - Wstar)) P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    have hinner (Y Z : Ω → Mat p.m p.n) (hY : MemLp Y 2 P.toMeasure)
        (hZ : MemLp Z 2 P.toMeasure) :
        Integrable (fun ω => inner ℝ (Y ω) (Z ω)) P.toMeasure := by
      have hp : Integrable (fun ω => ‖Y ω‖ * ‖Z ω‖) P.toMeasure :=
        hY.norm.integrable_mul hZ.norm
      have hm : AEStronglyMeasurable (fun ω => inner ℝ (Y ω) (Z ω)) P.toMeasure :=
        hY.aestronglyMeasurable.inner hZ.aestronglyMeasurable
      exact hp.mono' hm (Filter.Eventually.of_forall (fun ω => norm_inner_le_norm (Y ω) (Z ω)))
    have hquad (A : Matrix (Fin p.m) (Fin p.m) ℝ)
        (Y : Ω → Mat p.m p.n) (hY : MemLp Y 2 P.toMeasure) :
        Integrable (fun ω => Core.weightedQuadratic A (Y ω)) P.toMeasure := by
      have hc (ij : Fin p.m × Fin p.n) : MemLp (fun ω => Y ω ij) 2 P.toMeasure :=
        hY.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin p.m × Fin p.n => ℝ) ij)
      change Integrable (fun ω => ∑ j : Fin p.n, ∑ k : Fin p.m,
        (∑ i : Fin p.m, Y ω (i, j) * A i k) * Y ω (k, j)) P.toMeasure
      simp_rw [Finset.sum_mul]
      apply integrable_finsetSum
      intro j _
      apply integrable_finsetSum
      intro k _
      apply integrable_finsetSum
      intro i _
      have hh := ((hc (i, j)).integrable_mul (hc (k, j))).mul_const (A i k)
      exact hh.congr (Filter.Eventually.of_forall (fun ω => by
        change (Y ω (i, j) * Y ω (k, j)) * A i k = (Y ω (i, j) * A i k) * Y ω (k, j)
        ring))
    have hx := trajectory_memLp p I Wstar hS P ξ hξ T F hRad t ht
    have hd : MemLp (fun ω => Core.point p I.g (fun j => ξ j ω) t - Wstar) 2 P.toMeasure :=
      hx.sub (memLp_const Wstar)
    have hh := gradient_memLp p I Wstar hS P ξ hξ T F hRad t ht
    have hg := estimator_memLp p I Wstar hS P ξ hξ T F hRad hM t ht
    have hn := noise_memLp p I Wstar hS P ξ hξ T F hRad hM t ht
    exact ⟨hquad I.L⁻¹ _ hh, hquad I.V⁻¹ _ hn, hinner _ _ hg hd, hinner _ _ hh hd⟩
  )

lemma expected_inner_eq (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T)
    (hM : 1 ≤ p.M)
    (t : ℕ) (ht : t < T) :
    (∫ ω, inner ℝ (Core.batchGradient p I.g (fun j => ξ j ω) t (Core.point p I.g (fun j => ξ j ω) t)) (Core.point p I.g (fun j => ξ j ω) t - Wstar) ∂P.toMeasure) =
      ∫ ω, inner ℝ (I.H (Core.point p I.g (fun j => ξ j ω) t)) (Core.point p I.g (fun j => ξ j ω) t - Wstar) ∂P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    have hz := batch_inner_zero p I Wstar hS P ξ hξ hM t
      (fun ω => Core.point p I.g (fun j => ξ j ω) t)
      (trajectory_adapted p I.g hS.gradientMeasurable ξ t)
      F hRad.1 (hRad.2.mono (fun ω hω => (hω t ht).2))
    have hi := weighted_terms_integrable p I Wstar hS P ξ hξ T F hRad hM t ht
    simp only [inner_sub_left] at hz
    rw [integral_sub hi.2.2.1 hi.2.2.2] at hz
    exact sub_eq_zero.mp hz
  )

end OracleTemplate.AsgoFixedRadius
