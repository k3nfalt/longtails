import LongTails.Proofs.AsgoFixedRadiusRegularity
import LongTails.Proofs.AsgoFixedRadiusEnergy
import LongTails.Proofs.AsgoFixedRadiusMetric
import LongTails.Proofs.AsgoFixedRadiusAverage
import LongTails.Proofs.AsgoFixedRadiusTransport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory Matrix OracleTemplate OracleTemplate.Muon
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius
open LongTails.Algorithms.AsgoFixedRadiusOutput

lemma raw_rate (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (hT : 1 ≤ T) (hM : 1 ≤ p.M) (hR : 0 < p.R) (hk : 0 < p.k)
    (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T) :
    (∀ t < T, Integrable
      (fun ω => I.f (Core.point p I.g (fun j => ξ j ω) t) - I.f Wstar) P.toMeasure) ∧
      (1 / (T : ℝ)) *
        (∑ t ∈ Finset.range T,
          ∫ ω, I.f (Core.point p I.g (fun j => ξ j ω) t) - I.f Wstar ∂P.toMeasure) ≤
        4 * p.R ^ 2 * I.L.trace / (T : ℝ) +
          2 * Real.sqrt 2 * p.R * I.V.trace / Real.sqrt ((p.M : ℝ) * (T : ℝ)) +
          2 * p.k * F ^ 2 / (p.R * (T : ℝ)) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    have hTp : 0 < T := by omega
    have hMp : 0 < p.M := by omega
    have hTr : 0 < (T : ℝ) := by exact_mod_cast hTp
    have hMr : 0 < (p.M : ℝ) := by exact_mod_cast hMp
    have hgap (t : ℕ) (ht : t < T) :=
      gap_integrable p I Wstar hS P ξ hξ T F hRad t ht
    refine ⟨hgap, ?_⟩
    let x := fun t ω => Core.point p I.g (fun j => ξ j ω) t
    let g := fun t ω => Core.batchGradient p I.g (fun j => ξ j ω) t (x t ω)
    let h := fun t ω => I.H (x t ω)
    let z := fun t ω => g t ω - h t ω
    let s : ℝ := Real.sqrt ((T : ℝ) / (p.M : ℝ))
    let c : ℝ := s / (2 * p.R)
    let a : ℝ := 3 * p.R / 2
    let C : ℝ := a ^ 2 * I.L.trace + a ^ 2 * c * I.V.trace + p.k * F ^ 2 / (2 * p.R)
    have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hTr hMr)
    have hc : 0 < c := div_pos hs (by positivity)
    have hqH (t : ℕ) (ht : t < T) :
        Integrable (fun ω => Core.weightedQuadratic I.L⁻¹ (h t ω)) P.toMeasure :=
      (weighted_terms_integrable p I Wstar hS P ξ hξ T F hRad hM t ht).1
    have hqN (t : ℕ) (ht : t < T) :
        Integrable (fun ω => Core.weightedQuadratic I.V⁻¹ (z t ω)) P.toMeasure :=
      (weighted_terms_integrable p I Wstar hS P ξ hξ T F hRad hM t ht).2.1
    have hiG (t : ℕ) (ht : t < T) :
        Integrable (fun ω => inner ℝ (g t ω) (x t ω - Wstar)) P.toMeasure :=
      (weighted_terms_integrable p I Wstar hS P ξ hξ T F hRad hM t ht).2.2.1
    have hiH (t : ℕ) (ht : t < T) :
        Integrable (fun ω => inner ℝ (h t ω) (x t ω - Wstar)) P.toMeasure :=
      (weighted_terms_integrable p I Wstar hS P ξ hξ T F hRad hM t ht).2.2.2
    have hacc (ω : Ω) (t : ℕ) :
        Core.accumulator p I.g (fun j => ξ j ω) t =
          ∑ j ∈ Finset.range t, Core.gram (g j ω) := by
      induction t with
      | zero => rfl
      | succ t ih =>
          change Core.accumulator p I.g (fun j => ξ j ω) t + Core.gram (g t ω) = _
          rw [Finset.sum_range_succ, ih]
    have hpoly :
        (fun ω => ∑ t ∈ Finset.range T, inner ℝ (g t ω) (x t ω - Wstar)) ≤ᵐ[P.toMeasure]
          (fun ω => (∑ t ∈ Finset.range T, Core.weightedQuadratic I.L⁻¹ (h t ω)) / 2 +
            (∑ t ∈ Finset.range T, Core.weightedQuadratic I.V⁻¹ (z t ω)) / (2 * c) + C) := by
      filter_upwards [hRad.2] with ω hω
      have hreg := pathwise_regret (fun t => x t ω) (fun t => g t ω) Wstar
        p.R F p.k T hR hRad.1 hk (fun t ht => (hω t ht).1) (fun t ht => (hω t ht).2)
        (by
          intro t _
          change x t ω - p.R • ofMatrix
            ((Core.matrixRoot (Core.accumulator p I.g (fun j => ξ j ω) (t + 1)) +
              p.k • (1 : Matrix (Fin p.m) (Fin p.m) ℝ))⁻¹ * toMatrix (g t ω)) = _
          rw [hacc])
      have hmet := combined_metric_control I.L I.V (fun t => h t ω) (fun t => z t ω)
        p.R T p.M hS.smoothPos hS.variancePos hR hTp hMp
      have he (t : ℕ) : h t ω + z t ω = g t ω := by
        change h t ω + (g t ω - h t ω) = g t ω
        module
      simp only [he] at hmet
      change a * (Core.matrixRoot (∑ t ∈ Finset.range T, Core.gram (g t ω))).trace ≤
        (∑ t ∈ Finset.range T, Core.weightedQuadratic I.L⁻¹ (h t ω)) / 2 +
          (∑ t ∈ Finset.range T, Core.weightedQuadratic I.V⁻¹ (z t ω)) / (2 * c) +
          a ^ 2 * I.L.trace + a ^ 2 * c * I.V.trace at hmet
      change (∑ t ∈ Finset.range T, inner ℝ (g t ω) (x t ω - Wstar)) ≤
        a * (Core.matrixRoot (∑ t ∈ Finset.range T, Core.gram (g t ω))).trace +
          p.k * F ^ 2 / (2 * p.R) at hreg
      dsimp only [C]
      linarith only [hreg, hmet]
    have hQI := integrable_finsetSum (Finset.range T) (fun t ht => hqH t (Finset.mem_range.mp ht))
    have hNI := integrable_finsetSum (Finset.range T) (fun t ht => hqN t (Finset.mem_range.mp ht))
    have hGI := integrable_finsetSum (Finset.range T) (fun t ht => hiG t (Finset.mem_range.mp ht))
    have hUI := ((hQI.div_const 2).fun_add (hNI.div_const (2 * c))).fun_add (integrable_const C)
    have hE := integral_mono_ae hGI hUI hpoly
    rw [integral_add ((hQI.div_const 2).fun_add (hNI.div_const (2 * c))) (integrable_const C),
      integral_add (hQI.div_const 2) (hNI.div_const (2 * c)),
      integral_div, integral_div,
      integral_finsetSum _ (fun t ht => hiG t (Finset.mem_range.mp ht)),
      integral_finsetSum _ (fun t ht => hqH t (Finset.mem_range.mp ht)),
      integral_finsetSum _ (fun t ht => hqN t (Finset.mem_range.mp ht)),
      integral_const, probReal_univ, one_smul] at hE
    have hEG :
        (∑ t ∈ Finset.range T, ∫ ω, inner ℝ (g t ω) (x t ω - Wstar) ∂P.toMeasure) =
          ∑ t ∈ Finset.range T, ∫ ω, inner ℝ (h t ω) (x t ω - Wstar) ∂P.toMeasure := by
      apply Finset.sum_congr rfl
      intro t ht
      exact expected_inner_eq p I Wstar hS P ξ hξ T F hRad hM t (Finset.mem_range.mp ht)
    rw [hEG] at hE
    have hsm (t : ℕ) (ht : t < T) :
        (∫ ω, I.f (x t ω) - I.f Wstar ∂P.toMeasure) +
          (∫ ω, Core.weightedQuadratic I.L⁻¹ (h t ω) ∂P.toMeasure) / 2 ≤
            ∫ ω, inner ℝ (h t ω) (x t ω - Wstar) ∂P.toMeasure := by
      have hh := integral_mono ((hgap t ht).fun_add ((hqH t ht).div_const 2)) (hiH t ht)
        (fun ω => weighted_convexity I Wstar hS (x t ω))
      rw [integral_add (hgap t ht) ((hqH t ht).div_const 2), integral_div] at hh
      exact hh
    have hss := Finset.sum_le_sum (fun t (ht : t ∈ Finset.range T) => hsm t (Finset.mem_range.mp ht))
    rw [Finset.sum_add_distrib, ← Finset.sum_div] at hss
    have hNb :
        (∑ t ∈ Finset.range T, ∫ ω, Core.weightedQuadratic I.V⁻¹ (z t ω) ∂P.toMeasure) ≤
          (T : ℝ) * (I.V.trace / (p.M : ℝ)) := by
      have hh := Finset.sum_le_sum (fun t (ht : t ∈ Finset.range T) =>
        batch_noise_weighted p I Wstar hS P ξ hξ hM t (x t)
          (trajectory_adapted p I.g hS.gradientMeasurable ξ t) F hRad.1
          (hRad.2.mono (fun ω hω => (hω t (Finset.mem_range.mp ht)).2)))
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
    have hNb' := div_le_div_of_nonneg_right hNb (by positivity : 0 ≤ 2 * c)
    have hsum :
        (∑ t ∈ Finset.range T, ∫ ω, I.f (x t ω) - I.f Wstar ∂P.toMeasure) ≤
          (T : ℝ) * (I.V.trace / (p.M : ℝ)) / (2 * c) + C := by
      linarith only [hE, hss, hNb']
    have hs2 : s ^ 2 = (T : ℝ) / (p.M : ℝ) := Real.sq_sqrt (div_nonneg hTr.le hMr.le)
    have hnormal :
        (T : ℝ) * (I.V.trace / (p.M : ℝ)) / (2 * c) + C =
          (9 / 4 : ℝ) * p.R ^ 2 * I.L.trace +
            (17 / 8 : ℝ) * p.R * I.V.trace * s + p.k * F ^ 2 / (2 * p.R) := by
      dsimp only [C, a, c]
      have hTm : (T : ℝ) = s ^ 2 * (p.M : ℝ) := ((eq_div_iff hMr.ne').mp hs2).symm
      rw [hTm]
      field_simp [hR.ne', hMr.ne', hs.ne']
      ring
    rw [hnormal] at hsum
    have hL0 := hS.smoothPos.posSemidef.trace_nonneg
    have hV0 := hS.variancePos.posSemidef.trace_nonneg
    have hcoef : (17 / 8 : ℝ) ≤ 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hsignal :
        (9 / 4 : ℝ) * p.R ^ 2 * I.L.trace ≤ 4 * p.R ^ 2 * I.L.trace := by
      nlinarith [mul_nonneg (sq_nonneg p.R) hL0]
    have hnoise :
        (17 / 8 : ℝ) * p.R * I.V.trace * s ≤ 2 * Real.sqrt 2 * p.R * I.V.trace * s := by
      have hh := mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (mul_nonneg hR.le hV0) hs.le)
      nlinarith only [hh]
    have hdamp : p.k * F ^ 2 / (2 * p.R) ≤ 2 * p.k * F ^ 2 / p.R := by
      have hh : 0 ≤ p.k * F ^ 2 / p.R := by positivity
      have he : p.k * F ^ 2 / (2 * p.R) = (p.k * F ^ 2 / p.R) / 2 := by
        rw [div_div, mul_comm p.R 2]
      rw [he]
      have he2 : 2 * p.k * F ^ 2 / p.R = 2 * (p.k * F ^ 2 / p.R) := by ring
      rw [he2]
      linarith only [hh]
    have hsum' :
        (∑ t ∈ Finset.range T, ∫ ω, I.f (x t ω) - I.f Wstar ∂P.toMeasure) ≤
          4 * p.R ^ 2 * I.L.trace + 2 * Real.sqrt 2 * p.R * I.V.trace * s +
            2 * p.k * F ^ 2 / p.R := by
      linarith only [hsum, hsignal, hnoise, hdamp]
    have hden : 0 < Real.sqrt ((p.M : ℝ) * (T : ℝ)) := Real.sqrt_pos.mpr (mul_pos hMr hTr)
    have hprod : s * Real.sqrt ((p.M : ℝ) * (T : ℝ)) = (T : ℝ) := by
      change Real.sqrt ((T : ℝ) / (p.M : ℝ)) * Real.sqrt ((p.M : ℝ) * (T : ℝ)) = _
      rw [Real.sqrt_div hTr.le, Real.sqrt_mul hMr.le, ← mul_assoc,
        div_mul_cancel₀ _ (Real.sqrt_pos.mpr hMr).ne', ← pow_two, Real.sq_sqrt hTr.le]
    have hratio : s / (T : ℝ) = 1 / Real.sqrt ((p.M : ℝ) * (T : ℝ)) := by
      apply (div_eq_div_iff hTr.ne' hden.ne').mpr
      simpa only [one_mul] using hprod
    have hscale := mul_le_mul_of_nonneg_left hsum' (by positivity : 0 ≤ 1 / (T : ℝ))
    calc
      _ ≤ (1 / (T : ℝ)) *
          (4 * p.R ^ 2 * I.L.trace + 2 * Real.sqrt 2 * p.R * I.V.trace * s +
            2 * p.k * F ^ 2 / p.R) := hscale
      _ = 4 * p.R ^ 2 * I.L.trace / (T : ℝ) +
          (2 * Real.sqrt 2 * p.R * I.V.trace) * (s / (T : ℝ)) +
          2 * p.k * F ^ 2 / (p.R * (T : ℝ)) := by ring
      _ = _ := by rw [hratio]; ring
  )

lemma raw_rate_nuclear (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (T : ℕ) (hT : 1 ≤ T) (hM : 1 ≤ p.M) (hR : 0 < p.R) (hk : 0 < p.k)
    (F : ℝ) (hRad : Core.RadiusEnvelope p Wstar F I.g ξ P.toMeasure T) :
    (∀ t < T, Integrable
      (fun ω => I.f (Core.point p I.g (fun j => ξ j ω) t) - I.f Wstar) P.toMeasure) ∧
      (1 / (T : ℝ)) *
        (∑ t ∈ Finset.range T,
          ∫ ω, I.f (Core.point p I.g (fun j => ξ j ω) t) - I.f Wstar ∂P.toMeasure) ≤
        4 * p.R ^ 2 * nuclearNorm (ofMatrix I.L) / (T : ℝ) +
          2 * Real.sqrt 2 * p.R * nuclearNorm (ofMatrix I.V) /
            Real.sqrt ((p.M : ℝ) * (T : ℝ)) +
          2 * p.k * F ^ 2 / (p.R * (T : ℝ)) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    simpa only [trace_eq_nuclear I.L hS.smoothPos.posSemidef,
      trace_eq_nuclear I.V hS.variancePos.posSemidef] using
        raw_rate p I Wstar hS P ξ hξ T hT hM hR hk F hRad
  )

lemma execution_accuracy (p : LongTails.Setups.AsgoFixedRadius.Params) (hp : Valid p) (I : Core.Problem p.m p.n)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n)) (hO : Admissible p I O) :
    let A := Core.method (publicInput p)
    let result := fun seed : A.Seed × ((j : ℕ) → O.Seed j) =>
      execute O A (fun _ => p.M * horizon p) seed.1 seed.2
    let law := A.law.toMeasure.prod O.law.toMeasure
    Measurable result ∧ Integrable (fun seed => I.f (result seed) - I.f p.Wstar) law ∧
      (∫ seed, I.f (result seed) - I.f p.Wstar ∂law) ≤ p.delta := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    rcases oracle_conditions p I O hO with
      ⟨hS, hL, hV, decode, hexact, _, hiid, hrad⟩
    rcases hp with ⟨hR, hk, hM, hF, hell, hv, hd⟩
    have hp : Valid p := ⟨hR, hk, hM, hF, hell, hv, hd⟩
    let ξ := fun (j : ℕ) (ω : (k : ℕ) → O.Seed k) => decode j (ω j)
    let x := fun t ω => Core.point (publicInput p) I.g (fun j => ξ j ω) t
    let out := fun ω => output (publicInput p) I.g (fun j => ξ j ω) (horizon p)
    have hT := horizon_positive p
    have hT0 : horizon p ≠ 0 := by omega
    have hx (t : ℕ) : Measurable (x t) :=
      (trajectory_measurable (publicInput p) I.g hS.gradientMeasurable ξ hiid.measurable t).fst
    have hr := raw_rate (publicInput p) I p.Wstar hS O.law ξ hiid
      (horizon p) hT hM hR hk p.F hrad
    have heout : out = fun ω => (1 / (horizon p : ℝ)) •
        ∑ t ∈ Finset.range (horizon p), x t ω := by
      funext ω
      change (if horizon p = 0 then p.W0 else
        (1 / (horizon p : ℝ)) • ∑ t ∈ Finset.range (horizon p), x t ω) = _
      exact ite_eq_right hT0
    have hm : Measurable out := by
      rw [heout]
      exact average_measurable (horizon p) x (fun t _ => hx t)
    have hI : Integrable (fun ω => I.f (out ω) - I.f p.Wstar) O.law.toMeasure := by
      rw [heout]
      exact average_gap_integrable O.law (horizon p) hT I.f
        (objective_continuous I p.Wstar hS) hS.convex p.Wstar hS.minimizer x
        (fun t _ => hx t) hr.1
    have hrawout :
        (∫ ω, I.f (out ω) - I.f p.Wstar ∂O.law.toMeasure) ≤
          4 * p.R ^ 2 * I.L.trace / (horizon p : ℝ) +
            2 * Real.sqrt 2 * p.R * I.V.trace /
              Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) +
            2 * p.k * p.F ^ 2 / (p.R * (horizon p : ℝ)) := by
      rw [heout]
      exact (average_jensen O.law (horizon p) hT I.f
        (objective_continuous I p.Wstar hS) hS.convex p.Wstar hS.minimizer x
        (fun t _ => hx t) hr.1).trans hr.2
    have hfirst :
        4 * p.R ^ 2 * I.L.trace / (horizon p : ℝ) ≤
          4 * p.R ^ 2 * p.ell / (horizon p : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity)) (by positivity)
    have hsecond :
        2 * Real.sqrt 2 * p.R * I.V.trace /
            Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) ≤
          2 * Real.sqrt 2 * p.R * p.v /
            Real.sqrt ((p.M : ℝ) * (horizon p : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by positivity)) (by positivity)
    have hacc : (∫ ω, I.f (out ω) - I.f p.Wstar ∂O.law.toMeasure) ≤ p.delta :=
      hrawout.trans ((add_le_add (add_le_add hfirst hsecond) le_rfl).trans (rate_to_accuracy p hp))
    let A := Core.method (publicInput p)
    let result := fun seed : A.Seed × ((j : ℕ) → O.Seed j) =>
      execute O A (fun _ => p.M * horizon p) seed.1 seed.2
    have he : result = fun seed => out seed.2 := by
      funext seed
      exact execute_correspondence (publicInput p) I O decode hM hexact
        (horizon p) seed.1 seed.2
    change Measurable result ∧
      Integrable (fun seed => I.f (result seed) - I.f p.Wstar)
        (A.law.toMeasure.prod O.law.toMeasure) ∧
      (∫ seed, I.f (result seed) - I.f p.Wstar
        ∂(A.law.toMeasure.prod O.law.toMeasure)) ≤ p.delta
    rw [he]
    refine ⟨hm.comp measurable_snd, hI.comp_snd A.law.toMeasure, ?_⟩
    rw [integral_fun_snd (fun ω => I.f (out ω) - I.f p.Wstar), probReal_univ, one_smul]
    exact hacc
  )

end OracleTemplate.AsgoFixedRadius
