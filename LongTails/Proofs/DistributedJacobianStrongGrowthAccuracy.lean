import LongTails.Proofs.DistributedJacobianStrongGrowthParameters
import LongTails.Proofs.DistributedJacobianStrongGrowthWarmStart
import LongTails.Proofs.DistributedJacobianStrongGrowthGlobal

namespace LongTails.Proofs.DistributedJacobianStrongGrowthAccuracy

open MeasureTheory
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open DistributedJacobianStrongGrowthParameters

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma tuned_warm_failure (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (T : ℕ) (hεR : p.ε < p.R) :
    (S.law : Measure S.Seed)
      {ω | 3 * radius p T / 8 <
        ‖warmCenter p (warmCount p T) (warmWidth p T) (warmSpacing p T) g
          (fun j => S.sample j ω) - I.solution‖} ≤
      ENNReal.ofReal (p.ε ^ 2 / (8 * p.R ^ 2)) := by
  have hc := warm_confidence p hp T hεR
  have hs := warm_precision p hp T
  have hr := (radius_properties p hp T).1
  have hd : 0 < (p.d : ℝ) := Nat.cast_pos.mpr hp.1
  have hsqrt : 0 < Real.sqrt (p.d : ℝ) := Real.sqrt_pos.mpr hd
  have hb := DistributedJacobianStrongGrowthWarmStart.warmCenter_failure_probability
    p hp I hI g S hg (warmCount p T) (warmWidth p T) (warmSpacing p T)
    (radius p T / (4 * Real.sqrt p.d))
    (Real.exp (-(2 / (p.n : ℝ)) * Real.log (1 / (p.ε ^ 2 / (8 * p.R ^ 2)))) / 4)
    hs.1 (by positivity) hc.1 hc.2.1 hs.2 hc.2.2.2
  rw [warm_accuracy_radius p hp T, hc.2.2.1] at hb
  exact hb

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma tuned_output_accuracy (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (T : ℕ) (hεR : p.ε < p.R)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * growth p ^ T ≤ (p.n : ℝ)) :
    Measurable (fun ω => output p T g (fun j => S.sample j ω)) ∧
      Integrable (fun ω => ‖output p T g (fun j => S.sample j ω) - I.solution‖ ^ 2)
        (S.law : Measure S.Seed) ∧
      (∫ ω, ‖output p T g (fun j => S.sample j ω) - I.solution‖ ^ 2
        ∂(S.law : Measure S.Seed)) ≤ p.ε ^ 2 := by
  classical
  have hR : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hΩ : Nonempty p.Ω := hp.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨center, hm, hcR, hfactor⟩ := DistributedJacobianStrongGrowthWarmProcess.warmCenter_factor
    p (warmCount p T) (warmWidth p T) (warmSpacing p T) g hg.1
    (Classical.choice hΩ) hR.le
  let E := {z | ‖center z - I.solution‖ ≤ 3 * radius p T / 8}
  have hE : MeasurableSet E := measurableSet_le ((hm.sub_const I.solution).norm) measurable_const
  have hr := radius_properties p hp T
  have hs := refinement_precision p hp T hT hTκ
  have hb := DistributedJacobianStrongGrowthGlobal.random_warm_center_bound p hp I hI g S hg
    (warmCount p T) T hr.1 hT hTκ hn hr.2.2.1
    (refinementWidth p T) (refinementSpacing p T) hs.1 hs.2 center hm hcR E hE
    (fun _ hz => hz) (refinementCount p T)
  have hout : (fun ω => LongTails.Algorithms.DistributedLocalExtragradientProcess.refineRun p (warmCount p T) T
      (clipRadius p T) (refinementWidth p T) (refinementSpacing p T) (radius p T) g
      (center (fun i => S.sample i.val ω)) (fun j => S.sample j ω) (refinementCount p T)) =
      (fun ω => output p T g (fun j => S.sample j ω)) := by
    funext ω
    rw [hfactor (fun j => S.sample j ω)]
    rfl
  dsimp only at hb
  simp only [clipRadius, growth] at hout
  have houtpoint (ω : S.Seed) := congrFun hout ω
  simp only [houtpoint] at hb
  refine ⟨hb.1, hb.2.1, hb.2.2.trans ?_⟩
  have hbad := tuned_warm_failure p hp I hI g S hg T hεR
  have hevent : {ω | (fun i : Fin (p.n * warmCount p T) => S.sample i.val ω) ∉ E} =
      {ω | 3 * radius p T / 8 < ‖warmCenter p (warmCount p T) (warmWidth p T)
        (warmSpacing p T) g (fun j => S.sample j ω) - I.solution‖} := by
    ext ω
    simp only [E, Set.mem_ofPred_eq, not_le]
    rw [hfactor (fun j => S.sample j ω)]
  have hprob : (S.law : Measure S.Seed).real
      {ω | (fun i : Fin (p.n * warmCount p T) => S.sample i.val ω) ∉ E} ≤
        p.ε ^ 2 / (8 * p.R ^ 2) := by
    rw [hevent, measureReal_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hterms := refinement_accuracy_terms p hp T hT hTκ
  have hnoise := mul_le_mul_of_nonneg_left hprob (by positivity : 0 ≤ 4 * p.R ^ 2)
  have hcancel : 4 * p.R ^ 2 * (p.ε ^ 2 / (8 * p.R ^ 2)) = p.ε ^ 2 / 2 := by
    field_simp
    ring
  rw [hcancel] at hnoise
  change (1 - contraction p T / 2) ^ refinementCount p T * radius p T ^ 2 +
    (2 / contraction p T) * (1 + 2 / contraction p T) *
      (Real.sqrt p.d * refinementSpacing p T) ^ 2 + _ ≤ _
  nlinarith [hterms.1, hterms.2, sq_nonneg p.ε]

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma baseline_output_accuracy (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) :
    Measurable (fun ω => baselineOutput p g (fun j => S.sample j ω)) ∧
      Integrable (fun ω => ‖baselineOutput p g (fun j => S.sample j ω) - I.solution‖ ^ 2)
        (S.law : Measure S.Seed) ∧
      (∫ ω, ‖baselineOutput p g (fun j => S.sample j ω) - I.solution‖ ^ 2
        ∂(S.law : Measure S.Seed)) ≤ p.ε ^ 2 := by
  have hb := DistributedJacobianStrongGrowthWarmStart.warm_worker_bound p hp I hI g S hg
    (baselineCount p) p.root
  have hm := (LocalNonlinearExtragradientSampling.measurable_warmRun
    (p.μ / (p.ρ * p.L ^ 2)) (g p.root) p.x0 (hg.1 p.root) (baselineCount p)).comp
    (Measurable.of_eval fun j => S.iid.measurable (p.n * j + p.root.val))
  exact ⟨hm, hb.1, hb.2.trans (baseline_accuracy_term p hp)⟩

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma selected_output_accuracy (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) :
    Measurable (fun ω => selectedOutput p g (fun j => S.sample j ω)) ∧
      Integrable (fun ω => ‖selectedOutput p g (fun j => S.sample j ω) - I.solution‖ ^ 2)
        (S.law : Measure S.Seed) ∧
      (∫ ω, ‖selectedOutput p g (fun j => S.sample j ω) - I.solution‖ ^ 2
        ∂(S.law : Measure S.Seed)) ≤ p.ε ^ 2 := by
  by_cases hlarge : p.R ≤ p.ε
  · simp only [selectedOutput, ite_eq_left hlarge]
    refine ⟨measurable_const, integrable_const _, ?_⟩
    have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
    have hd : ‖p.x0 - I.solution‖ ≤ p.ε := hI.2.2.2.2.1.trans hlarge
    simpa using (sq_le_sq₀ (norm_nonneg _) hε.le).mpr hd
  · by_cases hn : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)
    · simp only [selectedOutput, ite_eq_right hlarge, ite_eq_left hn]
      have hT := localDepth_properties p hp hn
      exact tuned_output_accuracy p hp I hI g S hg (localDepth p) (lt_of_not_ge hlarge)
        hT.1 hT.2.1 hT.2.2
    · simp only [selectedOutput, ite_eq_right hlarge, ite_eq_right hn]
      exact baseline_output_accuracy p hp I hI g S hg

end LongTails.Proofs.DistributedJacobianStrongGrowthAccuracy
