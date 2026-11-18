import LongTails.TemplateLowerBound
import LongTails.Setups.GaussianAdditiveCubeFixedPoint
import LongTails.Proofs.AdditiveFixedPointHardness
import LongTails.Proofs.AdditiveFixedPointLowerExecution

open MeasureTheory
open scoped ENNReal

namespace LongTails.Theorems.AdditiveCubeFixedPointLowerBound

open OracleTemplate LongTails.Setups.AdditiveCubeFixedPoint
open LongTails.Proofs.AdditiveFixedPointFamily LongTails.Proofs.AdditiveFixedPointLowerBudget
open LongTails.Proofs.AdditiveFixedPointHardness LongTails.Proofs.AdditiveFixedPointLowerExecution
open LongTails.Proofs.AdditiveFixedPointBlocks LongTails.Proofs.AdditiveFixedPointProcess
open LongTails.Proofs.AdditiveFixedPointNoise LongTails.Proofs.AdditiveFixedPointTesting

noncomputable def budget : (let S := LongTails.Setups.GaussianAdditiveCubeFixedPoint.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(1 + (p.σ / p.ε) ^ 2 / (2 + Real.log p.d)) * max 1 ((p.R / p.ε) / (1 + Real.log (2 + ((p.R : ℝ) + p.σ) / p.ε))) / 67108864⌋₊

theorem result : NonConvergence LongTails.Setups.GaussianAdditiveCubeFixedPoint.spec budget := by
  intro p hp A ha b hb
  obtain ⟨⟨hd, _, hs, he⟩, hr, hdim⟩ := hp
  obtain ⟨space, hinit, hquery, hupdate, hout⟩ := ha
  let _ : MeasurableSpace A.State := space
  let π := A.law.map A.initial
  let query := fun x => (A.query x).2
  have hq : Measurable query := measurable_snd.comp hquery
  obtain ⟨L, t, hLd, hLr, hh⟩ := hidden_output π hq hout hupdate hd he hs hr hdim (hb 0)
  let hstep : 0 ≤ 8 * p.ε := by positivity
  let T := map (p := p) hstep t (L+1)
  refine ⟨T, oracle T, ⟨admissible (map_lipschitz hstep t _) hd, variance p, rfl⟩, ?_⟩
  dsimp only
  intro hsucc
  have hbudget : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  let pay := test (fun x => guess L 1 (A.output x) 0) (t L)
  have hpay : Measurable pay := test_measurable ((measurable_pi_apply 0).comp
    ((guess_measurable L 1).comp hout)) _
  let st := step query A.update hstep t (L+1)
  have hst : Measurable st.uncurry := step_measurable hq hupdate hstep t _
  change risk π (law (variance p) 0) st pay (b 0) ≤ _ at hh
  rw [risk, stateLaw_integral π _ hst hpay] at hh
  let out := fun z : A.Seed × (ℕ → Point p) => execute (oracle T) A b z.1 z.2
  apply success_requires_recovery _ t he hLd hLr out hsucc
  have heq (z : A.Seed × (ℕ → Point p)) : out z =
      A.output (LongTails.Proofs.HeavyTailedProductProcess.trajectory st (b 0) (A.initial z.1) z.2) := by
    unfold out
    conv_lhs => rw [hbudget]
    exact execute_trajectory (streams p) T A _ _ _
  simp_rw [heq]
  change (∫⁻ z : A.Seed × (ℕ → Point p), pay (LongTails.Proofs.HeavyTailedProductProcess.trajectory st
    (b 0) (A.initial z.1) z.2) ∂(A.law : Measure _).prod (Measure.infinitePi _)) ≤ _
  have hmeas := (LongTails.Proofs.HeavyTailedProductProcess.trajectory_measurable hst (b 0)).comp
    ((hinit.comp measurable_fst).prodMk measurable_snd)
  apply (lintegral_prod _ (hpay.comp hmeas).aemeasurable).le.trans
  change (∫⁻ s, LongTails.Proofs.AdditiveFixedPointProcess.average _ st pay (b 0) (A.initial s) ∂(A.law : Measure _)) ≤ _
  change (∫⁻ s, LongTails.Proofs.AdditiveFixedPointProcess.average _ st pay (b 0) s ∂Measure.map A.initial (A.law : Measure _)) ≤ _ at hh
  rwa [lintegral_map (average_measurable _ hst hpay _) hinit] at hh

end LongTails.Theorems.AdditiveCubeFixedPointLowerBound
