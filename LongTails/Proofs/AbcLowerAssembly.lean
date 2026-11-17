import LongTails.Proofs.AbcLowerParameters
import LongTails.Proofs.AbcHardContinuity
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.AbcLowerAssembly

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution LongTails.Proofs.AbcHardCounting
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcHardContinuity LongTails.Proofs.FiniteSumNondualLowerAveraging
open LongTails.Setups.HighDimensionalAbcNoiseNonconvex

noncomputable def chainDim (q : Params) : ℕ := chainLength q - 1

lemma chainDim_succ (q : Params) (hv : spec.valid q) : chainDim q + 1 = chainLength q := by
  have := chainLength_ge q hv
  unfold chainDim; omega

noncomputable def hardOracle (q : Params) (S : Scale) (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => reply S (revealProb q (chainDim q)) π q.x0 x ω

lemma hard_admissible (q : Params) (hv : spec.valid q) (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    spec.admissible q (objective (scaleOf q hv.1 hv.2.2.2.2.1) π q.x0)
      (hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π) := by
  have hL := hv.1
  have hA := hv.2.1
  have hB := hv.2.2.1
  have hC := hv.2.2.2.1
  have hε := hv.2.2.2.2.1
  have hv' : spec.valid q := hv
  set S := scaleOf q hv.1 hv.2.2.2.2.1
  have hn1 := chainDim_succ q hv'
  have hratio : S.a / S.lam = 60 * q.ε := amplitude_ratio q hL hε
  have hsmooth : 1024 * S.a / S.lam ^ 2 = q.L := smoothness_eq q hL hε
  let fstar : ℝ := S.a * (-3 * (((chainDim q) : ℝ) + 1))
  refine ⟨fun x ω => reply S (revealProb q (chainDim q)) π q.x0 x ω,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, fstar, stream_iid, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only [toGeneral]
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact objective_hasGradientAt S π q.x0 x
  · intro x y
    first | simp only [objective_gradient] | erw [objective_gradient, objective_gradient]
    rw [← hsmooth]
    exact objGrad_lipschitz S π q.x0 x y
  · intro x
    exact mul_le_mul_of_nonneg_left (hardValue_lower π _) S.ha.le
  · intro η hη
    refine ⟨q.x0 + S.lam • hardMinimizer π, ?_⟩
    have ht : toUnit S q.x0 (q.x0 + S.lam • hardMinimizer π) = hardMinimizer π := by
      simp only [toUnit, add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ S.hlam.ne',
        one_smul]
    simp only [objective, ht, hardValue_minimizer, fstar]
    linarith
  · have ht : toUnit S q.x0 q.x0 = 0 := by simp [toUnit]
    simp only [objective, ht, hardValue_zero, fstar]
    have h := amplitude_chain_le q hv'
    have hc : (((chainDim q) : ℝ) + 1) = chainLength q := by rw [← hn1]; push_cast; ring
    rw [hc]
    have : S.a = amplitude q := rfl
    rw [this]
    nlinarith [S.ha]
  · exact reply_measurable S _ π q.x0
  · intro x
    exact reply_integrable S _ π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact reply_integral S _ (revealProb_pos q hε (chainDim q)) (revealProb_le q hε (chainDim q)) π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact reply_variance_integrable S _ π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    first
      | rw [reply_variance S _ (revealProb_pos q hε (chainDim q)) (revealProb_le q hε (chainDim q))]
      | erw [reply_variance S _ (revealProb_pos q hε (chainDim q)) (revealProb_le q hε (chainDim q))]
    set w := toUnit S q.x0 x
    set m := stage (sel π w)
    have hsec := secret_norm S π q.x0 x
    rw [hratio] at hsec
    by_cases hfull : (chainDim q) + 1 ≤ m
    · rw [objGrad, knownPart, knownGrad_full π m w hfull, sub_self, norm_zero]
      have h1 : 0 ≤ objective S π q.x0 x - fstar := by
        simp only [objective, fstar]
        nlinarith [hardValue_lower π w, S.ha]
      nlinarith [mul_nonneg hA h1, mul_nonneg hB (sq_nonneg ‖objGrad S π q.x0 x‖), hC]
    · push Not at hfull
      have hlev : 0 ≤ levelBudget q (chainDim q) m := by
        unfold levelBudget
        have : (m : ℝ) ≤ (chainDim q) := by exact_mod_cast (by omega : m ≤ (chainDim q))
        have ha : 0 ≤ amplitude q := S.ha.le
        nlinarith [mul_nonneg (mul_nonneg hA ha) (sub_nonneg.mpr this)]
      have hvar := variance_le_budget q hε (chainDim q) m _ (norm_nonneg _)
        (le_of_le_of_eq hsec (by ring)) hlev
      refine hvar.trans ?_
      unfold levelBudget
      have hgap := hardValue_gap π m w (fun i hi => small_of_stage _ i hi)
      have hgrad := hardGrad_lower π w (last_small_of_stage _ (by omega))
      have hgo : 3 * q.ε ≤ ‖objGrad S π q.x0 x‖ := by
        rw [objGrad, norm_smul, Real.norm_of_nonneg (by have := S.ha; have := S.hlam; positivity),
          hratio]
        nlinarith
      have hf : 6 * q.A * amplitude q * (((chainDim q) : ℝ) - m) ≤ 2 * q.A * (objective S π q.x0 x - fstar) := by
        simp only [objective, fstar]
        have : amplitude q = S.a := rfl
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hgap (mul_nonneg hA S.ha.le)]
      have hg2 : 9 * q.B * q.ε ^ 2 ≤ q.B * ‖objGrad S π q.x0 x‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hgo 2
        nlinarith
      exact add_le_add (add_le_add hf hg2) le_rfl

lemma trueState_iterate (S : Scale) (qf : ℕ → ℝ) {d n : ℕ} (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) {St : Type*} (query : St → Space d) (update : St → Space d → St)
    (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (reply S qf π x0 (query sc.1) (ω sc.2)), sc.2 + 1))^[N]
      (initial, 0)) = (trueState S qf π x0 query update initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_hard (q : Params) (S : Scale) (π : Fin (chainDim q + 1) ↪ Fin q.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle q S π) A (fun _ => N) seed ω =
      A.output (trueState S (revealProb q (chainDim q)) π q.x0 (fun s => (A.query s).2) A.update
        (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (hardOracle q S π) A N seed ω
    (fun t query => reply S (revealProb q (chainDim q)) π q.x0 query.2 (ω t))
    (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (trueState_iterate S (revealProb q (chainDim q)) π q.x0
    (fun s => (A.query s).2) A.update (A.initial seed) ω N)

end LongTails.Proofs.AbcLowerAssembly
