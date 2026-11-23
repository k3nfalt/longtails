import LongTails.Proofs.ThirdOrderLowerParameters
import LongTails.Proofs.ThirdOrderMaskedScaling
import LongTails.Proofs.Execution
import LongTails.TemplateLowerBound
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.ThirdOrderLowerAssembly

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.ThirdOrderMaskedExecution
open LongTails.Proofs.ThirdOrderMaskedScaling LongTails.Proofs.ThirdOrderLowerParameters
open LongTails.Proofs.AbcHardOracle (unif Scale toUnit)
open LongTails.Proofs.AbcLowerMeasure (stream stream_iid)
open LongTails.Setups.HighDimensionalStochasticThirdOrderSmoothNonconvex

noncomputable def chainDim (q : Params) : ℕ := chainLength q - 1

lemma chainDim_succ (q : Params) (hv : spec.valid q) : chainDim q + 1 = chainLength q := by
  have := chainLength_ge q hv
  unfold chainDim; omega

noncomputable def hardOracle (q : Params) (S : Scale) (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => reply S (revealProb q) π q.x0 x ω

lemma hard_admissible (q : Params) (hv : spec.valid q) (π : Fin (chainDim q + 1) ↪ Fin q.d) :
    spec.admissible q (objective (scaleOf q hv.1 hv.2.2.2.2.1) π q.x0)
      (hardOracle q (scaleOf q hv.1 hv.2.2.2.2.1) π) := by
  have hL₁ := hv.1
  have hL₂ := hv.2.1
  have hL₃ := hv.2.2.1
  have hε := hv.2.2.2.2.1
  have hv' : spec.valid q := hv
  set S := scaleOf q hv.1 hv.2.2.2.2.1
  have hn1 := chainDim_succ q hv'
  have hratio : S.a / S.lam = 5 * q.ε := amplitude_ratio q hL₁ hε
  have hq0 := revealProb_pos q hε
  have hq1 := revealProb_le q hε
  refine ⟨fun x ω => reply S (revealProb q) π q.x0 x ω,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only [toGeneral]
  · exact objective_smooth S π q.x0
  · intro x y
    exact (objective_gradient_lipschitz S π q.x0 x y).trans
      (mul_le_mul_of_nonneg_right (smooth_first q hL₁ hε) (norm_nonneg _))
  · intro x y
    exact (objective_hessian_lipschitz S π q.x0 x y).trans
      (mul_le_mul_of_nonneg_right (smooth_second q hL₁ hL₂ hε) (norm_nonneg _))
  · intro x y
    exact (objective_third_lipschitz S π q.x0 x y).trans
      (mul_le_mul_of_nonneg_right (smooth_third q hL₁ hL₃ hε) (norm_nonneg _))
  · intro x
    refine (objective_gap S π q.x0 x).trans ?_
    have h := amplitude_chain_le q hv'
    have hc : (((chainDim q + 1 : ℕ)) : ℝ) = chainLength q := by rw [hn1]
    rw [hc]
    exact h
  · exact reply_measurable S _ π q.x0
  · intro x
    exact reply_integrable S _ π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact reply_integral S _ hq0 hq1 π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact reply_variance_integrable S _ π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    first
      | rw [reply_variance S _ hq0 hq1]
      | erw [reply_variance S _ hq0 hq1]
    have hsec := secret_norm S π q.x0 x
    rw [hratio] at hsec
    exact variance_le q hε _ (norm_nonneg _) (le_of_le_of_eq hsec (by ring))

lemma trueState_iterate (S : Scale) (p : ℝ) {d n : ℕ} (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) {St : Type*} (query : St → Space d) (update : St → Space d → St)
    (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (reply S p π x0 (query sc.1) (ω sc.2)), sc.2 + 1))^[N]
      (initial, 0)) = (trueState S p π x0 query update initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_hard (q : Params) (S : Scale) (π : Fin (chainDim q + 1) ↪ Fin q.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle q S π) A (fun _ => N) seed ω =
      A.output (trueState S (revealProb q) π q.x0 (fun s => (A.query s).2) A.update
        (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (hardOracle q S π) A N seed ω
    (fun t query => reply S (revealProb q) π q.x0 query.2 (ω t))
    (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (trueState_iterate S (revealProb q) π q.x0
    (fun s => (A.query s).2) A.update (A.initial seed) ω N)

end LongTails.Proofs.ThirdOrderLowerAssembly
