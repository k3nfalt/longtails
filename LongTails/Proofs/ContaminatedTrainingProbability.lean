import LongTails.Proofs.ContaminatedParallelFailures
import LongTails.Proofs.ContaminatedTreeMass

namespace LongTails.Proofs.ContaminatedTrainingProbability

open MeasureTheory
open scoped Classical
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (iterations height resolution)
open ContaminatedParallelHistory ContaminatedParallelSampling ContaminatedParallelFailures
open ContaminatedTreeProbability

variable {p : Params}

lemma precision_pos (p : Params) (op : Operation) : 1 ≤ op.precision p := by
  cases op <;> simp only [Operation.precision,levelConfidence,confidence] <;> omega

lemma unweighted (D : Data p) (o : ℕ → Operation) (t : ℕ) :
    (D.P : Measure _).real (bad D o t) ≤ 2 * Real.exp (-((o t).precision p:ℝ)) := by
  have h := weighted_failure D o t (precision_pos _ _) (fun _ => 1) measurable_const
    (integrable_const _) (fun _ => zero_le_one)
  change (∫ s, (bad D o t).indicator (fun _ => (1:ℝ)) s ∂(D.P : Measure _)) ≤ _ at h
  simpa only [integral_indicator (past_le p _ _ (bad_measurable D o t)),
    setIntegral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,integral_const,probReal_univ,one_smul,one_mul] using h

noncomputable def lvl (p : Params) (t : ℕ) := (levels (height (network p)))[t]?.getD 0

lemma training_tail (D : Data p) :
    (D.P : Measure _).real {s | 1 ≤ mass (fun t => weight p (lvl p t)) (bad D (trainOp p))
      (levels (height (network p))).length s} ≤ Real.exp (-(confidence p:ℝ)) := by
  let N := (levels (height (network p))).length
  let K := (iterations (network p):ℝ)
  let q := (confidence p:ℝ)
  let w (i : ℕ) := weight p (lvl p i)
  let b (i : ℕ) := bad D (trainOp p) i
  let r (i : ℕ) := 2 * Real.exp (-(levelConfidence p (lvl p i):ℝ))
  let θ := 2*q
  have hK : 0 < K := by dsimp [K,iterations]; positivity
  have hq : 0 < q := by dsimp [q,confidence]; positivity
  have hθ : 0 < θ := mul_pos (by norm_num) hq
  have hb (i : ℕ) : MeasurableSet (b i) := past_le p _ _ (bad_measurable D (trainOp p) i)
  have hprev (i : ℕ) : Measurable[past p (used p (trainOp p) i)] (mass w b i) := by
    let _ := past p (used p (trainOp p) i)
    exact mass_measurable w b i (fun j hj => past_mono p (used_mono p (trainOp p) hj) _ (bad_measurable D (trainOp p) j))
  have hcond (i : ℕ) : (∫ s, if s ∈ b i then Real.exp (θ * mass w b i s) else 0 ∂(D.P : Measure _)) ≤
      (∫ s, Real.exp (θ * mass w b i s) ∂(D.P : Measure _))*r i := by
    have hm : Measurable[past p (used p (trainOp p) i)] (fun s => Real.exp (θ * mass w b i s)) := by
      let _ := past p (used p (trainOp p) i)
      exact ((hprev i).const_mul θ).exp
    apply weighted_failure D _ i (precision_pos _ _) _ hm _ (fun _ => (Real.exp_pos _).le)
    apply Integrable.of_bound (hm.mono (past_le p _) le_rfl).aestronglyMeasurable (Real.exp (θ*i))
    apply Filter.Eventually.of_forall
    intro s
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ.le
    calc
      mass w b i s ≤ ∑ _j ∈ Finset.range i, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        split <;> first | exact min_le_left _ _ | exact zero_le_one
      _ = _ := by simp
  have hh := mass_tail (D.P : Measure _) w b r N hθ (fun i _ => weight_nonneg p _)
    (fun i _ => hb i) (fun i _ => precision_gain p (lvl p i)) (fun i _ => hcond i)
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hN : (N:ℝ) ≤ 2*K := by
    dsimp only [N,K,iterations]
    exact_mod_cast ContaminatedCalendarBudget.levels_length (height (network p))
  have hmul := mul_le_mul_of_nonneg_right hN (show 0 ≤ q/(4*K) by positivity)
  change (N:ℝ) * (q/(4*K)) - 2*q ≤ -q
  have he : (2*K)*(q/(4*K)) = q/2 := by field_simp; ring
  linarith only [hmul,he,hq]

end LongTails.Proofs.ContaminatedTrainingProbability
