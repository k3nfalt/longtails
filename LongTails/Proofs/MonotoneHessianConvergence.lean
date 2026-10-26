import LongTails.Proofs.MonotoneHessianFailure
import LongTails.Proofs.MonotoneHessianExecution

namespace LongTails.Proofs.MonotoneHessianConvergence

open OracleTemplate MeasureTheory LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant LongTails.Proofs.MonotoneHessianTransitions
open LongTails.Proofs.MonotoneHessianFailure
open scoped RealInnerProductSpace

variable (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (_root_.gradient f x)) x)
    (hg : ∀ x, HasFDerivAt (_root_.gradient f) (fderiv ℝ (_root_.gradient f) x) x)
    (hA : ∀ x, (fderiv ℝ (_root_.gradient f) x).toLinearMap.IsSymmetric)
    (hLip : ∀ x y, ‖fderiv ℝ (_root_.gradient f) x - fderiv ℝ (_root_.gradient f) y‖ ≤ p.H * ‖x - y‖)
    (O : Fin 2 × p.E → Reply p.E)
    (hO : ∀ x, O (0, x) = .inl (f x, _root_.gradient f x))
    (hH : ∀ x, O (1, x) = .inr (fderiv ℝ (_root_.gradient f) x))

include hp hf hg hA hLip hO hH

lemma seed_probability (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) :
    ENNReal.ofReal (1 - p.ρ) ≤ (Measure.pi fun _ : Fin (stages p) => blockLaw p)
      {signs | ‖_root_.gradient f ((LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O)‖ ≤ p.ε ∧
        curvatureGood p f ((LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O)} := by
  classical
  let initial : LongTails.Algorithms.MonotoneHessianReuse.State p :=
    ⟨⟨p.x0, f p.x0, _root_.gradient f p.x0⟩, none, false⟩
  let advance := fun st signs => (LongTails.Algorithms.MonotoneHessianReuse.step p st signs).eval O
  let P := Measure.pi fun _ : Fin (stages p) => blockLaw p
  let bad := {signs | MonotoneHessianProbability.badRun advance (badStep p f O) (stages p) initial signs}
  let good := {signs | ‖_root_.gradient f ((LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O)‖ ≤ p.ε ∧
    curvatureGood p f ((LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O)}
  have hi : StateValid p f (fderiv ℝ (_root_.gradient f)) initial :=
    ⟨⟨rfl, rfl⟩, fun snap hs => by simp [initial] at hs⟩
  have hvalid (st : LongTails.Algorithms.MonotoneHessianReuse.State p)
      (hi : StateValid p f (fderiv ℝ (_root_.gradient f)) st) (signs : Block p) :
      StateValid p f (fderiv ℝ (_root_.gradient f)) (advance st signs) := by
    by_cases hd : st.done = true
    · simpa only [advance, done_step p O st signs hd] using hi
    · exact (MonotoneHessianProgress.step_progress p hp f hf hg hA hLip O hO hH st
        (Bool.eq_false_iff.mpr hd) hi signs).1
  have hη : 0 ≤ p.ρ / stages p := div_nonneg hp.2.2.2.2.1.le (Nat.cast_nonneg _)
  have hbad := MonotoneHessianProbability.adaptive_failure (blockLaw p) advance (badStep p f O)
    (StateValid p f (fderiv ℝ (_root_.gradient f))) hvalid hη
    (fun st hi => step_failure_bound p hp f hf hg hA hLip O hO hH st hi) (stages p) initial hi
  have hK : (stages p : ℝ) ≠ 0 := by unfold stages; positivity
  have hbound : P bad ≤ ENNReal.ofReal p.ρ := by
    simpa only [mul_div_cancel₀ _ hK] using hbad
  have hsubset : badᶜ ⊆ good := by
    intro signs hs
    have ht := MonotoneHessianIteration.termination p hp f hf hg hA hLip O hO hH hgap signs
    have hc := loop_good p f O (stages p) initial signs
      (fun hh => by simp [initial] at hh) hs ht.1
    have he : (LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O =
        ((LongTails.Algorithms.MonotoneHessianReuse.loop p (stages p) initial signs).eval O).point.x := by
      simp only [LongTails.Algorithms.MonotoneHessianReuse.plan, QueryPlan.eval, hO, readPoint, QueryPlan.eval_map]
      rfl
    change _ ∧ _
    rw [he]
    exact ⟨ht.2, hc⟩
  have hbReal : P.real bad ≤ p.ρ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [measureReal_def, ENNReal.toReal_ofReal hp.2.2.2.2.1.le] using hh
  have hcomp : P.real badᶜ = 1 - P.real bad := by
    rw [measureReal_compl (Set.toFinite bad).measurableSet, probReal_univ]
  have hm := measureReal_mono (μ := P) hsubset
  have hh : 1 - p.ρ ≤ P.real good := by linarith
  have hout := ENNReal.ofReal_le_ofReal hh
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P good)] at hout
  exact hout

lemma execution_probability (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (Or : Oracle p.E (Reply p.E) 2) (b : Fin 2 → ℕ)
    (hanswer : ∀ history q seed, Or.answer history q seed = O q)
    (hcount : ∀ signs i, LongTails.Proofs.EnergyHessianExecution.counts O
      (LongTails.Algorithms.MonotoneHessianReuse.plan p signs) i ≤ b i) :
    spec.successful p f
      (fun seed : (LongTails.Algorithms.MonotoneHessianReuse.algorithm p).Seed × ((k : ℕ) → Or.Seed k) =>
        execute Or (LongTails.Algorithms.MonotoneHessianReuse.algorithm p) b seed.1 seed.2)
      ⟨((LongTails.Algorithms.MonotoneHessianReuse.algorithm p).law : Measure _).prod
        (Or.law : Measure _), inferInstance⟩ := by
  let good := {signs : (LongTails.Algorithms.MonotoneHessianReuse.algorithm p).Seed |
    ‖_root_.gradient f ((LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O)‖ ≤ p.ε ∧
      curvatureGood p f ((LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O)}
  have he (signs : (LongTails.Algorithms.MonotoneHessianReuse.algorithm p).Seed) (ξ : (k : ℕ) → Or.Seed k) :
      execute Or (LongTails.Algorithms.MonotoneHessianReuse.algorithm p) b signs ξ =
        (LongTails.Algorithms.MonotoneHessianReuse.plan p signs).eval O :=
    MonotoneHessianExecution.execute_of_counts p O Or b hanswer signs (hcount signs) ξ
  change ENNReal.ofReal (1 - p.ρ) ≤
    (((LongTails.Algorithms.MonotoneHessianReuse.algorithm p).law : Measure _).prod (Or.law : Measure _))
      {seed | ‖_root_.gradient f (execute Or (LongTails.Algorithms.MonotoneHessianReuse.algorithm p) b seed.1 seed.2)‖ ≤ p.ε ∧
        curvatureGood p f (execute Or (LongTails.Algorithms.MonotoneHessianReuse.algorithm p) b seed.1 seed.2)}
  have hset : {seed : (LongTails.Algorithms.MonotoneHessianReuse.algorithm p).Seed × ((k : ℕ) → Or.Seed k) |
      ‖_root_.gradient f (execute Or (LongTails.Algorithms.MonotoneHessianReuse.algorithm p) b seed.1 seed.2)‖ ≤ p.ε ∧
        curvatureGood p f (execute Or (LongTails.Algorithms.MonotoneHessianReuse.algorithm p) b seed.1 seed.2)} =
        good ×ˢ Set.univ := by
    ext seed
    simp only [Set.mem_ofPred_eq, he, Set.mem_prod, Set.mem_univ, and_true, good]
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  exact seed_probability p hp f hf hg hA hLip O hO hH hgap

end LongTails.Proofs.MonotoneHessianConvergence
