import LongTails.Proofs.CovarianceAcceleratedGuarantee
import LongTails.Proofs.CovarianceAcceleratedMeasurable

open MeasureTheory ProbabilityTheory Convexity OracleTemplate
open LongTails.Proofs.CovarianceAcceleratedParameters

namespace LongTails.Proofs.CovarianceAcceleratedSpecification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tuned_measurable_output {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (x0 : E) {L R σ s j ell : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hs : 0 ≤ s) (hj : 0 < j) (hell : 0 < ell)
    (k T : ℕ) (hk : 1 ≤ k) (hT : 1 ≤ T) (N : ℕ) :
    Measurable (fun ξ : ℕ → Ω => LongTails.Algorithms.CovarianceAccelerated.output
      (LongTails.Algorithms.CovarianceAcceleratedTuned.config x0 L R σ s j ell k T) g ξ N) := by
  let M := 100 * (σ * T + L * R * k)
  let ν := σ ^ 2 * T + j * M ^ 2 * ell / (T : ℝ) ^ 2
  let b := R / (32 * T * Real.sqrt ν)
  let η := 1 / (16 * R * s * T * Real.sqrt T / Real.sqrt ell + 64 * R * M + 64 * b * j * M ^ 2)
  let a := Real.sqrt (b / η)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hM : 0 < M := by dsimp [M]; positivity
  have hν : 0 < ν := tuning_variance_pos hM hj hell hTr
  have hb : 0 < b := by dsimp [b]; positivity
  have hη : 0 < η := (reciprocal_step_bounds hR hs hTr hell hM hb hj).1
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hb hη)
  have hmesh : 0 < R / (T : ℝ) ^ 2 := by positivity
  exact CovarianceAcceleratedMeasurable.measurable_output
    (LongTails.Algorithms.CovarianceAcceleratedGrid.config x0 R (R / (T : ℝ) ^ 2)
      a η (2 * η * L) (η * L * R ^ 2) (k - 1)) hg (show 0 ≤ 2 * η * L by positivity) (show 0 < η * L * R ^ 2 by positivity)
    (div_nonneg hR.le ha.le) (CovarianceAcceleratedGrid.centers_norm_le hR.le hmesh ha) N

lemma stream_guarantee (q : LongTails.Setups.CovarianceSmoothConvex.Params)
    (hv : LongTails.Setups.CovarianceSmoothConvex.spec.valid q)
    {μ : Measure q.Ω} [IsProbabilityMeasure μ] {P : Measure (ℕ → q.Ω)} [IsProbabilityMeasure P]
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k ξ => ξ k) μ P)
    {f : q.E → ℝ} {g : q.E → q.Ω → q.E}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g q.σ q.s)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (xstar : q.E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖q.x0 - xstar‖ ≤ q.R) :
    let J := Real.log ((2 : ℝ) ^ 56 * (1 + q.L * q.R ^ 2 / q.ε + q.R ^ 2 * q.σ ^ 2 / q.ε ^ 2) / q.δ ^ 2)
    let N := ⌈(2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt (q.L * q.R ^ 2 / q.ε) * J + q.R ^ 2 * (q.σ ^ 2 + q.s ^ 2 * Real.log (3 / q.δ)) / q.ε ^ 2)⌉₊
    Measurable (fun ξ => LongTails.Algorithms.CovarianceAcceleratedTuned.output q g ξ N) ∧
      P {ξ | q.ε < f (LongTails.Algorithms.CovarianceAcceleratedTuned.output q g ξ N) - f xstar} ≤ ENNReal.ofReal q.δ := by
  intro J N
  rcases hv with ⟨hL, hR, hσ, hs, hsσ, hε, hδ, hδ1⟩
  by_cases hz : q.R = 0
  · have hx : q.x0 = xstar := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [hz] using hdist) (norm_nonneg _)))
    simp only [LongTails.Algorithms.CovarianceAcceleratedTuned.output, ite_eq_left hz, hx, sub_self]
    refine ⟨measurable_const, ?_⟩
    simp only [show ¬q.ε < 0 by linarith, Set.ofPred_false, measure_empty]
    exact bot_le
  · have hRpos : 0 < q.R := lt_of_le_of_ne hR (Ne.symm hz)
    let ell := Real.log (3 / q.δ)
    let A := q.L * q.R ^ 2 / q.ε
    let S := q.R ^ 2 * q.σ ^ 2 / q.ε ^ 2
    let Q := q.R ^ 2 * (q.σ ^ 2 + q.s ^ 2 * ell) / q.ε ^ 2
    let j := Real.log (54 * (N : ℝ) / q.δ)
    let k := ⌈16 * j⌉₊
    let T := N - k
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hell : 0 < ell := lt_of_lt_of_le (by norm_num) (CovarianceAcceleratedBudget.confidence_log_one hδ hδ1)
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hQS : Q ≤ S * (1 + Real.log (3 / q.δ)) := by
      have hsq : q.s ^ 2 ≤ q.σ ^ 2 := by gcongr
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hell.le)
        (show 0 ≤ q.R ^ 2 / q.ε ^ 2 by positivity)
      dsimp [Q, S]
      change _ ≤ q.R ^ 2 * q.σ ^ 2 / q.ε ^ 2 * (1 + ell)
      ring_nf at hh ⊢
      linarith
    have hcal := CovarianceAcceleratedBudget.budget_calibration hA hS hQ hδ hδ1 hQS
    change 1 ≤ j ∧ Real.log (3 / q.δ) ≤ j ∧ j ≤ k ∧ 1 ≤ k ∧ 1 ≤ T ∧ _ at hcal
    have hmeas := tuned_measurable_output ho.measurable q.x0 hL hRpos hσ hs
      (show 0 < j by linarith [hcal.1]) hell k T hcal.2.2.2.1 hcal.2.2.2.2.1 N
    have hprob := CovarianceAcceleratedGuarantee.calibrated_failure_probability hsamples ho hc hg hlip
      hL hσ hs hsσ hRpos hε hδ hδ1 q.x0 xstar hmin hdist
    have hout (ξ : ℕ → q.Ω) : LongTails.Algorithms.CovarianceAcceleratedTuned.output q g ξ N =
        LongTails.Algorithms.CovarianceAccelerated.output
          (LongTails.Algorithms.CovarianceAcceleratedTuned.config q.x0 q.L q.R q.σ q.s j ell k T) g ξ N := by
      unfold LongTails.Algorithms.CovarianceAcceleratedTuned.output
      rw [ite_eq_right hz]
      rfl
    simp_rw [hout]
    refine ⟨hmeas, ?_⟩
    change P {ξ | q.ε < f (LongTails.Algorithms.CovarianceAccelerated.output
      (LongTails.Algorithms.CovarianceAcceleratedTuned.config q.x0 q.L q.R q.σ q.s j ell k T) g ξ N) - f xstar} ≤
        ENNReal.ofReal q.δ at hprob
    exact hprob

lemma successful_execution (q : LongTails.Setups.CovarianceSmoothConvex.Params)
    (hv : LongTails.Setups.CovarianceSmoothConvex.spec.valid q)
    (f : q.E → ℝ) (O : Oracle q.E q.E)
    (hO : LongTails.Setups.CovarianceSmoothConvex.spec.admissible q f O) :
    let J := Real.log ((2 : ℝ) ^ 56 * (1 + q.L * q.R ^ 2 / q.ε + q.R ^ 2 * q.σ ^ 2 / q.ε ^ 2) / q.δ ^ 2)
    let N := ⌈(2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt (q.L * q.R ^ 2 / q.ε) * J + q.R ^ 2 * (q.σ ^ 2 + q.s ^ 2 * Real.log (3 / q.δ)) / q.ε ^ 2)⌉₊
    let A := LongTails.Algorithms.CovarianceAcceleratedTuned.method q N
    LongTails.Setups.CovarianceSmoothConvex.spec.successful q f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  intro J N A
  rcases hO with ⟨g, μ, P, hsamples, rfl, hc, hg, hlip, ⟨xstar, hmin, hdist⟩, ho⟩
  have hstream := stream_guarantee q hv hsamples ho hc hg hlip xstar hmin hdist
  change Measurable (fun ξ => LongTails.Algorithms.CovarianceAcceleratedTuned.output q g ξ N) ∧
    (P : Measure _) {ξ | q.ε < f (LongTails.Algorithms.CovarianceAcceleratedTuned.output q g ξ N) - f xstar} ≤
      ENNReal.ofReal q.δ at hstream
  have heq :
      (fun seed : A.Seed × (ℕ → q.Ω) => execute
        { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        A (fun _ => N) seed.1 seed.2) =
      fun seed => LongTails.Algorithms.CovarianceAcceleratedTuned.output q g seed.2 N := by
    funext seed
    rcases seed with ⟨⟨⟩, ξ⟩
    by_cases hz : q.R = 0
    · simp only [LongTails.Algorithms.CovarianceAcceleratedTuned.output, ite_eq_left hz]
      unfold execute
      erw [executeWithTrace_eq_executeIndexedState]
      simp only [A, LongTails.Algorithms.CovarianceAcceleratedTuned.method, ite_eq_left hz]
    · let cfg := LongTails.Algorithms.CovarianceAcceleratedTuned.config q.x0 q.L q.R q.σ q.s
        (LongTails.Algorithms.CovarianceAcceleratedTuned.horizonLog N q.δ)
        (LongTails.Algorithms.CovarianceAcceleratedTuned.confidence q.δ)
        (LongTails.Algorithms.CovarianceAcceleratedTuned.warmup N q.δ)
        (LongTails.Algorithms.CovarianceAcceleratedTuned.steps N q.δ)
      let O' : Oracle q.E q.E :=
        { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      have hstate (n : ℕ) : (executeIndexedState O' A () ξ n).1 =
          LongTails.Algorithms.CovarianceAccelerated.trajectory cfg g ξ n := by
        induction n with
        | zero => rfl
        | succ n ih =>
          simp only [executeIndexedState, LongTails.Algorithms.CovarianceAccelerated.trajectory]
          change LongTails.Algorithms.CovarianceAccelerated.advance cfg
            (executeIndexedState O' A () ξ n).1
            (g (LongTails.Algorithms.CovarianceAccelerated.query cfg
              (executeIndexedState O' A () ξ n).1)
              (ξ (executeIndexedState O' A () ξ n).2.length)) = _
          erw [executeIndexedState_length, ih]
      simp only [LongTails.Algorithms.CovarianceAcceleratedTuned.output, ite_eq_right hz]
      unfold execute
      erw [executeWithTrace_eq_executeIndexedState]
      change (if q.R = 0 then q.x0 else (executeIndexedState O' A () ξ N).1.2.1) = _
      rw [ite_eq_right hz]
      exact congrArg (fun state : LongTails.Algorithms.CovarianceAccelerated.State cfg => state.2.1) (hstate N)
  change Measurable _ ∧ ∃ u, IsMinOn f Set.univ u ∧ _
  rw [heq]
  refine ⟨hstream.1.comp measurable_snd, xstar, hmin, ?_⟩
  let B : Set (ℕ → q.Ω) := {ξ | q.ε < f (LongTails.Algorithms.CovarianceAcceleratedTuned.output q g ξ N) - f xstar}
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hB : MeasurableSet B := measurableSet_lt measurable_const ((hfm.comp hstream.1).sub measurable_const)
  change ((Measure.dirac ()).prod (P : Measure _)) (Prod.snd ⁻¹' B) ≤ ENNReal.ofReal q.δ
  rw [(measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure _))).measure_preimage hB.nullMeasurableSet]
  exact hstream.2

lemma tuned_execute_calls (q : LongTails.Setups.CovarianceSmoothConvex.Params)
    (O : Oracle q.E q.E) (N : ℕ) (ξ : (k : ℕ) → O.Seed k) :
    (executeWithTrace O (LongTails.Algorithms.CovarianceAcceleratedTuned.method q N)
      (fun _ => N) () ξ).2.length = N := by
  erw [executeWithTrace_eq_executeIndexedState]
  exact executeIndexedState_length _ _ _ _ _

end LongTails.Proofs.CovarianceAcceleratedSpecification
