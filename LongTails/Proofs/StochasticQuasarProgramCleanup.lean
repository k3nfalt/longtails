import LongTails.Proofs.StochasticQuasarProgramMoments
import LongTails.Proofs.StochasticQuasarCleanupConfidence
import LongTails.Proofs.StochasticQuasarCleanupExecution

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma seeded_failure_composition {S V Ω : Type*} [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Ω]
    (μ : Measure Ω) (ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {cost : S → ℕ} (hc : Measurable cost) (X : S × (ℕ → Ω) → V) (hX : Measurable X)
    (hdep : ∀ s ξ ζ, (∀ i, i < cost s → ξ i = ζ i) → X (s, ξ) = X (s, ζ))
    {rough : Set V} (hr : MeasurableSet rough) {bad : Set (V × (ℕ → Ω))} (hb : MeasurableSet bad)
    {ε₀ ε₁ : ℝ≥0∞}
    (hrough : (ν.prod (Measure.infinitePi fun _ : ℕ => μ)) {w | X w ∈ rough} ≤ ε₀)
    (hconditional : ∀ v, v ∉ rough → (Measure.infinitePi fun _ : ℕ => μ) {ξ | (v, ξ) ∈ bad} ≤ ε₁) :
    (ν.prod (Measure.infinitePi fun _ : ℕ => μ)) {w | (X w, fun i => w.2 (cost w.1 + i)) ∈ bad} ≤ ε₀ + ε₁ := by
  let F : (S × V) × (ℕ → Ω) → ℝ≥0∞ := fun w => bad.indicator 1 (w.1.2, w.2)
  have hF : Measurable F := (measurable_const.indicator hb).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have he := LongTails.Proofs.StochasticEnvelopeFreshness.seed_prefix_tail_lintegral μ ν hc X hX hdep F hF
  have hleft : MeasurableSet {w : S × (ℕ → Ω) | (X w, fun i => w.2 (cost w.1 + i)) ∈ bad} :=
    hb.preimage (hX.prodMk (LongTails.Proofs.StochasticEnvelopeFreshness.measurable_seed_shift hc))
  have hl : (∫⁻ w, F ((w.1, X w), fun i => w.2 (cost w.1 + i))
      ∂ν.prod (Measure.infinitePi fun _ : ℕ => μ)) =
      (ν.prod (Measure.infinitePi fun _ : ℕ => μ)) {w | (X w, fun i => w.2 (cost w.1 + i)) ∈ bad} :=
    lintegral_indicator_one hleft
  rw [← hl, he]
  let R : Set (S × (ℕ → Ω)) := {w | X w ∈ rough}
  have hR : MeasurableSet R := hr.preimage hX
  calc
    _ ≤ ∫⁻ w, R.indicator (1 : (S × (ℕ → Ω)) → ℝ≥0∞) w + ε₁
        ∂ν.prod (Measure.infinitePi fun _ : ℕ => μ) := by
      apply lintegral_mono
      intro w
      change (∫⁻ ξ, F ((w.1, X w), ξ) ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ R.indicator 1 w + ε₁
      have hbad : MeasurableSet {ξ : ℕ → Ω | (X w, ξ) ∈ bad} :=
        hb.preimage (measurable_const.prodMk measurable_id)
      have hh : (∫⁻ ξ, F ((w.1, X w), ξ) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
          (Measure.infinitePi fun _ : ℕ => μ) {ξ | (X w, ξ) ∈ bad} := lintegral_indicator_one hbad
      rw [hh]
      by_cases hw : w ∈ R
      · simp only [Set.indicator_of_mem hw, Pi.one_apply]
        exact (prob_le_one (μ := Measure.infinitePi fun _ : ℕ => μ)).trans (le_add_right le_rfl)
      · simpa only [Set.indicator_of_notMem hw, zero_add] using hconditional (X w) hw
    _ = (ν.prod (Measure.infinitePi fun _ : ℕ => μ)) R + ε₁ := by
      have hi : Measurable (R.indicator (1 : (S × (ℕ → Ω)) → ℝ≥0∞)) := measurable_const.indicator hR
      rw [lintegral_add_left hi, lintegral_indicator_one hR,
        lintegral_const, measure_univ, mul_one]
    _ ≤ ε₀ + ε₁ := add_le_add hrough le_rfl

lemma complete_plan_failure (q : Params) (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2)
    {μ : Measure q.Ω} [IsProbabilityMeasure μ]
    {Q : Set q.E} {P : q.E → q.E} {f : q.E → ℝ} {G : q.E → q.E} {g : q.E → q.Ω → q.E}
    {u : q.E} (hP : ConstrainedMonotone.Proj Q P) (hx0 : q.x0 ∈ Q) (hu : u ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ q.D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ q.L * ‖y - w‖)
    (hmin : IsMinOn f Q u)
    (hquasar : ∀ y ∈ Q, q.γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ q.σ ^ 2) :
    ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | q.ε < f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (completePlan q w.1) 0) - f u} ≤ ENNReal.ofReal (3 * q.δ / 4) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  let M := constrainedEnvelope Q f q.L
  let X := fun w : ProgramSeed q × (ℕ → q.Ω) =>
    (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (outerPlan q w.1) 0).2.1
  let Y := fun (c : q.E) (ξ : ℕ → q.Ω) =>
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (cleanupPlan q.L q.σ q.D (outputRadius q) c q.x0 (outputBatch q) (outerOrder q)) 0
  have hX : Measurable X := (measurable_outer_execution hv hP.lipschitz.continuous.measurable hgm).snd.fst
  have hY : Measurable (Function.uncurry Y) :=
    (measurable_cleanup_joint hP.lipschitz.continuous.measurable hgm q.L q.σ q.D (outputRadius q)
      (outputBatch q) (outerOrder q) 0).comp
        ((measurable_fst.prodMk (measurable_const (a := q.x0))).prodMk measurable_snd)
  have hdep (seed : ProgramSeed q) (ξ ζ : ℕ → q.Ω)
      (h : ∀ i, i < outerCalls q seed → ξ i = ζ i) : X (seed, ξ) = X (seed, ζ) := by
    exact congrArg (fun state : ℝ × q.E × q.E => state.2.1)
      (StochasticCohypomonotone.sampledEval_congr _ (outerPlan q seed) ξ ζ 0
        (by simpa only [Nat.zero_add] using h))
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun y =>
    (constrainedEnvelope_hasGradient hv.1 hQ ⟨u, hu⟩ hcv hG hlip y).hasFDerivAt.continuousAt
  let rough : Set q.E := {c | q.ε / 8 < M c - f u}
  have hr : MeasurableSet rough := measurableSet_lt measurable_const (hMc.measurable.sub measurable_const)
  let bad : Set (q.E × (ℕ → q.Ω)) := {w | q.ε < f (P (Y w.1 w.2)) - f u}
  have hb : MeasurableSet bad := measurableSet_lt measurable_const
    (((projected_objective_continuous hP hG).measurable.comp hY).sub measurable_const)
  have hrough := outer_envelope_failure q hv he hP hx0 hu hQ hcv hD hG hlip hmin hquasar hgm hgi hmean hg2 hvar
  have hfix (c : q.E) (ξ : ℕ → q.Ω) : P (Y c ξ) = Y c ξ :=
    hP.fixed (sampled_cleanup_mem hP.mem g ξ q.L q.σ q.D (outputRadius q) c q.x0 (outputBatch q) (outerOrder q) 0)
  have hδ := hv.2.2.2.2.2.2.1
  have hconditional (c : q.E) (hc : c ∉ rough) :
      (Measure.infinitePi fun _ : ℕ => μ) {ξ | (c, ξ) ∈ bad} ≤ ENNReal.ofReal (q.δ / 4) := by
    have hε := hv.2.2.2.2.2.1
    have hD0 := hv.2.1
    have hg : f (constrainedProx Q f q.L c) + q.L * ‖constrainedProx Q f q.L c - c‖ ^ 2 - f u ≤ q.ε / 8 :=
      le_of_not_gt hc
    have hh := cleanup_failure_bound μ ω0 hP hv.1 hD0 (output_radius_pos hv)
      (by positivity : 0 < q.ε / (24 * q.D)) hε hx0 hQ hcv hD hG hlip hgm hgi hmean hg2 hvar
      (outputBatch q) (outerOrder q) (output_batch_pos q) (output_gradient_variance hv)
      (output_prox_error_sq hv).le (by ring_nf; rfl : 6 * (q.ε / (24 * q.D)) ≤ q.ε / (4 * q.D)) hg
    simp only [bad, Set.mem_ofPred_eq, hfix]
    apply hh.trans
    have ht := ENNReal.ofReal_le_ofReal (cleanup_replica_tail hv)
    apply (add_le_add ht ht).trans
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ q.δ / 8) (by positivity : 0 ≤ q.δ / 8)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hh := seeded_failure_composition μ (programLaw q : Measure _) (measurable_outer_calls q)
    X hX hdep hr hb hrough hconditional
  have heval (w : ProgramSeed q × (ℕ → q.Ω)) :
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (completePlan q w.1) 0 =
        Y (X w) (fun i => w.2 (outerCalls q w.1 + i)) := by
    rw [sampled_complete]
    exact StochasticCohypomonotone.sampledEval_shift _ _ w.2 (outerCalls q w.1)
  have hh' : ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | q.ε < f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (completePlan q w.1) 0) - f u} ≤ ENNReal.ofReal (q.δ / 2) + ENNReal.ofReal (q.δ / 4) := by
    simpa only [bad, Set.mem_ofPred_eq, hfix, ← heval] using hh
  apply hh'.trans
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ q.δ / 2) (by positivity : 0 ≤ q.δ / 4)]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma program_failure (q : Params) (hv : spec.valid q)
    {μ : Measure q.Ω} [IsProbabilityMeasure μ]
    {Q : Set q.E} {P : q.E → q.E} {f : q.E → ℝ} {G : q.E → q.E} {g : q.E → q.Ω → q.E}
    {u : q.E} (hP : ConstrainedMonotone.Proj Q P) (hx0 : q.x0 ∈ Q) (hu : u ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ q.D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ q.L * ‖y - w‖)
    (hmin : IsMinOn f Q u)
    (hquasar : ∀ y ∈ Q, q.γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ q.σ ^ 2) :
    ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
      {w | q.ε < f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (program q w.1).2 0) - f u} ≤ ENNReal.ofReal q.δ := by
  have hδ := hv.2.2.2.2.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hD0 := hv.2.1
  by_cases he : 4 * q.L * q.D ^ 2 ≤ q.ε
  · let Y := fun ξ : ℕ → q.Ω => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (initialCleanupPlan q.L q.x0 (outputBatch q) (outerOrder q)) 0
    have hfix (ξ : ℕ → q.Ω) : P (Y ξ) = Y ξ := by
      apply hP.fixed
      rw [show Y ξ = P (q.x0 - (1 / (3 * q.L)) •
        QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
          (robustGradientPlan q.x0 (outputBatch q) (outerOrder q)) 0) from
          sampled_initial_cleanup P g ξ q.L q.x0 (outputBatch q) (outerOrder q) 0]
      exact hP.mem _
    have hY : Measurable Y := measurable_initial_execution q hP.lipschitz.continuous.measurable hgm
    let A : Set (ℕ → q.Ω) := {ξ | q.ε < f (P (Y ξ)) - f u}
    have hA : MeasurableSet A := measurableSet_lt measurable_const
      (((projected_objective_continuous hP hG).measurable.comp hY).sub measurable_const)
    have hh := initial_cleanup_failure_bound μ hP hv.1 hD0
      (by positivity : 0 < q.ε / (24 * q.D)) hx0 hu hcv hD hG hlip
      (hgm.comp (measurable_const.prodMk measurable_id)) (hgi _ hx0) (hmean _ hx0) (hg2 _ hx0) (hvar _ hx0)
      (outputBatch q) (outerOrder q) (output_batch_pos q) (output_gradient_variance hv)
      (by ring_nf; rfl : 6 * (q.ε / (24 * q.D)) ≤ q.ε / (4 * q.D)) he
    have hp := measurePreserving_snd (μ := (programLaw q : Measure (ProgramSeed q)))
      (ν := Measure.infinitePi fun _ : ℕ => μ)
    have hb : (Measure.infinitePi fun _ : ℕ => μ) A ≤ ENNReal.ofReal (q.δ / 8) := by
      simp only [A, hfix]
      exact hh.trans (ENNReal.ofReal_le_ofReal (cleanup_replica_tail hv))
    have hl := (hp.measure_preimage hA.nullMeasurableSet).trans_le hb
    have hc : ((programLaw q : Measure _).prod (Measure.infinitePi fun _ : ℕ => μ))
        {w | q.ε < f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
          (program q w.1).2 0) - f u} ≤ ENNReal.ofReal (q.δ / 8) := by
      simpa only [sampled_program, he, ite_true, Set.preimage_ofPred_eq, A, hfix, Y] using hl
    exact hc.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · let C : Set (ProgramSeed q) := {seed | workCap q < outerCalls q seed}
    have hC : MeasurableSet C := measurableSet_lt measurable_const (measurable_outer_calls q)
    have hp := measurePreserving_fst (μ := (programLaw q : Measure (ProgramSeed q)))
      (ν := Measure.infinitePi fun _ : ℕ => μ)
    have hcap := (hp.measure_preimage hC.nullMeasurableSet).trans_le (program_work_cap_failure hv)
    let B : Set (ProgramSeed q × (ℕ → q.Ω)) := {w | q.ε <
      f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (completePlan q w.1) 0) - f u}
    have hb := complete_plan_failure q hv (le_of_not_ge he) hP hx0 hu hQ hcv hD hG hlip hmin hquasar
      hgm hgi hmean hg2 hvar
    have hsub : {w : ProgramSeed q × (ℕ → q.Ω) | q.ε <
        f (QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2 (program q w.1).2 0) - f u}
        ⊆ Prod.fst ⁻¹' C ∪ B := by
      intro w hw
      by_cases hc : outerCalls q w.1 ≤ workCap q
      · right
        simpa only [Set.mem_ofPred_eq, sampled_program, he, ite_false, hc, ite_true, B] using hw
      · exact Or.inl (lt_of_not_ge hc)
    apply (measure_mono hsub).trans
    apply (measure_union_le _ _).trans
    apply (add_le_add hcap hb).trans
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ q.δ / 8) (by positivity : 0 ≤ 3 * q.δ / 4)]
    apply ENNReal.ofReal_le_ofReal
    linarith

end OracleTemplate.StochasticQuasar
