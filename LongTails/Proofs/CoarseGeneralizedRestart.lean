import LongTails.Proofs.CoarseGeneralizedOutput
import LongTails.Proofs.CoarseGeneralizedWarmGuarantee
import LongTails.Proofs.RobustGeneralizedConvergence

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.CoarseGeneralized

lemma product_failure_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} {B : Set (Ω × Ξ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {a b : ℝ≥0∞} (hbad : P Aᶜ ≤ a)
    (hslice : ∀ x ∈ A, Q {z | (x, z) ∈ B} ≤ b) : (P.prod Q) B ≤ a + b := by
  let C := B ∩ Prod.fst ⁻¹' A
  have hC : MeasurableSet C := hB.inter (hA.preimage measurable_fst)
  have hCb : (P.prod Q) C ≤ b := by
    rw [Measure.prod_apply hC]
    calc
      (∫⁻ x, Q (Prod.mk x ⁻¹' C) ∂P) ≤ ∫⁻ _, b ∂P := by
        apply lintegral_mono
        intro x
        change Q (Prod.mk x ⁻¹' C) ≤ b
        by_cases hx : x ∈ A
        · have he : Prod.mk x ⁻¹' C = {z | (x, z) ∈ B} := by ext z; simp [C, hx]
          rw [he]
          exact hslice x hx
        · have he : Prod.mk x ⁻¹' C = ∅ := by ext z; simp [C, hx]
          simp [he]
      _ = b := by simp
  have hsub : B ⊆ Prod.fst ⁻¹' Aᶜ ∪ C := by
    intro w hw
    by_cases hx : w.1 ∈ A
    · exact Or.inr ⟨hw, hx⟩
    · exact Or.inl hx
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  have he : (P.prod Q) (Prod.fst ⁻¹' Aᶜ) = P Aᶜ :=
    measurePreserving_fst.measure_preimage hA.compl.nullMeasurableSet
  rw [he]
  exact add_le_add hbad hCb

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

noncomputable def extendPrefix (p : Params) (ω0 : p.Ω) (b : Fin (warmCost p) → p.Ω) : ℕ → p.Ω :=
  fun i => if hi : i < warmCost p then b ⟨i, hi⟩ else ω0

noncomputable def warmPrefix (p : Params) (oracle : p.E → p.Ω → p.E) (ω0 : p.Ω)
    (b : Fin (warmCost p) → p.Ω) : p.E := warmPoint p oracle (extendPrefix p ω0 b)

lemma measurable_extendPrefix (p : Params) (ω0 : p.Ω) : Measurable (extendPrefix p ω0) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i < warmCost p
  · simp only [extendPrefix, hi, ↓reduceDIte]
    exact measurable_pi_apply (⟨i, hi⟩ : Fin (warmCost p))
  · simp only [extendPrefix, hi, ↓reduceDIte]
    exact measurable_const

lemma measurable_warmPrefix (p : Params) {oracle : p.E → p.Ω → p.E}
    (ho : Measurable (Function.uncurry oracle)) (ω0 : p.Ω) : Measurable (warmPrefix p oracle ω0) :=
  (measurable_warmPoint p ho).comp (measurable_extendPrefix p ω0)

lemma warmPrefix_stream (p : Params) (oracle : p.E → p.Ω → p.E) (ω0 : p.Ω) (ξ : ℕ → p.Ω) :
    warmPrefix p oracle ω0 (fun i => ξ i) = warmPoint p oracle ξ := by
  apply warmPoint_congr_prefix
  intro i hi
  simp only [extendPrefix, hi, ↓reduceDIte]

lemma restart_rawAdvance (p : Params) (x : p.E) (oracle : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n call : ℕ) (s : RobustGeneralized.State p.E) :
    RobustGeneralized.rawAdvance (restartParams p x) oracle ξ n call s =
      RobustGeneralized.rawAdvance (restartParams p p.x0) oracle ξ n call s := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
      change RobustGeneralized.rawAdvance (restartParams p x) oracle ξ n (call + 1)
        ((RobustGeneralized.algorithm (restartParams p x)).update s
          (oracle (((RobustGeneralized.algorithm (restartParams p x)).query s).2) (ξ call))) = _
      erw [restart_query, restart_update, ih]
      rfl

lemma measurable_restart_run (p : Params) {oracle : p.E → p.Ω → p.E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : p.E × (ℕ → p.Ω) =>
      (RobustGeneralized.algorithm (restartParams p w.1)).output
        (RobustGeneralized.rawAdvance (restartParams p w.1) oracle w.2 n 0
          ((RobustGeneralized.algorithm (restartParams p w.1)).initial ()))) := by
  have hi : Measurable (fun w : p.E × (ℕ → p.Ω) =>
      (show RobustGeneralized.State p.E from by
        exact (RobustGeneralized.algorithm (restartParams p w.1)).initial ())) :=
    (measurable_restart_initial p).comp measurable_fst
  have hr := (RobustGeneralized.measurable_rawAdvance (restartParams p p.x0) ho n 0).comp
    (hi.prodMk measurable_snd)
  have hm := (RobustGeneralized.measurable_algorithm_output (restartParams p p.x0)).comp hr
  have he : (fun w : p.E × (ℕ → p.Ω) =>
      (RobustGeneralized.algorithm (restartParams p w.1)).output
        (RobustGeneralized.rawAdvance (restartParams p w.1) oracle w.2 n 0
          ((RobustGeneralized.algorithm (restartParams p w.1)).initial ()))) =
      (fun w : p.E × (ℕ → p.Ω) =>
        (RobustGeneralized.algorithm (restartParams p p.x0)).output
          (RobustGeneralized.rawAdvance (restartParams p p.x0) oracle w.2 n 0
            ((RobustGeneralized.algorithm (restartParams p w.1)).initial ()))) := by
    funext w
    erw [restart_rawAdvance, restart_output]
  erw [he]
  exact hm

lemma warmPrefix_failure_probability (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hdist : ‖p.x0 - u‖ ≤ p.R)
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (ω0 : p.Ω) :
    (Measure.pi fun _ : Fin (warmCost p) => μ)
      {b | p.R < ‖warmPrefix p oracle ω0 b - u‖ ∨
        restartGap p < f (warmPrefix p oracle ω0 b) - f u} ≤ ENNReal.ofReal (p.δ / 4) := by
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).measurable
  have hw := measurable_warmPrefix p ho.measurable ω0
  have hset : MeasurableSet {b | p.R < ‖warmPrefix p oracle ω0 b - u‖ ∨
      restartGap p < f (warmPrefix p oracle ω0 b) - f u} :=
    (measurableSet_lt measurable_const (hw.sub measurable_const).norm).union
      (measurableSet_lt measurable_const ((hfm.comp hw).sub measurable_const))
  have hm := (StochasticGeneralized.prefix_preserving μ (warmCost p)).measure_preimage hset.nullMeasurableSet
  rw [← hm]
  have hh := warmPoint_failure_probability p hp hc hf hg hH u hmin hdist ho
    (StochasticGeneralized.infinitePi_iid μ)
  simpa only [Set.preimage_ofPred_eq, warmPrefix_stream] using hh

lemma restart_failure_probability (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖)
    (u x : p.E) (hmin : IsMinOn f Set.univ u) (hdist : ‖x - u‖ ≤ p.R)
    (hgap : f x - f u ≤ restartGap p)
    (μ : ProbabilityMeasure p.Ω) (Q : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (Q : Measure _))
    {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω (μ : Measure _) f oracle p.σ)
    (n : ℕ)
    (hN : (4194304 * RobustGeneralized.shape (restartParams p x) +
      140737488355328 * (p.σ ^ 2 * p.R ^ 2 * (RobustGeneralized.confidence (restartParams p x)) ^ 2 / p.ε ^ 2)) *
      RobustGeneralized.logScale (restartParams p x) ≤ n) :
    (Q : Measure (ℕ → p.Ω)) {ξ : ℕ → p.Ω | p.ε < f ((RobustGeneralized.algorithm (restartParams p x)).output
      (RobustGeneralized.rawAdvance (restartParams p x) oracle ξ n 0
        ((RobustGeneralized.algorithm (restartParams p x)).initial ()))) - f u} ≤ ENNReal.ofReal (p.δ / 2) := by
  have hh := RobustGeneralized.execution_high_probability (restartParams p x)
    (restartParams_valid p hp x) hc hf hg hH u hmin hdist hgap μ Q hIID ho n hN
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr (fun z => (hf z).continuousAt)).measurable
  have hm : Measurable (fun ξ : ℕ → p.Ω =>
      (RobustGeneralized.algorithm (restartParams p x)).output
        (RobustGeneralized.rawAdvance (restartParams p x) oracle ξ n 0
          ((RobustGeneralized.algorithm (restartParams p x)).initial ()))) :=
    (measurable_restart_run p ho.measurable n).comp ((measurable_const (a := x)).prodMk measurable_id)
  have hset := measurableSet_lt (measurable_const (a := p.ε)) ((hfm.comp hm).sub (measurable_const (a := f u)))
  have he := (measurePreserving_snd (μ := Measure.dirac ()) (ν := (Q : Measure _))).measure_preimage
    hset.nullMeasurableSet
  erw [← he]
  apply (measure_mono (show _ ⊆ {w : Unit × (ℕ → p.Ω) |
    (restartParams p x).ε < f (execute
      { Seed := fun _ => p.Ω, law := Q, answer := fun _ (_, z) ω => oracle z ω }
      (RobustGeneralized.algorithm (restartParams p x)) (fun _ => n) w.1 w.2) - f u} from ?_)).trans hh
  rintro ⟨⟨⟩, ξ⟩ hξ
  change p.ε < f (execute
    { Seed := fun _ => p.Ω, law := Q, answer := fun _ (_, z) ω => oracle z ω }
    (RobustGeneralized.algorithm (restartParams p x)) (fun _ => n) () ξ) - f u
  erw [StochasticGradient.execute_advance]
  exact hξ

end OracleTemplate.CoarseGeneralized
