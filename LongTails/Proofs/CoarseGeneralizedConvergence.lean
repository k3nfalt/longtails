import LongTails.Proofs.CoarseGeneralizedRestart

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

lemma execution_high_probability (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hH : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ p.L0 + p.L1 * ‖gradient f x‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hdist : ‖p.x0 - u‖ ≤ p.R)
    (μ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (P : Measure _))
    {oracle : p.E → p.Ω → p.E}
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω (μ : Measure _) f oracle p.σ)
    (n : ℕ)
    (hN : ∀ x : p.E, (4194304 * RobustGeneralized.shape (restartParams p x) +
      140737488355328 * (p.σ ^ 2 * p.R ^ 2 * (RobustGeneralized.confidence (restartParams p x)) ^ 2 / p.ε ^ 2)) *
      RobustGeneralized.logScale (restartParams p x) ≤ n) :
    ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → p.Ω) |
      p.ε < f (execute
        { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
        (algorithm p) (fun _ => warmCost p + n) w.1 w.2) - f u} ≤ ENNReal.ofReal p.δ := by
  classical
  let ω0 : p.Ω := Classical.choice (nonempty_of_isProbabilityMeasure (μ : Measure p.Ω))
  let Q : ProbabilityMeasure (ℕ → p.Ω) := ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure p.Ω)), inferInstance⟩
  let W := warmPrefix p oracle ω0
  let A : Set (Fin (warmCost p) → p.Ω) := {b | ‖W b - u‖ ≤ p.R ∧ f (W b) - f u ≤ restartGap p}
  let F : (Fin (warmCost p) → p.Ω) × (ℕ → p.Ω) → p.E := fun w =>
    (RobustGeneralized.algorithm (restartParams p (W w.1))).output
      (RobustGeneralized.rawAdvance (restartParams p (W w.1)) oracle w.2 n 0
        ((RobustGeneralized.algorithm (restartParams p (W w.1))).initial ()))
  let B := {w | p.ε < f (F w) - f u}
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).measurable
  have hW : Measurable W := measurable_warmPrefix p ho.measurable ω0
  have hA : MeasurableSet A :=
    (measurableSet_le (hW.sub measurable_const).norm measurable_const).inter
      (measurableSet_le ((hfm.comp hW).sub measurable_const) measurable_const)
  have hF : Measurable F := (measurable_restart_run p ho.measurable n).comp
    ((hW.comp measurable_fst).prodMk measurable_snd)
  have hB : MeasurableSet B := measurableSet_lt measurable_const ((hfm.comp hF).sub measurable_const)
  have hbad : (Measure.pi fun _ : Fin (warmCost p) => (μ : Measure p.Ω)) Aᶜ ≤ ENNReal.ofReal (p.δ / 4) := by
    have hh := warmPrefix_failure_probability p hp hc hf hg hH u hmin hdist (μ : Measure p.Ω) ho ω0
    simpa only [A, W, Set.compl_ofPred, not_and_or, not_le] using hh
  have hslice : ∀ b ∈ A, (Q : Measure (ℕ → p.Ω)) {ξ | (b, ξ) ∈ B} ≤ ENNReal.ofReal (p.δ / 2) := by
    intro b hb
    exact restart_failure_probability p hp hc hf hg hH u (W b) hmin hb.1 hb.2 μ Q
      (StochasticGeneralized.infinitePi_iid (μ : Measure p.Ω)) ho n (hN (W b))
  have hprod : ((Measure.pi fun _ : Fin (warmCost p) => (μ : Measure p.Ω)).prod (Q : Measure _)) B ≤
      ENNReal.ofReal p.δ := by
    have hh := product_failure_bound (Measure.pi fun _ : Fin (warmCost p) => (μ : Measure p.Ω))
      (Q : Measure (ℕ → p.Ω)) hA hB hbad hslice
    apply hh.trans
    rw [← ENNReal.ofReal_add (by have hd := hp.2.2.2.2.2.2.1; positivity)
      (by have hd := hp.2.2.2.2.2.2.1; positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith [hp.2.2.2.2.2.2.1]
  have hmap := (hIID.prefix_tail_law (warmCost p)).comp
    (measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → p.Ω))))
  have hpre := hmap.measure_preimage hB.nullMeasurableSet
  apply (measure_mono (show _ ⊆ _ ⁻¹' B from ?_)).trans (hpre.le.trans hprod)
  rintro ⟨⟨⟩, ξ⟩ hbadξ
  change p.ε < f (execute
    { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
    (algorithm p) (fun _ => warmCost p + n) () ξ) - f u at hbadξ
  erw [execute_split p oracle ξ P Q n, StochasticGradient.execute_advance] at hbadξ
  change p.ε < f ((RobustGeneralized.algorithm (restartParams p (warmPrefix p oracle ω0 (fun i => ξ i)))).output
    (RobustGeneralized.rawAdvance (restartParams p (warmPrefix p oracle ω0 (fun i => ξ i))) oracle
      (fun k => ξ (warmCost p + k)) n 0
      ((RobustGeneralized.algorithm (restartParams p (warmPrefix p oracle ω0 (fun i => ξ i)))).initial ()))) - f u
  erw [warmPrefix_stream]
  exact hbadξ

end OracleTemplate.CoarseGeneralized
