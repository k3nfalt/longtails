import LongTails.Proofs.RobustSampleBlocks
import LongTails.Algorithms.ClippedExtragradientSamples

open MeasureTheory

namespace OracleTemplate.ClippedExtragradient

variable {Ω : Type*} [MeasurableSpace Ω]


lemma groupSamples_preserving (P : Measure Ω) [IsProbabilityMeasure P] (r k : ℕ) :
    MeasurePreserving (groupSamples (Ω := Ω) r k)
      (Measure.pi fun _ : Fin (r * k) => P)
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => P) := by
  have hh := RobustGradient.stream_groups_preserving P k r
  refine ⟨by unfold groupSamples; fun_prop, ?_⟩
  rw [← (StochasticGeneralized.prefix_preserving P (r * k)).map_eq,
    Measure.map_map (by unfold groupSamples; fun_prop) (by fun_prop)]
  convert hh.map_eq using 1
  congr 1
  funext ξ i j
  simp only [Function.comp_def, groupSamples, Nat.mul_comm]


lemma splitBatches_preserving (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (splitBatches (Ω := Ω) n) (Measure.pi fun _ : Fin (n + n) => P)
      ((Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P))) :=
  RobustGradient.finite_split_preserving P n n


lemma splitTrial_preserving (P : Measure Ω) [IsProbabilityMeasure P] (n k : ℕ) :
    MeasurePreserving (splitTrial (Ω := Ω) n k)
      (Measure.pi fun _ : Fin ((n + n) * k) => P)
      (Measure.pi fun _ : Fin k =>
        (Measure.pi (fun _ : Fin n => P)).prod (Measure.pi (fun _ : Fin n => P))) :=
  (measurePreserving_pi _ _ (fun _ : Fin k => splitBatches_preserving P n)).comp
    (groupSamples_preserving P (n + n) k)


lemma measurable_splitStage (t : Tuning) (s : ℕ) :
    Measurable (splitStage (Ω := Ω) t s) := by
  unfold splitStage splitTrial splitBatches groupSamples
  fun_prop

lemma splitStage_preserving (P : Measure Ω) [IsProbabilityMeasure P] (t : Tuning) (s : ℕ) :
    MeasurePreserving (splitStage (Ω := Ω) t s)
      (Measure.pi fun _ : Fin (stageCalls t s) => P)
      (Measure.pi fun _ : Fin (repetitions t) => Measure.pi fun _ : Fin (innerSteps t s) =>
        (Measure.pi (fun _ : Fin (batchSize t s) => P)).prod
          (Measure.pi (fun _ : Fin (batchSize t s) => P))) :=
  (measurePreserving_pi _ _ (fun _ : Fin (repetitions t) =>
    splitTrial_preserving P (batchSize t s) (innerSteps t s))).comp
      (groupSamples_preserving P ((batchSize t s + batchSize t s) * innerSteps t s) (repetitions t))

lemma measurable_guarded_block {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (cost : ℕ → ℕ) (reply : (s : ℕ) → A → (Fin (cost s) → Ω) → B)
    (fallback : A → B) (hfallback : Measurable fallback)
    (hreply : ∀ s, Measurable (fun w : A × (Fin (cost s) → Ω) => reply s w.1 w.2)) (n : ℕ) :
    Measurable (fun w : (ℕ × A) × (Fin n → Ω) =>
      if h : n = cost w.1.1 then reply w.1.1 w.1.2 (fun i => w.2 (Fin.cast h.symm i))
      else fallback w.1.2) := by
  have hf (s : ℕ) : Measurable (fun w : A × (Fin n → Ω) =>
      if h : n = cost s then reply s w.1 (fun i => w.2 (Fin.cast h.symm i))
      else fallback w.1) := by
    by_cases h : n = cost s
    · subst n
      simpa only [Function.uncurry, dite_true, Fin.cast_refl, id_eq] using hreply s
    · simp only [h, dite_false]
      exact hfallback.comp measurable_fst
  have hg : Measurable (fun w : ℕ × (A × (Fin n → Ω)) =>
      if h : n = cost w.1 then reply w.1 w.2.1 (fun i => w.2.2 (Fin.cast h.symm i))
      else fallback w.2.1) := measurable_from_prod_countable_right hf
  exact hg.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

end OracleTemplate.ClippedExtragradient
