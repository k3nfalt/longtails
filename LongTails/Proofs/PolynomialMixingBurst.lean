import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.PolynomialMixingSubgradient
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.PolynomialMixingBurst

open LongTails.Setups.PolynomialMixingSubgradient

abbrev Bits := ℕ → Bool

noncomputable def bitLaw (a : unitInterval) : Measure Bool := bernoulliMeasure true false a

instance (a : unitInterval) : IsProbabilityMeasure (bitLaw a) := by
  unfold bitLaw
  infer_instance

noncomputable def bitsLaw (a : unitInterval) : Measure Bits :=
  Measure.infinitePi fun _ : ℕ => bitLaw a

instance (a : unitInterval) : IsProbabilityMeasure (bitsLaw a) := by
  unfold bitsLaw
  infer_instance

def burst (m : ℕ) (b : Bits) (k : ℕ) : ℝ :=
  if ∃ i : Fin m, b (k + i.val) = true then 1 else 0

lemma measurable_burst (m : ℕ) : Measurable (burst m) := by
  apply Measurable.of_eval
  intro k
  apply Measurable.ite _ measurable_const measurable_const
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_eq_fun (measurable_pi_apply (k + i.val)) measurable_const

noncomputable def burstLaw (m : ℕ) (a : unitInterval) : ProbabilityMeasure Path :=
  ⟨(bitsLaw a).map (burst m), (Measure.isProbabilityMeasure_map_iff (measurable_burst m).aemeasurable).mpr inferInstance⟩

lemma bits_shift (a : unitInterval) (t : ℕ) :
    (bitsLaw a).map (fun b k => b (t + k)) = bitsLaw a := by
  have h := (OracleTemplate.StochasticGeneralized.infinitePi_iid (bitLaw a)).prefix_tail_law t
  have h' := (measurePreserving_snd (μ := Measure.pi fun _ : Fin t => bitLaw a)
    (ν := bitsLaw a)).comp h
  exact h'.map_eq

lemma burst_shift (m t : ℕ) (b : Bits) :
    future t (burst m b) = burst m (fun k => b (t + k)) := by
  funext k
  simp only [future, burst, Nat.add_assoc]

lemma burst_stationary (m : ℕ) (a : unitInterval) (t : ℕ) :
    (burstLaw m a : Measure Path).map (future t) = (burstLaw m a : Measure Path) := by
  have hf : Measurable (future t) := by unfold future; fun_prop
  change ((bitsLaw a).map (burst m)).map (future t) = (bitsLaw a).map (burst m)
  rw [Measure.map_map hf (measurable_burst m)]
  have he : future t ∘ burst m = burst m ∘ (fun (b : Bits) k => b (t + k)) :=
    funext (burst_shift m t)
  rw [he, ← Measure.map_map (measurable_burst m) (by fun_prop), bits_shift]

def silent (m : ℕ) : Set Bits := {b | ∀ i < m, b i = false}

lemma silent_eq_pi (m : ℕ) :
    silent m = Set.pi (↑(Finset.range m) : Set ℕ) (fun _ => {false}) := by
  ext b
  simp [silent, Set.mem_pi]

lemma measurableSet_silent (m : ℕ) : MeasurableSet (silent m) := by
  rw [silent_eq_pi]
  exact MeasurableSet.pi (Finset.countable_toSet _) fun _ _ => measurableSet_singleton _

lemma silent_probability (m : ℕ) (a : unitInterval) :
    (bitsLaw a).real (silent m) = (1 - (a : ℝ)) ^ m := by
  rw [silent_eq_pi, measureReal_def, bitsLaw, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [bitLaw, bernoulliMeasure_apply a (measurableSet_singleton false),
    unitInterval.coe_symm_eq]

lemma burst_zero_on_silent {b : Bits} {m N : ℕ} (hs : b ∈ silent (N + m)) :
    ∀ k ≤ N, burst m b k = 0 := by
  intro k hk
  apply ite_eq_right
  rintro ⟨i, hi⟩
  have hb := hs (k + i.val) (by have := i.isLt; omega)
  simp [hb] at hi

end LongTails.Proofs.PolynomialMixingBurst
