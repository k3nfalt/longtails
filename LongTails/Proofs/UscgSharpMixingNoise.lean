import LongTails.Proofs.BernoulliCountCrossing
import LongTails.Proofs.UscgSharpMixingConstants
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.UscgSharpMixingNoise

open MeasureTheory ProbabilityTheory

def indicator (b : Bool) : ℕ := if b then 1 else 0

noncomputable def noise (p g : ℝ) (b : Bool) : ℝ :=
  -2 * g + (2 * g / p) * (indicator b : ℝ)

lemma indicator_le_one (b : Bool) : indicator b ≤ 1 := by cases b <;> simp [indicator]

lemma noise_mean (p : unitInterval) (hp : 0 < (p : ℝ)) (g : ℝ) :
    (∫ b, noise p g b ∂bernoulliMeasure true false p) = 0 := by
  rw [integral_bernoulliMeasure]
  simp [noise, indicator]
  field_simp
  ring

lemma noise_variance (p : unitInterval) (hp : 0 < (p : ℝ)) (g : ℝ) :
    (∫ b, noise p g b ^ 2 ∂bernoulliMeasure true false p) =
      4 * g ^ 2 * (1 - (p : ℝ)) / p := by
  rw [integral_bernoulliMeasure]
  simp [noise, indicator]
  field_simp
  ring

noncomputable def streamLaw (p : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p)

instance (p : unitInterval) : IsProbabilityMeasure (streamLaw p) := by
  unfold streamLaw
  infer_instance

def count (n : ℕ) (ξ : ℕ → Bool) : ℕ := ∑ i ∈ Finset.range n, indicator (ξ i)

lemma count_measurable (n : ℕ) : Measurable (fun ξ => (count n ξ : ℝ)) := by
  simp only [count, Nat.cast_sum]
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_finite (fun b => (indicator b : ℝ))).comp (measurable_pi_apply i)

lemma count_mean (p : unitInterval) (i : ℕ) :
    (∫ ξ, (indicator (ξ i) : ℝ) ∂streamLaw p) = (p : ℝ) := by
  have hm : Measurable (fun b => (indicator b : ℝ)) := measurable_of_finite _
  have he := integral_map (μ := streamLaw p) (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable
  rw [show (streamLaw p).map (fun ξ => ξ i) = bernoulliMeasure true false p from
    Measure.infinitePi_map_eval _ _] at he
  rw [← he, integral_bernoulliMeasure]
  simp [indicator]

def sparseEvent (R : ℝ) (T : ℕ) : Set (ℕ → Bool) :=
  {ξ | ∀ n, 0 < n → n ≤ T → 2 * R * (count n ξ : ℝ) < n}

lemma sparse_measurable (R : ℝ) (T : ℕ) : MeasurableSet (sparseEvent R T) := by
  unfold sparseEvent
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt ((count_measurable n).const_mul (2 * R)) measurable_const

lemma sparse_probability (p : unitInterval) {R : ℝ}
    (hp : 0 < (p : ℝ)) (hR : 0 < R) (hpR : (p : ℝ) * R ≤ 3 / 64) (T : ℕ) :
    1 / 2 < (streamLaw p).real (sparseEvent R T) := by
  have hc : 0 < 1 / (2 * R) := by positivity
  obtain ⟨_, _, hlog, hsmall⟩ := UscgSharpMixingConstants.probability_constants hp hR hpR
  have hind : iIndepFun (fun i (ξ : ℕ → Bool) => (indicator (ξ i) : ℝ)) (streamLaw p) :=
    iIndepFun_infinitePi (fun _ => measurable_of_finite (fun b => (indicator b : ℝ)))
  have htail := BernoulliCountCrossing.iid_bernoulli_crossing_log
    (fun i => (measurable_of_finite (fun b => (indicator b : ℝ))).comp (measurable_pi_apply i))
    hind (fun _ ξ => indicator_le_one (ξ _)) (count_mean p)
    hp p.2.2 hc hlog T
  have he : {ξ | ∃ n, 0 < n ∧ n ≤ T ∧ (1 / (2 * R)) * n ≤
      ((∑ i ∈ Finset.range n, indicator (ξ i) : ℕ) : ℝ)} = (sparseEvent R T)ᶜ := by
    ext ξ
    simp only [sparseEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt]
    congr! 2 with n
    rw [show (1 / (2 * R)) * (n : ℝ) = (n : ℝ) / (2 * R) by ring,
      div_le_iff₀ (show 0 < 2 * R by positivity)]
    simp [count, mul_comm]
    tauto
  rw [he, measureReal_compl (sparse_measurable R T)] at htail
  simp only [probReal_univ] at htail
  have hq : Real.exp 1 * (p : ℝ) / (1 / (2 * R)) = 2 * Real.exp 1 * (p : ℝ) * R := by
    field_simp
  rw [hq] at htail
  linarith

lemma sparse_probability_of_memory (p : unitInterval) {a : ℝ}
    (hp : 0 < (p : ℝ)) (ha : 0 < a) (hr : 256 ≤ a / p) (T : ℕ) :
    1 / 2 < (streamLaw p).real (sparseEvent ((Real.log (4 * a / p) + 2) / a) T) := by
  obtain ⟨_, hR, hpR⟩ := UscgSharpMixingConstants.radius_bounds ha hp hr
  exact sparse_probability p hp hR hpR T

lemma public_variance {e σ : ℝ} (he : 0 < e) :
    4 * (2 * e) ^ 2 * (1 - 16 / (σ ^ 2 / e ^ 2 + 16)) /
      (16 / (σ ^ 2 / e ^ 2 + 16)) = σ ^ 2 := by
  have hd : 0 < σ ^ 2 / e ^ 2 + 16 := by positivity
  field_simp
  ring

end LongTails.Proofs.UscgSharpMixingNoise
