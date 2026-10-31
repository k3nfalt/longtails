import LongTails.Algorithms.AffineGradientEstimator
import LongTails.Proofs.RobustEstimatorMoments

namespace OracleTemplate.AffineGradient

variable {E : Type*} [NormedAddCommGroup E]

lemma firstCenter_selected {n : ℕ} (α ν : ℝ) (v : Fin n → E) (s : List (Fin n))
    (h : ∃ i ∈ s, n < 2 * (neighbors α ν v i).card) :
    ∃ i ∈ s, n < 2 * (neighbors α ν v i).card ∧ firstCenter α ν v s = v i := by
  classical
  induction s with
  | nil => simp at h
  | cons i s ih =>
    by_cases hi : n < 2 * (neighbors α ν v i).card
    · exact ⟨i, List.mem_cons_self, hi, by simp only [firstCenter, hi, ↓reduceIte]⟩
    · have hs : ∃ j ∈ s, n < 2 * (neighbors α ν v j).card := by
        obtain ⟨j, hj, hp⟩ := h
        rcases List.mem_cons.mp hj with rfl | hj
        · exact False.elim (hi hp)
        · exact ⟨j, hj, hp⟩
      obtain ⟨j, hj, hp, he⟩ := ih hs
      exact ⟨j, List.mem_cons_of_mem i hj, hp, by simpa only [firstCenter, hi, ↓reduceIte] using he⟩

lemma center_accuracy {n : ℕ} {α ν : ℝ} (hν : 0 ≤ ν) (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (v : Fin n → E) (q : E)
    (h : n < 2 * (Finset.univ.filter (fun i => ‖v i - q‖ ≤ α * (‖q‖ + ν) / 8)).card) :
    ‖center α ν v - q‖ ≤ 3 * α * (‖q‖ + ν) := by
  classical
  let good := Finset.univ.filter (fun i => ‖v i - q‖ ≤ α * (‖q‖ + ν) / 8)
  have hgood : n < 2 * good.card := h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < good.card by omega)
  have hsubset : good ⊆ neighbors α ν v i := by
    intro j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have ht := norm_sub_le (v i - q) (v j - q)
    have hid : v i - q - (v j - q) = v i - v j := by abel
    rw [hid] at ht
    have hq := norm_le_norm_sub_add q (v i)
    rw [norm_sub_rev q] at hq
    have hb : ‖q‖ + ν ≤ 2 * (‖v i‖ + ν) := by
      nlinarith [norm_nonneg q]
    have hm := mul_le_mul_of_nonneg_left hb hα
    nlinarith [mul_nonneg hα (norm_nonneg (v i))]
  have hmajor : n < 2 * (neighbors α ν v i).card := by
    have hc := Finset.card_le_card hsubset
    omega
  obtain ⟨j, _, hj, hout⟩ := firstCenter_selected α ν v (List.finRange n) ⟨i, by simp, hmajor⟩
  obtain ⟨k, hk, hkgood⟩ := RobustGradient.majorities_intersect
    (neighbors α ν v j) good hj hgood
  have hjk : ‖v j - v k‖ ≤ α * (‖v j‖ + ν) := (Finset.mem_filter.mp hk).2
  have hkq : ‖v k - q‖ ≤ α * (‖q‖ + ν) / 8 := (Finset.mem_filter.mp hkgood).2
  have ht := norm_sub_le (v j - v k) (q - v k)
  have hid : v j - v k - (q - v k) = v j - q := by abel
  rw [hid, norm_sub_rev q] at ht
  have hn := norm_le_norm_sub_add (v j) q
  have hm := mul_le_mul_of_nonneg_left hn hα
  rw [center, hout]
  nlinarith [mul_nonneg hα (norm_nonneg q), norm_nonneg (v j - q)]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_neighbors_card {n : ℕ} (ν : ℝ) (i : Fin n) :
    Measurable (fun w : ℝ × (Fin n → E) => (neighbors w.1 ν w.2 i).card) := by
  classical
  simp only [neighbors, Finset.card_filter]
  apply Finset.measurable_sum
  intro j hj
  apply Measurable.ite
  · apply measurableSet_le
    · exact (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply j).comp measurable_snd)).norm
    · exact measurable_fst.mul ((((measurable_pi_apply i).comp measurable_snd).norm).add_const ν)
  · exact measurable_const
  · exact measurable_const

lemma measurable_firstCenter {n : ℕ} (ν : ℝ) (s : List (Fin n)) :
    Measurable (fun w : ℝ × (Fin n → E) => firstCenter w.1 ν w.2 s) := by
  induction s with
  | nil => exact measurable_const
  | cons i s ih =>
    simp only [firstCenter]
    exact Measurable.ite
      (measurableSet_lt measurable_const ((measurable_neighbors_card ν i).const_mul 2))
      ((measurable_pi_apply i).comp measurable_snd) ih

@[fun_prop] lemma measurable_center (ν : ℝ) (n : ℕ) :
    Measurable (fun w : ℝ × (Fin n → E) => center w.1 ν w.2) :=
  measurable_firstCenter ν (List.finRange n)

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma center_failure_probability {V : Ω → E} (hV : Measurable V) (q : E)
    {α ν : ℝ} (hν : 0 ≤ ν) (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hp : P.real {ω | α * (‖q‖ + ν) / 8 < ‖V ω - q‖} ≤ 1 / 16) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | 3 * α * (‖q‖ + ν) < ‖center α ν (fun i => V (ξ i)) - q‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  classical
  apply (measure_mono ?_).trans (RobustGradient.majority_failure_probability
    (measurableSet_lt measurable_const ((hV.sub measurable_const).norm)) hp k)
  intro ξ hξ
  have hgood : ¬ k < 2 * (Finset.univ.filter (fun i => ‖V (ξ i) - q‖ ≤ α * (‖q‖ + ν) / 8)).card := by
    intro hg
    exact (not_le_of_gt hξ) (center_accuracy hν hα hα1 (fun i => V (ξ i)) q hg)
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (p := fun i => ‖V (ξ i) - q‖ ≤ α * (‖q‖ + ν) / 8)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  change k ≤ 2 * (Finset.univ.filter (fun i => α * (‖q‖ + ν) / 8 < ‖V (ξ i) - q‖)).card
  omega

end OracleTemplate.AffineGradient
