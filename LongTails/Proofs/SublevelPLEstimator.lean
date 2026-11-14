import LongTails.Algorithms.SublevelRobustGradient
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.RobustPilot

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E : Type} [NormedAddCommGroup E]

lemma robustCenter_accuracy {n : ℕ} (hn : 0 < n) {B : ℝ} (v : Fin n → E) (u : E)
    (h : n < 2 * (Finset.univ.filter (fun i => ‖v i - u‖ ≤ B / 6)).card) :
    ‖robustCenter hn B v - u‖ ≤ B / 2 := by
  classical
  have hex : ∃ i, n < 2 * (neighbors B v i).card := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter
      (fun i => ‖v i - u‖ ≤ B / 6)).card by omega)
    refine ⟨i, lt_of_lt_of_le h (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))⟩
    intro j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    calc ‖v i - v j‖ = ‖(v i - u) - (v j - u)‖ := by congr 1; abel
      _ ≤ ‖v i - u‖ + ‖v j - u‖ := norm_sub_le _ _
      _ ≤ B / 6 + B / 6 := add_le_add hi' hj'
      _ = B / 3 := by ring
  unfold robustCenter
  simp only [hex, ↓reduceIte]
  exact pilotCenter_accuracy v u h

lemma robustCenter_mem {n : ℕ} (hn : 0 < n) (B : ℝ) (v : Fin n → E) :
    ∃ i, robustCenter hn B v = v i := by
  classical
  unfold robustCenter
  split_ifs with hex
  · obtain ⟨i, _, _, hi⟩ := firstPilot_selected B v (List.finRange n)
      (by obtain ⟨i, hi⟩ := hex; exact ⟨i, List.mem_finRange i, hi⟩)
    exact ⟨i, hi⟩
  · exact ⟨⟨0, hn⟩, rfl⟩

lemma robustCenter_sq_le {n : ℕ} (hn : 0 < n) (B : ℝ) (v : Fin n → E) (u : E) :
    ‖robustCenter hn B v - u‖ ^ 2 ≤ ∑ i, ‖v i - u‖ ^ 2 := by
  obtain ⟨i, hi⟩ := robustCenter_mem hn B v
  rw [hi]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖v j - u‖) (Finset.mem_univ i)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_robustCenter {n : ℕ} (hn : 0 < n) (B : ℝ) :
    Measurable (robustCenter hn B : (Fin n → E) → E) := by
  classical
  have hpair : Measurable (fun v : Fin n → E => (B, v)) := measurable_const.prodMk measurable_id
  have hset : MeasurableSet {v : Fin n → E | ∃ i, n < 2 * (neighbors B v i).card} := by
    have : {v : Fin n → E | ∃ i, n < 2 * (neighbors B v i).card} =
        ⋃ i, {v : Fin n → E | n < 2 * (neighbors B v i).card} := by
      ext v; simp
    rw [this]
    refine MeasurableSet.iUnion (fun i => ?_)
    exact measurableSet_lt measurable_const
      (((measurable_neighbors_card i).comp hpair).const_mul 2)
  have hpc : Measurable (fun v : Fin n → E => pilotCenter B v) :=
    (measurable_pilotCenter n).comp hpair
  unfold robustCenter
  exact Measurable.ite hset hpc (measurable_pi_apply _)

end OracleTemplate.SublevelRobustGradient
