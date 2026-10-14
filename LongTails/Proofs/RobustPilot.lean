import LongTails.Proofs.RobustCenteredClipping

namespace OracleTemplate.RobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma firstPilot_selected {n : ℕ} (B : ℝ) (v : Fin n → E) (s : List (Fin n))
    (h : ∃ i ∈ s, n < 2 * (neighbors B v i).card) :
    ∃ i ∈ s, n < 2 * (neighbors B v i).card ∧ firstPilot B v s = v i := by
  classical
  induction s with
  | nil => simp at h
  | cons i s ih =>
    by_cases hi : n < 2 * (neighbors B v i).card
    · exact ⟨i, List.mem_cons_self, hi, by simp only [firstPilot, hi, ↓reduceIte]⟩
    · have hs : ∃ j ∈ s, n < 2 * (neighbors B v j).card := by
        obtain ⟨j, hj, hp⟩ := h
        rcases List.mem_cons.mp hj with rfl | hj
        · exact False.elim (hi hp)
        · exact ⟨j, hj, hp⟩
      obtain ⟨j, hj, hp, he⟩ := ih hs
      exact ⟨j, List.mem_cons_of_mem i hj, hp, by simpa only [firstPilot, hi, ↓reduceIte] using he⟩

lemma majorities_intersect {n : ℕ} (s t : Finset (Fin n))
    (hs : n < 2 * s.card) (ht : n < 2 * t.card) :
    ∃ i, i ∈ s ∧ i ∈ t := by
  classical
  by_contra h
  have hd : Disjoint s t := Finset.disjoint_left.mpr (by
    intro i hi hit
    exact h ⟨i, hi, hit⟩)
  have hc := Finset.card_le_card (Finset.subset_univ (s ∪ t))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin] at hc
  omega

omit [InnerProductSpace ℝ E] in
lemma pilotCenter_accuracy {n : ℕ} {B : ℝ} (v : Fin n → E) (u : E)
    (h : n < 2 * (Finset.univ.filter (fun i => ‖v i - u‖ ≤ B / 6)).card) :
    ‖pilotCenter B v - u‖ ≤ B / 2 := by
  classical
  let good := Finset.univ.filter (fun i => ‖v i - u‖ ≤ B / 6)
  have hgood : n < 2 * good.card := h
  have hne : good.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  have hsubset : good ⊆ neighbors B v i := by
    intro j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he : v i - v j = (v i - u) + (u - v j) := by abel
    rw [he]
    have ht := norm_add_le (v i-u) (u-v j)
    rw [norm_sub_rev u] at ht
    linarith
  have hmajor : n < 2 * (neighbors B v i).card := by
    have hc := Finset.card_le_card hsubset
    omega
  have he := firstPilot_selected B v (List.finRange n) ⟨i, by simp, hmajor⟩
  obtain ⟨j, _, hj, hout⟩ := he
  obtain ⟨k, hk, hkgood⟩ := majorities_intersect (neighbors B v j) good hj hgood
  have hjk : ‖v j-v k‖ ≤ B/3 := (Finset.mem_filter.mp hk).2
  have hku : ‖v k-u‖ ≤ B/6 := (Finset.mem_filter.mp hkgood).2
  rw [pilotCenter, hout]
  have he : v j-u = (v j-v k)+(v k-u) := by abel
  rw [he]
  have ht := norm_add_le (v j-v k) (v k-u)
  linarith

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] in
lemma measurable_neighbors_card {n : ℕ} (i : Fin n) :
    Measurable (fun w : ℝ × (Fin n → E) => (neighbors w.1 w.2 i).card) := by
  classical
  simp only [neighbors, Finset.card_filter]
  apply Finset.measurable_sum
  intro j hj
  apply Measurable.ite
  · apply measurableSet_le
    · exact (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply j).comp measurable_snd)).norm
    · exact measurable_fst.div_const 3
  · exact measurable_const
  · exact measurable_const

omit [InnerProductSpace ℝ E] in
lemma measurable_firstPilot {n : ℕ} (s : List (Fin n)) :
    Measurable (fun w : ℝ × (Fin n → E) => firstPilot w.1 w.2 s) := by
  induction s with
  | nil => exact measurable_const
  | cons i s ih =>
    simp only [firstPilot]
    exact Measurable.ite
      (measurableSet_lt measurable_const ((measurable_neighbors_card i).const_mul 2))
      ((measurable_pi_apply i).comp measurable_snd) ih

omit [InnerProductSpace ℝ E] in
lemma measurable_pilotCenter (n : ℕ) :
    Measurable (fun w : ℝ × (Fin n → E) => pilotCenter w.1 w.2) :=
  measurable_firstPilot (List.finRange n)

end OracleTemplate.RobustGradient
