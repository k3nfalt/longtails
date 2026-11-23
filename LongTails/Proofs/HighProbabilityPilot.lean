import LongTails.Algorithms.HighProbabilityStationarity
import LongTails.Proofs.RobustPilot
import LongTails.Proofs.AdaptivePilotConfidence

open MeasureTheory

namespace LongTails.Proofs.HighProbabilityPilot

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma qualifies_of_majority {m : ℕ} {B s : ℝ} {k : ℕ} (v : Fin m → E) (u : E)
    (hk : 6 * s ≤ 2 ^ k * B)
    (hmaj : m < 2 * (Finset.univ.filter (fun i => ‖v i - u‖ ≤ s)).card) :
    qualifies B v k := by
  classical
  have hne : (Finset.univ.filter (fun i => ‖v i - u‖ ≤ s)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))⟩
  intro j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have he : v i - v j = (v i - u) + (u - v j) := by abel
  rw [he]
  have ht := norm_add_le (v i - u) (u - v j)
  rw [norm_sub_rev u] at ht
  linarith

omit [InnerProductSpace ℝ E] in
lemma pilotCenter_close {m : ℕ} {B s : ℝ} (v : Fin m → E) (u : E)
    (hq : ∃ i, m < 2 * (neighbors B v i).card)
    (hmaj : m < 2 * (Finset.univ.filter (fun i => ‖v i - u‖ ≤ s)).card) :
    ‖pilotCenter B v - u‖ ≤ B / 3 + s := by
  classical
  obtain ⟨i, hi⟩ := hq
  obtain ⟨j, _, hj, hout⟩ := firstPilot_selected B v (List.finRange m) ⟨i, by simp, hi⟩
  obtain ⟨l, hl, hlgood⟩ := majorities_intersect (neighbors B v j) _ hj hmaj
  have hjl : ‖v j - v l‖ ≤ B / 3 := (Finset.mem_filter.mp hl).2
  have hlu : ‖v l - u‖ ≤ s := (Finset.mem_filter.mp hlgood).2
  rw [pilotCenter, hout]
  have he : v j - u = (v j - v l) + (v l - u) := by abel
  rw [he]
  have ht := norm_add_le (v j - v l) (v l - u)
  linarith

omit [InnerProductSpace ℝ E] in
lemma gradedPilot_close {m : ℕ} {B s : ℝ} {K : ℕ} (v : Fin m → E) (u fb : E)
    (hs : B ≤ 12 * s) (hK : 6 * s ≤ 2 ^ K * B)
    (hmaj : m < 2 * (Finset.univ.filter (fun i => ‖v i - u‖ ≤ s)).card) :
    ‖gradedPilot B K v fb - u‖ ≤ 5 * s := by
  classical
  have hex : ∃ k, 6 * s ≤ 2 ^ k * B := ⟨K, hK⟩
  set k0 := Nat.find hex with hk0def
  have hk0 : 6 * s ≤ 2 ^ k0 * B := Nat.find_spec hex
  have hk0K : k0 ≤ K := Nat.find_min' hex hK
  have hq0 : qualifies B v k0 := qualifies_of_majority v u hk0 hmaj
  have hh : ∃ k, k ≤ K ∧ qualifies B v k := ⟨k0, hk0K, hq0⟩
  have hlevel : gradedLevel B K v = some (Nat.find hh) := by
    simp only [gradedLevel, dite_eq_left hh]
  have hsmall : Nat.find hh ≤ k0 := Nat.find_min' hh ⟨hk0K, hq0⟩
  have hspec := (Nat.find_spec hh).2
  have hval : gradedPilot B K v fb = pilotCenter (2 ^ Nat.find hh * B) v := by
    simp only [gradedPilot, hlevel]
  rw [hval]
  have hc := pilotCenter_close (B := 2 ^ Nat.find hh * B) v u hspec hmaj
  have hB0 : 0 ≤ B := by
    by_contra hneg
    push Not at hneg
    have : 2 ^ K * B < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    have : 0 ≤ s := by
      have := (Finset.univ.filter (fun i => ‖v i - u‖ ≤ s)).card_pos.mp (by omega)
      obtain ⟨i, hi⟩ := this
      exact (norm_nonneg _).trans (Finset.mem_filter.mp hi).2
    linarith
  have hmono : 2 ^ Nat.find hh * B ≤ 2 ^ k0 * B :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hsmall) hB0
  have hk0b : 2 ^ k0 * B ≤ 12 * s := by
    rcases Nat.eq_zero_or_pos k0 with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hs
    · obtain ⟨k, hk⟩ : ∃ k, k0 = k + 1 := ⟨k0 - 1, by omega⟩
      have hnot : ¬ (6 * s ≤ 2 ^ k * B) := Nat.find_min hex (by omega)
      push Not at hnot
      rw [hk, pow_succ]
      nlinarith
  linarith

omit [InnerProductSpace ℝ E] in
lemma gradedPilot_ok {m : ℕ} {B : ℝ} {K : ℕ} (v : Fin m → E) (u fb : E)
    (hmaj : m < 2 * (Finset.univ.filter (fun i => ‖v i - u‖ ≤ B / 6)).card) :
    ‖gradedPilot B K v fb - u‖ ≤ B / 2 := by
  classical
  have hq0 : qualifies B v 0 := qualifies_of_majority v u (by simp; linarith) hmaj
  have hh : ∃ k, k ≤ K ∧ qualifies B v k := ⟨0, Nat.zero_le _, hq0⟩
  have hzero : Nat.find hh = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' hh ⟨Nat.zero_le _, hq0⟩)
  have hval : gradedPilot B K v fb = pilotCenter B v := by
    simp only [gradedPilot, gradedLevel, dite_eq_left hh, hzero, pow_zero, one_mul]
  rw [hval]
  exact pilotCenter_accuracy v u hmaj

instance optionNatMeasurable : MeasurableSpace (Option ℕ) := ⊤

instance optionNatDiscrete : DiscreteMeasurableSpace (Option ℕ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] in
lemma measurableSet_qualifies {m : ℕ} (B : ℝ) (k : ℕ) :
    MeasurableSet {v : Fin m → E | qualifies B v k} := by
  classical
  have h : {v : Fin m → E | qualifies B v k} =
      ⋃ i : Fin m, {v | m < 2 * (neighbors (2 ^ k * B) v i).card} := by
    ext v
    simp [qualifies]
  rw [h]
  refine MeasurableSet.iUnion fun i => ?_
  have hm : Measurable (fun v : Fin m → E => (neighbors (2 ^ k * B) v i).card) :=
    (measurable_neighbors_card i).comp (measurable_const.prodMk measurable_id)
  exact measurableSet_lt measurable_const (hm.const_mul 2)

omit [InnerProductSpace ℝ E] in
lemma measurable_gradedLevel {m : ℕ} (B : ℝ) (K : ℕ) :
    Measurable (fun v : Fin m → E => gradedLevel B K v) := by
  classical
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
    have h : (fun v : Fin m → E => gradedLevel B K v) ⁻¹' {none} =
        ⋂ k ∈ Finset.range (K + 1), {v | ¬ qualifies B v k} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, gradedLevel, Set.mem_iInter,
        Finset.mem_range, Set.mem_ofPred_eq]
      constructor
      · intro hv k hk hqk
        have hh : ∃ k, k ≤ K ∧ qualifies B v k := ⟨k, by omega, hqk⟩
        simp [dite_eq_left hh] at hv
      · intro hv
        have hh : ¬ ∃ k, k ≤ K ∧ qualifies B v k := fun ⟨k, hk, hqk⟩ => hv k (by omega) hqk
        simp [dite_eq_right hh]
    rw [h]
    exact Finset.measurableSet_biInter _ fun k _ => (measurableSet_qualifies B k).compl
  | some k =>
    by_cases hk : k ≤ K
    · have h : (fun v : Fin m → E => gradedLevel B K v) ⁻¹' {some k} =
          {v | qualifies B v k} ∩ ⋂ j ∈ Finset.range k, {v | ¬ qualifies B v j} := by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff, gradedLevel, Set.mem_inter_iff,
          Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
        constructor
        · intro hv
          by_cases hh : ∃ k, k ≤ K ∧ qualifies B v k
          · simp only [dite_eq_left hh, Option.some.injEq] at hv
            subst hv
            exact ⟨(Nat.find_spec hh).2, fun j hj hqj =>
              Nat.find_min hh hj ⟨le_trans hj.le (Nat.find_spec hh).1, hqj⟩⟩
          · simp [dite_eq_right hh] at hv
        · rintro ⟨hqk, hmin⟩
          have hh : ∃ k, k ≤ K ∧ qualifies B v k := ⟨k, hk, hqk⟩
          simp only [dite_eq_left hh, Option.some.injEq]
          apply le_antisymm (Nat.find_min' hh ⟨hk, hqk⟩)
          by_contra hlt
          push Not at hlt
          exact hmin _ hlt (Nat.find_spec hh).2
      rw [h]
      exact (measurableSet_qualifies B k).inter
        (Finset.measurableSet_biInter _ fun j _ => (measurableSet_qualifies B j).compl)
    · have h : (fun v : Fin m → E => gradedLevel B K v) ⁻¹' {some k} = ∅ := by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff, gradedLevel, Set.mem_empty_iff_false,
          iff_false]
        intro hv
        by_cases hh : ∃ k, k ≤ K ∧ qualifies B v k
        · simp only [dite_eq_left hh, Option.some.injEq] at hv
          exact hk (hv ▸ (Nat.find_spec hh).1)
        · simp [dite_eq_right hh] at hv
      rw [h]
      exact MeasurableSet.empty

omit [InnerProductSpace ℝ E] in
lemma measurable_gradedPilot {m : ℕ} (B : ℝ) (K : ℕ) (fb : E) :
    Measurable (fun v : Fin m → E => gradedPilot B K v fb) := by
  let F : Option ℕ × (Fin m → E) → E := fun w =>
    match w.1 with
    | some k => pilotCenter (2 ^ k * B) w.2
    | none => fb
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro o
    cases o with
    | none => exact measurable_const
    | some k => exact (measurable_pilotCenter m).comp (measurable_const.prodMk measurable_id)
  have he : (fun v : Fin m → E => gradedPilot B K v fb) = fun v => F (gradedLevel B K v, v) := by
    funext v
    simp only [gradedPilot, F]
    cases gradedLevel B K v <;> rfl
  rw [he]
  exact hF.comp ((measurable_gradedLevel B K).prodMk measurable_id)

end LongTails.Proofs.HighProbabilityPilot
