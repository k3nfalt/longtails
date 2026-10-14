import LongTails.Proofs.ReshufflingWordEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma one_add_pow_le_two {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (hmt : (m : ℝ) * t ≤ 1 / 2) : (1 + t) ^ m ≤ 2 := by
  calc
    _ ≤ (Real.exp t) ^ m := pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp t) m
    _ = Real.exp ((m : ℝ) * t) := (Real.exp_nat_mul t m).symm
    _ ≤ 1 / (1 - (m : ℝ) * t) :=
      Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)
    _ ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)

lemma step_operator_norm (A : E →L[ℝ] E) {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hA : ‖A‖ ≤ L) :
    ‖1 + (-η) • A‖ ≤ 1 + η * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖x + (-η) • A x‖ ≤ _
  calc
    _ ≤ ‖x‖ + ‖(-η) • A x‖ := norm_add_le _ _
    _ = ‖x‖ + η * ‖A x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη]
    _ ≤ ‖x‖ + η * (L * ‖x‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) hη)
    _ = _ := by ring

lemma step_product_norm (A : I → E →L[ℝ] E) {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hA : ∀ i, ‖A i‖ ≤ L)
    (w : List I) (hstep : (w.length : ℝ) * (η * L) ≤ 1 / 2) :
    ‖(w.map (fun i => 1 + (-η) • A i)).prod‖ ≤ 2 := by
  exact (norm_word_le _ (by positivity) (fun i => step_operator_norm (A i) hL hη (hA i)) w).trans
    (one_add_pow_le_two (mul_nonneg hη hL) w.length hstep)

lemma norm_product_difference (A B : I → E →L[ℝ] E) {M : ℝ}
    (hM : 1 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ i, ‖B i‖ ≤ M) (w : List I) :
    ‖(w.map A).prod - (w.map B).prod‖ ≤
      M ^ w.length * (w.map (fun i => ‖A i - B i‖)).sum := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
    have hd : 0 ≤ (w.map (fun j => ‖A j - B j‖)).sum :=
      List.sum_nonneg (by intro r hr; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr; exact norm_nonneg _)
    calc
      _ = ‖A i * ((w.map A).prod - (w.map B).prod) + (A i - B i) * (w.map B).prod‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖A i * ((w.map A).prod - (w.map B).prod)‖ + ‖(A i - B i) * (w.map B).prod‖ := norm_add_le _ _
      _ ≤ ‖A i‖ * ‖(w.map A).prod - (w.map B).prod‖ + ‖A i - B i‖ * ‖(w.map B).prod‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * (M ^ w.length * (w.map (fun j => ‖A j - B j‖)).sum) +
          ‖A i - B i‖ * M ^ w.length := by
        exact add_le_add (mul_le_mul (hA i) ih (norm_nonneg _) hM0)
          (mul_le_mul_of_nonneg_left (norm_word_le B hM0 hB w) (norm_nonneg _))
      _ ≤ M * (M ^ w.length * (w.map (fun j => ‖A j - B j‖)).sum) +
          M * (‖A i - B i‖ * M ^ w.length) := by
        apply add_le_add le_rfl
        exact le_mul_of_one_le_left (by positivity) hM
      _ = _ := by rw [pow_succ]; ring

lemma step_difference_norm (A B : E →L[ℝ] E) {L η : ℝ}
    (hη : 0 ≤ η) (hA : ‖A‖ ≤ L) (hB : ‖B‖ ≤ L) :
    ‖(1 + (-η) • A) - (1 + (-η) • B)‖ ≤ 2 * η * L := by
  rw [show (1 + (-η) • A) - (1 + (-η) • B) = (-η) • (A - B) by module,
    norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη]
  calc
    _ ≤ η * (‖A‖ + ‖B‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hη
    _ ≤ η * (L + L) := mul_le_mul_of_nonneg_left (add_le_add hA hB) hη
    _ = _ := by ring

lemma swap_difference_sum [DecidableEq I] (A : I → E →L[ℝ] E) {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hA : ∀ i, ‖A i‖ ≤ L) (a b : I) (w : List I) :
    (w.map (fun i => ‖(1 + (-η) • A i) - (1 + (-η) • A (Equiv.swap a b i))‖)).sum ≤
      2 * η * L * ((w.count a : ℝ) + w.count b) := by
  have hd : ∀ i, ‖(1 + (-η) • A i) - (1 + (-η) • A (Equiv.swap a b i))‖ ≤ 2 * η * L :=
    fun i => step_difference_norm _ _ hη (hA i) (hA _)
  have hd0 : 0 ≤ 2 * η * L := by positivity
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hia : i = a
    · subst i
      by_cases hab : a = b
      · subst b
        simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one]
        nlinarith [hd a]
      · simp only [List.count_cons_self, List.count_cons_of_ne hab, Nat.cast_add, Nat.cast_one]
        nlinarith [hd a]
    · by_cases hib : i = b
      · subst i
        simp only [List.count_cons_self, List.count_cons_of_ne hia, Nat.cast_add, Nat.cast_one]
        nlinarith [hd b]
      · simp only [Equiv.swap_apply_of_ne_of_ne hia hib, sub_self, norm_zero, zero_add]
        simpa [List.count_cons, hia, hib, Ne.symm hia, Ne.symm hib] using ih

lemma swap_product_difference [DecidableEq I] (A : I → E →L[ℝ] E) {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hA : ∀ i, ‖A i‖ ≤ L) (a b : I) (w : List I)
    (hstep : (w.length : ℝ) * (η * L) ≤ 1 / 2) (hcount : w.count a + w.count b ≤ 4) :
    ‖(w.map (fun i => 1 + (-η) • A i)).prod -
      (w.map (fun i => 1 + (-η) • A (Equiv.swap a b i))).prod‖ ≤ 16 * η * L := by
  have hb := norm_product_difference (fun i => 1 + (-η) • A i)
    (fun i => 1 + (-η) • A (Equiv.swap a b i)) (show 1 ≤ 1 + η * L by nlinarith [mul_nonneg hη hL])
    (fun i => step_operator_norm _ hL hη (hA i))
    (fun i => step_operator_norm _ hL hη (hA _)) w
  have hp := one_add_pow_le_two (mul_nonneg hη hL) w.length hstep
  have hd := swap_difference_sum A hL hη hA a b w
  have hc : (w.count a : ℝ) + w.count b ≤ 4 := by exact_mod_cast hcount
  calc
    _ ≤ _ := hb
    _ ≤ 2 * (2 * η * L * ((w.count a : ℝ) + w.count b)) :=
      mul_le_mul hp hd (List.sum_nonneg (by intro r hr; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; positivity)) (by norm_num)
    _ ≤ 2 * (2 * η * L * 4) := by gcongr
    _ = _ := by ring

end OracleTemplate.Reshuffling
