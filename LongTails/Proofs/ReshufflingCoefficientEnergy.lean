import LongTails.Proofs.ReshufflingSymmetrization
import LongTails.Proofs.ReshufflingWordEnergy

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma permutation_finset_family_energy {I W : Type*} [Fintype I] [DecidableEq I]
    (A : I → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (s : Finset W) (words : W → List I) (m : ℕ) (hm : 2 ≤ m)
    (hw : ∀ w ∈ s, (words w).length = m) (x : E) :
    (Fintype.card I : ℝ) *
        |∑ w ∈ s, ∑ π : Equiv.Perm I,
          ⟪x, ((words w).map (fun i => A (π i))).prod x⟫| ≤
      s.card * (Fintype.card (Equiv.Perm I) : ℝ) * L ^ (m - 2) * ∑ i, ‖A i x‖ ^ 2 := by
  calc
    _ ≤ (Fintype.card I : ℝ) * ∑ w ∈ s,
        |∑ π : Equiv.Perm I, ⟪x, ((words w).map (fun i => A (π i))).prod x⟫| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ = ∑ w ∈ s, (Fintype.card I : ℝ) *
        |∑ π : Equiv.Perm I, ⟪x, ((words w).map (fun i => A (π i))).prod x⟫| :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _w ∈ s, (Fintype.card (Equiv.Perm I) : ℝ) *
        L ^ (m - 2) * ∑ i, ‖A i x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro w hws
      have he := permutation_full_word_energy A hL hs hA (words w) (by rw [hw w hws]; exact hm) x
      simpa only [hw w hws] using he
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma free_collision_energy {n : ℕ} (A : Fin n → E →L[ℝ] E) {L : ℝ}
    (hL : 0 ≤ L) (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (hA : ∀ i, ‖A i‖ ≤ L) (m : ℕ) (hm : 2 ≤ m) (x : E) :
    (n : ℝ) * |∑ f ∈ Finset.univ.filter (fun f : Fin m → Fin n => ¬Function.Injective f),
        ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫| ≤
      ((Finset.univ.filter (fun f : Fin m → Fin n => ¬Function.Injective f)).card : ℝ) *
        L ^ (m - 2) * ∑ i, ‖A i x‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun f : Fin m → Fin n => ¬Function.Injective f)
  have hr : ∀ π : Equiv.Perm (Fin n),
      (∑ f ∈ s, ⟪x, (List.ofFn (fun j => A (π (f j)))).prod x⟫) =
      ∑ f ∈ s, ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫ := by
    intro π
    simpa only [s, Finset.sum_filter, ite_not] using
      noninjective_relabel_sum m (fun f => ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫) π
  have he := permutation_finset_family_energy A hL hs hA s List.ofFn m hm
    (fun _ _ => List.length_ofFn) x
  simp only [List.map_ofFn, Function.comp_def, Fintype.card_fin] at he
  rw [Finset.sum_comm] at he
  simp_rw [hr] at he
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n))) : (0 : ℝ) ≤ _)] at he
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hc).mp
  convert he using 1 <;> ring

lemma repeated_two_word_average {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → E →L[ℝ] E) (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (w : List I) (hw : w.length = 2) (hr : ¬w.Nodup) (x : E) :
    (Fintype.card I : ℝ) *
        (∑ π : Equiv.Perm I, ⟪x, (w.map (fun i => A (π i))).prod x⟫) =
      (Fintype.card (Equiv.Perm I) : ℝ) * ∑ i, ‖A i x‖ ^ 2 := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hw
  have hab : a = b := by simpa using hr
  subst b
  have he : ∀ i, ⟪x, A i (A i x)⟫ = ‖A i x‖ ^ 2 := by
    intro i
    have hi : ⟪A i x, A i x⟫ = ⟪x, A i (A i x)⟫ := hs i x (A i x)
    rw [← hi, real_inner_self_eq_norm_sq]
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mul_apply_eq_comp, he] using permutation_marginal_sum (fun i => ‖A i x‖ ^ 2) a

lemma palindrome_repeated_two_energy {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (x : E) :
    (∑ π : Equiv.Perm (Fin n),
      ((((w ++ w.reverse).sublistsLen 2).filter (fun v => decide (¬v.Nodup))).map
        (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ i, ‖A i x‖ ^ 2 := by
  classical
  let family := ((w ++ w.reverse).sublistsLen 2).filter (fun v => decide (¬v.Nodup))
  have he : ∀ v ∈ family, (n : ℝ) *
      (∑ π : Equiv.Perm (Fin n), ⟪x, (v.map (fun i => A (π i))).prod x⟫) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ i, ‖A i x‖ ^ 2 := by
    intro v hv
    obtain ⟨hv, hr⟩ := List.mem_filter.mp hv
    simpa only [Fintype.card_fin] using repeated_two_word_average A hs v
      (List.length_of_sublistsLen hv) (of_decide_eq_true hr) x
  rw [finset_sum_list_sum]
  apply (mul_left_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne'))
  change (n : ℝ) * (family.map _).sum = _
  rw [← List.sum_map_mul_left]
  have hm : (family.map (fun v => (n : ℝ) *
      (∑ π : Equiv.Perm (Fin n), ⟪x, (v.map (fun i => A (π i))).prod x⟫))).sum =
      (family.length : ℝ) * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ∑ i, ‖A i x‖ ^ 2) := by
    rw [List.map_congr_left he]
    simp
  rw [hm, show (family.length : ℝ) = n by
    simpa only [family, hlen] using palindrome_repeated_two_count w hw]

lemma free_repeated_two_energy {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → E →L[ℝ] E) (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (x : E) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin 2 → I => ¬Function.Injective f),
      ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫) = ∑ i, ‖A i x‖ ^ 2 := by
  classical
  have hdiag : ∀ f : Fin 2 → I, ¬Function.Injective f → f 0 = f 1 := by
    intro f hf
    by_contra hn
    apply hf
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  let e : {f : Fin 2 → I // ¬Function.Injective f} ≃ I :=
    { toFun := fun f => f.val 0
      invFun := fun i => ⟨fun _ => i, fun h => by have heq := @h 0 1 rfl; exact (by decide : (0 : Fin 2) ≠ 1) heq⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext j
        fin_cases j
        · rfl
        · exact hdiag f.val f.property
      right_inv := fun _ => rfl }
  rw [Finset.sum_subtype (p := fun f : Fin 2 → I => ¬Function.Injective f) _ (by simp)]
  apply Fintype.sum_equiv e
  intro f
  have he : ∀ i, ⟪x, A i (A i x)⟫ = ‖A i x‖ ^ 2 := by
    intro i
    have hi : ⟪A i x, A i x⟫ = ⟪x, A i (A i x)⟫ := hs i x (A i x)
    rw [← hi, real_inner_self_eq_norm_sq]
  simp [List.ofFn_succ, hdiag f.val f.property, he, e, mul_apply_eq_comp]

lemma palindrome_repeated_energy_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (k : ℕ) (x : E) :
    |∑ π : Equiv.Perm (Fin n),
      ((((w ++ w.reverse).sublistsLen (k + 2)).filter (fun v => decide (¬v.Nodup))).map
        (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum| ≤
      4 * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (2 * n * L) ^ k * ∑ i, ‖A i x‖ ^ 2 := by
  classical
  let family := ((w ++ w.reverse).sublistsLen (k + 2)).filter (fun v => decide (¬v.Nodup))
  have he := permutation_family_energy A hL hs hA family (k + 2) (by omega)
    (fun v hv => List.length_of_sublistsLen (List.mem_filter.mp hv).1) x
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at he
  have hc : (family.length : ℝ) ≤ 2 * (2 * (n : ℝ)) ^ (k + 1) := by
    rw [show (family.length : ℝ) = _ by exact palindrome_repeated_count w hw (k + 2), hlen]
    exact palindrome_collision_le k n
  rw [finset_sum_list_sum]
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp
  calc
    _ ≤ (family.length : ℝ) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        L ^ k * ∑ i, ‖A i x‖ ^ 2 := he
    _ ≤ (2 * (2 * (n : ℝ)) ^ (k + 1)) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        L ^ k * ∑ i, ‖A i x‖ ^ 2 := by gcongr
    _ = _ := by rw [pow_succ, mul_pow]; ring

lemma free_scaled_collision_energy_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (k : ℕ) (x : E) :
    2 ^ (k + 2) / ((k + 2).factorial : ℝ) *
      |∑ f ∈ Finset.univ.filter (fun f : Fin (k + 2) → Fin n => ¬Function.Injective f),
        ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫| ≤
      4 * (2 * n * L) ^ k * ∑ i, ‖A i x‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun f : Fin (k + 2) → Fin n => ¬Function.Injective f)
  have hc : (s.card : ℝ) = (n : ℝ) ^ (k + 2) - n.descFactorial (k + 2) := by
    have ht := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (k + 2) → Fin n))) (p := Function.Injective)
    rw [injective_word_card] at ht
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at ht
    have hr : (n.descFactorial (k + 2) : ℝ) + s.card = (n : ℝ) ^ (k + 2) := by exact_mod_cast ht
    linarith
  have he := free_collision_energy A hL hs hA (k + 2) (by omega) x
  simp only [Nat.add_sub_cancel] at he
  have hscaled := mul_le_mul_of_nonneg_left he
    (show (0 : ℝ) ≤ 2 ^ (k + 2) / ((k + 2).factorial : ℝ) by positivity)
  have hb := scaled_free_collision_le k n
  rw [← hc] at hb
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp
  calc
    _ ≤ (2 ^ (k + 2) / ((k + 2).factorial : ℝ) * s.card) * L ^ k * ∑ i, ‖A i x‖ ^ 2 := by
      convert hscaled using 1 <;> ring
    _ ≤ (2 * (2 * (n : ℝ)) ^ (k + 1)) * L ^ k * ∑ i, ‖A i x‖ ^ 2 := by gcongr
    _ = _ := by rw [pow_succ, mul_pow]; ring

lemma free_power_energy {I : Type*} [Fintype I]
    (A : I → E →L[ℝ] E) (m : ℕ) (x : E) :
    (∑ f : Fin m → I, ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫) =
      ⟪x, ((∑ i, A i) ^ m) x⟫ := by
  rw [sum_power_words]
  simp only [sum_apply, inner_sum]

lemma palindrome_coefficient_remainder {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (hA : ∀ i, ‖A i‖ ≤ L)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (k : ℕ) (x : E) :
    |(∑ π : Equiv.Perm (Fin n),
      (((w ++ w.reverse).sublistsLen (k + 2)).map
        (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum) -
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 2 ^ (k + 2) / (k + 2).factorial *
        ⟪x, ((∑ i, A i) ^ (k + 2)) x⟫| ≤
      8 * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (2 * n * L) ^ k * ∑ i, ‖A i x‖ ^ 2 := by
  classical
  have hi := palindrome_coefficient_identity (fun v => ⟪x, (v.map A).prod x⟫) w hw hlen (k + 2)
  simp only [List.map_map, Function.comp_def, List.map_ofFn] at hi
  rw [free_power_energy] at hi
  have hr := palindrome_repeated_energy_bound hn A hL hs hA w hw hlen k x
  have hf := free_scaled_collision_energy_bound hn A hL hs hA k x
  let C : ℝ := Fintype.card (Equiv.Perm (Fin n))
  let a : ℝ := 2 ^ (k + 2) / ((k + 2).factorial : ℝ)
  let B : ℝ := ∑ f ∈ Finset.univ.filter (fun f : Fin (k + 2) → Fin n => ¬Function.Injective f),
    ⟪x, (List.ofFn (fun j => A (f j))).prod x⟫
  let R : ℝ := ∑ π : Equiv.Perm (Fin n),
    ((((w ++ w.reverse).sublistsLen (k + 2)).filter (fun v => decide (¬v.Nodup))).map
      (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum
  rw [hi]
  have he : C * 2 ^ (k + 2) / (k + 2).factorial *
      (⟪x, ((∑ i, A i) ^ (k + 2)) x⟫ - B) + R -
      C * 2 ^ (k + 2) / (k + 2).factorial * ⟪x, ((∑ i, A i) ^ (k + 2)) x⟫ = R - C * a * B := by
    dsimp [a]; ring
  change |C * 2 ^ (k + 2) / (k + 2).factorial *
      (⟪x, ((∑ i, A i) ^ (k + 2)) x⟫ - B) + R -
      C * 2 ^ (k + 2) / (k + 2).factorial * ⟪x, ((∑ i, A i) ^ (k + 2)) x⟫| ≤ _
  rw [he]
  have hc : 0 ≤ C := Nat.cast_nonneg _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  calc
    _ ≤ |R| + |C * a * B| := abs_sub _ _
    _ = |R| + C * (a * |B|) := by rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg ha]; ring
    _ ≤ 4 * C * (2 * n * L) ^ k * (∑ i, ‖A i x‖ ^ 2) +
        C * (4 * (2 * n * L) ^ k * ∑ i, ‖A i x‖ ^ 2) :=
      add_le_add hr (mul_le_mul_of_nonneg_left hf hc)
    _ = _ := by ring

lemma palindrome_coefficient_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → E →L[ℝ] E) (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (x : E) :
    (∑ π : Equiv.Perm (Fin n), (((w ++ w.reverse).sublistsLen 2).map
      (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        (2 * ⟪x, ((∑ i, A i) ^ 2) x⟫ - ∑ i, ‖A i x‖ ^ 2) := by
  have hi := palindrome_coefficient_identity (fun v => ⟪x, (v.map A).prod x⟫) w hw hlen 2
  simp only [List.map_map, Function.comp_def, List.map_ofFn] at hi
  rw [free_power_energy, free_repeated_two_energy A hs x,
    palindrome_repeated_two_energy hn A hs w hw hlen x] at hi
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num, show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] at hi
  rw [hi]
  ring

lemma repeated_small_empty {I : Type*} [DecidableEq I] (w : List I) (m : ℕ) (hm : m ≤ 1) :
    ((w.sublistsLen m).filter (fun v => decide (¬v.Nodup))) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro v hv
  have hlen := List.length_of_sublistsLen hv
  have hn : v.Nodup := by
    cases v with
    | nil => simp
    | cons a v =>
      cases v with
      | nil => simp
      | cons b v => simp only [List.length_cons] at hlen; omega
  simp [hn]

lemma palindrome_coefficient_one {n : ℕ}
    (A : Fin n → E →L[ℝ] E)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n) (x : E) :
    (∑ π : Equiv.Perm (Fin n), (((w ++ w.reverse).sublistsLen 1).map
      (fun v => ⟪x, (v.map (fun i => A (π i))).prod x⟫)).sum) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 2 * ⟪x, (∑ i, A i) x⟫ := by
  classical
  have hi := palindrome_coefficient_identity (fun v => ⟪x, (v.map A).prod x⟫) w hw hlen 1
  simp only [List.map_map, Function.comp_def, List.map_ofFn] at hi
  rw [free_power_energy, repeated_small_empty _ 1 le_rfl] at hi
  have hempty : Finset.univ.filter (fun f : Fin 1 → Fin n => ¬Function.Injective f) = ∅ := by
    ext f
    simp [Function.injective_of_subsingleton]
  simpa [hempty] using hi

end OracleTemplate.Reshuffling
