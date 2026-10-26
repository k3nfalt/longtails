import LongTails.Algorithms.LocalFiniteSumAcceleration
import LongTails.Proofs.SvrgConvex

namespace OracleTemplate.GeneralizedFiniteSum

lemma slotCount_pos {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    0 < slotCount w i := by
  unfold slotCount
  omega

lemma slotTotal_lower {n : ℕ} (w : Fin n → ℝ) : n ≤ slotTotal w := by
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i, slotCount w i := Finset.sum_le_sum fun i _ => slotCount_pos w i

lemma slotTotal_upper {n : ℕ} (w : Fin n → ℝ) : slotTotal w ≤ 2 * n := by
  classical
  let W := ∑ i, max 0 (w i)
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => le_max_left _ _
  have hsum : (∑ i, (n : ℝ) * max 0 (w i) / W) ≤ n := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change (n : ℝ) * W / W ≤ n
    by_cases hz : W = 0
    · simp [hz]
    · rw [mul_div_cancel_right₀ _ hz]
  have hc (i : Fin n) : (slotCount w i : ℝ) ≤ (n : ℝ) * max 0 (w i) / W + 1 := by
    unfold slotCount
    push_cast
    have hf := Nat.floor_le (div_nonneg (mul_nonneg (Nat.cast_nonneg n)
      (le_max_left 0 (w i))) hW)
    change (⌊(n : ℝ) * max 0 (w i) / W⌋₊ : ℝ) + 1 ≤ _
    linarith
  have ht : (slotTotal w : ℝ) ≤ 2 * n := by
    calc
      (slotTotal w : ℝ) = ∑ i, (slotCount w i : ℝ) := by simp [slotTotal]
      _ ≤ ∑ i, ((n : ℝ) * max 0 (w i) / W + 1) := Finset.sum_le_sum fun i _ => hc i
      _ = (∑ i, (n : ℝ) * max 0 (w i) / W) + n := by rw [Finset.sum_add_distrib]; simp
      _ ≤ 2 * n := by linarith
  exact_mod_cast ht

lemma slotTotal_factorial {n : ℕ} [NeZero n] (w : Fin n → ℝ) :
    0 < slotTotal w ∧ slotTotal w ∣ (2 * n).factorial := by
  have hp : 0 < slotTotal w := lt_of_lt_of_le (NeZero.pos n) (slotTotal_lower w)
  exact ⟨hp, Nat.dvd_factorial hp (slotTotal_upper w)⟩

lemma drawIndex_sum {n : ℕ} [NeZero n] {V : Type*} [AddCommMonoid V]
    (w : Fin n → ℝ) (f : Fin n → V) :
    ∑ seed : Fin ((2 * n).factorial), f (drawIndex w seed) =
      ((2 * n).factorial / slotTotal w) • ∑ i, slotCount w i • f i := by
  classical
  let D := slotTotal w
  let M := (2 * n).factorial
  have h := slotTotal_factorial w
  let e : Fin D × Fin (M / D) ≃ Fin M :=
    finProdFinEquiv.trans (finCongr (Nat.mul_div_cancel' h.2))
  let g : Fin D → V := fun j => f ((finSigmaFinEquiv (n := slotCount w)).symm j).1
  have hd : ∀ seed : Fin M, f (drawIndex w seed) = g (e.symm seed).1 := by
    intro seed
    simp only [drawIndex, dite_eq_left h]
    rfl
  have hs : ∑ j : Fin D, g j = ∑ i, slotCount w i • f i := by
    calc
      _ = ∑ j : (i : Fin n) × Fin (slotCount w i), f j.1 :=
        Fintype.sum_equiv (finSigmaFinEquiv (n := slotCount w)).symm _ _ (fun _ => rfl)
      _ = _ := by rw [Fintype.sum_sigma]; simp
  calc
    _ = ∑ seed : Fin M, g (e.symm seed).1 := Finset.sum_congr rfl (fun seed _ => hd seed)
    _ = ∑ p : Fin D × Fin (M / D), g p.1 :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    _ = (M / D) • ∑ j : Fin D, g j := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.smul_sum]
    _ = _ := by rw [hs]

lemma drawIndex_mean {n : ℕ} [NeZero n] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : Fin n → ℝ) (f : Fin n → V) :
    ((2 * n).factorial : ℝ)⁻¹ • (∑ seed : Fin ((2 * n).factorial), f (drawIndex w seed)) =
      ∑ i, ((slotCount w i : ℝ) / slotTotal w) • f i := by
  classical
  have h := slotTotal_factorial w
  have hD : (slotTotal w : ℝ) ≠ 0 := by exact_mod_cast h.1.ne'
  have hM : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hmul : (slotTotal w : ℝ) * (((2 * n).factorial / slotTotal w : ℕ) : ℝ) =
      (2 * n).factorial := by exact_mod_cast Nat.mul_div_cancel' h.2
  rw [drawIndex_sum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  field_simp
  nlinarith

lemma direction_unbiased {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : Fin n → ℝ) (cached reply : Fin n → E) :
    ((2 * n).factorial : ℝ)⁻¹ •
      (∑ seed : Fin ((2 * n).factorial),
        direction w cached (drawIndex w seed) (reply (drawIndex w seed))) =
      (n : ℝ)⁻¹ • ∑ i, reply i := by
  classical
  rw [drawIndex_mean w (fun i => direction w cached i (reply i))]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hD : (slotTotal w : ℝ) ≠ 0 := by exact_mod_cast (slotTotal_factorial w).1.ne'
  have hc (i : Fin n) : (slotCount w i : ℝ) ≠ 0 := by exact_mod_cast (slotCount_pos w i).ne'
  have hs : ∑ i, ((slotCount w i : ℝ) / slotTotal w) = 1 := by
    rw [← Finset.sum_div]
    rw [← Nat.cast_sum]
    change (slotTotal w : ℝ) / slotTotal w = 1
    exact div_self hD
  simp only [direction, smul_add, smul_smul, Finset.sum_add_distrib]
  have he (i : Fin n) : (slotCount w i : ℝ) / slotTotal w *
      ((slotTotal w : ℝ) / ((n : ℝ) * slotCount w i)) = (n : ℝ)⁻¹ := by
    field_simp [hc i]
  simp_rw [he]
  rw [← Finset.sum_smul, ← Finset.sum_mul, hs, one_mul, ← Finset.smul_sum,
    Finset.sum_sub_distrib, smul_sub]
  abel

lemma inverse_weight_bound {n : ℕ} [NeZero n] (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    (slotTotal w : ℝ) / ((n : ℝ) * slotCount w i) * w i ≤
      2 * ((∑ j, w j) / n) := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hc : (0 : ℝ) < slotCount w i := by exact_mod_cast slotCount_pos w i
  have hW : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => hw j
  have hD : (slotTotal w : ℝ) ≤ 2 * n := by exact_mod_cast slotTotal_upper w
  have hm : ∀ j, max 0 (w j) = w j := fun j => max_eq_right (hw j)
  by_cases hz : ∑ j, w j = 0
  · have hi : w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp hz i (Finset.mem_univ i)
    simp [hi, hz]
  have hWp : 0 < ∑ j, w j := lt_of_le_of_ne hW (Ne.symm hz)
  have hf := Nat.lt_floor_add_one ((n : ℝ) * w i / (∑ j, w j))
  have hci : (n : ℝ) * w i ≤ slotCount w i * (∑ j, w j) := by
    have hh : (n : ℝ) * w i / (∑ j, w j) ≤ (slotCount w i : ℝ) := by
      simpa only [slotCount, hm, Nat.cast_add, Nat.cast_one] using le_of_lt hf
    exact (div_le_iff₀ hWp).mp hh
  rw [show 2 * ((∑ j, w j) / (n : ℝ)) = (2 * ∑ j, w j) / n by ring]
  apply (le_div_iff₀ hn).mpr
  have he : (slotTotal w : ℝ) / ((n : ℝ) * slotCount w i) * w i * n =
      slotTotal w * w i / slotCount w i := by field_simp
  rw [he]
  apply (div_le_iff₀ hc).mpr
  nlinarith [mul_le_mul_of_nonneg_right hD (hw i)]

lemma importance_second_moment {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (w : Fin n → ℝ) (d : Fin n → E) (H : Fin n → ℝ) (C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hH : ∀ i, 0 ≤ H i) (hC : 0 ≤ C)
    (hd : ∀ i, ‖d i‖ ^ 2 ≤ C * w i * H i) :
    ((2 * n).factorial : ℝ)⁻¹ *
      (∑ seed : Fin ((2 * n).factorial),
        ‖((slotTotal w : ℝ) / ((n : ℝ) * slotCount w (drawIndex w seed))) •
          d (drawIndex w seed)‖ ^ 2) ≤
      2 * C * ((∑ i, w i) / n) * ((∑ i, H i) / n) := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hD : (0 : ℝ) < slotTotal w := by exact_mod_cast (slotTotal_factorial w).1
  have hc (i : Fin n) : (0 : ℝ) < slotCount w i := by exact_mod_cast slotCount_pos w i
  let c := fun i => (slotTotal w : ℝ) / ((n : ℝ) * slotCount w i)
  have hc0 (i : Fin n) : 0 ≤ c i := by dsimp [c]; positivity
  have hp (i : Fin n) :
      ((slotCount w i : ℝ) / slotTotal w) * ‖c i • d i‖ ^ 2 ≤
        (2 * C * ((∑ j, w j) / n) / n) * H i := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have he : (slotCount w i : ℝ) / slotTotal w * c i ^ 2 = c i / n := by
      dsimp [c]
      field_simp
    rw [← mul_assoc, he]
    calc
      _ ≤ (c i / n) * (C * w i * H i) :=
        mul_le_mul_of_nonneg_left (hd i) (div_nonneg (hc0 i) hn.le)
      _ = (c i * w i) * (C * H i / n) := by ring
      _ ≤ (2 * ((∑ j, w j) / n)) * (C * H i / n) :=
        mul_le_mul_of_nonneg_right (inverse_weight_bound w hw i)
          (div_nonneg (mul_nonneg hC (hH i)) hn.le)
      _ = _ := by ring
  have hm := drawIndex_mean w (fun i => ‖c i • d i‖ ^ 2)
  simp only [smul_eq_mul] at hm
  change ((2 * n).factorial : ℝ)⁻¹ * (∑ seed, ‖c (drawIndex w seed) • d (drawIndex w seed)‖ ^ 2) ≤ _
  rw [hm]
  calc
    _ ≤ ∑ i, (2 * C * ((∑ j, w j) / n) / n) * H i := Finset.sum_le_sum fun i _ => hp i
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma direction_variance {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : Fin n → ℝ) (cached reply : Fin n → E)
    (H : Fin n → ℝ) (C : ℝ) (hw : ∀ i, 0 ≤ w i) (hH : ∀ i, 0 ≤ H i)
    (hC : 0 ≤ C) (hd : ∀ i, ‖reply i - cached i‖ ^ 2 ≤ C * w i * H i) :
    ((2 * n).factorial : ℝ)⁻¹ *
      (∑ seed : Fin ((2 * n).factorial),
        ‖direction w cached (drawIndex w seed) (reply (drawIndex w seed)) -
          (n : ℝ)⁻¹ • ∑ i, reply i‖ ^ 2) ≤
      2 * C * ((∑ i, w i) / n) * ((∑ i, H i) / n) := by
  classical
  let d := fun i => reply i - cached i
  let v := fun seed : Fin ((2 * n).factorial) =>
    ((slotTotal w : ℝ) / ((n : ℝ) * slotCount w (drawIndex w seed))) • d (drawIndex w seed)
  have hm : ((2 * n).factorial : ℝ)⁻¹ • ∑ seed, v seed = (n : ℝ)⁻¹ • ∑ i, d i := by
    have h := direction_unbiased w (fun _ => (0 : E)) d
    simpa only [direction, Finset.sum_const_zero, smul_zero, zero_add, sub_zero] using h
  have he (seed : Fin ((2 * n).factorial)) :
      direction w cached (drawIndex w seed) (reply (drawIndex w seed)) -
        (n : ℝ)⁻¹ • ∑ i, reply i =
      v seed - ((2 * n).factorial : ℝ)⁻¹ • ∑ j, v j := by
    rw [hm]
    simp only [direction, d, Finset.sum_sub_distrib, smul_sub, v]
    abel
  simp_rw [he]
  let : NeZero (2 * n).factorial := ⟨Nat.factorial_ne_zero _⟩
  have hv := FiniteSum.centered_second_moment v
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_inv_mul] at hv
  exact hv.trans (importance_second_moment w d H C hw hH hC hd)

lemma direction_norm {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : Fin n → ℝ) (cached reply : Fin n → E)
    (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hr : 0 ≤ r)
    (hd : ∀ i, ‖reply i - cached i‖ ≤ 2 * w i * r) (i : Fin n) :
    ‖direction w cached i (reply i)‖ ≤
      ‖(n : ℝ)⁻¹ • ∑ j, cached j‖ + 4 * ((∑ j, w j) / n) * r := by
  let c := (slotTotal w : ℝ) / ((n : ℝ) * slotCount w i)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hh := mul_le_mul_of_nonneg_left (hd i) hc
  have hb := mul_le_mul_of_nonneg_right (inverse_weight_bound w hw i) (show 0 ≤ 2 * r by positivity)
  have hv : ‖c • (reply i - cached i)‖ ≤ 4 * ((∑ j, w j) / n) * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    dsimp [c] at hh ⊢
    nlinarith only [hh, hb]
  exact (norm_add_le _ _).trans (by linarith only [hv])

end OracleTemplate.GeneralizedFiniteSum
