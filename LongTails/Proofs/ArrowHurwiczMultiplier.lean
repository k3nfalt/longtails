import LongTails.Proofs.ArrowHurwiczSpectral
import LongTails.Proofs.ArrowHurwiczToeplitz

open Real Finset

namespace OracleTemplate.ArrowHurwicz

noncomputable def bandU (T : ℕ) (k : ℤ) : ℝ :=
  (if 2 ≤ k ∧ k ≤ T + 1 then max (bandKer (k - 1)) 0 else 0) +
    (if -(T : ℤ) ≤ k ∧ k ≤ -1 then max (-bandKer (-k)) 0 else 0)

noncomputable def bandMass (T : ℕ) : ℝ := ∑ k ∈ win (3 * T + 3), bandU T k

noncomputable def bandBeta (T : ℕ) : ℝ := 2 / (bandKer 0 - bandMass T)

noncomputable def bandH (T : ℕ) (k : ℤ) : ℝ :=
  (if k = 0 then 1 + bandBeta T * bandMass T else 0) - (if k = 1 then 1 else 0) - bandBeta T * bandU T k

lemma bandU_nonneg (T : ℕ) (k : ℤ) : 0 ≤ bandU T k := by
  unfold bandU; apply add_nonneg <;> split_ifs <;> simp

lemma bandU_supp (T : ℕ) (k : ℤ) (hk : bandU T k ≠ 0) : 2 ≤ k ∧ k ≤ T + 1 ∨ -(T : ℤ) ≤ k ∧ k ≤ -1 := by
  unfold bandU at hk; split_ifs at hk with h1 h2 <;> simp_all

lemma bandU_sums (T : ℕ) :
    bandMass T = ∑ i ∈ range T, |bandCoef (i + 1)| ∧
      ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k ≤ ∑ i ∈ range T, ((i : ℝ) + 2) * |bandCoef (i + 1)| := by
  set Up : ℤ → ℝ := fun k => if 2 ≤ k ∧ k ≤ T + 1 then max (bandKer (k - 1)) 0 else 0
  set Um : ℤ → ℝ := fun k => if -(T : ℤ) ≤ k ∧ k ≤ -1 then max (-bandKer (-k)) 0 else 0
  have hU : ∀ k, bandU T k = Up k + Um k := fun k => rfl
  have sP : ∀ f : ℤ → ℝ, ∑ k ∈ win (3 * T + 3), f k * Up k = ∑ i ∈ range T, f (2 + i) * max (bandCoef (i + 1)) 0 := by
    intro f
    rw [win_sum_range (3 * T + 3) 2 T _ (by
      intro k hk
      by_contra hc
      apply hk; simp only [Up]; rw [ite_eq_right (by omega)]; simp) (by omega) (by omega)]
    apply sum_congr rfl; intro i hi
    have hi' := mem_range.mp hi
    simp only [Up]; rw [ite_eq_left (by omega)]
    rw [show (2 + (i : ℤ)) - 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring, bandKer_nat]
  have sM : ∀ f : ℤ → ℝ, ∑ k ∈ win (3 * T + 3), f k * Um k = ∑ i ∈ range T, f (-(i : ℤ) - 1) * max (-bandCoef (i + 1)) 0 := by
    intro f
    rw [win_sum_range (3 * T + 3) (-(T : ℤ)) T _ (by
      intro k hk
      by_contra hc
      apply hk; simp only [Um]; rw [ite_eq_right (by omega)]; simp) (by omega) (by omega)]
    rw [← sum_range_reflect]
    apply sum_congr rfl; intro i hi
    have hi' := mem_range.mp hi
    simp only [Um]; rw [ite_eq_left (by omega)]
    have e : -(T : ℤ) + ((T - 1 - i : ℕ) : ℤ) = -(i : ℤ) - 1 := by omega
    rw [e, show -(-(i : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring, bandKer_nat]
  have hab : ∀ a : ℝ, max a 0 + max (-a) 0 = |a| := by
    intro a; rcases le_total 0 a with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  constructor
  · unfold bandMass
    simp_rw [hU, sum_add_distrib]
    have h1 := sP (fun _ => 1); have h2 := sM (fun _ => 1)
    simp only [one_mul] at h1 h2
    rw [h1, h2, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => hab _
  · simp_rw [hU, mul_add, sum_add_distrib]
    rw [sP, sM, ← sum_add_distrib]
    apply sum_le_sum; intro i _
    have e1 : |((2 + (i : ℤ) : ℤ) : ℝ)| = (i : ℝ) + 2 := by
      push_cast; rw [abs_of_nonneg (by positivity)]; ring
    have e2 : |((-(i : ℤ) - 1 : ℤ) : ℝ)| = (i : ℝ) + 1 := by
      push_cast; rw [abs_of_nonpos (by linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])]; ring
    rw [e1, e2, ← hab (bandCoef (i + 1))]
    have := le_max_right (-bandCoef (i + 1)) 0
    nlinarith

lemma bandBeta_facts (T : ℕ) :
    0 < bandBeta T ∧ bandBeta T * (bandKer 0 - bandMass T) = 2 ∧ bandBeta T * bandMass T ≤ 4.86 ∧
      bandBeta T * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k ≤ 13.79 := by
  obtain ⟨e1, e2⟩ := bandU_sums T
  obtain ⟨s1, s2⟩ := bandCoef_sum_le T
  have c0 : 0.415 ≤ bandKer 0 := by rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, bandKer_nat]; exact bandCoef_zero_ge
  have hm : 0 ≤ bandMass T := by unfold bandMass; exact sum_nonneg fun k _ => bandU_nonneg T k
  have hd : 0.121 ≤ bandKer 0 - bandMass T := by rw [e1]; linarith
  have hdpos : 0 < bandKer 0 - bandMass T := by linarith
  have hw : 0 ≤ ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k :=
    sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (bandU_nonneg T k)
  unfold bandBeta
  refine ⟨by positivity, by field_simp, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
    have : bandMass T ≤ 0.294 := by rw [e1]; exact s1
    nlinarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
    nlinarith

lemma bandH_sum (T : ℕ) : ∑ k ∈ win (3 * T + 3), bandH T k = 0 := by
  unfold bandH
  rw [sum_sub_distrib, sum_sub_distrib, sum_ite_eq' (win (3 * T + 3)) (0 : ℤ),
    sum_ite_eq' (win (3 * T + 3)) (1 : ℤ), ite_eq_left (mem_win.mpr (by simp only [abs_zero]; push_cast; omega)),
    ite_eq_left (mem_win.mpr (by simp only [abs_one]; push_cast; omega)), ← mul_sum]
  unfold bandMass; ring

lemma bandH_supp (T : ℕ) (k : ℤ) (hk : bandH T k ≠ 0) : |k| ≤ T + 1 := by
  by_contra hc
  apply hk
  unfold bandH
  rw [ite_eq_right (by intro h; subst h; simp at hc; omega), ite_eq_right (by intro h; subst h; simp at hc)]
  have : bandU T k = 0 := by
    by_contra h; have := bandU_supp T k h; rw [abs_le] at hc; omega
  rw [this]; ring

lemma bandH_abs_le (T : ℕ) (k : ℤ) :
    |bandH T k| ≤ (if k = 0 then 1 + bandBeta T * bandMass T else 0) + (if k = 1 then 1 else 0) +
      bandBeta T * bandU T k := by
  obtain ⟨hb, -, -, -⟩ := bandBeta_facts T
  have hm : 0 ≤ bandMass T := by unfold bandMass; exact sum_nonneg fun k _ => bandU_nonneg T k
  have hu := bandU_nonneg T k
  unfold bandH
  have h1 : |(if k = 0 then 1 + bandBeta T * bandMass T else 0)| = (if k = 0 then 1 + bandBeta T * bandMass T else 0) := by
    split_ifs
    · exact abs_of_nonneg (by positivity)
    · simp
  have h2 : |(if k = 1 then (1 : ℝ) else 0)| = (if k = 1 then 1 else 0) := by split_ifs <;> simp
  calc _ ≤ |(if k = 0 then 1 + bandBeta T * bandMass T else 0) - (if k = 1 then (1 : ℝ) else 0)| +
        |bandBeta T * bandU T k| := abs_sub _ _
    _ ≤ |(if k = 0 then 1 + bandBeta T * bandMass T else 0)| + |(if k = 1 then (1 : ℝ) else 0)| +
        |bandBeta T * bandU T k| := by gcongr; exact abs_sub _ _
    _ = _ := by rw [h1, h2, abs_of_nonneg (by positivity)]

lemma bandH_mass (T : ℕ) :
    ∑ k ∈ win (3 * T + 3), |bandH T k| ≤ 12 ∧ ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * |bandH T k| ≤ 15 := by
  obtain ⟨hb, -, hW, hK⟩ := bandBeta_facts T
  have m0 : (0 : ℤ) ∈ win (3 * T + 3) := mem_win.mpr (by simp only [abs_zero]; push_cast; omega)
  have m1 : (1 : ℤ) ∈ win (3 * T + 3) := mem_win.mpr (by simp only [abs_one]; push_cast; omega)
  constructor
  · calc _ ≤ ∑ k ∈ win (3 * T + 3), ((if k = 0 then 1 + bandBeta T * bandMass T else 0) +
          (if k = 1 then 1 else 0) + bandBeta T * bandU T k) := sum_le_sum fun k _ => bandH_abs_le T k
      _ = 2 + 2 * (bandBeta T * bandMass T) := by
          rw [sum_add_distrib, sum_add_distrib, sum_ite_eq' _ (0 : ℤ), sum_ite_eq' _ (1 : ℤ),
            ite_eq_left m0, ite_eq_left m1, ← mul_sum]
          unfold bandMass; ring
      _ ≤ 12 := by linarith
  · calc _ ≤ ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * ((if k = 0 then 1 + bandBeta T * bandMass T else 0) +
          (if k = 1 then 1 else 0) + bandBeta T * bandU T k) :=
          sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (bandH_abs_le T k) (abs_nonneg _)
      _ = 1 + bandBeta T * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k := by
          simp_rw [mul_add, sum_add_distrib, mul_ite, mul_zero]
          rw [sum_ite_eq' _ (0 : ℤ), sum_ite_eq' _ (1 : ℤ), ite_eq_left m0, ite_eq_left m1, mul_sum]
          simp only [Int.cast_zero, abs_zero, zero_mul, Int.cast_one, abs_one, mul_one, zero_add]
          congr 1; apply sum_congr rfl; intro k _; ring
      _ ≤ 15 := by linarith

lemma bandH_diff (T : ℕ) (d : ℤ) (hd1 : -(T : ℤ) - 1 ≤ d) (hd2 : d ≤ T) :
    bandH T (d + 1) - bandH T (-d) = -bandBeta T * bandKer d := by
  obtain ⟨-, hβ, -, -⟩ := bandBeta_facts T
  have pos : ∀ e : ℤ, 0 ≤ e → e ≤ T → bandH T (e + 1) - bandH T (-e) = -bandBeta T * bandKer e := by
    intro e he1 he2
    rcases eq_or_lt_of_le he1 with h0 | hpos
    · subst h0
      unfold bandH
      have u0 : bandU T 0 = 0 := by unfold bandU; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp
      have u1 : bandU T 1 = 0 := by unfold bandU; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp
      simp [u0, u1]
      linear_combination hβ
    · unfold bandH
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      unfold bandU
      rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      rw [show e + 1 - 1 = e by ring, show -(-e) = e by ring]
      rcases le_total 0 (bandKer e) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  rcases le_or_gt 0 d with h | h
  · exact pos d h hd2
  · have := pos (-d - 1) (by omega) (by omega)
    rw [show -d - 1 + 1 = -d by ring, show -(-d - 1) = d + 1 by ring, bandKer_neg] at this
    linarith

open scoped RealInnerProductSpace

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma qfull_nonpos (K : E →L[ℝ] F) {L η : ℝ} (hK : ‖K‖ ≤ L) (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2) (T : ℕ)
    (xp : ℤ → E) (yp : ℤ → F) (hx : ∀ k, ¬ (1 ≤ k ∧ k ≤ (T : ℤ)) → xp k = 0)
    (hy : ∀ k, ¬ (1 ≤ k ∧ k ≤ (T : ℤ)) → yp k = 0) :
    ∑ t ∈ win (3 * T + 3), ∑ s ∈ win (3 * T + 3), bandH T (t + 1 - s) *
      ((⟪xp t, xp s⟫ + ⟪yp t, yp s⟫) - (⟪xp (t + 1), xp s⟫ + ⟪yp (t + 1), yp s⟫) -
        η * ⟪yp t, K (xp s)⟫ + η * ⟪yp s, K (xp (t + 1))⟫) ≤ 0 := by
  set P : ℤ → ℤ → ℝ := fun t s => ⟪xp t, xp s⟫ + ⟪yp t, yp s⟫
  set Kg : ℤ → ℤ → ℝ := fun t s => ⟪yp t, K (xp s)⟫
  have supp : ∀ t s : ℤ, ¬ ((1 ≤ t ∧ t ≤ T) ∧ (1 ≤ s ∧ s ≤ T)) → P t s = 0 ∧ Kg t s = 0 := by
    intro t s h
    by_cases ht : 1 ≤ t ∧ t ≤ (T : ℤ)
    · have hs : ¬ (1 ≤ s ∧ s ≤ (T : ℤ)) := fun hs => h ⟨ht, hs⟩
      simp [P, Kg, hx s hs, hy s hs]
    · simp [P, Kg, hx t ht, hy t ht]
  have hP : ∀ t s, P t s ≠ 0 → (1 ≤ t ∧ t ≤ T) ∧ (1 ≤ s ∧ s ≤ T) := by
    intro t s h; by_contra hc; exact h (supp t s hc).1
  have hKs : ∀ t s, Kg t s ≠ 0 → (1 ≤ t ∧ t ≤ T) ∧ (1 ≤ s ∧ s ≤ T) := by
    intro t s h; by_contra hc; exact h (supp t s hc).2
  have hsym : ∀ t s, P t s = P s t := by intro t s; simp only [P]; rw [real_inner_comm, real_inner_comm (yp t)]
  have e := toeplitz_identity T (3 * T + 3) η P Kg (bandH T) hP hKs hsym (by omega)
  simp only [P, Kg] at e
  rw [e]
  obtain ⟨hβ, -, -, -⟩ := bandBeta_facts T
  have key : ∀ t s : ℤ,
      ((bandH T (t - s + 1) - bandH T (-(t - s)) - (bandH T (t - s) - bandH T (-(t - s) + 1))) / 2 * P t s -
        η * (bandH T (t - s + 1) - bandH T (-(t - s))) * Kg t s) =
      -bandBeta T * ((bandKer (t - s) - bandKer (t - s - 1)) / 2 * P t s - η * bandKer (t - s) * Kg t s) := by
    intro t s
    by_cases h : (1 ≤ t ∧ t ≤ T) ∧ (1 ≤ s ∧ s ≤ T)
    · have d1 := bandH_diff T (t - s) (by omega) (by omega)
      have d2 := bandH_diff T (t - s - 1) (by omega) (by omega)
      rw [show t - s - 1 + 1 = t - s by ring, show -(t - s - 1) = -(t - s) + 1 by ring] at d2
      rw [d1, d2]; ring
    · rw [(supp t s h).1, (supp t s h).2]; ring
  simp only [P, Kg] at key
  simp_rw [key, ← mul_sum]
  have := band_form_nonneg K hK hη hηL (win (3 * T + 3)) xp yp
  nlinarith

end OracleTemplate.ArrowHurwicz
