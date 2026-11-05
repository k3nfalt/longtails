import LongTails.Proofs.StochasticGeneralizedWeights
import LongTails.Proofs.CoarseGeneralizedCounting
import LongTails.Algorithms.NoisyDampedNewton

namespace LongTails.Proofs.NoisyMsAccounting

lemma proposal_charge (p q a : ℝ) (ha : 0 ≤ a)
    (hstep : q ≤ 3 / 4 * p + a ∨ (a = p ∧ q ≤ 4 * p)) :
    p ≤ 4 * (p - q) + 13 * a := by
  rcases hstep with h | ⟨h, hq⟩ <;> nlinarith

lemma total_charges (p w a : ℕ → ℝ) (n : ℕ)
    (hp : 0 ≤ p n) (hstep : ∀ i < n, w i ≤ 4 * (p i - p (i + 1)) + 13 * a i) :
    ∑ i ∈ Finset.range n, w i ≤ 4 * p 0 + 13 * ∑ i ∈ Finset.range n, a i := by
  have hledger : ∀ k ≤ n, (∑ i ∈ Finset.range k, w i) + 4 * p k ≤
      4 * p 0 + 13 * ∑ i ∈ Finset.range k, a i := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      have hc := hstep k (by omega)
      have hh := ih (by omega)
      linarith
  have hh := hledger n le_rfl
  linarith

lemma total_proposals (p a : ℕ → ℝ) (n : ℕ)
    (hp : ∀ i ≤ n, 0 ≤ p i) (ha : ∀ i < n, 0 ≤ a i)
    (hstep : ∀ i < n, p (i + 1) ≤ 3 / 4 * p i + a i ∨
      (a i = p i ∧ p (i + 1) ≤ 4 * p i)) :
    ∑ i ∈ Finset.range n, p i ≤ 4 * p 0 + 13 * ∑ i ∈ Finset.range n, a i :=
  total_charges p p a n (hp n le_rfl) (fun i hi => proposal_charge _ _ _ (ha i hi) (hstep i hi))

lemma stopped_proposals (p a : ℕ → ℝ) (active : ℕ → Prop) [DecidablePred active] (n : ℕ)
    (hp : 0 ≤ p n) (ha : ∀ i < n, 0 ≤ a i)
    (hstep : ∀ i < n, active i → p (i + 1) ≤ 3 / 4 * p i + a i ∨
      (a i = p i ∧ p (i + 1) ≤ 4 * p i))
    (hstop : ∀ i < n, ¬ active i → p (i + 1) = p i ∧ a i = 0) :
    ∑ i ∈ Finset.range n, (if active i then p i else 0) ≤
      4 * p 0 + 13 * ∑ i ∈ Finset.range n, a i := by
  apply total_charges p (fun i => if active i then p i else 0) a n hp
  intro i hin
  by_cases hi : active i
  · simpa only [ite_eq_left hi] using proposal_charge _ _ _ (ha i hin) (hstep i hin hi)
  · simp only [ite_eq_right hi, (hstop i hin hi).1, (hstop i hin hi).2, sub_self,
      mul_zero, add_zero, le_refl]

lemma walk_length (distance charge : ℕ → ℕ) (n : ℕ)
    (hstep : ∀ k, distance (k + 1) + 1 ≤ distance k + 2 * charge k) :
    n ≤ distance 0 + 2 * ∑ k ∈ Finset.range n, charge k := by
  have hledger : ∀ k, distance k + k ≤
      distance 0 + 2 * ∑ i ∈ Finset.range k, charge i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hh := hstep k
      omega
  have hh := hledger n
  omega

lemma dyadic_distance_step (level next threshold : ℕ) (rejected : Bool)
    (hnext : next = if rejected then level + 1 else level - 1) :
    (next - threshold + (threshold - next)) + 1 ≤
      level - threshold + (threshold - level) +
        2 * (if (rejected = true ∧ threshold ≤ level) ∨
          (rejected = false ∧ level ≤ threshold) then 1 else 0) := by
  cases rejected <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
    false_and, true_and, false_or, or_false] at * <;> split_ifs at * <;> omega

lemma moving_dyadic_distance_step (level next threshold nextThreshold : ℕ) (rejected : Bool)
    (hnext : next = if rejected then level + 1 else level - 1)
    (hk : nextThreshold ≤ threshold) :
    (next - nextThreshold + (nextThreshold - next)) + 1 ≤
      level - threshold + (threshold - level) +
        2 * (if (rejected = true ∧ threshold ≤ level) ∨
          (rejected = false ∧ level ≤ threshold) then 1 else 0) + (threshold - nextThreshold) := by
  have hh := dyadic_distance_step level next threshold rejected hnext
  omega

lemma moving_walk_length (level threshold charge : ℕ → ℕ) (n : ℕ)
    (hzero : level 0 = 0) (hk : ∀ i ∈ Finset.range n, threshold (i + 1) ≤ threshold i)
    (hstep : ∀ i ∈ Finset.range n,
      (level (i + 1) - threshold (i + 1) + (threshold (i + 1) - level (i + 1))) + 1 ≤
        level i - threshold i + (threshold i - level i) + 2 * charge i +
          (threshold i - threshold (i + 1))) :
    n ≤ 2 * ∑ i ∈ Finset.range n, charge i + 2 * threshold 0 := by
  have hledger : ∀ k, k ≤ n → level k - threshold k + (threshold k - level k) + k + threshold k ≤
      2 * threshold 0 + 2 * ∑ i ∈ Finset.range k, charge i := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [hzero, Nat.zero_sub, Nat.sub_zero, Nat.add_zero, Finset.sum_range_zero, mul_zero]
      omega
    | succ k ih =>
      intro hkn
      rw [Finset.sum_range_succ]
      have hmem : k ∈ Finset.range n := Finset.mem_range.mpr (Nat.lt_of_succ_le hkn)
      have hh := hstep k hmem
      have hh' := hk k hmem
      have hi := ih (by omega)
      omega
  have hh := hledger n le_rfl
  omega

lemma dyadic_walk_count (level threshold : ℕ → ℕ) (rejected : ℕ → Bool) (n : ℕ)
    (hzero : level 0 = 0) (hk : ∀ i ∈ Finset.range n, threshold (i + 1) ≤ threshold i)
    (hnext : ∀ i ∈ Finset.range n, level (i + 1) = if rejected i then level i + 1 else level i - 1) :
    n ≤ 2 * (((Finset.range n).filter (fun i => rejected i = true ∧ threshold i ≤ level i)).card +
      ((Finset.range n).filter (fun i => rejected i = false ∧ level i ≤ threshold i)).card) +
      2 * threshold 0 := by
  classical
  let charge := fun i => if (rejected i = true ∧ threshold i ≤ level i) ∨
    (rejected i = false ∧ level i ≤ threshold i) then 1 else 0
  have hwalk := moving_walk_length level threshold charge n hzero hk
    (fun i hi => moving_dyadic_distance_step _ _ _ _ _ (hnext i hi) (hk i hi))
  have he (i : ℕ) : charge i =
      (if rejected i = true ∧ threshold i ≤ level i then 1 else 0) +
      (if rejected i = false ∧ level i ≤ threshold i then 1 else 0) := by
    dsimp [charge]
    cases rejected i <;> simp
  simp_rw [he, Finset.sum_add_distrib] at hwalk
  simpa only [← Finset.card_filter] using hwalk

lemma relative_increment_count (A : ℕ → ℝ) (n : ℕ) (s : Finset ℕ) (c : ℝ)
    (hc : 0 ≤ c) (hs : s ⊆ Finset.range n)
    (hpos : ∀ i ∈ Finset.range n, 0 < A i)
    (hmono : ∀ i ∈ Finset.range n, A i ≤ A (i + 1))
    (hstep : ∀ i ∈ s, 1 ≤ c * ((A (i + 1) - A i) / A (i + 1))) :
    (s.card : ℝ) ≤ c * (Real.log (A n) - Real.log (A 0)) := by
  have hsum := OracleTemplate.CoarseGeneralized.sum_relative_increment_le_log A (Nat.zero_le n)
    (by simpa only [Nat.Ico_zero_eq_range] using hpos)
    (by simpa only [Nat.Ico_zero_eq_range] using hmono)
  simp only [Nat.Ico_zero_eq_range] at hsum
  calc
    _ = ∑ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ s, c * ((A (i + 1) - A i) / A (i + 1)) := Finset.sum_le_sum hstep
    _ ≤ ∑ i ∈ Finset.range n, c * ((A (i + 1) - A i) / A (i + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hs
      intro i hi _
      exact mul_nonneg hc (div_nonneg (sub_nonneg.mpr (hmono i hi))
        ((hpos i hi).le.trans (hmono i hi)))
    _ = c * ∑ i ∈ Finset.range n, ((A (i + 1) - A i) / A (i + 1)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hc

lemma low_full_relative_increment (A η p Q : ℝ) (hA : 0 < A) (hp : 0 < p)
    (hQ : 0 ≤ Q) (hroot : η * p ^ 2 = A + p) (hsmall : η * A ≤ 2 * Q ^ 2) :
    1 ≤ (2 * Q + 1) * (p / (A + p)) := by
  have he := congrArg (fun x : ℝ => x * A) hroot
  have hm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg p)
  have hs : A ^ 2 ≤ (2 * Q * p) ^ 2 := by
    nlinarith only [he, hm, mul_nonneg hA.le hp.le, sq_nonneg (Q * p)]
  have hb : A ≤ 2 * Q * p :=
    (sq_le_sq₀ hA.le (by positivity : 0 ≤ 2 * Q * p)).mp hs
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (add_pos hA hp)).mpr
  nlinarith only [hb]

lemma dyadic_threshold_exists (floor Λ : ℝ) (hf : 0 < floor) :
    ∃ k : ℕ, Λ ≤ floor * 2 ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (Λ / floor) (show (1 : ℝ) < 2 by norm_num)
  exact ⟨k, (div_le_iff₀ hf).mp hk.le |>.trans_eq (mul_comm _ _)⟩

noncomputable def dyadicThreshold (floor Λ : ℝ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, Λ ≤ floor * 2 ^ k then Nat.find h else 0

lemma dyadic_threshold_spec (floor Λ : ℝ) (hf : 0 < floor) :
    Λ ≤ floor * 2 ^ dyadicThreshold floor Λ := by
  classical
  simpa only [dyadicThreshold, dite_eq_left (dyadic_threshold_exists floor Λ hf)] using
    Nat.find_spec (dyadic_threshold_exists floor Λ hf)

lemma dyadic_threshold_mono (floor Λ Λ' : ℝ) (hf : 0 < floor) (h : Λ' ≤ Λ) :
    dyadicThreshold floor Λ' ≤ dyadicThreshold floor Λ := by
  classical
  simp only [dyadicThreshold, dite_eq_left (dyadic_threshold_exists floor Λ hf),
    dite_eq_left (dyadic_threshold_exists floor Λ' hf)]
  exact Nat.find_min' _ (h.trans (Nat.find_spec (dyadic_threshold_exists floor Λ hf)))

lemma dyadic_threshold_upper (floor Λ : ℝ) (hf : 0 < floor) (hΛ : floor ≤ Λ) :
    floor * 2 ^ dyadicThreshold floor Λ ≤ 2 * Λ := by
  classical
  let h := dyadic_threshold_exists floor Λ hf
  change floor * 2 ^ (if hh : ∃ k : ℕ, Λ ≤ floor * 2 ^ k then Nat.find hh else 0) ≤ _
  rw [dite_eq_left h]
  cases hk : Nat.find h with
  | zero => simp only [pow_zero, mul_one]; linarith
  | succ k =>
    have hmin := Nat.find_min h (show k < Nat.find h by omega)
    have hlt : floor * 2 ^ k < Λ := lt_of_not_ge hmin
    rw [pow_succ]
    nlinarith only [hlt]

lemma dyadic_threshold_log (floor Λ : ℝ) (hf : 0 < floor) (hΛ : floor ≤ Λ) :
    (dyadicThreshold floor Λ : ℝ) ≤ 1 + Real.log (Λ / floor) / Real.log 2 := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 1 ≤ Λ / floor := (one_le_div hf).mpr hΛ
  let h := dyadic_threshold_exists floor Λ hf
  simp only [dyadicThreshold, dite_eq_left h]
  cases hk : Nat.find h with
  | zero =>
    have hl := Real.log_nonneg hratio
    simp only [Nat.cast_zero]
    positivity
  | succ k =>
    have hmin := Nat.find_min h (show k < Nat.find h by omega)
    have hp : (2 : ℝ) ^ k ≤ Λ / floor :=
      (le_div_iff₀ hf).mpr (by nlinarith only [le_of_lt (lt_of_not_ge hmin)])
    have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ k) hp
    rw [Real.log_pow] at hl
    have hd := (le_div_iff₀ hl2).mpr hl
    simp only [Nat.cast_succ]
    linarith

lemma dyadic_threshold_low (floor Λ η : ℝ) (level : ℕ) (hf : 0 < floor)
    (hΛ : floor ≤ Λ) (hη : η = floor * 2 ^ level)
    (hlevel : level ≤ dyadicThreshold floor Λ) : η ≤ 2 * Λ := by
  rw [hη]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hlevel) hf.le).trans
    (dyadic_threshold_upper floor Λ hf hΛ)

lemma dyadic_threshold_high (floor Λ η : ℝ) (level : ℕ) (hf : 0 < floor)
    (hη : η = floor * 2 ^ level) (hlevel : dyadicThreshold floor Λ ≤ level) : Λ ≤ η := by
  rw [hη]
  exact (dyadic_threshold_spec floor Λ hf).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hlevel) hf.le)

lemma movement_charge (h Λ α δ M₀ M₁ ρ τ r D : ℝ)
    (hh : 0 ≤ h) (hΛ : 0 ≤ Λ) (hα : 0 ≤ α)
    (hM₁ : 0 ≤ M₁) (hρ : 0 ≤ ρ)
    (hD : h * Λ * r ^ 2 ≤ D) (hτ : 2 * Λ ≤ τ) (hcut : 8 * δ ≤ α * Λ)
    (hm : ρ / 2 < r ∨ α / 16 < M₁ * r ^ 2 ∨ α * τ < 8 * δ + 16 * M₀ * r) :
    h * Λ * ρ ^ 2 ≤ 4 * D ∨ h * Λ * α ≤ 16 * M₁ * D ∨
      h * α ^ 2 * Λ ^ 3 ≤ 256 * M₀ ^ 2 * D := by
  rcases hm with hm | hm | hm
  · left
    have hs := pow_le_pow_left₀ hρ (by linarith : ρ ≤ 2 * r) 2
    have hc := mul_le_mul_of_nonneg_left hs (mul_nonneg hh hΛ)
    nlinarith only [hc, hD]
  · right; left
    have hs := mul_le_mul_of_nonneg_left (show α ≤ 16 * M₁ * r ^ 2 by linarith)
      (mul_nonneg hh hΛ)
    have hc := mul_le_mul_of_nonneg_left hD (show 0 ≤ 16 * M₁ by positivity)
    nlinarith only [hs, hc]
  · right; right
    have ht := mul_le_mul_of_nonneg_left hτ hα
    have hs : α * Λ ≤ 16 * M₀ * r := by linarith
    have hs2 := pow_le_pow_left₀ (mul_nonneg hα hΛ) hs 2
    have hc := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hh hΛ)
    have hd := mul_le_mul_of_nonneg_left hD (show 0 ≤ 256 * M₀ ^ 2 by positivity)
    nlinarith only [hc, hd]

lemma moving_movement_charge (A W Q α δ M₀ M₁ ρ τ r D : ℝ)
    (hA : 0 < A) (hW : A ≤ W) (hα : 0 ≤ α) (hM₁ : 0 ≤ M₁) (hρ : 0 ≤ ρ)
    (hD : Q ^ 2 * r ^ 2 ≤ D) (hτ : 2 * Q ^ 2 ≤ τ * A) (hcut : 8 * δ * A ≤ α * Q ^ 2)
    (hm : ρ / 2 < r ∨ α / 16 < M₁ * r ^ 2 ∨ α * τ < 8 * δ + 16 * M₀ * r) :
    Q ^ 2 * ρ ^ 2 ≤ 4 * D ∨ Q ^ 2 * α ≤ 16 * M₁ * D ∨
      α ^ 2 * Q ^ 6 ≤ 256 * M₀ ^ 2 * W ^ 2 * D := by
  have hDn : 0 ≤ D := (mul_nonneg (sq_nonneg Q) (sq_nonneg r)).trans hD
  rcases hm with hm | hm | hm
  · left
    have hs := pow_le_pow_left₀ hρ (by linarith : ρ ≤ 2 * r) 2
    have hc := mul_le_mul_of_nonneg_left hs (sq_nonneg Q)
    nlinarith only [hc, hD]
  · right; left
    have hs := mul_le_mul_of_nonneg_left (show α ≤ 16 * M₁ * r ^ 2 by linarith)
      (sq_nonneg Q)
    have hc := mul_le_mul_of_nonneg_left hD (show 0 ≤ 16 * M₁ by positivity)
    nlinarith only [hs, hc]
  · right; right
    have ht := mul_le_mul_of_nonneg_left hτ hα
    have hmA := mul_le_mul_of_nonneg_right hm.le hA.le
    have hs : α * Q ^ 2 ≤ 16 * M₀ * r * A := by nlinarith only [ht, hmA, hcut]
    have hs2 := pow_le_pow_left₀ (mul_nonneg hα (sq_nonneg Q)) hs 2
    have hc := mul_le_mul_of_nonneg_left hs2 (sq_nonneg Q)
    have hd := mul_le_mul_of_nonneg_left hD (show 0 ≤ 256 * M₀ ^ 2 * A ^ 2 by positivity)
    have hAw := pow_le_pow_left₀ hA.le hW 2
    have hw := mul_le_mul_of_nonneg_right hAw (show 0 ≤ 256 * M₀ ^ 2 * D by positivity)
    nlinarith only [hc, hd, hw]

lemma three_charge_count {ι : Type*} (s : Finset ι) (D : ι → ℝ)
    (x y z a b c S : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hD : ∀ i ∈ s, 0 ≤ D i) (hsum : ∑ i ∈ s, D i ≤ S)
    (hcharge : ∀ i ∈ s, x ≤ a * D i ∨ y ≤ b * D i ∨ z ≤ c * D i) :
    (s.card : ℝ) ≤ (a / x + b / y + c / z) * S := by
  let C := a / x + b / y + c / z
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (i : ι) (hi : i ∈ s) : 1 ≤ C * D i := by
    have hDi := hD i hi
    have h₁ : 0 ≤ a * D i / x := by positivity
    have h₂ : 0 ≤ b * D i / y := by positivity
    have h₃ : 0 ≤ c * D i / z := by positivity
    have he : C * D i = a * D i / x + b * D i / y + c * D i / z := by dsimp [C]; ring
    rw [he]
    rcases hcharge i hi with h | h | h
    · have hh := (one_le_div hx).mpr h
      linarith
    · have hh := (one_le_div hy).mpr h
      linarith
    · have hh := (one_le_div hz).mpr h
      linarith
  calc
    _ = ∑ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ s, C * D i := Finset.sum_le_sum hpoint
    _ = C * ∑ i ∈ s, D i := (Finset.mul_sum _ _ _).symm
    _ ≤ C * S := mul_le_mul_of_nonneg_left hsum hC

lemma high_rejection_count {ι : Type*} (s : Finset ι) (D : ι → ℝ)
    (Q α ρ M₀ M₁ W S : ℝ) (hQ : 0 < Q) (hα : 0 < α) (hρ : 0 < ρ)
    (hM₁ : 0 ≤ M₁) (hD : ∀ i ∈ s, 0 ≤ D i) (hsum : ∑ i ∈ s, D i ≤ S)
    (hρQ : 4 * S ≤ Q ^ 3 * ρ ^ 2) (h₁Q : 16 * M₁ * S ≤ Q ^ 3 * α)
    (h₀Q : 256 * M₀ ^ 2 * W ^ 2 * S ≤ α ^ 2 * Q ^ 7)
    (hcharge : ∀ i ∈ s, Q ^ 2 * ρ ^ 2 ≤ 4 * D i ∨
      Q ^ 2 * α ≤ 16 * M₁ * D i ∨ α ^ 2 * Q ^ 6 ≤ 256 * M₀ ^ 2 * W ^ 2 * D i) :
    (s.card : ℝ) ≤ 3 * Q := by
  have hcount := three_charge_count s D (Q ^ 2 * ρ ^ 2) (Q ^ 2 * α) (α ^ 2 * Q ^ 6)
    4 (16 * M₁) (256 * M₀ ^ 2 * W ^ 2) S (by positivity) (by positivity)
    (by positivity) (by norm_num) (by positivity) (by positivity) hD hsum hcharge
  have h₁ : (4 / (Q ^ 2 * ρ ^ 2)) * S ≤ Q := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < Q ^ 2 * ρ ^ 2)).mpr
    nlinarith only [hρQ]
  have h₂ : (16 * M₁ / (Q ^ 2 * α)) * S ≤ Q := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < Q ^ 2 * α)).mpr
    nlinarith only [h₁Q]
  have h₃ : (256 * M₀ ^ 2 * W ^ 2 / (α ^ 2 * Q ^ 6)) * S ≤ Q := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < α ^ 2 * Q ^ 6)).mpr
    nlinarith only [h₀Q]
  nlinarith only [hcount, h₁, h₂, h₃]

lemma moving_prefix_count (A D : ℕ → ℝ) (level threshold : ℕ → ℕ)
    (rejected : ℕ → Bool) (n : ℕ) (Q α ρ M₀ M₁ W S c : ℝ)
    (hQ : 0 < Q) (hα : 0 < α) (hρ : 0 < ρ) (hM₁ : 0 ≤ M₁) (hc : 0 ≤ c)
    (hzero : level 0 = 0) (hk : ∀ i ∈ Finset.range n, threshold (i + 1) ≤ threshold i)
    (hnext : ∀ i ∈ Finset.range n, level (i + 1) = if rejected i then level i + 1 else level i - 1)
    (hpos : ∀ i ∈ Finset.range n, 0 < A i)
    (hmono : ∀ i ∈ Finset.range n, A i ≤ A (i + 1))
    (hD : ∀ i ∈ Finset.range n, 0 ≤ D i) (hsum : ∑ i ∈ Finset.range n, D i ≤ S)
    (hρQ : 4 * S ≤ Q ^ 3 * ρ ^ 2) (h₁Q : 16 * M₁ * S ≤ Q ^ 3 * α)
    (h₀Q : 256 * M₀ ^ 2 * W ^ 2 * S ≤ α ^ 2 * Q ^ 7)
    (hhigh : ∀ i ∈ Finset.range n, rejected i = true → threshold i ≤ level i →
      Q ^ 2 * ρ ^ 2 ≤ 4 * D i ∨ Q ^ 2 * α ≤ 16 * M₁ * D i ∨
        α ^ 2 * Q ^ 6 ≤ 256 * M₀ ^ 2 * W ^ 2 * D i)
    (hlow : ∀ i ∈ Finset.range n, rejected i = false → level i ≤ threshold i →
      1 ≤ c * ((A (i + 1) - A i) / A (i + 1))) :
    (n : ℝ) ≤ 6 * Q + 2 * c * (Real.log (A n) - Real.log (A 0)) + 2 * threshold 0 := by
  classical
  let hi := (Finset.range n).filter (fun i => rejected i = true ∧ threshold i ≤ level i)
  let lo := (Finset.range n).filter (fun i => rejected i = false ∧ level i ≤ threshold i)
  have hh : (hi.card : ℝ) ≤ 3 * Q := by
    apply high_rejection_count hi D Q α ρ M₀ M₁ W S hQ hα hρ hM₁
    · intro i hi
      exact hD i (Finset.mem_filter.mp hi).1
    · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi _ => hD i hi)).trans hsum
    · exact hρQ
    · exact h₁Q
    · exact h₀Q
    · intro i hi
      obtain ⟨hi, hh, ht⟩ := Finset.mem_filter.mp hi
      exact hhigh i hi hh ht
  have hl : (lo.card : ℝ) ≤ c * (Real.log (A n) - Real.log (A 0)) := by
    apply relative_increment_count A n lo c hc (Finset.filter_subset _ _) hpos hmono
    intro i hi
    obtain ⟨hi, hh, ht⟩ := Finset.mem_filter.mp hi
    exact hlow i hi hh ht
  have hw := dyadic_walk_count level threshold rejected n hzero hk hnext
  have hw' : (n : ℝ) ≤ 2 * ((hi.card : ℝ) + (lo.card : ℝ)) + 2 * threshold 0 := by
    exact_mod_cast hw
  linarith

lemma quadratic_root_upper (G A q u : ℝ) (hG : 0 < G) (hq : 0 < q)
    (heq : G * q ^ 2 = A + q) (hu : 1 ≤ G * u) (hupper : A + u ≤ G * u ^ 2) :
    q ≤ u := by
  by_contra hh
  have hd : 0 < q - u := by linarith
  have hder : 0 < G * (q + u) - 1 := by nlinarith only [hu, mul_pos hG hq]
  have hp := mul_pos hd hder
  nlinarith only [hp, heq, hupper]

lemma doubled_weight (G A p a q : ℝ) (hG : 0 < G) (hA : 0 ≤ A)
    (hp : 0 < p) (ha : 0 ≤ a) (hq : 0 < q)
    (heq : G * p ^ 2 = A + p) (heq' : (2 * G) * q ^ 2 = A + a + q) :
    q ≤ 3 / 4 * p + a := by
  have hGp := OracleTemplate.StochasticGeneralized.weight_scale_lower hA hp heq
  apply quadratic_root_upper (2 * G) (A + a) q (3 / 4 * p + a) (by positivity) hq heq'
  · nlinarith [mul_nonneg hG.le ha]
  · have hm := mul_le_mul_of_nonneg_right hGp ha
    have hs := mul_nonneg hG.le (sq_nonneg a)
    nlinarith only [heq, hA, hp.le, ha, hm, hs]

lemma halved_weight (G G' A p q : ℝ) (hG : 0 < G) (hG' : G / 2 ≤ G')
    (hA : 0 ≤ A) (hp : 0 < p) (hq : 0 < q)
    (heq : G * p ^ 2 = A + p) (heq' : G' * q ^ 2 = A + p + q) : q ≤ 4 * p := by
  have hGp := OracleTemplate.StochasticGeneralized.weight_scale_lower hA hp heq
  apply quadratic_root_upper G' (A + p) q (4 * p) (by linarith) hq heq'
  · have hm := mul_le_mul_of_nonneg_right hG' hp.le
    nlinarith only [hm, hGp]
  · have hm := mul_le_mul_of_nonneg_right hG' (sq_nonneg p)
    nlinarith only [hm, heq, hA, hp.le]

open OracleTemplate.GeneralizedAccelerated (tentativeWeight tentativeWeight_pos tentativeWeight_equation)
open LongTails.Algorithms.NoisyDampedNewton (Trial actualWeight finish)

lemma finish_weight_cases {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Trial E) (hA : 0 ≤ t.previous.A) (hη : 0 < t.previous.guess)
    (hτ : t.previous.guess ≤ t.curvature) (floor : ℝ) (u : E) :
    tentativeWeight (finish floor t u) ≤ 3 / 4 * tentativeWeight t.previous + actualWeight t ∨
      (actualWeight t = tentativeWeight t.previous ∧
        tentativeWeight (finish floor t u) ≤ 4 * tentativeWeight t.previous) := by
  have ht : 0 < t.curvature := hη.trans_le hτ
  have hp := tentativeWeight_pos t.previous hη
  have heq := tentativeWeight_equation t.previous hA hη
  have ha : 0 < actualWeight t := mul_pos (div_pos hη ht) hp
  have hAn : 0 ≤ (finish floor t u).A := add_nonneg hA ha.le
  have hηn : 0 < (finish floor t u).guess := by
    unfold finish
    dsimp only
    split_ifs
    · exact lt_of_lt_of_le (by positivity : 0 < t.previous.guess / 2) (le_max_right _ _)
    · positivity
  have hq := tentativeWeight_pos (finish floor t u) hηn
  have heq' := tentativeWeight_equation (finish floor t u) hAn hηn
  by_cases hh : t.curvature = t.previous.guess
  · right
    have hw : actualWeight t = tentativeWeight t.previous := by
      unfold actualWeight
      rw [hh, div_self hη.ne', one_mul]
    refine ⟨hw, ?_⟩
    apply halved_weight t.previous.guess (finish floor t u).guess t.previous.A
      (tentativeWeight t.previous) (tentativeWeight (finish floor t u)) hη
      (by simp only [finish, ite_eq_left hh]; exact le_max_right _ _) hA hp hq heq
    simpa only [finish, hw, ite_eq_left hh] using heq'
  · left
    apply doubled_weight t.previous.guess t.previous.A (tentativeWeight t.previous)
      (actualWeight t) (tentativeWeight (finish floor t u)) hη hA hp ha.le hq heq
    simpa only [finish, ite_eq_right hh] using heq'

lemma floored_dyadic_half (floor : ℝ) (hf : 0 ≤ floor) (level : ℕ) :
    max floor (floor * 2 ^ level / 2) = floor * 2 ^ (level - 1) := by
  cases level with
  | zero =>
    simp only [pow_zero, mul_one, Nat.zero_sub]
    exact max_eq_left (by linarith)
  | succ k =>
    simp only [Nat.succ_sub_one, pow_succ]
    rw [show floor * (2 ^ k * 2) / 2 = floor * 2 ^ k by ring]
    exact max_eq_right (le_mul_of_one_le_right hf (one_le_pow₀ (by norm_num)))

lemma finish_dyadic_level {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Trial E) (floor : ℝ) (hf : 0 ≤ floor) (level : ℕ)
    (hlevel : t.previous.guess = floor * 2 ^ level) (u : E) :
    (finish floor t u).guess =
      floor * 2 ^ (if t.curvature = t.previous.guess then level - 1 else level + 1) := by
  classical
  by_cases hh : t.curvature = t.previous.guess
  · simp only [finish, ite_eq_left hh]
    rw [hlevel]
    exact floored_dyadic_half floor hf level
  · simp only [finish, ite_eq_right hh]
    rw [hlevel, pow_succ]
    ring

end LongTails.Proofs.NoisyMsAccounting
