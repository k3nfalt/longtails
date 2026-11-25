import LongTails.Proofs.LogisticSpatialResponse

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LogisticRawClock

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma scalar_window {a : ℕ → ℝ} {h j : ℕ} {P N B : ℝ}
    (hj : j ≤ h) (hP : 0 ≤ P) (hN : 0 ≤ N) (hs : 0 < P+N)
    (hu : ∀ t < h, a (t+1)-a t ≤ P) (hl : ∀ t < h, a t-a (t+1) ≤ N)
    (hb : N*(a 0+B)+P*(a h+B)+(h:ℝ)*P*N ≤ 0) : a j+B ≤ 0 := by
  have front : ∀ k ≤ h, a k ≤ a 0+(k:ℝ)*P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      push_cast
      linarith [ih (Nat.le_of_succ_le hk),hu k hk]
  have back : ∀ k, j+k ≤ h → a j ≤ a (j+k)+(k:ℝ)*N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hlt : j+k < h := by omega
      have hh := hl (j+k) hlt
      push_cast
      rw [Nat.add_succ]
      linarith [ih hlt.le]
  have hback := back (h-j) (by omega)
  rw [Nat.add_sub_cancel' hj, Nat.cast_sub hj] at hback
  have left := mul_le_mul_of_nonneg_left (front j hj) hN
  have right := mul_le_mul_of_nonneg_left hback hP
  apply (le_of_mul_le_mul_left (a := P+N) _ hs)
  nlinarith only [left,right,hb]

noncomputable def capacity (X : Fin n → E) (z : E) : ℝ :=
  ∑ i, (n:ℝ)⁻¹*max 0 ⟪X i,z⟫

lemma capacity_nonneg (X : Fin n → E) (z : E) : 0 ≤ capacity X z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (le_max_left _ _)

lemma velocity_upper (X : Fin n → E) (z : E) (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc 0 1) :
    ⟪∑ i, ((n:ℝ)⁻¹*q i) • X i,z⟫ ≤ capacity X z := by
  rw [sum_inner]
  apply Finset.sum_le_sum
  intro i _
  rw [real_inner_smul_left,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ q i*max 0 ⟪X i,z⟫ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (hq i).1
    _ ≤ 1*max 0 ⟪X i,z⟫ := mul_le_mul_of_nonneg_right (hq i).2 (le_max_left _ _)
    _ = _ := one_mul _

lemma noisy_velocity (X : Fin n → E) (z w w' : E) (q : Fin n → ℝ) (ε : ℝ)
    (hq : ∀ i, q i ∈ Set.Icc 0 1)
    (he : ⟪w'-w-∑ i, ((n:ℝ)⁻¹*q i) • X i,z⟫ ≤ ε) :
    ⟪w',z⟫-⟪w,z⟫ ≤ capacity X z+ε := by
  rw [inner_sub_left,inner_sub_left] at he
  linarith [velocity_upper X z q hq]

lemma raw_window (X : Fin n → E) (weights : Fin n → ℝ) (w : ℕ → E)
    (q s : ℕ → Fin n → ℝ) (b : Fin n → ℝ) (h j : ℕ) (P N B ε : ℝ)
    (hweights : ∀ i, 0 ≤ weights i) (hpos : ∃ i, 0 < weights i) (hj : j ≤ h)
    (hq : ∀ t < h, ∀ i, q t i ∈ Set.Icc 0 1)
    (he : let z := ∑ i, weights i • X i
          ∀ t < h, |⟪w (t+1)-w t-∑ i, ((n:ℝ)⁻¹*q t i) • X i,z⟫| ≤ ε)
    (hz : let z := ∑ i, weights i • X i
          capacity X z+ε ≤ P ∧ capacity X (-z)+ε ≤ N)
    (hP : 0 ≤ P) (hN : 0 ≤ N) (hs : 0 < P+N)
    (hm : ∀ i, 0 < s j i → -b i < ⟪w j,X i⟫)
    (hB : (∑ i, weights i*b i) ≤ B)
    (hb : let z := ∑ i, weights i • X i
          N*(⟪w 0,z⟫+B)+P*(⟪w h,z⟫+B)+(h:ℝ)*P*N ≤ 0) :
    ∃ i, s j i ≤ 0 := by
  let z := ∑ i, weights i • X i
  have hu (t : ℕ) (ht : t < h) := (noisy_velocity X z (w t) (w (t+1)) (q t) ε (hq t ht) ((abs_le.mp (he t ht)).2)).trans hz.1
  have hl (t : ℕ) (ht : t < h) : ⟪w t,z⟫-⟪w (t+1),z⟫ ≤ N := by
    have hh := noisy_velocity X (-z) (w t) (w (t+1)) (q t) ε (hq t ht) (by
      rw [inner_neg_right]; linarith [(abs_le.mp (he t ht)).1])
    rw [inner_neg_right,inner_neg_right] at hh
    linarith [hz.2]
  have H := scalar_window (a := fun t => ⟪w t,z⟫) hj hP hN hs hu hl hb
  by_contra! hp
  obtain ⟨i,hi⟩ := hpos
  have hm' (l : Fin n) : 0 < ⟪w j,X l⟫+b l := by linarith [hm l (hp l)]
  have hsum : 0 < ∑ l, weights l*(⟪w j,X l⟫+b l) :=
    Finset.sum_pos' (fun l _ => mul_nonneg (hweights l) (hm' l).le)
      ⟨i,Finset.mem_univ i,mul_pos hi (hm' i)⟩
  dsimp only [z] at H
  rw [inner_sum] at H
  simp only [real_inner_smul_right] at H
  simp only [mul_add,Finset.sum_add_distrib] at hsum
  linarith

end LongTails.Proofs.LogisticRawClock
