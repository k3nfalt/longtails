import LongTails.Algorithms.GrowthProfile

namespace LongTails.Proofs.RelativeGrowthProfile

open LongTails.Algorithms.GrowthProfile

variable {n : ℕ} [NeZero n] {h : Fin n → ℝ} {ρ t : ℝ}

omit [NeZero n] in
private lemma denom_pos (hh : ∀ i, 0 < h i) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    0 < 1 - t + t * h i := by
  rcases ht.2.lt_or_eq with hlt | rfl
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr hlt) (mul_nonneg ht.1 (hh i).le)
  · simpa using hh i

omit [NeZero n] in
lemma share_pos (hh : ∀ i, 0 < h i) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    0 < share h t i := div_pos (hh i) (denom_pos hh ht i)

lemma total_pos (hh : ∀ i, 0 < h i) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < ∑ i, share h t i := Finset.sum_pos (fun i _ => share_pos hh ht i) Finset.univ_nonempty

lemma normalized_pos (hh : ∀ i, 0 < h i) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    0 < normalized h t i :=
  div_pos (mul_pos (Nat.cast_pos.mpr (NeZero.pos n)) (share_pos hh ht i)) (total_pos hh ht)

lemma mass (hh : ∀ i, 0 < h i) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, normalized h t i = n := by
  simp only [normalized, ← Finset.sum_div, ← Finset.mul_sum]
  field_simp [(total_pos hh ht).ne']

lemma parameter_spec (hh : ∀ i, 0 < h i) (hρ : 1 ≤ ρ) :
    parameter h ρ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∑ i, profile h ρ i ^ 2 ≤ n * ρ ∧
    (parameter h ρ = 0 ∨ ∑ i, profile h ρ i ^ 2 = n * ρ) := by
  classical
  by_cases ex : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ ∑ i, normalized h s i ^ 2 = n * ρ
  · have he : parameter h ρ = ex.choose := dite_eq_left ex
    obtain ⟨hl, hu, hv⟩ := ex.choose_spec
    exact ⟨he ▸ ⟨hl, hu⟩, by simpa only [profile, he] using hv.le,
      Or.inr (by simpa only [profile, he] using hv)⟩
  have he : parameter h ρ = 0 := dite_eq_right ex
  let V := fun t => ∑ i, normalized h t i ^ 2
  have continuous_share (i : Fin n) : ContinuousOn (fun t => share h t i) (Set.Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => (denom_pos hh ht i).ne')
  have continuous_sum : ContinuousOn (fun t => ∑ i, share h t i) (Set.Icc 0 1) :=
    continuousOn_finsetSum _ (fun i _ => continuous_share i)
  have hV : ContinuousOn V (Set.Icc 0 1) :=
    continuousOn_finsetSum _ fun i _ =>
      (((continuousOn_const.mul (continuous_share i)).div continuous_sum
        (fun t ht => (total_pos hh ht).ne')).pow 2)
  have h1 (i : Fin n) : normalized h 1 i = 1 := by
    simp [normalized, share, (hh _).ne', NeZero.ne n]
  have he1 : V 1 ≤ n * ρ := by
    simp only [V, h1, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hρ
  have hzero : V 0 ≤ n * ρ := by
    by_contra! hbad
    obtain ⟨s, hs, hv⟩ := intermediate_value_Icc' zero_le_one hV
      (show (n : ℝ) * ρ ∈ Set.Icc (V 1) (V 0) from ⟨he1, hbad.le⟩)
    exact ex ⟨s, hs.1, hs.2, hv⟩
  exact ⟨by rw [he]; exact ⟨le_rfl, zero_le_one⟩, by simpa only [profile, he] using hzero,
    Or.inl he⟩

lemma weighted_support (hh : ∀ i, 0 < h i) (hρ : 1 ≤ ρ) (a : Fin n → ℝ)
    (hs : ∑ i, a i = n) (ha : ∑ i, a i ^ 2 ≤ n * ρ) :
    ∑ i, profile h ρ i / h i * profile h ρ i ≤ ∑ i, profile h ρ i / h i * a i := by
  classical
  let t := parameter h ρ
  let u := profile h ρ
  obtain ⟨ht, _, halt⟩ := parameter_spec hh hρ
  have hu : ∑ i, u i = n := mass hh ht
  have K (i : Fin n) : (1-t) * (u i / h i) + t * u i = n / ∑ j, share h t j := by
    dsimp only [u, profile, normalized, t]
    unfold share
    field_simp [(hh i).ne', (denom_pos hh ht i).ne', (total_pos hh ht).ne']
  have zeroMass : ∑ i, (a i - u i) = 0 := by rw [Finset.sum_sub_distrib, hs, hu, sub_self]
  have orth : (1-t) * (∑ i, u i / h i * a i - ∑ i, u i / h i * u i) +
      t * (∑ i, u i * a i - ∑ i, u i ^ 2) = 0 := by
    have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ =>
      congrArg (fun z => z * (a i - u i)) (K i))
    simp only [← Finset.mul_sum, zeroMass, mul_zero] at he
    convert he using 1
    simp only [mul_sub, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sq]
    ring
  rcases ht.2.lt_or_eq with hlt | he
  · have hc : t * (∑ i, u i * a i - ∑ i, u i ^ 2) ≤ 0 := by
      rcases halt with h0 | hactive
      · change t = 0 at h0
        rw [h0, zero_mul]
      · apply mul_nonpos_of_nonneg_of_nonpos ht.1
        have hcross := Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (a i-u i)
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          mul_assoc, ← Finset.mul_sum] at hcross
        change ∑ i, u i ^ 2 = n * ρ at hactive
        simp_rw [mul_comm (a _) (u _)] at hcross
        linarith
    change ∑ i, u i / h i * u i ≤ ∑ i, u i / h i * a i
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (by linarith only [orth, hc]) (sub_pos.mpr hlt))
  · have hunit (i : Fin n) : u i = 1 := by
      change normalized h (parameter h ρ) i = 1
      rw [he]
      simp [normalized, share, (hh _).ne', NeZero.ne n]
    have hact : ∑ i, profile h ρ i ^ 2 = n * ρ := halt.resolve_left (by linarith)
    change ∑ i, u i ^ 2 = n * ρ at hact
    simp only [hunit, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hact
    have hsum : ∑ i, (a i - 1)^2 = 0 := by
      apply le_antisymm _ (Finset.sum_nonneg (fun i _ => sq_nonneg (a i - 1)))
      simp only [sub_sq, one_pow, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs]
      linarith
    have ha1 i : a i = u i := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i - 1))).mp hsum i (Finset.mem_univ i)
      rw [hunit]
      nlinarith
    change ∑ i, u i / h i * u i ≤ ∑ i, u i / h i * a i
    simp_rw [ha1]
    exact le_rfl

end LongTails.Proofs.RelativeGrowthProfile
