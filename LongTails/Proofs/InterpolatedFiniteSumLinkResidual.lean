import LongTails.Proofs.InterpolatedFiniteSumExponential

open scoped BigOperators

namespace LongTails.Proofs.InterpolatedFiniteSumLinkResidual

open InterpolatedFiniteSumProfiles InterpolatedFiniteSumExponential

lemma profile_first_support (y : ℝ) : 1 / 2 - y ≤ profile (y - 1) := by
  have hh := InterpolatedFiniteSumChains.profile_support_one (1 - y)
  have he : 1 - y = -(y - 1) := by ring
  rw [he, profile_even] at hh
  linarith only [hh]

lemma first_exponential_support (η y : ℝ) (hη : 0 ≤ η) :
    Real.exp η - 1 - 2 * η * Real.exp η * y ≤ Real.exp (2 * η * profile (y - 1)) - 1 := by
  have hp := mul_le_mul_of_nonneg_left (profile_first_support y) (by positivity : 0 ≤ 2 * η)
  have he := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp (2 * η * profile (y - 1) - η)) (Real.exp_pos η).le
  have hid : Real.exp η * Real.exp (2 * η * profile (y - 1) - η) =
      Real.exp (2 * η * profile (y - 1)) := by rw [← Real.exp_add]; congr 1; ring
  rw [hid] at he
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos η).le
  nlinarith only [hm, he]

noncomputable def loss (η L a : ℝ) (y : ℕ → ℝ) : ℕ → ℝ
  | 0 => Real.exp (2 * η * profile (y 0 / a - 1)) - 1
  | j + 1 => Real.exp (linkPotential L (y j - y (j + 1))) - 1

lemma loss_nonnegative (η L a : ℝ) (y : ℕ → ℝ) (hη : 0 ≤ η) (j : ℕ) :
    0 ≤ loss η L a y j := by
  cases j with
  | zero => exact sub_nonneg.mpr (Real.one_le_exp (by exact mul_nonneg (by positivity) (profile_nonnegative _)))
  | succ j => exact sub_nonneg.mpr (Real.one_le_exp (linkPotential_nonnegative _ _))

lemma prefix_lower (η L a : ℝ) (y : ℕ → ℝ) (hη : 0 ≤ η) (ha : 0 < a) (hL : 0 < L) (r : ℕ) :
    let s := 2 * η * Real.exp η / a
    let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
    Real.exp η - 1 - s * y r - r * K ≤ ∑ j ∈ Finset.range (r + 1), loss η L a y j := by
  dsimp only
  let s := 2 * η * Real.exp η / a
  let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
  change Real.exp η - 1 - s * y r - r * K ≤ _
  have hs : 0 ≤ s := by dsimp [s]; positivity
  induction r with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, loss, Nat.cast_zero, zero_mul, sub_zero]
    convert first_exponential_support η (y 0 / a) hη using 1
    dsimp [s]
    ring
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have hh := link_conjugate_bound s L (y r - y (r + 1)) hs hL
    change s * (y r - y (r + 1)) - loss η L a y (r + 1) ≤ K at hh
    simp only [Nat.cast_succ]
    nlinarith only [hh, ih]

lemma total_lower (η L a θ : ℝ) (y : ℕ → ℝ) (hη : 0 ≤ η) (ha : 0 < a) (hL : 0 < L)
    (T r : ℕ) (hr : r ≤ T)
    (hterminal : Real.exp η - 1 ≤ T * (256 * ((2 * η * Real.exp η / a) / L) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / L))))))
    (hθ : 0 ≤ θ) (hy : r < T → y r ≤ θ) :
    let s := 2 * η * Real.exp η / a
    let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
    Real.exp η - 1 - s * θ - r * K ≤ ∑ j ∈ Finset.range T, loss η L a y j := by
  dsimp only
  let s := 2 * η * Real.exp η / a
  let K := 256 * (s / L) * (1 + max 0 (Real.log (256 * (s / L))))
  change Real.exp η - 1 - s * θ - r * K ≤ _
  have hs : 0 ≤ s := by dsimp [s]; positivity
  by_cases hrt : r < T
  · have hp := prefix_lower η L a y hη ha hL r
    have hsum : (∑ j ∈ Finset.range (r + 1), loss η L a y j) ≤
        ∑ j ∈ Finset.range T, loss η L a y j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun j _ _ => loss_nonnegative η L a y hη j)
    have hh := mul_le_mul_of_nonneg_left (hy hrt) hs
    change Real.exp η - 1 - s * y r - r * K ≤ _ at hp
    linarith only [hp, hsum, hh]
  · have he : r = T := by omega
    subst r
    have hsum := Finset.sum_nonneg (s := Finset.range T) (fun j _ => loss_nonnegative η L a y hη j)
    have hh := mul_nonneg hs hθ
    change Real.exp η - 1 ≤ (T : ℝ) * K at hterminal
    linarith only [hterminal, hsum, hh]

end LongTails.Proofs.InterpolatedFiniteSumLinkResidual
