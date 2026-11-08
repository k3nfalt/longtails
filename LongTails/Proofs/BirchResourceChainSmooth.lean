import LongTails.Proofs.BirchResourceChain

namespace LongTails.Proofs.BirchResourceChain

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Proofs.BirchResourceChainScalars

lemma grad_split {D : ℕ} (x : Point D) (i : Fin D) :
    gradient objective x i = (if i.val = 0 then -payoffSlope (coord x i) else 0) +
      (if i.val < D - 1 then leftSlope x i else 0) +
      (if 0 < i.val then rightSlope x (i.val - 1) else 0) := by
  rw [gradient_coordinate, sum_add_distrib, ← add_assoc]
  congr 1
  · congr 1
    · by_cases hi : i.val = 0 <;> simp [coefficient, hi, eq_comm]
    · by_cases hi : i.val < D - 1
      · rw [ite_eq_left hi, sum_eq_single_of_mem i.val (mem_range.mpr hi)]
        · simp [coefficient]
        · intro j _ hj
          simp [coefficient, hj]
      · rw [ite_eq_right hi]
        apply sum_eq_zero
        intro j hj
        have hne : j ≠ i.val := fun he => hi (he ▸ mem_range.mp hj)
        simp [coefficient, hne]
  · by_cases hi : 0 < i.val
    · have hv := i.isLt
      have hl : i.val - 1 ∈ range (D - 1) := mem_range.mpr (by omega)
      have he : i.val - 1 + 1 = i.val := by omega
      rw [ite_eq_left hi, sum_eq_single_of_mem (i.val - 1) hl]
      · simp [coefficient, he]
      · intro j _ hj
        have hne : j + 1 ≠ i.val := by omega
        simp [coefficient, hne]
    · rw [ite_eq_right hi]
      apply sum_eq_zero
      intro j _
      have hne : j + 1 ≠ i.val := by omega
      simp [coefficient, hne]

lemma product_diff (a b c d A C da dc : ℝ)
    (hA : |b| ≤ A) (hC : |c| ≤ C) (ha : |a - b| ≤ da) (hc : |c - d| ≤ dc) :
    |a * c - b * d| ≤ C * da + A * dc := by
  have hC' := (abs_nonneg c).trans hC
  have hA' := (abs_nonneg b).trans hA
  calc
    _ = |(a - b) * c + b * (c - d)| := by ring_nf
    _ ≤ |(a - b) * c| + |b * (c - d)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, mul_comm |a - b| |c|]
      exact add_le_add (mul_le_mul hC ha (abs_nonneg _) hC')
        (mul_le_mul hA hc (abs_nonneg _) hA')

lemma signed_diff (neg : Bool) (a b : ℝ) :
    |(if neg then -a else a) - (if neg then -b else b)| = |a - b| := by
  cases neg
  · rfl
  · simp only [ite_true]
    rw [show -a - -b = -(a - b) by ring, abs_neg]

lemma left_lip {D : ℕ} (x y : Point D) (j : ℕ) :
    |leftSlope x j - leftSlope y j| ≤ 8 * |coord x j - coord y j| +
      |coord x (j + 1) - coord y (j + 1)| := by
  let a := fun z : Point D => gateSlope (-coord z j) * payoff (-coord z (j + 1))
  let b := fun z : Point D => gateSlope (coord z j) * payoff (coord z (j + 1))
  have h (neg : Bool) :
      let f := fun (z : Point D) k => if neg then -coord z k else coord z k
      |gateSlope (f x j) * payoff (f x (j + 1)) -
        gateSlope (f y j) * payoff (f y (j + 1))| ≤
        4 * |coord x j - coord y j| + (1 / 2) * |coord x (j + 1) - coord y (j + 1)| := by
    dsimp only
    apply product_diff
    · rw [abs_of_nonneg (gateSlope_range _).1]
      exact (gateSlope_range _).2
    · rw [abs_of_nonneg (payoff_range _).1]
      exact (payoff_range _).2
    · refine (gateSlope_lip _ _).trans ?_
      exact (signed_diff neg _ _).le
    · refine (payoff_lip _ _).trans ?_
      exact (signed_diff neg _ _).le
  have he : leftSlope x j - leftSlope y j = (a y - a x) + (b y - b x) := by
    unfold leftSlope a b
    ring
  rw [he]
  have h₁ := h true
  have h₂ := h false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h₁ h₂
  have hab := abs_add_le (a y - a x) (b y - b x)
  rw [abs_sub_comm (a y) (a x), abs_sub_comm (b y) (b x)] at hab
  linarith only [hab, h₁, h₂]

lemma right_lip {D : ℕ} (x y : Point D) (j : ℕ) :
    |rightSlope x j - rightSlope y j| ≤ 2 * |coord x j - coord y j| +
      |coord x (j + 1) - coord y (j + 1)| := by
  let a := fun z : Point D => gate (-coord z j) * payoffSlope (-coord z (j + 1))
  let b := fun z : Point D => gate (coord z j) * payoffSlope (coord z (j + 1))
  have h (neg : Bool) :
      let f := fun (z : Point D) k => if neg then -coord z k else coord z k
      |gate (f x j) * payoffSlope (f x (j + 1)) -
        gate (f y j) * payoffSlope (f y (j + 1))| ≤
        1 * |coord x j - coord y j| + (1 / 2) * |coord x (j + 1) - coord y (j + 1)| := by
    dsimp only
    apply product_diff
    · rw [abs_of_nonneg (gate_range _).1]
      exact (gate_range _).2
    · rw [abs_of_nonneg (payoffSlope_range _).1]
      exact (payoffSlope_range _).2
    · refine (gate_lip _ _).trans ?_
      exact (signed_diff neg _ _).le
    · refine (payoffSlope_lip _ _).trans ?_
      exact (signed_diff neg _ _).le
  have he : rightSlope x j - rightSlope y j = (a y - a x) + (b y - b x) := by
    unfold rightSlope a b
    ring
  rw [he]
  have h₁ := h true
  have h₂ := h false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h₁ h₂
  have hab := abs_add_le (a y - a x) (b y - b x)
  rw [abs_sub_comm (a y) (a x), abs_sub_comm (b y) (b x)] at hab
  linarith only [hab, h₁, h₂]

def delta {D : ℕ} (x y : Point D) (j : ℕ) : ℝ := |coord x j - coord y j|

def prevDelta {D : ℕ} (x y : Point D) (j : ℕ) : ℝ :=
  if j = 0 then 0 else delta x y (j - 1)

lemma grad_diff_coord {D : ℕ} (x y : Point D) (i : Fin D) :
    |gradient objective x i - gradient objective y i| ≤
      10 * (prevDelta x y i + delta x y i + delta x y (i + 1)) := by
  rw [grad_split x i, grad_split y i]
  let a := fun z : Point D => if i.val = 0 then -payoffSlope (coord z i) else 0
  let b := fun z : Point D => if i.val < D - 1 then leftSlope z i else 0
  let c := fun z : Point D => if 0 < i.val then rightSlope z (i.val - 1) else 0
  have ha : |a x - a y| ≤ delta x y i := by
    dsimp only [a, delta]
    by_cases hz : i.val = 0
    · simp only [ite_eq_left hz, neg_sub_neg]
      rw [abs_sub_comm]
      exact payoffSlope_lip _ _
    · simp [hz, abs_nonneg]
  have hb : |b x - b y| ≤ 8 * delta x y i + delta x y (i + 1) := by
    by_cases hz : i.val < D - 1
    · simpa only [b, ite_eq_left hz, delta] using left_lip x y i
    · simp [b, hz, delta]
      positivity
  have hc : |c x - c y| ≤ 2 * prevDelta x y i + delta x y i := by
    by_cases hz : 0 < i.val
    · have he : i.val - 1 + 1 = i.val := by omega
      simpa only [c, prevDelta, ite_eq_left hz, ite_eq_right (Nat.ne_of_gt hz), delta, he] using
        right_lip x y (i.val - 1)
    · have he : i.val = 0 := by omega
      simp [c, prevDelta, he, delta]
  change |a x + b x + c x - (a y + b y + c y)| ≤ _
  rw [show a x + b x + c x - (a y + b y + c y) =
    (a x - a y + (b x - b y)) + (c x - c y) by ring]
  have h₁ := abs_add_le (a x - a y + (b x - b y)) (c x - c y)
  have h₂ := abs_add_le (a x - a y) (b x - b y)
  have hpre : 0 ≤ prevDelta x y i := by unfold prevDelta delta; split <;> positivity
  have hδ : 0 ≤ delta x y (i.val + 1) := abs_nonneg _
  linarith only [ha, hb, hc, h₁, h₂, hpre, hδ]

lemma coord_norm_sq {D : ℕ} (x y : Point D) :
    ∑ i ∈ range D, delta x y i ^ 2 = ‖x - y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  change delta x y i ^ 2 = ‖x i - y i‖ ^ 2
  simp [delta, coord, i.isLt, Real.norm_eq_abs]

lemma next_sq_sum {D : ℕ} (x y : Point D) :
    ∑ i ∈ range D, delta x y (i + 1) ^ 2 ≤ ∑ i ∈ range D, delta x y i ^ 2 := by
  have he : (∑ i ∈ range (D + 1), delta x y i ^ 2) =
      (∑ i ∈ range D, delta x y i ^ 2) := by
    rw [sum_range_succ]
    simp [delta, coord]
  rw [sum_range_succ'] at he
  linarith only [he, sq_nonneg (delta x y 0)]

lemma prev_sq_sum {D : ℕ} (x y : Point D) (n : ℕ) :
    ∑ i ∈ range n, prevDelta x y i ^ 2 ≤ ∑ i ∈ range n, delta x y i ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ', sum_range_succ]
    simp [prevDelta]
    positivity

lemma objective_smooth {D : ℕ} (x y : Point D) :
    ‖gradient objective x - gradient objective y‖ ≤ 30 * ‖x - y‖ := by
  have hcoord (i : Fin D) :
      ‖(gradient objective x - gradient objective y) i‖ ^ 2 ≤
        300 * (prevDelta x y i ^ 2 + delta x y i ^ 2 + delta x y (i + 1) ^ 2) := by
    change ‖gradient objective x i - gradient objective y i‖ ^ 2 ≤ _
    rw [Real.norm_eq_abs]
    have h := grad_diff_coord x y i
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).2 h
    nlinarith only [hsq, sq_nonneg (prevDelta x y i - delta x y i),
      sq_nonneg (prevDelta x y i - delta x y (i + 1)),
      sq_nonneg (delta x y i - delta x y (i + 1))]
  have hsum := sum_le_sum (s := (univ : Finset (Fin D))) (fun i _ => hcoord i)
  rw [← EuclideanSpace.norm_sq_eq, ← mul_sum] at hsum
  rw [Fin.sum_univ_eq_sum_range
    (fun j => prevDelta x y j ^ 2 + delta x y j ^ 2 + delta x y (j + 1) ^ 2)] at hsum
  simp only [sum_add_distrib] at hsum
  have h := coord_norm_sq x y
  have hp := prev_sq_sum x y D
  have hn := next_sq_sum x y
  have hs : ‖gradient objective x - gradient objective y‖ ^ 2 ≤ (30 * ‖x - y‖) ^ 2 := by
    nlinarith only [hsum, h, hp, hn]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hs

end LongTails.Proofs.BirchResourceChain
