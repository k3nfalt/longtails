import LongTails.Proofs.SampleLossChain

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SampleLossCalculus
open LongTails.Proofs.SampleLossMixture LongTails.Proofs.SampleLossChain

namespace LongTails.Proofs.SampleLossRegularity

variable {E B : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

variable (P : ℕ → E →L[ℝ] B) {u : ℕ → B}

omit [CompleteSpace B] in
lemma increment_current (v : E) (j : ℕ) : 2048 * ‖P j v‖ ≤ increment P v j := by
  cases j with
  | zero => rfl
  | succ j => simp only [increment]; linarith [norm_nonneg (P j v)]

omit [CompleteSpace B] in
lemma increment_previous (v : E) (j : ℕ) : 2048 * ‖P j v‖ ≤ increment P v (j + 1) := by
  simp only [increment]
  linarith [norm_nonneg (P (j + 1) v)]

omit [CompleteSpace B] in
lemma increment_nonneg (v : E) (j : ℕ) : 0 ≤ increment P v j :=
  (mul_nonneg (by norm_num) (norm_nonneg _)).trans (increment_current P v j)

lemma signal_bounds (hu : ∀ j, ‖u j‖ ≤ 1) (j : ℕ) (x v : E) :
    |signal P u j (x + v) - signal P u j x| ≤ increment P v j ∧
    |signal P u j (x + v) - signal P u j x - fderiv ℝ (signal P u j) x v| ≤
      increment P v j ^ 2 := by
  have hs := alignment_sub (u j) (P j x) (P j (x + v))
  have ht := alignment_model (u j) (P j x) (P j (x + v))
  simp only [map_add, add_sub_cancel_left] at hs ht
  have hn := norm_nonneg (P j v)
  have hc := increment_current P v j
  simp only [signal_fderiv, signal, map_add]
  constructor
  · nlinarith [hu j, mul_nonneg (sub_nonneg.mpr (hu j)) hn]
  · have hc2 := sq_le_sq' (by linarith : -(increment P v j) ≤ 2048 * ‖P j v‖) hc
    nlinarith [mul_nonneg (sub_nonneg.mpr (hu j)) (sq_nonneg ‖P j v‖)]

lemma incoming_bounds (hu : ∀ j, ‖u j‖ ≤ 1) (j : ℕ) (x v : E) :
    |fderiv ℝ (incoming P u j) x v| ≤ Real.sqrt (incoming P u j x) * increment P v j ∧
    |incoming P u j (x + v) - incoming P u j x - fderiv ℝ (incoming P u j) x v| ≤
      increment P v j ^ 2 := by
  cases j with
  | zero => simp [incoming, increment]
  | succ j =>
    rw [incoming_fderiv]
    obtain ⟨h1, h2⟩ := gate_alignment_model (hu j) (P j x) (P j (x + v))
    simp only [map_add, add_sub_cancel_left] at h1 h2
    have hc := increment_previous P v j
    have hn := norm_nonneg (P j v)
    simp only [incoming, signal, map_add]
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)),
      h2.trans (sq_le_sq' (by linarith) hc)⟩

lemma perturbation_model {w : ℕ → B} (hu : ∀ j, ‖u j‖ ≤ 1) (hw : ∀ j, ‖w j‖ ≤ 1)
    (n : ℕ) (x v : E) :
    |perturbation P u w n (x + v) - perturbation P u w n x -
      fderiv ℝ (perturbation P u w n) x v| ≤ 16 * ∑ j ∈ Finset.range n, increment P v j ^ 2 := by
  unfold perturbation
  rw [mixture_fderiv _ _ (incoming_differentiable P u) (signal_differentiable P w)]
  exact (mixture_model _ _ _ _ _ _ _ (fun j => incoming_mem P u j x)
    (fun j => incoming_mem P u j (x + v))
    (fun j => (alignment_abs _ _).trans (hw j)) (fun j => (alignment_abs _ _).trans (hw j))
    (increment_nonneg P v) (fun j => (incoming_bounds P hu j x v).1)
    (fun j => (incoming_bounds P hu j x v).2) (fun j => (signal_bounds P hw j x v).1)
    (fun j => (signal_bounds P hw j x v).2) n).2

omit [CompleteSpace B] in
lemma increment_energy (v : E) (n : ℕ) :
    ∑ j ∈ Finset.range n, increment P v j ^ 2 ≤
      16777216 * ∑ j ∈ Finset.range n, ‖P j v‖ ^ 2 := by
  suffices h : ∀ k : ℕ, (∑ j ∈ Finset.range (k+1), increment P v j ^ 2) +
      8388608 * ‖P k v‖ ^ 2 ≤ 16777216 * ∑ j ∈ Finset.range (k+1), ‖P j v‖ ^ 2 by
    cases n with
    | zero => simp
    | succ k => linarith [h k, sq_nonneg ‖P k v‖]
  intro k
  induction k with
  | zero => simp [increment]; nlinarith [sq_nonneg ‖P 0 v‖]
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j => ‖P j v‖ ^ 2)]
    rw [show increment P v (k+1) = 2048 * (‖P (k+1) v‖ + ‖P k v‖) from rfl]
    nlinarith [sq_nonneg (‖P (k+1) v‖ - ‖P k v‖)]

private lemma product_model {a a' b b' da db r : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (ha' : 0 ≤ a' ∧ a' ≤ 1) (hb : |b| ≤ 1) (hr : 0 ≤ r)
    (hd : |da| ≤ Real.sqrt a * r) (ht : |a' - a - da| ≤ r ^ 2)
    (hl : |b' - b| ≤ r) (he : |b' - b - db| ≤ r ^ 2) :
    |a' * (1 + b') - a * (1 + b) - (da * (1 + b) + a * db)| ≤ 5 * r ^ 2 := by
  have hs : Real.sqrt a ≤ 1 := by
    nlinarith [Real.sq_sqrt ha.1, ha.2, Real.sqrt_nonneg a]
  have hdiff : |a' - a| ≤ 2 * r := by
    by_cases h : 1 ≤ r
    · exact abs_le.mpr ⟨by linarith [ha.2, ha'.1], by linarith [ha.1, ha'.2]⟩
    · have hf := abs_add_le (a' - a - da) da
      rw [sub_add_cancel] at hf
      nlinarith [mul_le_mul_of_nonneg_right hs hr, mul_nonneg hr (by linarith : 0 ≤ 1-r)]
  have hprod := abs_add_le ((a'-a-da)*(1+b) + a*(b'-b-db)) ((a'-a)*(b'-b))
  have hsum := abs_add_le ((a'-a-da)*(1+b)) (a*(b'-b-db))
  have h1 : |1+b| ≤ 2 := by linarith [abs_add_le (1 : ℝ) b, (abs_one : |(1 : ℝ)| = 1)]
  rw [show a' * (1+b') - a*(1+b) - (da*(1+b)+a*db) =
    ((a'-a-da)*(1+b) + a*(b'-b-db)) + (a'-a)*(b'-b) by ring]
  simp only [abs_mul, abs_of_nonneg ha.1] at hprod hsum
  nlinarith [mul_le_mul ht h1 (abs_nonneg _) (sq_nonneg r),
    mul_le_mul ha.2 he (abs_nonneg _) zero_le_one,
    mul_le_mul hdiff hl (abs_nonneg _) (by linarith : 0 ≤ 2*r)]

lemma link_model (hu : ∀ j, ‖u j‖ ≤ 1) (j : ℕ) (x v : E) :
    |link P u j (x + v) - link P u j x - fderiv ℝ (link P u j) x v| ≤
      5 * increment P v j ^ 2 := by
  have ha := derivative_line x v (incoming_differentiable P u j x)
  have hb := derivative_line x v (signal_differentiable P u j x)
  have hd := ha.mul ((hasDerivAt_const 0 (1 : ℝ)).add hb)
  simp only [zero_smul, add_zero, zero_add] at hd
  have hf := (derivative_line x v (link_differentiable P u j x)).unique hd
  rw [hf]
  simpa [link, mul_comm, add_comm, add_left_comm] using
    product_model (incoming_mem P u j x) (incoming_mem P u j (x+v))
      (show |signal P u j x| ≤ 1 from (alignment_abs _ _).trans (hu j))
      (increment_nonneg P v j) (incoming_bounds P hu j x v).1 (incoming_bounds P hu j x v).2
      (signal_bounds P hu j x v).1 (signal_bounds P hu j x v).2

lemma base_direction (n : ℕ) (x v : E) :
    fderiv ℝ (base P u n) x v =
      2 * ⟪x, v⟫ - ∑ j ∈ Finset.range n, fderiv ℝ (link P u j) x v := by
  have hs := HasFDerivAt.fun_sum (u := Finset.range n)
    (fun j _ => (link_differentiable P u j x).hasFDerivAt)
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub hs).fderiv
  change fderiv ℝ (fun z => ‖z‖ ^ 2 - ∑ j ∈ Finset.range n, link P u j z) x v = _
  erw [hd]
  simp [innerSL_apply_apply]

lemma base_model (hu : ∀ j, ‖u j‖ ≤ 1) (n : ℕ) (x v : E) :
    |base P u n (x + v) - base P u n x - fderiv ℝ (base P u n) x v| ≤
      ‖v‖ ^ 2 + 5 * ∑ j ∈ Finset.range n, increment P v j ^ 2 := by
  rw [base_direction]
  unfold base
  rw [norm_add_sq_real]
  let d := fun j => link P u j (x+v) - link P u j x - fderiv ℝ (link P u j) x v
  have hd : ∑ j ∈ Finset.range n, d j = (∑ j ∈ Finset.range n, link P u j (x+v)) -
      (∑ j ∈ Finset.range n, link P u j x) - ∑ j ∈ Finset.range n, fderiv ℝ (link P u j) x v := by
    simp [d, Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => link_model P hu j x v)
  rw [← Finset.mul_sum] at h
  have hsum := Finset.abs_sum_le_sum_abs d (Finset.range n)
  have htri := abs_add_le (‖v‖ ^ 2) (-(∑ j ∈ Finset.range n, d j))
  rw [abs_of_nonneg (sq_nonneg ‖v‖), abs_neg, ← sub_eq_add_neg] at htri
  change (∑ j ∈ Finset.range n, |d j|) ≤ _ at h
  convert htri.trans (add_le_add_right (hsum.trans h) _) using 1
  rw [hd]
  congr 1
  ring

lemma sampleLoss_smooth [CompleteSpace E] {w : ℕ → B} (hu : ∀ j, ‖u j‖ ≤ 1) (hw : ∀ j, ‖w j‖ ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) (n : ℕ) (energy : ∀ v, ∑ j ∈ Finset.range n, ‖P j v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (x y : E) : ‖gradient (sampleLoss P u w M n) x - gradient (sampleLoss P u w M n) y‖ ≤
      2147483648 * (1 + M) * ‖x - y‖ := by
  have model (z v : E) : |sampleLoss P u w M n (z + v) - sampleLoss P u w M n z -
      fderiv ℝ (sampleLoss P u w M n) z v| ≤ 335544320 * (1 + M) * ‖v‖ ^ 2 := by
    have hd := (((hasFDerivAt_const (2 * (n : ℝ) + M) z).add (base_differentiable P u n z).hasFDerivAt).add
      ((perturbation_differentiable P u w n z).hasFDerivAt.const_mul M)).fderiv
    have hb := base_model P hu n z v
    have hp := perturbation_model P hu hw n z v
    have he := (increment_energy P v n).trans (mul_le_mul_of_nonneg_left (energy v) (by norm_num))
    let db := base P u n (z+v) - base P u n z - fderiv ℝ (base P u n) z v
    let dp := perturbation P u w n (z+v) - perturbation P u w n z - fderiv ℝ (perturbation P u w n) z v
    have ht := abs_add_le db (M * dp)
    rw [abs_mul, abs_of_nonneg hM] at ht
    change |db| ≤ _ at hb
    change |dp| ≤ _ at hp
    have hh : |db + M * dp| ≤ 335544320 * (1 + M) * ‖v‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hp hM, mul_le_mul_of_nonneg_left he hM,
        mul_nonneg hM (sq_nonneg ‖v‖), sq_nonneg ‖v‖]
    convert hh using 2
    unfold sampleLoss db dp
    erw [hd]
    simp
    ring
  have h := grad_lipschitz_of_model (show 0 ≤ 335544320 * (1 + M) by positivity)
    (sampleLoss_differentiable P u w M n) model x y
  nlinarith [mul_nonneg (add_nonneg zero_le_one hM) (norm_nonneg (x-y))]

end LongTails.Proofs.SampleLossRegularity
