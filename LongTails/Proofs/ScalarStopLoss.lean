import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace OracleTemplate.ScalarStopLoss

noncomputable def weight (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => weight d n / (1+d n)

lemma weight_nonneg (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    0 ≤ weight d n := by
  induction n with
  | zero => simp [weight]
  | succ n ih => exact div_nonneg ih (by linarith [hd n])

lemma weight_le_one (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    weight d n ≤ 1 := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [weight]
    apply (div_le_iff₀ (by linarith [hd n] : 0 < 1+d n)).mpr
    linarith [hd n]

lemma weight_identity (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    weight d n = (1+d n) * weight d (n+1) := by
  rw [weight]
  have h : 1+d n ≠ 0 := ne_of_gt (by linarith [hd n])
  field_simp

lemma weighted_drift (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (n : ℕ) :
    (1-d n)/2 * weight d n ≤ (1+d n)/2 * weight d (n+1) := by
  have he := weight_identity d hd n
  have hn := weight_nonneg d hd n
  nlinarith [mul_nonneg (hd n) hn]

lemma slope_energy_step (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hu : ∀ n, d n ≤ 1) (n : ℕ) :
    d (n+1) * weight d n ≤ 4 * (weight d (n+1)-weight d (n+2)) := by
  have h1 := weight_identity d hd n
  have h2 := weight_identity d hd (n+1)
  have hn := weight_nonneg d hd (n+2)
  have he : weight d n = (1+d n)*(1+d (n+1))*weight d (n+2) := by
    rw [h1, h2]
    ring
  have hp : (1+d n)*(1+d (n+1)) ≤ 4 := by
    have hprod := mul_nonneg (sub_nonneg.mpr (hu n))
      (show 0 ≤ 1+d (n+1) by linarith [hd (n+1)])
    nlinarith [hu (n+1)]
  have hx : 0 ≤ d (n+1)*weight d (n+2) := mul_nonneg (hd _) hn
  have hm := mul_le_mul_of_nonneg_right hp hx
  calc
    d (n+1)*weight d n = (1+d n)*(1+d (n+1))*(d (n+1)*weight d (n+2)) := by
      rw [he]
      ring
    _ ≤ 4*(d (n+1)*weight d (n+2)) := hm
    _ = 4*(weight d (n+1)-weight d (n+2)) := by rw [h2]; ring

lemma slope_energy_sum (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hu : ∀ n, d n ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, d (n+1)*weight d n ≤
      4*(weight d 1-weight d (N+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := slope_energy_step d hd hu N
    have he : N+1+1 = N+2 := by omega
    rw [he]
    linarith

lemma slope_energy_bound (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hu : ∀ n, d n ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, d (n+1)*weight d n ≤ 4 := by
  have hs := slope_energy_sum d hd hu N
  have h1 := weight_le_one d hd 1
  have hn := weight_nonneg d hd (N+1)
  linarith

lemma slope_energy_shifted (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hu : ∀ n, d n ≤ 1) (a N : ℕ) :
    ∑ n ∈ Finset.range N, d (a+n+1)*weight d (a+n) ≤
      4*(weight d (a+1)-weight d (a+N+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := slope_energy_step d hd hu (a+N)
    have he : a+(N+1)+1 = a+N+2 := by omega
    rw [he]
    linarith

lemma slope_energy_shifted_bound (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hu : ∀ n, d n ≤ 1) (a N : ℕ) :
    ∑ n ∈ Finset.range N, d (a+n+1)*weight d (a+n) ≤ 4 := by
  have hs := slope_energy_shifted d hd hu a N
  have h1 := weight_le_one d hd (a+1)
  have hn := weight_nonneg d hd (a+N+1)
  linarith

lemma summation_by_parts (d P : ℕ → ℝ) (a n : ℕ) :
    ∑ j ∈ Finset.range n, (d (a+j+1)-d (a+j))*P (a+j+1) =
      (∑ j ∈ Finset.range n, d (a+j)*(P (a+j)-P (a+j+1))) +
        d (a+n)*P (a+n)-d a*P a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Nat.add_assoc]
    ring

noncomputable def envelope (d : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k N, weight d (j-1)

lemma envelope_nonneg (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (N k : ℕ) :
    0 ≤ envelope d N k := by
  exact Finset.sum_nonneg (fun j _ => weight_nonneg d hd (j-1))

lemma envelope_above (d : ℕ → ℝ) {N k : ℕ} (h : N ≤ k) :
    envelope d N k = 0 := by
  simp [envelope, Finset.Ico_eq_empty_of_le h]

lemma envelope_step (d : ℕ → ℝ) {N k : ℕ} (h : k < N) :
    envelope d N k = weight d (k-1)+envelope d N (k+1) := by
  exact Finset.sum_eq_sum_Ico_succ_bot h _

lemma envelope_difference_le (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (N k : ℕ) :
    envelope d N k-envelope d N (k+1) ≤ weight d (k-1) := by
  by_cases h : k < N
  · rw [envelope_step d h]
    linarith
  · rw [envelope_above d (by omega : N ≤ k),
      envelope_above d (by omega : N ≤ k+1)]
    simpa using weight_nonneg d hd (k-1)

lemma envelope_objective (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hu : ∀ n, d n ≤ 1) (N : ℕ) :
    d 2*envelope d N 2 +
      (∑ j ∈ Finset.range N, (d (2+j+1)-d (2+j))*envelope d N (2+j+1)) ≤ 4 := by
  rw [summation_by_parts, envelope_above d (by omega : N ≤ 2+N)]
  simp only [mul_zero, add_zero]
  have hs : (∑ j ∈ Finset.range N,
      d (2+j)*(envelope d N (2+j)-envelope d N (2+j+1))) ≤
      ∑ j ∈ Finset.range N, d (1+j+1)*weight d (1+j) := by
    apply Finset.sum_le_sum
    intro j _
    have he := envelope_difference_le d hd N (2+j)
    have hj : 2+j-1 = 1+j := by omega
    rw [hj] at he
    have hm := mul_le_mul_of_nonneg_left he (hd (2+j))
    convert hm using 1
    congr 2
    omega
  have hb := slope_energy_shifted_bound d hd hu 1 N
  linarith

lemma envelope_boundary (d : ℕ → ℝ) {N : ℕ} (h : 2 ≤ N) :
    envelope d N 1 = envelope d N 2+1 := by
  rw [envelope_step d (by omega : 1 < N)]
  simp [weight, add_comm]

lemma envelope_superharmonic (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    {N k : ℕ} (hk : 2 ≤ k) (hN : k < N) :
    (1-d (k-2))/2 * envelope d N (k-1) +
      (1+d (k-2))/2 * envelope d N (k+1) ≤ envelope d N k := by
  have hkm : k-1 < N := by omega
  have he1 := envelope_step d hkm
  have he2 := envelope_step d hN
  have hi1 : k-1+1 = k := by omega
  have hi2 : k-1-1 = k-2 := by omega
  have hi3 : k-2+1 = k-1 := by omega
  rw [hi1, hi2] at he1
  have hw := weighted_drift d hd (k-2)
  rw [hi3] at hw
  rw [he1, he2]
  nlinarith

lemma finite_envelope_induction (d : ℕ → ℝ) (H : ℕ → ℕ → ℝ) (N : ℕ)
    (hd : ∀ n, 0 ≤ d n) (hu : ∀ n, d n ≤ 1)
    (hinit : ∀ k, H 0 k ≤ 0)
    (hupper : ∀ n ≤ N, ∀ k, N ≤ k → H n k ≤ 0)
    (hboundary : ∀ n ≤ N, H n 1 ≤ H n 2+1)
    (hstep : ∀ n < N, ∀ k, 2 ≤ k → k < N →
      H (n+1) k ≤ (1-d (k-2))/2 * H n (k-1) +
        (1+d (k-2))/2 * H n (k+1)) :
    ∀ n ≤ N, ∀ k, 2 ≤ k → H n k ≤ envelope d N k := by
  intro n
  induction n with
  | zero =>
    intro _ k _
    exact (hinit k).trans (envelope_nonneg d hd N k)
  | succ n ih =>
    intro hn k hk
    by_cases hNk : N ≤ k
    · exact (hupper (n+1) hn k hNk).trans (envelope_nonneg d hd N k)
    have hkN : k < N := lt_of_not_ge hNk
    have hnN : n ≤ N := by omega
    have hlo : H n (k-1) ≤ envelope d N (k-1) := by
      by_cases hkm : 2 ≤ k-1
      · exact ih hnN (k-1) hkm
      · have he : k = 2 := by omega
        subst k
        rw [show 2-1 = 1 from rfl, envelope_boundary d (by omega)]
        have hb := hboundary n hnN
        have hi := ih hnN 2 le_rfl
        linarith
    have hhi := ih hnN (k+1) (by omega)
    have hp : 0 ≤ (1-d (k-2))/2 := by linarith [hu (k-2)]
    have hq : 0 ≤ (1+d (k-2))/2 := by linarith [hd (k-2)]
    calc
      H (n+1) k ≤ (1-d (k-2))/2 * H n (k-1) +
          (1+d (k-2))/2 * H n (k+1) := hstep n (by omega) k hk hkN
      _ ≤ (1-d (k-2))/2 * envelope d N (k-1) +
          (1+d (k-2))/2 * envelope d N (k+1) :=
        add_le_add (mul_le_mul_of_nonneg_left hlo hp) (mul_le_mul_of_nonneg_left hhi hq)
      _ ≤ envelope d N k := envelope_superharmonic d hd hk hkN

lemma hinge_chord {x v a : ℝ} (hv : |v| ≤ 1) :
    max 0 (x+v-a) ≤ (1+v)/2 * max 0 (x+1-a) +
      (1-v)/2 * max 0 (x-1-a) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hv
  have hp : 0 ≤ (1+v)/2 := by linarith
  have hq : 0 ≤ (1-v)/2 := by linarith
  apply max_le
  · positivity
  · have h1 := mul_le_mul_of_nonneg_left (le_max_right 0 (x+1-a)) hp
    have h2 := mul_le_mul_of_nonneg_left (le_max_right 0 (x-1-a)) hq
    nlinarith

lemma hinge_threshold_shift {x a b : ℝ} (hab : a ≤ b) :
    max 0 (x-a) ≤ max 0 (x-b) + (b-a) := by
  apply max_le
  · have := le_max_left 0 (x-b)
    linarith
  · have := le_max_right 0 (x-b)
    linarith

lemma hinge_secant_bounds (x a : ℝ) :
    0 ≤ (max 0 (x+1-a)-max 0 (x-1-a))/2 ∧
      (max 0 (x+1-a)-max 0 (x-1-a))/2 ≤ 1 := by
  have hm : max 0 (x-1-a) ≤ max 0 (x+1-a) := max_le_max le_rfl (by linarith)
  have hs := hinge_threshold_shift (x := x) (a := a-1) (b := a+1) (by linarith)
  have he1 : x-(a-1) = x+1-a := by ring
  have he2 : x-(a+1) = x-1-a := by ring
  rw [he1, he2] at hs
  constructor <;> linarith

lemma hinge_drift_comparison (x a d v : ℝ)
    (hv : a-1 ≤ x → v ≤ -d) :
    (max 0 (x+1-a)+max 0 (x-1-a))/2 +
      (max 0 (x+1-a)-max 0 (x-1-a))/2*v ≤
        (1-d)/2*max 0 (x+1-a)+(1+d)/2*max 0 (x-1-a) := by
  by_cases h : a-1 ≤ x
  · have hm := mul_le_mul_of_nonneg_left (hv h) (hinge_secant_bounds x a).1
    nlinarith
  · have h1 : max 0 (x+1-a) = 0 := max_eq_left (by linarith)
    have h2 : max 0 (x-1-a) = 0 := max_eq_left (by linarith)
    simp [h1, h2]


end OracleTemplate.ScalarStopLoss
