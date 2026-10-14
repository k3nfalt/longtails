import LongTails.Proofs.TemporalLinearResponse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Module

namespace OracleTemplate.TemporalDiscrepancy

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma linear_response_formula (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (v : ℕ → V) (e : ℕ → E)
    (hstep : ∀ n, v (n + 1) = T (v n) + B (e n)) (n : ℕ) :
    v n = (T ^ n) (v 0) + ∑ i ∈ Finset.range n, (T ^ (n - 1 - i)) (B (e i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hstep, ih, map_add, map_sum, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero]
    rw [pow_succ']
    have hh : ∑ i ∈ Finset.range n, T ((T ^ (n - 1 - i)) (B (e i))) =
        ∑ i ∈ Finset.range n, (T ^ (n - i)) (B (e i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [show n - i = (n - 1 - i) + 1 by omega, pow_succ']
      rfl
    rw [hh]
    exact add_assoc _ _ _

lemma operator_sum_by_parts (K : ℕ → E →L[ℝ] E) (e : ℕ → E) (n : ℕ) :
    (∑ i ∈ Finset.range n, K i (e i)) =
      K (n - 1) (∑ i ∈ Finset.range n, e i) -
        ∑ i ∈ Finset.range (n - 1), (K (i + 1) - K i)
          (∑ j ∈ Finset.range (i + 1), e j) := by
  exact Finset.sum_range_by_parts (fun i => (K i).toLinearMap) e n

lemma balanced_convolution_bound (K : ℕ → E →L[ℝ] E) (e : ℕ → E)
    {α β q D : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hq : 0 ≤ q) (hq1 : q < 1)
    (hD : 0 ≤ D) (hK0 : ∀ x, ‖K 0 x‖ ≤ α * ‖x‖)
    (hKd : ∀ j x, ‖(K (j + 1) - K j) x‖ ≤ β * q ^ j * ‖x‖)
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, K (n - 1 - i) (e i)‖ ≤ (α + β / (1 - q)) * D := by
  have hden : 0 < 1 - q := by linarith
  cases n with
  | zero => simpa using mul_nonneg (add_nonneg hα (div_nonneg hβ hden.le)) hD
  | succ n =>
    rw [operator_sum_by_parts]
    simp only [Nat.add_sub_cancel, Nat.sub_self]
    have hs : ‖∑ i ∈ Finset.range n,
        (K (n - (i + 1)) - K (n - i)) (∑ j ∈ Finset.range (i + 1), e j)‖ ≤
        β * D * ∑ i ∈ Finset.range n, q ^ i := by
      calc
        _ ≤ ∑ i ∈ Finset.range n,
            ‖(K (n - (i + 1)) - K (n - i)) (∑ j ∈ Finset.range (i + 1), e j)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range n, β * q ^ (n - 1 - i) * D := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          have hni : n - i = (n - 1 - i) + 1 := by omega
          have hni' : n - (i + 1) = n - 1 - i := by omega
          rw [hni, hni', sub_apply, norm_sub_rev,
            ← sub_apply]
          exact (hKd _ _).trans (mul_le_mul_of_nonneg_left (he _) (by positivity))
        _ = β * D * ∑ i ∈ Finset.range n, q ^ i := by
          simp_rw [show ∀ i, β * q ^ (n - 1 - i) * D =
            β * D * q ^ (n - 1 - i) by intro i; ring]
          rw [← Finset.mul_sum, Finset.sum_range_reflect]
    have hg : (∑ i ∈ Finset.range n, q ^ i) ≤ 1 / (1 - q) := by
      apply (le_div_iff₀ hden).mpr
      rw [geom_sum_mul_neg]
      linarith [pow_nonneg hq n]
    have hfirst := (hK0 _).trans (mul_le_mul_of_nonneg_left (he (n + 1)) hα)
    have hsecond := hs.trans (mul_le_mul_of_nonneg_left hg (mul_nonneg hβ hD))
    have hh := norm_sub_le (K 0 (∑ i ∈ Finset.range (n + 1), e i))
      (∑ i ∈ Finset.range n,
        (K (n - (i + 1)) - K (n - i)) (∑ j ∈ Finset.range (i + 1), e j))
    calc
      _ ≤ α * D + β * D * (1 / (1 - q)) := hh.trans (add_le_add hfirst hsecond)
      _ = _ := by ring

lemma difference_response_identity (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (v : ℕ → V) (s : ℕ → E)
    (hv : ∀ k, v (k + 1) = T (v k) + B (s (k + 1) - s k)) (k : ℕ) :
    v (k + 1) - B (s (k + 1)) =
      T (v k - B (s k)) + (T.comp B - B) (s k) := by
  rw [hv, map_sub, map_sub]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  abel

lemma bounded_forcing_response (T : V →L[ℝ] V) (p : Seminorm ℝ V)
    (v w : ℕ → V) {ρ C : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hT : ∀ x, p (T x) ≤ ρ * p x)
    (hv : ∀ k, v (k + 1) = T (v k) + w k)
    (hw : ∀ k, p (w k) ≤ C) (n : ℕ) :
    p (v n) ≤ ρ ^ n * p (v 0) + C / (1 - ρ) := by
  have hd : 0 < 1 - ρ := sub_pos.mpr hρ1
  induction n with
  | zero =>
    simpa only [pow_zero, one_mul] using
      le_add_of_nonneg_right (div_nonneg hC hd.le)
  | succ n ih =>
    rw [hv]
    calc
      _ ≤ p (T (v n)) + p (w n) := map_add_le_add p _ _
      _ ≤ ρ * p (v n) + C := add_le_add (hT _) (hw _)
      _ ≤ ρ * (ρ ^ n * p (v 0) + C / (1 - ρ)) + C :=
        add_le_add (mul_le_mul_of_nonneg_left ih hρ) le_rfl
      _ = ρ ^ (n + 1) * p (v 0) + C / (1 - ρ) := by
        rw [pow_succ]
        field_simp; ring

lemma difference_response_bound (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (p : Seminorm ℝ V) (v : ℕ → V) (s : ℕ → E)
    {ρ β γ D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hD : 0 ≤ D)
    (hT : ∀ x, p (T x) ≤ ρ * p x)
    (hB : ∀ x, p (B x) ≤ β * ‖x‖)
    (hTB : ∀ x, p ((T.comp B - B) x) ≤ γ * ‖x‖)
    (hs : ∀ k, ‖s k‖ ≤ D) (hs0 : s 0 = 0)
    (hv : ∀ k, v (k + 1) = T (v k) + B (s (k + 1) - s k)) (n : ℕ) :
    p (v n) ≤ ρ ^ n * p (v 0) + (β + γ / (1 - ρ)) * D := by
  have hh := bounded_forcing_response T p
    (fun k => v k - B (s k)) (fun k => (T.comp B - B) (s k))
    hρ hρ1 (mul_nonneg hγ hD) hT
    (difference_response_identity T B v s hv)
    (fun k => (hTB _).trans (mul_le_mul_of_nonneg_left (hs k) hγ)) n
  simp only [hs0, map_zero, sub_zero] at hh
  have hb := (hB (s n)).trans (mul_le_mul_of_nonneg_left (hs n) hβ)
  calc
    p (v n) = p ((v n - B (s n)) + B (s n)) := by rw [sub_add_cancel]
    _ ≤ p (v n - B (s n)) + p (B (s n)) := map_add_le_add p _ _
    _ ≤ (ρ ^ n * p (v 0) + γ * D / (1 - ρ)) + β * D := add_le_add hh hb
    _ = _ := by ring

lemma chebyshev_second_abs_le (n : ℕ) {c : ℝ} (hc : |c| ≤ 1) :
    |(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, Polynomial.Chebyshev.U_eq_X_mul_U_add_T]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    calc
      _ ≤ |c * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c| +
          |(Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval c| := abs_add_le _ _
      _ ≤ 1 * ((n : ℝ) + 1) + 1 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hc ih (abs_nonneg _) (by norm_num))
          (Polynomial.Chebyshev.abs_eval_T_real_le_one _ hc)
      _ = _ := by push_cast; ring

noncomputable def chebyshevImpulse (r c : ℝ) (n : ℕ) : ℝ :=
  r ^ n * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c

lemma chebyshev_impulse_difference (r c : ℝ) (n : ℕ) :
    chebyshevImpulse r c (n + 1) - chebyshevImpulse r c n =
      r ^ (n + 1) * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval c +
        r ^ n * (r * c - 1) * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c := by
  simp only [chebyshevImpulse, Nat.cast_add, Nat.cast_one,
    Polynomial.Chebyshev.U_eq_X_mul_U_add_T, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X, pow_succ]
  ring

lemma chebyshev_impulse_difference_bound {r c : ℝ}
    (hr : 0 ≤ r) (hc : |c| ≤ 1) (hd : |r * c - 1| ≤ 2 * (1 - r)) (n : ℕ) :
    |chebyshevImpulse r c (n + 1) - chebyshevImpulse r c n| ≤
      r ^ (n + 1) + 2 * (1 - r) * (n + 1) * r ^ n := by
  rw [chebyshev_impulse_difference]
  apply (abs_add_le _ _).trans
  simp only [abs_mul, abs_pow, abs_of_nonneg hr]
  have hfirst := mul_le_mul_of_nonneg_left
    (Polynomial.Chebyshev.abs_eval_T_real_le_one ((n : ℤ) + 1) hc)
    (pow_nonneg hr (n + 1))
  have hsecond := mul_le_mul hd (chebyshev_second_abs_le n hc)
    (abs_nonneg ((Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c))
    ((abs_nonneg (r * c - 1)).trans hd)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond (pow_nonneg hr n)
  nlinarith only [hfirst, hsecond']

lemma geometric_derivative_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    (n + 1 : ℝ) * (1 - q) * q ^ n ≤ 1 := by
  have hsum : (n + 1 : ℝ) * q ^ n ≤ ∑ j ∈ Finset.range (n + 1), q ^ j := by
    calc
      _ = ∑ _j ∈ Finset.range (n + 1), q ^ n := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj =>
        pow_le_pow_of_le_one hq hq1 (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hq1)
  rw [geom_sum_mul_neg] at hm
  nlinarith [pow_nonneg hq (n + 1)]

lemma geometric_derivative_envelope {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    (n + 1 : ℝ) * (1 - r) * r ^ n ≤ 2 * (Real.sqrt r) ^ n := by
  let q := Real.sqrt r
  have hq : 0 ≤ q := Real.sqrt_nonneg r
  have hq1 : q ≤ 1 := (Real.sqrt_le_one).mpr hr1
  have hsq : q ^ 2 = r := Real.sq_sqrt hr
  have hd := geometric_derivative_bound hq hq1 n
  have hmul := mul_le_mul_of_nonneg_right hd
    (show 0 ≤ (1 + q) * q ^ n by positivity)
  have he : (n + 1 : ℝ) * (1 - r) * r ^ n =
      ((n + 1 : ℝ) * (1 - q) * q ^ n) * ((1 + q) * q ^ n) := by
    rw [← hsq, ← pow_mul, Nat.mul_comm 2 n, pow_mul]
    ring
  rw [he]
  calc
    _ ≤ (1 + q) * q ^ n := by simpa using hmul
    _ ≤ 2 * q ^ n := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq n)

lemma chebyshev_difference_envelope {r c q : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hc : |c| ≤ 1)
    (hd : |r * c - 1| ≤ 2 * (1 - r)) (hq : Real.sqrt r ≤ q) (n : ℕ) :
    |chebyshevImpulse r c (n + 1) - chebyshevImpulse r c n| ≤ 5 * q ^ n := by
  have hq0 := (Real.sqrt_nonneg r).trans hq
  have hroot1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
  have hroot : r ≤ Real.sqrt r := by
    have hs := Real.sq_sqrt hr
    nlinarith [Real.sqrt_nonneg r]
  have hp : r ^ (n + 1) ≤ q ^ n := by
    apply (pow_le_pow_of_le_one hr hr1 (Nat.le_succ n)).trans
    exact pow_le_pow_left₀ hr (hroot.trans hq) n
  have hd' := geometric_derivative_envelope hr hr1 n
  have hp' := pow_le_pow_left₀ (Real.sqrt_nonneg r) hq n
  have hh := chebyshev_impulse_difference_bound hr hc hd n
  nlinarith only [hp, hd', hp', hh]

lemma accelerated_characteristic_parameters {θ m : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ m) (hm1 : m ≤ 1 - θ) :
    let r := Real.sqrt (m * (1 - θ))
    let c := m / r
    0 ≤ r ∧ r ≤ 1 - θ ∧ |c| ≤ 1 ∧ r * c = m ∧
      r ^ 2 = m * (1 - θ) ∧ |r * c - 1| ≤ 2 * (1 - r) := by
  let r := Real.sqrt (m * (1 - θ))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = m * (1 - θ) := Real.sq_sqrt (mul_nonneg hm (by linarith))
  have hmr : m ≤ r := by nlinarith [mul_nonneg hm (sub_nonneg.mpr hm1)]
  have hr1 : r ≤ 1 - θ := by
    have hh := mul_le_mul_of_nonneg_right hm1 (show 0 ≤ 1 - θ by linarith)
    nlinarith
  have hc : 0 ≤ m / r := div_nonneg hm hr
  have hc1 : m / r ≤ 1 := by
    by_cases hz : r = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hr (Ne.symm hz))).mpr hmr
  have hrc : r * (m / r) = m := by
    by_cases hz : r = 0
    · have hmz : m = 0 := by linarith
      simp [hz, hmz]
    · field_simp
  refine ⟨hr, hr1, (abs_of_nonneg hc).symm ▸ hc1, hrc, hr2, ?_⟩
  rw [hrc, abs_of_nonpos (show m - 1 ≤ 0 by linarith)]
  nlinarith [sq_nonneg (1 - r), mul_nonneg hm hθ]

lemma chebyshev_impulse_recurrence (r c : ℝ) (n : ℕ) :
    chebyshevImpulse r c (n + 2) =
      (2 * r * c) * chebyshevImpulse r c (n + 1) - r ^ 2 * chebyshevImpulse r c n := by
  simp only [chebyshevImpulse, Nat.cast_add, Nat.cast_ofNat,
    Polynomial.Chebyshev.U_add_two, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, pow_add]
  ring

lemma chebyshev_impulse_abs_bound {r c q : ℝ} (hr : 0 ≤ r)
    (hrq : r ≤ q) (hc : |c| ≤ 1) (n : ℕ) :
    |chebyshevImpulse r c n| ≤ (n + 1) * q ^ n := by
  rw [chebyshevImpulse, abs_mul, abs_pow, abs_of_nonneg hr]
  have hh := mul_le_mul (pow_le_pow_left₀ hr hrq n) (chebyshev_second_abs_le n hc)
    (abs_nonneg _) (pow_nonneg (hr.trans hrq) n)
  simpa only [mul_comm] using hh

end OracleTemplate.TemporalDiscrepancy
