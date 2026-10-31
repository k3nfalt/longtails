import LongTails.Proofs.LazyAnchoredOuter
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LazyAnchoredBudget

open LongTails.Setups.UnconstrainedLipschitzJacobianMonotone
open LongTails.Algorithms.LazyAnchoredExtraProximal
open LongTails.Proofs.LazyAnchoredInner
open LongTails.Proofs.LazyAnchoredOuter
open LongTails.Proofs.LazyAnchoredLyapunov

noncomputable section

variable {p : Params}

lemma attemptTicks_eq (k : ℕ) :
    ∀ J, attemptTicks (p := p) k J = ∑ j ∈ Finset.range J, 2 * iterations p k j
  | 0 => rfl
  | J + 1 => by rw [attemptTicks, attemptTicks_eq k J, Finset.sum_range_succ]; ring

lemma outerTicks_le (F : p.E → p.E) {k : ℕ} {z Fz : p.E} (h : Succeeds F k z Fz) :
    outerTicks F k z Fz ≤
      2 + ∑ j ∈ Finset.range (firstAttempt F k z Fz + 1), 2 * iterations p k j := by
  obtain ⟨hlt, -, -, -⟩ := first_spec F h
  unfold outerTicks
  rw [attemptTicks_eq, Finset.sum_range_succ]
  omega

lemma radiusBound_nonneg (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) : 0 ≤ radiusBound p k := by
  unfold radiusBound
  have := step_pos hp k; have := cumulative_succ_pos hp k; have := hp.1
  positivity

lemma iterations_le (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (k j : ℕ) :
    (iterations p k j : ℝ) ≤
      8 / 3 * condition p k j * Real.log (36 * condition p k j ^ 2) + 2 := by
  have hK := condition_ge_one hL hp k j
  have hlog : 0 ≤ Real.log (36 * condition p k j ^ 2) := Real.log_nonneg (by nlinarith)
  have h := Nat.ceil_lt_add_one (show 0 ≤ 8 / 3 * condition p k j *
      Real.log (36 * condition p k j ^ 2) by positivity)
  unfold iterations
  push_cast
  linarith

lemma guess_succ (k j : ℕ) : guess p k (j + 1) = 2 * guess p k j := by
  unfold guess; rw [pow_succ]; ring

lemma guess_mono (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) {j j' : ℕ} (h : j ≤ j') :
    guess p k j ≤ guess p k j' := by
  unfold guess
  have := radiusBound_nonneg hp k
  gcongr
  · norm_num

lemma guess_top (k : ℕ) : guess p k (doublings p k) = radiusBound p k := by
  unfold guess; field_simp

lemma guess_le_radius (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) {j : ℕ} (h : j ≤ doublings p k) :
    guess p k j ≤ radiusBound p k := by
  rw [← guess_top k]; exact guess_mono hp k h

lemma guess_zero_small (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) :
    p.L * step p k * guess p k 0 < 1 := by
  have hx : 0 ≤ p.L * step p k * radiusBound p k := by
    have := step_pos hp k; have := radiusBound_nonneg hp k; positivity
  have h1 : p.L * step p k * radiusBound p k ≤ (⌈p.L * step p k * radiusBound p k⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h2 : ⌈p.L * step p k * radiusBound p k⌉₊ < 2 ^ doublings p k := by
    unfold doublings
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (⌈p.L * step p k * radiusBound p k⌉₊ : ℝ) < 2 ^ doublings p k := by
    exact_mod_cast h2
  have h4 : p.L * step p k * guess p k 0 =
      p.L * step p k * radiusBound p k / 2 ^ doublings p k := by
    unfold guess; ring
  rw [h4, div_lt_one (by positivity)]
  linarith

lemma sum_guess (hp : 0 < p.D ∧ 0 < p.ε) (k J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), guess p k j ≤ 2 * guess p k J := by
  induction J with
  | zero => simp only [zero_add, Finset.sum_range_one]; linarith [guess_nonneg hp k 0]
  | succ J ih =>
    rw [Finset.sum_range_succ, guess_succ]
    linarith

lemma firstAttempt_le (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {k : ℕ}
    {z Fz : p.E} (hR : ‖center p k z Fz - resolvent F k z‖ ≤ radiusBound p k) :
    firstAttempt F k z Fz ≤ doublings p k := by
  classical
  obtain ⟨i, hi, hacc⟩ := attempt_success F hreg hp (j := doublings p k)
    (resolvent_spec F hreg hp k z) (by rw [guess_top]; exact hR)
  have h : Succeeds F k z Fz := ⟨doublings p k, i, hi, hacc⟩
  simp only [firstAttempt, h, ↓reduceDIte]
  exact Nat.find_min' h ⟨i, hi, hacc⟩

lemma firstAttempt_guess (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε)
    {k : ℕ} {z Fz : p.E} (h : Succeeds F k z Fz) (hpos : 1 ≤ firstAttempt F k z Fz) :
    guess p k (firstAttempt F k z Fz - 1) < ‖center p k z Fz - resolvent F k z‖ := by
  obtain ⟨-, -, hfail, -⟩ := first_spec F h
  by_contra hle
  obtain ⟨i, hi, hacc⟩ := attempt_success F hreg hp (j := firstAttempt F k z Fz - 1)
    (resolvent_spec F hreg hp k z) (le_of_not_gt hle)
  exact hfail _ (by omega) i hi hacc


lemma outerTicks_real (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {k : ℕ}
    {z Fz : p.E} (hR : ‖center p k z Fz - resolvent F k z‖ ≤ radiusBound p k) :
    (outerTicks F k z Fz : ℝ) ≤
      2 + 16 / 3 * Real.log (36 * (5 * p.L * step p k * radiusBound p k + 1) ^ 2) *
          ((doublings p k : ℝ) + 11 + 20 * (p.L * step p k * ‖center p k z Fz - resolvent F k z‖)) +
        4 * ((doublings p k : ℝ) + 1) := by
  have hL := hreg.L_nonneg
  have ha := step_pos hp k
  set R := ‖center p k z Fz - resolvent F k z‖ with hRdef
  set d := doublings p k
  set Λ := Real.log (36 * (5 * p.L * step p k * radiusBound p k + 1) ^ 2)
  obtain ⟨i0, hi0, hacc0⟩ := attempt_success F hreg hp (j := d)
    (resolvent_spec F hreg hp k z) (by rw [guess_top]; exact hR)
  have hs : Succeeds F k z Fz := ⟨d, i0, hi0, hacc0⟩
  set J := firstAttempt F k z Fz
  have hJd : J ≤ d := firstAttempt_le F hreg hp hR
  have hticks := outerTicks_le F hs
  have hcast : (outerTicks F k z Fz : ℝ) ≤
      2 + ∑ j ∈ Finset.range (J + 1), 2 * (iterations p k j : ℝ) := by
    exact_mod_cast hticks
  have hKtop : ∀ j ∈ Finset.range (J + 1),
      condition p k j ≤ 5 * p.L * step p k * radiusBound p k + 1 := by
    intro j hj
    have hj' : j ≤ d := by rw [Finset.mem_range] at hj; omega
    unfold condition
    have := guess_le_radius hp k hj'
    have : 0 ≤ 5 * p.L * step p k := by positivity
    nlinarith
  have hx0 : 0 ≤ p.L * step p k * radiusBound p k :=
    mul_nonneg (mul_nonneg hL ha.le) (radiusBound_nonneg hp k)
  have hΛ0 : 0 ≤ Λ := by
    apply Real.log_nonneg
    nlinarith
  have hiter : ∀ j ∈ Finset.range (J + 1),
      (iterations p k j : ℝ) ≤ 8 / 3 * condition p k j * Λ + 2 := by
    intro j hj
    have h1 := iterations_le hL hp k j
    have hK1 := condition_ge_one hL hp k j
    have h2 : Real.log (36 * condition p k j ^ 2) ≤ Λ := by
      apply Real.log_le_log (by positivity)
      have := hKtop j hj
      nlinarith
    have h3 : 8 / 3 * condition p k j * Real.log (36 * condition p k j ^ 2) ≤
        8 / 3 * condition p k j * Λ := by
      apply mul_le_mul_of_nonneg_left h2; positivity
    linarith
  have hsumI : ∑ j ∈ Finset.range (J + 1), 2 * (iterations p k j : ℝ) ≤
      ∑ j ∈ Finset.range (J + 1), (16 / 3 * Λ * condition p k j + 4) := by
    apply Finset.sum_le_sum
    intro j hj
    have := hiter j hj
    nlinarith
  have hsumK : ∑ j ∈ Finset.range (J + 1), condition p k j =
      5 * p.L * step p k * ∑ j ∈ Finset.range (J + 1), guess p k j + (J + 1) := by
    unfold condition
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp
  have hguessJ : 5 * p.L * step p k * (2 * guess p k J) ≤ 10 + 20 * (p.L * step p k * R) := by
    have hLaR : 0 ≤ p.L * step p k * R := by positivity
    rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
    · rw [hJ0]
      have := guess_zero_small hL hp k
      nlinarith
    · have hlt := firstAttempt_guess F hreg hp hs hJpos
      have hJ' : J = (J - 1) + 1 := by omega
      have hg : guess p k J = 2 * guess p k (J - 1) := by
        conv_lhs => rw [hJ']
        exact guess_succ k (J - 1)
      rw [hg]
      have : 0 ≤ p.L * step p k := by positivity
      nlinarith
  have hsg := sum_guess hp k J
  have hLa : 0 ≤ 5 * p.L * step p k := by positivity
  have hfin : ∑ j ∈ Finset.range (J + 1), (16 / 3 * Λ * condition p k j + 4) ≤
      16 / 3 * Λ * ((d : ℝ) + 11 + 20 * (p.L * step p k * R)) + 4 * ((d : ℝ) + 1) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumK]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hJd' : (J : ℝ) ≤ d := by exact_mod_cast hJd
    have h1 : 5 * p.L * step p k * ∑ j ∈ Finset.range (J + 1), guess p k j ≤
        10 + 20 * (p.L * step p k * R) := by
      have := mul_le_mul_of_nonneg_left hsg hLa
      linarith
    have h2 : 5 * p.L * step p k * ∑ j ∈ Finset.range (J + 1), guess p k j + ((J : ℝ) + 1) ≤
        (d : ℝ) + 11 + 20 * (p.L * step p k * R) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 16 / 3 * Λ by positivity)
    push_cast
    nlinarith
  linarith


lemma step_radius (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) :
    step p k * radiusBound p k ≤ 2 * scale p * p.D := by
  have hs := scale_pos hp
  have hD := hp.1
  unfold radiusBound
  have hc : cumulative p (k + 1) = scale p * (k + 1) * (k + 2) / 2 := by
    unfold cumulative; push_cast; ring
  rw [hc]
  unfold step
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [show scale p * (↑k + 1) * (p.D * (scale p * (↑k + 1)) / (scale p * (↑k + 1) * (↑k + 2) / 2))
    = 2 * scale p * p.D * ((k + 1) / (k + 2)) by field_simp]
  have : ((k : ℝ) + 1) / (k + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h2 : 0 ≤ 2 * scale p * p.D := by positivity
  nlinarith

lemma doublings_le (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) :
    doublings p k ≤ Nat.log 2 ⌈2 * p.L * scale p * p.D⌉₊ + 1 := by
  unfold doublings
  have : p.L * step p k * radiusBound p k ≤ 2 * p.L * scale p * p.D := by
    have := step_radius hp k
    rw [mul_assoc]
    nlinarith
  have := Nat.log_mono_right (b := 2) (Nat.ceil_mono this)
  omega

lemma lambda_le (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) :
    Real.log (36 * (5 * p.L * step p k * radiusBound p k + 1) ^ 2) ≤
      Real.log (36 * (5 * (2 * p.L * scale p * p.D) + 1) ^ 2) := by
  have h0 : 0 ≤ p.L * step p k * radiusBound p k := by
    have := step_pos hp k; have := radiusBound_nonneg hp k; positivity
  have h00 : 0 < 5 * p.L * step p k * radiusBound p k + 1 := by nlinarith
  apply Real.log_le_log (by positivity)
  have : p.L * step p k * radiusBound p k ≤ 2 * p.L * scale p * p.D := by
    have := step_radius hp k
    rw [mul_assoc]
    nlinarith
  have h1 : 5 * p.L * step p k * radiusBound p k + 1 ≤ 5 * (2 * p.L * scale p * p.D) + 1 := by
    nlinarith
  have h2 : 0 ≤ 5 * p.L * step p k * radiusBound p k + 1 := by nlinarith
  nlinarith [mul_le_mul h1 h1 h2 (by linarith)]

lemma total_real (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    ∀ k, k ≤ outerCount p →
      (totalTicks F k : ℝ) ≤
        k * (2 + 16 / 3 * Real.log (36 * (5 * (2 * p.L * scale p * p.D) + 1) ^ 2) *
              ((Nat.log 2 ⌈2 * p.L * scale p * p.D⌉₊ + 1 : ℕ) + 11) +
            4 * ((Nat.log 2 ⌈2 * p.L * scale p * p.D⌉₊ + 1 : ℕ) + 1)) +
          16 / 3 * Real.log (36 * (5 * (2 * p.L * scale p * p.D) + 1) ^ 2) * 20 *
            ∑ l ∈ Finset.range k, p.L * step p l * radius F l
  | 0, _ => by simp [totalTicks]
  | k + 1, hk => by
    have hL := hreg.L_nonneg
    have ih := total_real F hreg hp hxs hD k (by omega)
    obtain ⟨hprev, -⟩ := aep_invariant F hreg hp hxs hD (k + 1) hk
    obtain ⟨-, hR, -⟩ := hprev k (by omega)
    have hstep := outerTicks_real F hreg hp hR
    set Λ := Real.log (36 * (5 * (2 * p.L * scale p * p.D) + 1) ^ 2)
    set d := (Nat.log 2 ⌈2 * p.L * scale p * p.D⌉₊ + 1 : ℕ)
    have hΛk := lambda_le hL hp k
    have hdk : (doublings p k : ℝ) ≤ d := by exact_mod_cast doublings_le hL hp k
    have hΛ0 : 0 ≤ Real.log (36 * (5 * p.L * step p k * radiusBound p k + 1) ^ 2) := by
      apply Real.log_nonneg
      have : 0 ≤ p.L * step p k * radiusBound p k := by
        have := step_pos hp k; have := radiusBound_nonneg hp k; positivity
      nlinarith
    have hrad0 : 0 ≤ p.L * step p k * radius F k := by
      have := step_pos hp k; unfold radius; positivity
    have hdk0 : (0 : ℝ) ≤ doublings p k := by positivity
    have hstep' : (outerTicks F k (outerSeq F k).1 (outerSeq F k).2 : ℝ) ≤
        2 + 16 / 3 * Λ * ((d : ℝ) + 11) + 4 * ((d : ℝ) + 1) +
          16 / 3 * Λ * 20 * (p.L * step p k * radius F k) := by
      have h1 : 16 / 3 * Real.log (36 * (5 * p.L * step p k * radiusBound p k + 1) ^ 2) *
          ((doublings p k : ℝ) + 11 + 20 * (p.L * step p k * radius F k)) ≤
          16 / 3 * Λ * ((d : ℝ) + 11 + 20 * (p.L * step p k * radius F k)) := by
        apply mul_le_mul _ (by linarith) (by linarith) (by linarith)
        linarith
      have hstep2 : (outerTicks F k (outerSeq F k).1 (outerSeq F k).2 : ℝ) ≤
          2 + 16 / 3 * Real.log (36 * (5 * p.L * step p k * radiusBound p k + 1) ^ 2) *
            ((doublings p k : ℝ) + 11 + 20 * (p.L * step p k * radius F k)) +
          4 * ((doublings p k : ℝ) + 1) := hstep
      nlinarith
    rw [totalTicks, Finset.sum_range_succ]
    push_cast
    nlinarith


lemma gap_sum (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    ∑ l ∈ Finset.range (outerCount p), (cumulative p (l + 1) / step p l) ^ 2 * gap F l ^ 2 ≤
      4 / 3 * p.D ^ 2 := by
  obtain ⟨-, hV⟩ := aep_invariant F hreg hp hxs hD (outerCount p) le_rfl
  have hlow : -(p.D ^ 2 / 2) ≤ potential p.x0 (cumulative p (outerCount p))
      (outerSeq F (outerCount p)).1 (F (outerSeq F (outerCount p)).1) := by
    apply potential_lower p.x0 xs _ _ _ p.D (cumulative_nonneg hp _) hD
    have := hreg.mono (outerSeq F (outerCount p)).1 xs; rwa [hxs, sub_zero] at this
  linarith

lemma ratio_sq (hp : 0 < p.D ∧ 0 < p.ε) (k : ℕ) :
    (step p k ^ 2 / cumulative p (k + 1)) ^ 2 ≤ 4 * scale p ^ 2 := by
  have hs := scale_pos hp
  have hc : cumulative p (k + 1) = scale p * (k + 1) * (k + 2) / 2 := by
    unfold cumulative; push_cast; ring
  rw [hc]
  unfold step
  rw [show (scale p * (↑k + 1)) ^ 2 / (scale p * (↑k + 1) * (↑k + 2) / 2) =
    2 * scale p * ((k + 1) / (k + 2)) by field_simp]
  have h1 : ((k : ℝ) + 1) / (k + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h0 : 0 ≤ ((k : ℝ) + 1) / (k + 2) := by positivity
  have : 2 * scale p * ((k + 1) / (k + 2)) ≤ 2 * scale p := by nlinarith
  have h3 : 0 ≤ 2 * scale p * (((k : ℝ) + 1) / (k + 2)) := by positivity
  nlinarith

lemma radius_sum_sq (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) {xs : p.E}
    (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    (∑ l ∈ Finset.range (outerCount p), p.L * step p l * radius F l) ^ 2 ≤
      12 * p.L ^ 2 * scale p ^ 2 * p.D ^ 2 * outerCount p := by
  have hL := hreg.L_nonneg
  obtain ⟨hprev, -⟩ := aep_invariant F hreg hp hxs hD (outerCount p) le_rfl
  set N := outerCount p
  have h1 : ∑ l ∈ Finset.range N, p.L * step p l * radius F l ≤
      3 / 2 * p.L * ∑ l ∈ Finset.range N, step p l * gap F l := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨-, -, hrd⟩ := hprev l (Finset.mem_range.mp hl)
    have := step_pos hp l
    have h := mul_le_mul_of_nonneg_left hrd (show 0 ≤ p.L * step p l by positivity)
    nlinarith
  have hcs : (∑ l ∈ Finset.range N, step p l * gap F l) ^ 2 ≤
      (∑ l ∈ Finset.range N, (step p l ^ 2 / cumulative p (l + 1)) ^ 2) *
        ∑ l ∈ Finset.range N, ((cumulative p (l + 1) / step p l) * gap F l) ^ 2 := by
    have e : ∀ l ∈ Finset.range N, step p l * gap F l =
        (step p l ^ 2 / cumulative p (l + 1)) * ((cumulative p (l + 1) / step p l) * gap F l) := by
      intro l _
      have := step_pos hp l; have := cumulative_succ_pos hp l
      field_simp
    rw [Finset.sum_congr rfl e]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hA : ∑ l ∈ Finset.range N, (step p l ^ 2 / cumulative p (l + 1)) ^ 2 ≤
      4 * scale p ^ 2 * N := by
    calc _ ≤ ∑ l ∈ Finset.range N, 4 * scale p ^ 2 :=
          Finset.sum_le_sum (fun l _ => ratio_sq hp l)
      _ = 4 * scale p ^ 2 * N := by simp; ring
  have hB : ∑ l ∈ Finset.range N, ((cumulative p (l + 1) / step p l) * gap F l) ^ 2 ≤
      4 / 3 * p.D ^ 2 := by
    have := gap_sum F hreg hp hxs hD
    calc _ = ∑ l ∈ Finset.range N, (cumulative p (l + 1) / step p l) ^ 2 * gap F l ^ 2 := by
          apply Finset.sum_congr rfl; intro l _; ring
      _ ≤ _ := this
  have hS0 : 0 ≤ ∑ l ∈ Finset.range N, step p l * gap F l :=
    Finset.sum_nonneg (fun l _ => by have := step_pos hp l; unfold gap; positivity)
  have hR0 : 0 ≤ ∑ l ∈ Finset.range N, p.L * step p l * radius F l :=
    Finset.sum_nonneg (fun l _ => by have := step_pos hp l; unfold radius; positivity)
  have hBn : 0 ≤ ∑ l ∈ Finset.range N, ((cumulative p (l + 1) / step p l) * gap F l) ^ 2 :=
    Finset.sum_nonneg (fun l _ => by positivity)
  have hsq : (∑ l ∈ Finset.range N, step p l * gap F l) ^ 2 ≤
      4 * scale p ^ 2 * N * (4 / 3 * p.D ^ 2) := by
    calc _ ≤ _ := hcs
      _ ≤ 4 * scale p ^ 2 * N * (4 / 3 * p.D ^ 2) :=
        mul_le_mul hA hB hBn (by positivity)
  have h2 : (∑ l ∈ Finset.range N, p.L * step p l * radius F l) ^ 2 ≤
      (3 / 2 * p.L * ∑ l ∈ Finset.range N, step p l * gap F l) ^ 2 :=
    pow_le_pow_left₀ hR0 h1 2
  calc _ ≤ _ := h2
    _ = 9 / 4 * p.L ^ 2 * (∑ l ∈ Finset.range N, step p l * gap F l) ^ 2 := by ring
    _ ≤ 9 / 4 * p.L ^ 2 * (4 * scale p ^ 2 * N * (4 / 3 * p.D ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hsq; positivity
    _ = _ := by ring

lemma outer_rel (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (hm : 1 ≤ p.m) :
    (p.L * p.D ^ 2 / p.ε) ^ 2 ≤ (p.m : ℝ) ^ 2 * (outerCount p : ℝ) ^ 5 := by
  have hm0 : (0 : ℝ) < p.m := by exact_mod_cast hm
  set x := p.L * p.D ^ 2 / (p.m * p.ε) with hx
  have hx0 : 0 ≤ x := by have := hp.1; have := hp.2; positivity
  have hN : x ^ (2 / 5 : ℝ) ≤ outerCount p := by
    unfold outerCount
    push_cast
    have := Nat.le_ceil (x ^ (2 / 5 : ℝ))
    linarith
  have hxr : x = (x ^ (2 / 5 : ℝ)) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_mul hx0]; norm_num
  have h1 : x ≤ (outerCount p : ℝ) ^ (5 / 2 : ℝ) := by
    rw [hxr]
    exact Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have h2 : x ^ 2 ≤ (outerCount p : ℝ) ^ 5 := by
    have h3 := pow_le_pow_left₀ hx0 h1 2
    have h4 : ((outerCount p : ℝ) ^ (5 / 2 : ℝ)) ^ 2 = (outerCount p : ℝ) ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    linarith
  have e : p.L * p.D ^ 2 / p.ε = p.m * x := by
    rw [hx]; field_simp
  rw [e, mul_pow]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)


lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith

lemma log_nat_le (n : ℕ) (hn : 1 ≤ n) : Real.log n ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) := Real.log_lt_log hn0 h2
  rw [Real.log_pow] at h3
  have h4 := log_two_le_one
  have h5 : (0 : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by positivity
  push_cast at h3 h5 ⊢
  nlinarith

lemma log_const_le : Real.log 60516 ≤ 12 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h12]
  calc (60516 : ℝ) ≤ 2.7182818283 ^ 12 := by norm_num
    _ ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h.le 12

lemma final_arith {N m ℓ Λ d S X : ℝ} (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) (hΛ : Λ ≤ 14 * ℓ) (hd0 : 0 ≤ d) (hd : d ≤ ℓ + 3) (hS0 : 0 ≤ S)
    (hS : S ≤ 14 * m * N)
    (hX : X ≤ N * (2 + 16 / 3 * Λ * (d + 11) + 4 * (d + 1)) + 16 / 3 * Λ * 20 * S) :
    X ≤ 2 ^ 15 * (m + 1) * N * ℓ ^ 2 := by
  have hA : Λ * (d + 11) ≤ (14 * ℓ) * (ℓ + 14) :=
    mul_le_mul hΛ (by linarith) (by linarith) (by linarith)
  have hB : Λ * S ≤ (14 * ℓ) * (14 * m * N) := mul_le_mul hΛ hS hS0 (by linarith)
  have hm : 0 ≤ m := by
    have : 0 ≤ 14 * m * N := le_trans hS0 hS
    nlinarith
  have hC : 2 + 16 / 3 * Λ * (d + 11) + 4 * (d + 1) ≤ 1142 * ℓ ^ 2 := by nlinarith
  have hD : N * (2 + 16 / 3 * Λ * (d + 11) + 4 * (d + 1)) ≤ N * (1142 * ℓ ^ 2) :=
    mul_le_mul_of_nonneg_left hC (by linarith)
  have hE : 16 / 3 * Λ * 20 * S ≤ 20907 * m * N * ℓ ^ 2 := by
    have h1 : 16 / 3 * Λ * 20 * S = 320 / 3 * (Λ * S) := by ring
    have h2 : (14 * ℓ) * (14 * m * N) ≤ 196 * m * N * ℓ ^ 2 := by
      have : ℓ ≤ ℓ ^ 2 := by nlinarith
      have hmN : 0 ≤ m * N := by nlinarith
      nlinarith
    nlinarith
  have hF : N * (1142 * ℓ ^ 2) + 20907 * m * N * ℓ ^ 2 ≤ 2 ^ 15 * (m + 1) * N * ℓ ^ 2 := by
    have hNℓ : 0 ≤ N * ℓ ^ 2 := by positivity
    nlinarith
  linarith

lemma lambda_bound {Q : ℝ} {n : ℕ} (hn : 1 ≤ n) (hQ0 : 0 ≤ Q) (hQ : Q ≤ 8 * n) :
    Real.log (36 * (5 * Q + 1) ^ 2) ≤ 14 * ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 36 * (5 * Q + 1) ^ 2 ≤ 60516 * (n : ℝ) ^ 2 := by
    have : 5 * Q + 1 ≤ 41 * n := by linarith
    have h0 : 0 ≤ 5 * Q + 1 := by linarith
    nlinarith [mul_le_mul this this h0 (by linarith)]
  have h2 : Real.log (36 * (5 * Q + 1) ^ 2) ≤ Real.log (60516 * (n : ℝ) ^ 2) :=
    Real.log_le_log (by positivity) h1
  have e : Real.log (60516 * (n : ℝ) ^ 2) = Real.log 60516 + 2 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h3 := log_const_le
  have h4 := log_nat_le n hn
  have h5 : (1 : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.log 2 n + 1 by omega)
  linarith

lemma doublings_bound {Q : ℝ} {n : ℕ} (hn : 1 ≤ n) (hQ : Q ≤ 8 * n) :
    Nat.log 2 ⌈Q⌉₊ + 1 ≤ (Nat.log 2 n + 1) + 3 := by
  have h1 : ⌈Q⌉₊ ≤ 8 * n := by
    apply Nat.ceil_le.mpr; push_cast; linarith
  have h0 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : 8 * n < 2 ^ (Nat.log 2 n + 1 + 3) := by
    rw [pow_add]; norm_num; linarith
  have h3 : Nat.log 2 ⌈Q⌉₊ ≤ Nat.log 2 (8 * n) := Nat.log_mono_right h1
  have h4 : Nat.log 2 (8 * n) < Nat.log 2 n + 1 + 3 := Nat.log_lt_of_lt_pow (by omega) h2
  omega

lemma Q_bound (hL : 0 ≤ p.L) (hp : 0 < p.D ∧ 0 < p.ε) (hm : 1 ≤ p.m) :
    2 * p.L * scale p * p.D ≤ 8 * ((p.m * outerCount p : ℕ) : ℝ) := by
  set N := outerCount p with hNdef
  have hN1 : 1 ≤ N := by simp only [hNdef, outerCount]; omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hmr : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hD0 := hp.1
  have hε0 := hp.2
  set T := p.L * p.D ^ 2 / p.ε with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hQ : 2 * p.L * scale p * p.D = 8 * T / (N * (N + 1)) := by
    simp only [hTdef, scale, hNdef]; field_simp; ring
  have hrel : T ^ 2 ≤ (p.m : ℝ) ^ 2 * (N : ℝ) ^ 5 := outer_rel hL hp hm
  have hTN : T ≤ p.m * (N : ℝ) ^ 3 := by
    have h5 : (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 6 := pow_le_pow_right₀ hNr (by norm_num)
    have h1 : T ^ 2 ≤ (p.m * (N : ℝ) ^ 3) ^ 2 := by
      have : (p.m : ℝ) ^ 2 * (N : ℝ) ^ 5 ≤ (p.m * (N : ℝ) ^ 3) ^ 2 := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
      linarith
    exact (pow_le_pow_iff_left₀ hT0 (by positivity) (by norm_num)).mp h1
  rw [hQ, div_le_iff₀ (by positivity)]
  push_cast
  have h3 : (N : ℝ) ^ 3 ≤ N * (N * (N + 1)) := by nlinarith
  have h4 : (p.m : ℝ) * N ^ 3 ≤ p.m * N * (N * (N + 1)) := by
    have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ p.m by positivity)
    linarith
  nlinarith

lemma S_bound (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) (hm : 1 ≤ p.m)
    {xs : p.E} (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    ∑ l ∈ Finset.range (outerCount p), p.L * step p l * radius F l ≤
      14 * p.m * outerCount p := by
  have hL := hreg.L_nonneg
  set N := outerCount p with hNdef
  have hN1 : 1 ≤ N := by simp only [hNdef, outerCount]; omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hmr : (1 : ℝ) ≤ p.m := by exact_mod_cast hm
  have hD0 := hp.1
  have hε0 := hp.2
  have hS := radius_sum_sq F hreg hp hxs hD
  set S := ∑ l ∈ Finset.range N, p.L * step p l * radius F l with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun l _ =>
    mul_nonneg (mul_nonneg hL (step_pos hp l).le) (norm_nonneg _))
  set T := p.L * p.D ^ 2 / p.ε with hTdef
  have hrel : T ^ 2 ≤ (p.m : ℝ) ^ 2 * (N : ℝ) ^ 5 := outer_rel hL hp hm
  have h1 : 12 * p.L ^ 2 * scale p ^ 2 * p.D ^ 2 * N = 192 * T ^ 2 * N / (N * (N + 1)) ^ 2 := by
    simp only [hTdef, scale, hNdef]; field_simp; ring
  have h2 : 192 * T ^ 2 * N / (N * (N + 1)) ^ 2 ≤ (14 * p.m * N) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : (N : ℝ) ^ 4 ≤ (N * (N + 1)) ^ 2 := by
      have h8 : (N : ℝ) * N ≤ N * (N + 1) := by nlinarith
      have h9 := pow_le_pow_left₀ (by positivity) h8 2
      calc (N : ℝ) ^ 4 = (N * N) ^ 2 := by ring
        _ ≤ _ := h9
    have h4 : 192 * T ^ 2 * N ≤ 192 * ((p.m : ℝ) ^ 2 * N ^ 5) * N := by
      have := mul_le_mul_of_nonneg_left hrel (show (0 : ℝ) ≤ 192 by norm_num)
      nlinarith
    have h5 : 192 * ((p.m : ℝ) ^ 2 * N ^ 5) * N ≤ (14 * p.m * N) ^ 2 * (N * (N + 1)) ^ 2 := by
      have : 192 * ((p.m : ℝ) ^ 2 * N ^ 5) * N = 192 * (p.m : ℝ) ^ 2 * N ^ 2 * N ^ 4 := by ring
      rw [this]
      have h6 : (14 * p.m * N) ^ 2 * (N * (N + 1)) ^ 2 = 196 * (p.m : ℝ) ^ 2 * N ^ 2 *
          (N * (N + 1)) ^ 2 := by ring
      rw [h6]
      have hpos : (0 : ℝ) ≤ (p.m : ℝ) ^ 2 * N ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 hpos]
    linarith
  have h7 : S ^ 2 ≤ (14 * p.m * N) ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ hS0 (by positivity) (by norm_num)).mp h7

lemma ticks_budget (F : p.E → p.E) (hreg : Regular p F) (hp : 0 < p.D ∧ 0 < p.ε) (hm : 1 ≤ p.m)
    {xs : p.E} (hxs : F xs = 0) (hD : ‖p.x0 - xs‖ ≤ p.D) :
    totalTicks F (outerCount p) ≤
      2 ^ 15 * (p.m + 1) * outerCount p * (Nat.log 2 (p.m * outerCount p) + 1) ^ 2 := by
  have hL := hreg.L_nonneg
  have hN1 : 1 ≤ outerCount p := by unfold outerCount; omega
  have hmN : 1 ≤ p.m * outerCount p := Nat.mul_le_mul hm hN1
  have hQ := Q_bound hL hp hm
  have hQ0 : 0 ≤ 2 * p.L * scale p * p.D := by have := scale_pos hp; have := hp.1; positivity
  have hΛ := lambda_bound hmN hQ0 hQ
  have hd := doublings_bound hmN hQ
  have hS := S_bound F hreg hp hm hxs hD
  have hS0 : 0 ≤ ∑ l ∈ Finset.range (outerCount p), p.L * step p l * radius F l :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (mul_nonneg hL (step_pos hp l).le) (norm_nonneg _))
  have htot := total_real F hreg hp hxs hD (outerCount p) le_rfl
  have hd' : (((Nat.log 2 ⌈2 * p.L * scale p * p.D⌉₊ + 1 : ℕ)) : ℝ) ≤
      ((Nat.log 2 (p.m * outerCount p) + 1 : ℕ) : ℝ) + 3 := by exact_mod_cast hd
  have key := final_arith (N := (outerCount p : ℝ)) (m := (p.m : ℝ))
    (ℓ := ((Nat.log 2 (p.m * outerCount p) + 1 : ℕ) : ℝ)) (by exact_mod_cast hN1)
    (by exact_mod_cast (show 1 ≤ Nat.log 2 (p.m * outerCount p) + 1 by omega))
    hΛ (by positivity) hd' hS0 (by linarith) htot
  have : ((totalTicks F (outerCount p) : ℕ) : ℝ) ≤
      ((2 ^ 15 * (p.m + 1) * outerCount p * (Nat.log 2 (p.m * outerCount p) + 1) ^ 2 : ℕ) : ℝ) := by
    push_cast at key ⊢
    linarith
  exact_mod_cast this

end

end LongTails.Proofs.LazyAnchoredBudget
