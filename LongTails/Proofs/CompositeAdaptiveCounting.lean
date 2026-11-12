import LongTails.Proofs.CompositeAdaptiveGeometry
import LongTails.Proofs.CohypomonotoneNewtonEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.CompositeAdaptive

noncomputable def logBarrier (c A : ℝ) : ℝ :=
  Real.log (max 1 (Real.log (1 / (c * A))))

lemma logBarrier_nonneg (c A : ℝ) : 0 ≤ logBarrier c A :=
  Real.log_nonneg (le_max_left _ _)

lemma logBarrier_antitone {c A B : ℝ} (hc : 0 < c) (hA : 0 < A) (hAB : A ≤ B) :
    logBarrier c B ≤ logBarrier c A := by
  have hB : 0 < B := hA.trans_le hAB
  apply Real.log_le_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))
  apply max_le_max_left
  apply Real.log_le_log (by positivity)
  exact one_div_le_one_div_of_le (mul_pos hc hA) (mul_le_mul_of_nonneg_left hAB hc.le)

lemma reciprocal_log_increment {u v w : ℝ} (hv : 0 < v) (hw : 0 ≤ w)
    (hwu : w ≤ u - v) (huv : u ≤ 2 * v) :
    w / v ≤ 2 * (Real.log u - Real.log v) := by
  have hvu : v ≤ u := by linarith
  have hu : 0 < u := hv.trans_le hvu
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne', inv_div] at hl
  have he : 1 - v / u = (u - v) / u := by field_simp
  rw [he] at hl
  have hmid : (u - v) / v ≤ 2 * ((u - v) / u) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hv hu]
    have hm := mul_le_mul_of_nonneg_left huv (sub_nonneg.mpr hvu)
    nlinarith
  calc
    w / v ≤ (u - v) / v := div_le_div_of_nonneg_right hwu hv.le
    _ ≤ 2 * ((u - v) / u) := hmid
    _ ≤ 2 * (Real.log u - Real.log v) := mul_le_mul_of_nonneg_left hl (by norm_num)

lemma early_fraction_logBarrier {c A a : ℝ} (hc : 0 < c) (hA : 0 < A)
    (ha : 0 ≤ a) (haA : a ≤ A) (hearly : 1 ≤ Real.log (1 / (c * (A + a)))) :
    (a / (A + a)) / Real.log (1 / (c * (A + a))) ≤
      2 * (logBarrier c A - logBarrier c (A + a)) := by
  have hB : 0 < A + a := by positivity
  have hid : Real.log (1 / (c * A)) - Real.log (1 / (c * (A + a))) =
      Real.log (A + a) - Real.log A := by
    rw [Real.log_div one_ne_zero (mul_ne_zero hc.ne' hA.ne'),
      Real.log_div one_ne_zero (mul_ne_zero hc.ne' hB.ne'),
      Real.log_mul hc.ne' hA.ne', Real.log_mul hc.ne' hB.ne']
    ring
  have hlo := LongTails.Proofs.CohypomonotoneNewtonEnergy.fraction_le_log_increment hA ha
  have hlog2 : Real.log (A + a) - Real.log A ≤ Real.log 2 := by
    rw [← Real.log_div hB.ne' hA.ne']
    apply Real.log_le_log (div_pos hB hA)
    apply (div_le_iff₀ hA).mpr
    linarith
  have hlog2one : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hcurv : Real.log (1 / (c * A)) ≤ 2 * Real.log (1 / (c * (A + a))) := by
    linarith
  have hfirst : 1 ≤ Real.log (1 / (c * A)) := by
    have hn : 0 ≤ a / (A + a) := div_nonneg ha hB.le
    linarith
  have hh := reciprocal_log_increment (by linarith : 0 < Real.log (1 / (c * (A + a))))
    (div_nonneg ha hB.le) (by linarith : a / (A + a) ≤
      Real.log (1 / (c * A)) - Real.log (1 / (c * (A + a)))) hcurv
  simpa only [logBarrier, max_eq_right hfirst, max_eq_right hearly] using hh

lemma early_fraction_sum (A a : ℕ → ℝ) (N : ℕ) (s : Finset ℕ) {c : ℝ}
    (hc : 0 < c) (hA : ∀ k ≤ N, 0 < A k) (ha : ∀ k < N, 0 ≤ a k)
    (haA : ∀ k < N, a k ≤ A k) (hrec : ∀ k < N, A (k + 1) = A k + a k)
    (hsub : s ⊆ Finset.range N)
    (hearly : ∀ k ∈ s, 1 ≤ Real.log (1 / (c * A (k + 1)))) :
    (∑ k ∈ s, (a k / A (k + 1)) / Real.log (1 / (c * A (k + 1)))) ≤
      2 * logBarrier c (A 0) := by
  have hd : ∀ k ∈ Finset.range N, 0 ≤ logBarrier c (A k) - logBarrier c (A (k + 1)) := by
    intro k hk
    have hkN := Finset.mem_range.mp hk
    apply sub_nonneg.mpr
    apply logBarrier_antitone hc (hA k hkN.le)
    rw [hrec k hkN]
    exact le_add_of_nonneg_right (ha k hkN)
  have ht : ∀ k ∈ s, (a k / A (k + 1)) / Real.log (1 / (c * A (k + 1))) ≤
      2 * (logBarrier c (A k) - logBarrier c (A (k + 1))) := by
    intro k hk
    have hkN := Finset.mem_range.mp (hsub hk)
    have hh := early_fraction_logBarrier hc (hA k hkN.le) (ha k hkN) (haA k hkN)
      (by rw [← hrec k hkN]; exact hearly k hk)
    rwa [← hrec k hkN] at hh
  have hs := Finset.sum_le_sum ht
  rw [← Finset.mul_sum] at hs
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hd k hk)
  rw [Finset.sum_range_sub'] at hb
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [logBarrier_nonneg c (A N)]

lemma weighted_curvature_count {ι : Type*} (s : Finset ι) (A a D h : ι → ℝ)
    {C L1 R H : ℝ} (hC : 0 ≤ C) (hA : ∀ i ∈ s, 0 < A i) (hh : ∀ i ∈ s, 0 < h i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hD : ∀ i ∈ s, 0 ≤ D i)
    (hcurv : ∀ i ∈ s, A i * h i ≤ C * L1 ^ 2 * a i ^ 2 * D i)
    (henergy : (∑ i ∈ s, a i * D i) ≤ 3 * R ^ 2)
    (hlog : (∑ i ∈ s, (a i / A i) / h i) ≤ H) :
    (s.card : ℝ) ^ 2 ≤ 3 * C * (L1 * R) ^ 2 * H := by
  have hu : ∀ i ∈ s, 0 ≤ a i * D i := fun i hi => mul_nonneg (ha i hi) (hD i hi)
  have hv : ∀ i ∈ s, 0 ≤ C * L1 ^ 2 * ((a i / A i) / h i) := by
    intro i hi
    exact mul_nonneg (by positivity) (div_nonneg (div_nonneg (ha i hi) (hA i hi).le) (hh i hi).le)
  have hp : ∀ i ∈ s, (1 : ℝ) ^ 2 ≤ (a i * D i) * (C * L1 ^ 2 * ((a i / A i) / h i)) := by
    intro i hi
    have he : (a i * D i) * (C * L1 ^ 2 * ((a i / A i) / h i)) =
        (C * L1 ^ 2 * a i ^ 2 * D i) / (A i * h i) := by ring
    rw [he, one_pow]
    exact (one_le_div (mul_pos (hA i hi) (hh i hi))).mpr (hcurv i hi)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hu hv hp
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have he : (∑ i ∈ s, C * L1 ^ 2 * ((a i / A i) / h i)) =
      C * L1 ^ 2 * ∑ i ∈ s, (a i / A i) / h i := by rw [Finset.mul_sum]
  rw [he] at hc
  have hv0 : 0 ≤ C * L1 ^ 2 * ∑ i ∈ s, (a i / A i) / h i := by
    rw [← he]
    exact Finset.sum_nonneg hv
  have hvH := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ C * L1 ^ 2)
  calc
    (s.card : ℝ) ^ 2 ≤ (∑ i ∈ s, a i * D i) * (C * L1 ^ 2 * ∑ i ∈ s, (a i / A i) / h i) := hc
    _ ≤ (3 * R ^ 2) * (C * L1 ^ 2 * H) :=
      mul_le_mul henergy hvH hv0 (by positivity)
    _ = _ := by ring

lemma clipped_log_ratio {u v t : ℝ} (hvu : v ≤ u) (hgap : u - v ≤ 1)
    (ht : t ≤ u - v) :
    t / max 1 v ≤ 2 * ((u - v) + max 1 v - max 1 u +
      Real.log (max 1 u) - Real.log (max 1 v)) := by
  have hv1 : 1 ≤ max 1 v := le_max_left _ _
  have hv0 : 0 < max 1 v := by linarith
  have he0 : 0 ≤ max 1 u - max 1 v := sub_nonneg.mpr (max_le_max_left 1 hvu)
  have he : max 1 u - max 1 v ≤ u - v := by
    by_cases hv : 1 ≤ v
    · rw [max_eq_right hv, max_eq_right (hv.trans hvu)]
    · rw [max_eq_left (le_of_not_ge hv)]
      by_cases hu : 1 ≤ u
      · rw [max_eq_right hu]
        linarith
      · rw [max_eq_left (le_of_not_ge hu)]
        linarith
  have hmax : max 1 u ≤ 2 * max 1 v := by linarith
  have hr := reciprocal_log_increment hv0 he0 (le_refl (max 1 u - max 1 v)) hmax
  have hq0 : 0 ≤ (u - v) - (max 1 u - max 1 v) := by linarith
  have hq := div_le_self hq0 hv1
  have hs : (u - v) / max 1 v = ((u - v) - (max 1 u - max 1 v)) / max 1 v +
      (max 1 u - max 1 v) / max 1 v := by ring
  have ht' := div_le_div_of_nonneg_right ht hv0.le
  linarith

noncomputable def countPotential (c A : ℝ) : ℝ :=
  Real.log A + max 1 (Real.log (1 / (c * A))) - logBarrier c A

lemma weighted_fraction_potential_step {c A a : ℝ} (hc : 0 < c) (hA : 0 < A)
    (ha : 0 ≤ a) (haA : a ≤ A) :
    (a / (A + a)) / max 1 (Real.log (1 / (c * (A + a)))) ≤
      2 * (countPotential c (A + a) - countPotential c A) := by
  have hB : 0 < A + a := by positivity
  have hid : Real.log (1 / (c * A)) - Real.log (1 / (c * (A + a))) =
      Real.log (A + a) - Real.log A := by
    rw [Real.log_div one_ne_zero (mul_ne_zero hc.ne' hA.ne'),
      Real.log_div one_ne_zero (mul_ne_zero hc.ne' hB.ne'),
      Real.log_mul hc.ne' hA.ne', Real.log_mul hc.ne' hB.ne']
    ring
  have hlo := LongTails.Proofs.CohypomonotoneNewtonEnergy.fraction_le_log_increment hA ha
  have hn : 0 ≤ a / (A + a) := div_nonneg ha hB.le
  have hlog2 : Real.log (A + a) - Real.log A ≤ Real.log 2 := by
    rw [← Real.log_div hB.ne' hA.ne']
    apply Real.log_le_log (div_pos hB hA)
    apply (div_le_iff₀ hA).mpr
    linarith
  have hh := clipped_log_ratio
    (by linarith : Real.log (1 / (c * (A + a))) ≤ Real.log (1 / (c * A)))
    (by linarith [Real.log_two_lt_d9] : Real.log (1 / (c * A)) -
      Real.log (1 / (c * (A + a))) ≤ 1)
    (by linarith : a / (A + a) ≤ Real.log (1 / (c * A)) -
      Real.log (1 / (c * (A + a))))
  dsimp only [countPotential, logBarrier]
  linarith

lemma weighted_fraction_sum (A a : ℕ → ℝ) (N : ℕ) (s : Finset ℕ) {c : ℝ}
    (hc : 0 < c) (hA : ∀ k ≤ N, 0 < A k) (ha : ∀ k < N, 0 ≤ a k)
    (haA : ∀ k < N, a k ≤ A k) (hrec : ∀ k < N, A (k + 1) = A k + a k)
    (hsub : s ⊆ Finset.range N) :
    (∑ k ∈ s, (a k / A (k + 1)) / max 1 (Real.log (1 / (c * A (k + 1))))) ≤
      2 * (countPotential c (A N) - countPotential c (A 0)) := by
  have ht : ∀ k ∈ Finset.range N,
      (a k / A (k + 1)) / max 1 (Real.log (1 / (c * A (k + 1)))) ≤
      2 * (countPotential c (A (k + 1)) - countPotential c (A k)) := by
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hh := weighted_fraction_potential_step hc (hA k hkN.le) (ha k hkN) (haA k hkN)
    rwa [← hrec k hkN] at hh
  have hd : ∀ k ∈ Finset.range N, 0 ≤ countPotential c (A (k + 1)) - countPotential c (A k) := by
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hn : 0 ≤ (a k / A (k + 1)) / max 1 (Real.log (1 / (c * A (k + 1)))) :=
      div_nonneg (div_nonneg (ha k hkN) (hA (k + 1) (by omega)).le)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _))
    linarith [ht k hk]
  have hs := Finset.sum_le_sum (fun k hk => ht k (hsub hk))
  rw [← Finset.mul_sum] at hs
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hd k hk)
  rw [Finset.sum_range_sub (fun k => countPotential c (A k)) N] at hb
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  linarith

lemma countPotential_bounds {c A : ℝ} (hc : 0 < c) (hA : 0 < A) :
    -Real.log c - logBarrier c A ≤ countPotential c A ∧
      countPotential c A ≤ -Real.log c + 1 + Real.log (1 + c * A) := by
  have hcA : 0 < c * A := mul_pos hc hA
  have hid : Real.log A + Real.log (1 / (c * A)) = -Real.log c := by
    rw [Real.log_div one_ne_zero hcA.ne', Real.log_mul hc.ne' hA.ne']
    simp
  have hw : 0 ≤ max 1 (Real.log (1 / (c * A))) - Real.log (1 / (c * A)) :=
    sub_nonneg.mpr (le_max_right _ _)
  have hl0 : 0 ≤ Real.log (1 + c * A) := Real.log_nonneg (by linarith)
  have hl : Real.log (c * A) ≤ Real.log (1 + c * A) :=
    Real.log_le_log hcA (by linarith)
  have hb0 := logBarrier_nonneg c A
  constructor
  · dsimp only [countPotential]
    linarith
  · by_cases hh : 1 ≤ Real.log (1 / (c * A))
    · dsimp only [countPotential]
      rw [max_eq_right hh]
      linarith
    · have hh' := le_of_not_ge hh
      have he : Real.log (1 / (c * A)) = -Real.log (c * A) := by
        rw [Real.log_div one_ne_zero hcA.ne', Real.log_one, zero_sub]
      dsimp only [countPotential]
      rw [max_eq_left hh']
      linarith

lemma countPotential_span {c A B W : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hB : 0 < B) (hW : 1 ≤ W) (hinit : Real.log (1 / (c * A)) ≤ W) :
    countPotential c B - countPotential c A ≤
      1 + Real.log (1 + c * B) + Real.log W := by
  have ha := (countPotential_bounds hc hA).1
  have hb := (countPotential_bounds hc hB).2
  have hw : logBarrier c A ≤ Real.log W := by
    apply Real.log_le_log (by positivity : 0 < max 1 (Real.log (1 / (c * A))))
    exact max_le hW hinit
  linarith

lemma weighted_curvature_boundary {a B S w L1 D : ℝ} (hB : 0 < B)
    (hw : 0 ≤ w) (hboundary : 1 / 64 ≤ a ^ 2 * S / B)
    (hsurplus : S * w ≤ 128 * L1 ^ 2 * D) :
    B * w ≤ 8192 * L1 ^ 2 * a ^ 2 * D := by
  have hb := (le_div_iff₀ hB).mp hboundary
  have hm := mul_le_mul_of_nonneg_right hb hw
  have hs := mul_le_mul_of_nonneg_left hsurplus (sq_nonneg a)
  nlinarith

lemma countPotential_parameter_span {c A B κ τ : ℝ} (hc : 0 < c)
    (hA : 0 < A) (hB : 0 < B) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hinit : Real.log (1 / (c * A)) ≤ 5 * κ) (hfinal : c * B ≤ 2048 * τ) :
    countPotential c B - countPotential c A ≤ 4 * Real.log (128 * (1 + κ + τ)) := by
  let V := 128 * (1 + κ + τ)
  have hV : 128 ≤ V := by dsimp [V]; linarith
  have hV0 : 0 < V := by linarith
  have hlog : 1 ≤ Real.log V := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ V)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hh
    norm_num at hh
    linarith [Real.log_two_gt_d9]
  have hW : 1 + 5 * κ ≤ V := by dsimp [V]; linarith
  have hprod : 1 + c * B ≤ V ^ 2 := by
    have hn := sq_nonneg (κ + τ)
    dsimp [V]
    nlinarith
  have hb := Real.log_le_log (by positivity : 0 < 1 + c * B) hprod
  rw [Real.log_pow] at hb
  norm_num at hb
  have hw := Real.log_le_log (by positivity : 0 < 1 + 5 * κ) hW
  have hs := countPotential_span hc hA hB
    (by linarith : 1 ≤ 1 + 5 * κ) (by linarith : Real.log (1 / (c * A)) ≤ 1 + 5 * κ)
  change countPotential c B - countPotential c A ≤ 4 * Real.log V
  linarith

lemma curvature_sqrt_progress {A a μ : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hμ : 0 < μ) (hbound : A + a ≤ μ * a ^ 2) :
    1 ≤ 2 * Real.sqrt μ * (Real.sqrt (A + a) - Real.sqrt A) := by
  have hB : 0 < A + a := by positivity
  have hroot : Real.sqrt (A + a) ≤ Real.sqrt μ * a := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha.le)).mp
    rw [mul_pow, Real.sq_sqrt hB.le, Real.sq_sqrt hμ.le]
    exact hbound
  have hstep : a ≤ 2 * Real.sqrt (A + a) * (Real.sqrt (A + a) - Real.sqrt A) := by
    nlinarith [sq_nonneg (Real.sqrt (A + a) - Real.sqrt A), Real.sq_sqrt hB.le, Real.sq_sqrt hA]
  have hm := mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg μ)
  apply le_of_mul_le_mul_left (a := Real.sqrt (A + a)) ?_ (Real.sqrt_pos.mpr hB)
  nlinarith

lemma low_curvature_progress {A a S M : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hM : 0 < M) (hS : S ≤ 3 * M) (hboundary : 1 / 64 ≤ a ^ 2 * S / (A + a)) :
    1 ≤ 2 * Real.sqrt (192 * M) * (Real.sqrt (A + a) - Real.sqrt A) := by
  have hb := (le_div_iff₀ (by positivity : 0 < A + a)).mp hboundary
  have hm := mul_le_mul_of_nonneg_left hS (sq_nonneg a)
  apply curvature_sqrt_progress hA ha (by positivity)
  nlinarith

lemma low_curvature_count (A a S : ℕ → ℝ) (N : ℕ) (s : Finset ℕ) {M : ℝ}
    (hM : 0 < M) (hA : ∀ k ≤ N, 0 ≤ A k) (ha : ∀ k < N, 0 < a k)
    (hrec : ∀ k < N, A (k + 1) = A k + a k) (hsub : s ⊆ Finset.range N)
    (hS : ∀ k ∈ s, S k ≤ 3 * M)
    (hboundary : ∀ k ∈ s, 1 / 64 ≤ a k ^ 2 * S k / A (k + 1)) :
    (s.card : ℝ) ≤ 2 * Real.sqrt (192 * M) * Real.sqrt (A N) := by
  have hstep : ∀ k ∈ s, (1 : ℝ) ≤
      2 * Real.sqrt (192 * M) * (Real.sqrt (A (k + 1)) - Real.sqrt (A k)) := by
    intro k hk
    have hkN := Finset.mem_range.mp (hsub hk)
    have hh := low_curvature_progress (hA k hkN.le) (ha k hkN) hM (hS k hk)
      (by rw [← hrec k hkN]; exact hboundary k hk)
    rwa [← hrec k hkN] at hh
  have hsum := Finset.sum_le_sum hstep
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [← Finset.mul_sum] at hsum
  have hmono : ∀ k ∈ Finset.range N, 0 ≤ Real.sqrt (A (k + 1)) - Real.sqrt (A k) := by
    intro k hk
    have hkN := Finset.mem_range.mp hk
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    rw [hrec k hkN]
    linarith [ha k hkN]
  have htotal := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hmono k hk)
  rw [Finset.sum_range_sub (fun k => Real.sqrt (A k)) N] at htotal
  have hm := mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ 2 * Real.sqrt (192 * M))
  nlinarith [Real.sqrt_nonneg (A 0), Real.sqrt_nonneg (192 * M)]

lemma low_curvature_parameter_count {K M A τ : ℝ} (hK : 0 ≤ K) (hM : 0 < M)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hbound : M * A ≤ 8 * τ)
    (hcount : K ≤ 2 * Real.sqrt (192 * M) * Real.sqrt A) :
    K ≤ 79 * Real.sqrt τ := by
  have hs := pow_le_pow_left₀ hK hcount 2
  have hprod : (2 * Real.sqrt (192 * M) * Real.sqrt A) ^ 2 = 768 * M * A := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 192 * M), Real.sq_sqrt hA]
    ring
  rw [hprod] at hs
  apply (sq_le_sq₀ hK (by positivity : 0 ≤ 79 * Real.sqrt τ)).mp
  rw [mul_pow, Real.sq_sqrt hτ]
  nlinarith

lemma cap_count (A a : ℕ → ℝ) (N : ℕ) (s : Finset ℕ)
    (hA : ∀ k ≤ N, 0 < A k) (ha : ∀ k < N, 0 ≤ a k)
    (hrec : ∀ k < N, A (k + 1) = A k + a k) (hsub : s ⊆ Finset.range N)
    (hcap : ∀ k ∈ s, a k = A k) :
    (s.card : ℝ) * Real.log 2 ≤ Real.log (A N) - Real.log (A 0) := by
  have he : ∀ k ∈ s, Real.log 2 = Real.log (A (k + 1)) - Real.log (A k) := by
    intro k hk
    have hkN := Finset.mem_range.mp (hsub hk)
    rw [hrec k hkN, hcap k hk, show A k + A k = 2 * A k by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (hA k hkN.le).ne']
    ring
  have hsum := Finset.sum_congr rfl he
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hmono : ∀ k ∈ Finset.range N, 0 ≤ Real.log (A (k + 1)) - Real.log (A k) := by
    intro k hk
    have hkN := Finset.mem_range.mp hk
    apply sub_nonneg.mpr
    apply Real.log_le_log (hA k hkN.le)
    rw [hrec k hkN]
    linarith [ha k hkN]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hmono k hk)
  rw [Finset.sum_range_sub (fun k => Real.log (A k)) N] at hh
  rwa [hsum]

lemma high_curvature_parameter_count {K κ ℓ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hℓ : 0 ≤ ℓ) (hcount : K ^ 2 ≤ 196608 * κ ^ 2 * ℓ) :
    K ≤ 444 * κ * Real.sqrt ℓ := by
  apply (sq_le_sq₀ hK (by positivity : 0 ≤ 444 * κ * Real.sqrt ℓ)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hℓ]
  nlinarith [mul_nonneg (sq_nonneg κ) hℓ]

lemma curvature_boundary_product {A a S : ℝ} (hA : 0 < A) (ha : 0 < a)
    (haA : a ≤ A) (hS : 0 ≤ S) (hboundary : 1 / 64 ≤ a ^ 2 * S / (A + a)) :
    1 / 16 ≤ (A + a) * S := by
  have hB : 0 < A + a := by positivity
  have hsquare : a ^ 2 ≤ (A + a) ^ 2 / 4 := by nlinarith
  have hc := (le_div_iff₀ hB).mp hboundary
  have hm := mul_le_mul_of_nonneg_right hsquare hS
  apply le_of_mul_le_mul_left (a := A + a) ?_ hB
  nlinarith

lemma displacement_parameter_count {K κ H ℓ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hH : 0 ≤ H) (hℓ : 1 ≤ ℓ) (hspan : H ≤ 6 * (1 + κ) * ℓ)
    (hcount : K ^ 3 ≤ 49152 * κ ^ 2 * H ^ 2) :
    K ≤ 123 * (1 + κ) ^ (4 / 3 : ℝ) * ℓ := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hbase : 0 ≤ 1 + κ := by positivity
  have hpower : ((1 + κ) ^ (4 / 3 : ℝ)) ^ 3 = (1 + κ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    norm_num
  have hκsq : κ ^ 2 ≤ (1 + κ) ^ 2 := by nlinarith
  have hℓpow : ℓ ^ 2 ≤ ℓ ^ 3 := by nlinarith
  apply (pow_le_pow_iff_left₀ hK (by positivity : 0 ≤ 123 * (1 + κ) ^ (4 / 3 : ℝ) * ℓ)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  calc
    K ^ 3 ≤ 49152 * κ ^ 2 * H ^ 2 := hcount
    _ ≤ 49152 * κ ^ 2 * (6 * (1 + κ) * ℓ) ^ 2 := by gcongr
    _ = 1769472 * κ ^ 2 * (1 + κ) ^ 2 * ℓ ^ 2 := by ring
    _ ≤ 1769472 * (1 + κ) ^ 2 * (1 + κ) ^ 2 * ℓ ^ 3 := by gcongr
    _ = 1769472 * ((1 + κ) ^ 4 * ℓ ^ 3) := by ring
    _ ≤ 123 ^ 3 * ((1 + κ) ^ 4 * ℓ ^ 3) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (123 * (1 + κ) ^ (4 / 3 : ℝ) * ℓ) ^ 3 := by
      rw [mul_pow, mul_pow, hpower]
      ring

lemma cap_parameter_count {K κ H ℓ : ℝ} (hK : 0 ≤ K)
    (hcount : K * Real.log 2 ≤ H) (hspan : H ≤ 6 * (1 + κ) * ℓ) :
    K ≤ 9 * (1 + κ) * ℓ := by
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog2 hK
  nlinarith

lemma combined_parameter_count {N Kcap Klow Khigh Kdisp κ τ ℓ : ℝ}
    (hκ : 0 ≤ κ) (hℓ : 1 ≤ ℓ) (hcount : N ≤ Kcap + Klow + Khigh + Kdisp)
    (hcap : Kcap ≤ 9 * (1 + κ) * ℓ) (hlow : Klow ≤ 79 * Real.sqrt τ)
    (hhigh : Khigh ≤ 444 * κ * Real.sqrt ℓ)
    (hdisp : Kdisp ≤ 123 * (1 + κ) ^ (4 / 3 : ℝ) * ℓ) :
    N ≤ 1024 * ((1 + κ) ^ (4 / 3 : ℝ) + Real.sqrt τ) * ℓ := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hbase : 1 ≤ 1 + κ := by linarith
  have hp := Real.self_le_rpow_of_one_le hbase (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have hp0 : 0 ≤ (1 + κ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hr : Real.sqrt ℓ ≤ ℓ := by nlinarith [Real.sq_sqrt hℓ0, Real.sqrt_nonneg ℓ]
  have hc := mul_le_mul_of_nonneg_right hp hℓ0
  have hh := mul_le_mul (by linarith : κ ≤ (1 + κ) ^ (4 / 3 : ℝ)) hr
    (Real.sqrt_nonneg ℓ) hp0
  have hl := mul_le_mul_of_nonneg_left hℓ (Real.sqrt_nonneg τ)
  nlinarith [mul_nonneg hp0 hℓ0, mul_nonneg (Real.sqrt_nonneg τ) hℓ0]

end OracleTemplate.CompositeAdaptive
