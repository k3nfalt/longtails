import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
import LongTails.Algorithms.SpectralGradient

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma probe_error (C : E → E) (q : ℕ → E) {δ : ℝ}
    (hC : ∀ x y, ‖C x - C y‖ ≤ ‖x - y‖) {n : ℕ}
    (hr : ∀ j < n, ‖q (j + 1) - C (q j)‖ ≤ δ) :
    ∀ j ≤ n, ‖q j - C^[j] (q 0)‖ ≤ (j : ℝ) * δ := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := by omega
    have hp := ih (by omega)
    rw [Function.iterate_succ_apply']
    calc
      ‖q (j + 1) - C (C^[j] (q 0))‖ ≤
          ‖q (j + 1) - C (q j)‖ + ‖C (q j) - C (C^[j] (q 0))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + (j : ℝ) * δ := add_le_add (hr j hjn) ((hC _ _).trans hp)
      _ = ((j + 1 : ℕ) : ℝ) * δ := by push_cast; ring

omit [NormedSpace ℝ E] in
lemma probe_comparison (C D : E → E) (q : ℕ → E) {δ : ℝ}
    (hC : ∀ x y, ‖C x - C y‖ ≤ ‖x - y‖)
    (hD : ∀ x y, ‖D x - D y‖ ≤ ‖x - y‖) {n : ℕ}
    (hrC : ∀ j < n, ‖q (j + 1) - C (q j)‖ ≤ δ)
    (hrD : ∀ j < n, ‖q (j + 1) - D (q j)‖ ≤ δ) {j : ℕ} (hj : j ≤ n) :
    ‖C^[j] (q 0) - D^[j] (q 0)‖ ≤ 2 * (j : ℝ) * δ := by
  have h1 := probe_error C q hC hrC j hj
  have h2 := probe_error D q hD hrD j hj
  rw [norm_sub_rev] at h1
  calc
    _ ≤ ‖C^[j] (q 0) - q j‖ + ‖q j - D^[j] (q 0)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (j : ℝ) * δ + (j : ℝ) * δ := add_le_add h1 h2
    _ = _ := by ring

lemma annihilating_sum_bound (C D : E → E) (q : ℕ → E) (c : ℕ → ℝ)
    {δ : ℝ}
    (hC : ∀ x y, ‖C x - C y‖ ≤ ‖x - y‖)
    (hD : ∀ x y, ‖D x - D y‖ ≤ ‖x - y‖) {n : ℕ}
    (hrC : ∀ j < n, ‖q (j + 1) - C (q j)‖ ≤ δ)
    (hrD : ∀ j < n, ‖q (j + 1) - D (q j)‖ ≤ δ)
    (hann : ∑ j ∈ Finset.range (n + 1), c j • D^[j] (q 0) = 0) :
    ‖∑ j ∈ Finset.range (n + 1), c j • C^[j] (q 0)‖ ≤
      2 * δ * ∑ j ∈ Finset.range (n + 1), |c j| * (j : ℝ) := by
  have he : (∑ j ∈ Finset.range (n + 1), c j • C^[j] (q 0)) =
      ∑ j ∈ Finset.range (n + 1), c j • (C^[j] (q 0) - D^[j] (q 0)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hann, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), ‖c j • (C^[j] (q 0) - D^[j] (q 0))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), |c j| * (2 * (j : ℝ) * δ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (probe_comparison C D q hC hD hrC hrD (by simpa using hj)) (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

noncomputable def sweep (C : E →ₗ[ℝ] E) : List ℝ → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | r :: rs => (sweep C rs).comp (r • C + (1 - r) • LinearMap.id)

lemma sweep_cons (C : E →ₗ[ℝ] E) (r : ℝ) (rs : List ℝ) (x : E) :
    sweep C (r :: rs) x = r • sweep C rs (C x) + (1 - r) • sweep C rs x := by
  simp [sweep]

lemma sweep_comparison (C D : E →ₗ[ℝ] E) (q : ℕ → E) {δ K : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hC : ∀ x y, ‖C x - C y‖ ≤ ‖x - y‖)
    (hD : ∀ x y, ‖D x - D y‖ ≤ ‖x - y‖) {n : ℕ}
    (hrC : ∀ j < n, ‖q (j + 1) - C (q j)‖ ≤ δ)
    (hrD : ∀ j < n, ‖q (j + 1) - D (q j)‖ ≤ δ)
    (rs : List ℝ) (hrs : ∀ r ∈ rs, |r| + |1 - r| ≤ K)
    (j : ℕ) (hj : j + rs.length ≤ n) :
    ‖sweep C rs ((C : E → E)^[j] (q 0)) -
        sweep D rs ((D : E → E)^[j] (q 0))‖ ≤
      2 * ((j + rs.length : ℕ) : ℝ) * δ * K ^ rs.length := by
  induction rs generalizing j with
  | nil =>
    simpa [sweep] using probe_comparison C D q hC hD hrC hrD hj
  | cons r rs ih =>
    have ht : ∀ r ∈ rs, |r| + |1 - r| ≤ K := fun s hs => hrs s (by simp [hs])
    have h0 := ih ht j (by simpa using Nat.le_trans (Nat.le_succ _) hj)
    have h1 := ih ht (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)
    let B := 2 * ((j + 1 + rs.length : ℕ) : ℝ) * δ * K ^ rs.length
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have h0' : ‖sweep C rs ((C : E → E)^[j] (q 0)) -
        sweep D rs ((D : E → E)^[j] (q 0))‖ ≤ B := by
      apply h0.trans
      dsimp [B]
      gcongr
      omega
    have he : sweep C (r :: rs) ((C : E → E)^[j] (q 0)) -
        sweep D (r :: rs) ((D : E → E)^[j] (q 0)) =
        r • (sweep C rs ((C : E → E)^[j + 1] (q 0)) -
          sweep D rs ((D : E → E)^[j + 1] (q 0))) +
        (1 - r) • (sweep C rs ((C : E → E)^[j] (q 0)) -
          sweep D rs ((D : E → E)^[j] (q 0))) := by
      rw [sweep_cons, sweep_cons]
      simp only [Function.iterate_succ_apply', smul_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖r • (sweep C rs ((C : E → E)^[j + 1] (q 0)) -
          sweep D rs ((D : E → E)^[j + 1] (q 0)))‖ +
        ‖(1 - r) • (sweep C rs ((C : E → E)^[j] (q 0)) -
          sweep D rs ((D : E → E)^[j] (q 0)))‖ := norm_add_le _ _
      _ ≤ |r| * B + |1 - r| * B := by
        simpa only [norm_smul, Real.norm_eq_abs] using
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg r))
            (mul_le_mul_of_nonneg_left h0' (abs_nonneg (1 - r)))
      _ = (|r| + |1 - r|) * B := by ring
      _ ≤ K * B := mul_le_mul_of_nonneg_right (hrs r (by simp)) hB
      _ = _ := by simp only [B, List.length_cons, pow_succ]; push_cast; ring

lemma sweep_norm (C : E →ₗ[ℝ] E) {K : ℝ} (hK : 0 ≤ K) (rs : List ℝ)
    (hstep : ∀ r ∈ rs, ∀ x, ‖r • C x + (1 - r) • x‖ ≤ K * ‖x‖) (x : E) :
    ‖sweep C rs x‖ ≤ K ^ rs.length * ‖x‖ := by
  induction rs generalizing x with
  | nil => simp [sweep]
  | cons r rs ih =>
    change ‖sweep C rs (r • C x + (1 - r) • x)‖ ≤ _
    calc
      _ ≤ K ^ rs.length * ‖r • C x + (1 - r) • x‖ :=
        ih (fun s hs => hstep s (by simp [hs])) _
      _ ≤ K ^ rs.length * (K * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hstep r (by simp) x) (pow_nonneg hK _)
      _ = _ := by simp [pow_succ, mul_assoc]

lemma sweep_commute (C : E →ₗ[ℝ] E) (rs : List ℝ) (x : E) :
    sweep C rs (C x) = C (sweep C rs x) := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih => simp only [sweep_cons, map_add, map_smul, ih]

lemma sweep_iterate (C : E →ₗ[ℝ] E) (rs : List ℝ) (j : ℕ) (x : E) :
    sweep C rs ((C : E → E)^[j] x) = (C : E → E)^[j] (sweep C rs x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      sweep_commute, ih]

lemma iterate_norm (C : E →ₗ[ℝ] E) (hC : ∀ x, ‖C x‖ ≤ ‖x‖) (j : ℕ) (x : E) :
    ‖(C : E → E)^[j] x‖ ≤ ‖x‖ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply']; exact (hC _).trans ih

lemma sweep_probe_bound (C D : E →ₗ[ℝ] E) (q : ℕ → E) {δ K A : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hC : ∀ x y, ‖C x - C y‖ ≤ ‖x - y‖)
    (hD : ∀ x y, ‖D x - D y‖ ≤ ‖x - y‖) {n : ℕ}
    (hrC : ∀ j < n, ‖q (j + 1) - C (q j)‖ ≤ δ)
    (hrD : ∀ j < n, ‖q (j + 1) - D (q j)‖ ≤ δ)
    (rs : List ℝ) (hlen : rs.length = n)
    (hrs : ∀ r ∈ rs, |r| + |1 - r| ≤ A)
    (hstep : ∀ r ∈ rs, ∀ x, ‖r • C x + (1 - r) • x‖ ≤ K * ‖x‖)
    (hann : sweep D rs (q 0) = 0) :
    ‖sweep C rs (q n)‖ ≤ (2 * A ^ n + K ^ n) * (n : ℝ) * δ := by
  have hp := probe_error C q hC hrC n le_rfl
  have hc := sweep_comparison C D q hδ hA hC hD hrC hrD rs hrs 0 (by omega)
  simp only [Function.iterate_zero, id_eq, hann, sub_zero, zero_add, hlen] at hc
  have hcn (x : E) : ‖C x‖ ≤ ‖x‖ := by simpa only [map_zero, sub_zero] using hC x 0
  have he : sweep C rs (q n) =
      sweep C rs (q n - (C : E → E)^[n] (q 0)) +
      (C : E → E)^[n] (sweep C rs (q 0)) := by
    rw [map_sub, ← sweep_iterate]
    abel
  rw [he]
  calc
    _ ≤ ‖sweep C rs (q n - (C : E → E)^[n] (q 0))‖ +
        ‖(C : E → E)^[n] (sweep C rs (q 0))‖ := norm_add_le _ _
    _ ≤ K ^ n * ((n : ℝ) * δ) + 2 * (n : ℝ) * δ * A ^ n := by
      apply add_le_add
      · have hh := sweep_norm C hK rs hstep (q n - (C : E → E)^[n] (q 0))
        rw [hlen] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left hp (pow_nonneg hK _))
      · exact (iterate_norm C hcn n _).trans hc
    _ = _ := by ring

lemma sweep_rescale (H : E →ₗ[ℝ] E) {a : ℝ} (ha : a ≠ 0) (rs : List ℝ) :
    sweep (LinearMap.id - a • H) (rs.map (fun η => η / a)) =
      sweep (LinearMap.id - H) rs := by
  induction rs with
  | nil => rfl
  | cons η rs ih =>
    simp only [List.map_cons, sweep, ih]
    congr 1
    ext x
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    simp only [smul_sub, smul_smul, div_mul_cancel₀ _ ha]
    module

lemma sweep_descent_cons (H : E →ₗ[ℝ] E) (η : ℝ) (rs : List ℝ) (x : E) :
    sweep (LinearMap.id - H) (η :: rs) x =
      sweep (LinearMap.id - H) rs (x - η • H x) := by
  change sweep (LinearMap.id - H) rs _ = _
  congr 1
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  module

lemma sweep_descent_norm (H : E →ₗ[ℝ] E) {K : ℝ} (hK : 0 ≤ K) (rs : List ℝ)
    (hstep : ∀ η ∈ rs, ∀ x, ‖x - η • H x‖ ≤ K * ‖x‖) (x : E) :
    ‖sweep (LinearMap.id - H) rs x‖ ≤ K ^ rs.length * ‖x‖ := by
  apply sweep_norm _ hK rs
  intro η hη y
  have he : η • ((LinearMap.id - H : E →ₗ[ℝ] E) y) + (1 - η) • y = y - η • H y := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    module
  rw [he]
  exact hstep η hη y

end OracleTemplate.SpectralGradient
