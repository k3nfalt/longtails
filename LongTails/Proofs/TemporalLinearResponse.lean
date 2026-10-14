import LongTails.Proofs.SgdExecution
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

open scoped BigOperators

namespace OracleTemplate.TemporalDiscrepancy

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma cumulative_response (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (v : ℕ → V) (e : ℕ → E) (hzero : v 0 = 0)
    (hstep : ∀ k, v (k + 1) = T (v k) + B (e k)) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), v (k + 1)) =
      T (∑ k ∈ Finset.range N, v (k + 1)) +
        B (∑ k ∈ Finset.range (N + 1), e k) := by
  simp_rw [hstep]
  rw [Finset.sum_add_distrib, ← map_sum, ← map_sum]
  congr 1
  rw [Finset.sum_range_succ']
  simp only [hzero, add_zero]
  simp_rw [hstep]

lemma cumulative_response_bound (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (p : Seminorm ℝ V)
    (v : ℕ → V) (e : ℕ → E) (hzero : v 0 = 0)
    (hstep : ∀ k, v (k + 1) = T (v k) + B (e k))
    {ρ β D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hT : ∀ x, p (T x) ≤ ρ * p x) (hB : ∀ x, p (B x) ≤ β * ‖x‖)
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ D) (N : ℕ) :
    p (∑ k ∈ Finset.range N, v (k + 1)) ≤ β * D / (1 - ρ) := by
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ1
  induction N with
  | zero => simpa using div_nonneg (mul_nonneg hβ hD) hden.le
  | succ N ih =>
    rw [cumulative_response T B v e hzero hstep N]
    calc
      _ ≤ p (T (∑ k ∈ Finset.range N, v (k + 1))) +
          p (B (∑ k ∈ Finset.range (N + 1), e k)) := map_add_le_add p _ _
      _ ≤ ρ * p (∑ k ∈ Finset.range N, v (k + 1)) +
          β * ‖∑ k ∈ Finset.range (N + 1), e k‖ := add_le_add (hT _) (hB _)
      _ ≤ ρ * (β * D / (1 - ρ)) + β * D :=
        add_le_add (mul_le_mul_of_nonneg_left ih hρ)
          (mul_le_mul_of_nonneg_left (he _) hβ)
      _ = β * D / (1 - ρ) := by field_simp; ring

lemma tail_response_bound (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (p : Seminorm ℝ V)
    (v : ℕ → V) (e : ℕ → E) (hzero : v 0 = 0)
    (hstep : ∀ k, v (k + 1) = T (v k) + B (e k))
    {ρ β D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hT : ∀ x, p (T x) ≤ ρ * p x) (hB : ∀ x, p (B x) ≤ β * ‖x‖)
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ D) (start count : ℕ) :
    p (∑ k ∈ Finset.range count, v (start + k + 1)) ≤ 2 * β * D / (1 - ρ) := by
  have hsum := Finset.sum_range_add (fun k => v (k + 1)) start count
  have h1 := cumulative_response_bound T B p v e hzero hstep hρ hρ1 hβ hD hT hB he start
  have h2 := cumulative_response_bound T B p v e hzero hstep hρ hρ1 hβ hD hT hB he (start + count)
  have hid : (∑ k ∈ Finset.range count, v (start + k + 1)) =
      (∑ k ∈ Finset.range (start + count), v (k + 1)) -
        (∑ k ∈ Finset.range start, v (k + 1)) := by
    rw [hsum]
    abel
  rw [hid]
  calc
    _ ≤ p (∑ k ∈ Finset.range (start + count), v (k + 1)) +
        p (∑ k ∈ Finset.range start, v (k + 1)) := map_sub_le_add p _ _
    _ ≤ β * D / (1 - ρ) + β * D / (1 - ρ) := add_le_add h2 h1
    _ = _ := by ring

lemma seminorm_sum_range_le (p : Seminorm ℝ V) (v : ℕ → V) (N : ℕ) :
    p (∑ k ∈ Finset.range N, v k) ≤ ∑ k ∈ Finset.range N, p (v k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (map_add_le_add p _ _).trans (add_le_add ih (le_refl _))

lemma tail_iterates_bound (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (p : Seminorm ℝ V) (v : ℕ → V) (e : ℕ → E)
    (hstep : ∀ k, v (k + 1) = T (v k) + B (e k))
    {ρ β D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hT : ∀ x, p (T x) ≤ ρ * p x) (hB : ∀ x, p (B x) ≤ β * ‖x‖)
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ D) (start count : ℕ) :
    p (∑ k ∈ Finset.range count, v (start + k + 1)) ≤
      count * (ρ ^ start * p (v 0)) + 2 * β * D / (1 - ρ) := by
  let w := fun k => (T : V → V)^[k] (v 0)
  have hw (k : ℕ) : w (k + 1) = T (w k) :=
    Function.iterate_succ_apply' T k (v 0)
  have hwbound (k : ℕ) : p (w k) ≤ ρ ^ k * p (v 0) := by
    induction k with
    | zero => simp [w]
    | succ k ih =>
      rw [hw]
      calc
        _ ≤ ρ * p (w k) := hT _
        _ ≤ ρ * (ρ ^ k * p (v 0)) := mul_le_mul_of_nonneg_left ih hρ
        _ = _ := by rw [pow_succ]; ring
  have hz : v 0 - w 0 = 0 := by simp [w]
  have hnoise (k : ℕ) : v (k + 1) - w (k + 1) = T (v k - w k) + B (e k) := by
    rw [hstep, hw, map_sub]
    abel
  have hn := tail_response_bound T B p (fun k => v k - w k) e hz hnoise
    hρ hρ1 hβ hD hT hB he start count
  have hc : p (∑ k ∈ Finset.range count, w (start + k + 1)) ≤
      count * (ρ ^ start * p (v 0)) := by
    apply (seminorm_sum_range_le p _ count).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range count, ρ ^ start * p (v 0) := by
        apply Finset.sum_le_sum
        intro k _
        exact (hwbound _).trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hρ hρ1.le (by omega)) (apply_nonneg p _))
      _ = _ := by simp
  have hid : (∑ k ∈ Finset.range count, v (start + k + 1)) =
      (∑ k ∈ Finset.range count, w (start + k + 1)) +
        ∑ k ∈ Finset.range count, (v (start + k + 1) - w (start + k + 1)) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [hid]
  exact (map_add_le_add p _ _).trans (add_le_add hc hn)

lemma tail_average_bound (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (p : Seminorm ℝ V) (v : ℕ → V) (e : ℕ → E)
    (hstep : ∀ k, v (k + 1) = T (v k) + B (e k))
    {ρ β D : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hT : ∀ x, p (T x) ≤ ρ * p x) (hB : ∀ x, p (B x) ≤ β * ‖x‖)
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ D) (start count : ℕ) (hc : 0 < count) :
    p ((count : ℝ)⁻¹ • ∑ k ∈ Finset.range count, v (start + k + 1)) ≤
      ρ ^ start * p (v 0) + 2 * β * D / ((1 - ρ) * count) := by
  have hn : (0 : ℝ) < count := by exact_mod_cast hc
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  apply (mul_le_mul_of_nonneg_left
    (tail_iterates_bound T B p v e hstep hρ hρ1 hβ hD hT hB he start count)
    (inv_nonneg.mpr hn.le)).trans_eq
  field_simp

end OracleTemplate.TemporalDiscrepancy
