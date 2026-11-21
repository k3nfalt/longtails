import LongTails.Proofs.ComponentHessianFamily

namespace LongTails.Proofs.ComponentHessianGap

open scoped RealInnerProductSpace
open ComponentHessianFamily ComponentHessianChain ComponentHessianLocalization
open FiniteSumNondualLowerComponents RelativeHessianSimulation

variable {d k n : ℕ}

noncomputable def anchorPoint (π : Fin (k + 1) ↪ Fin d) := hiddenPoint π (4 * (k + 1 : ℕ))

lemma anchor_norm_sq (π : Fin (k + 1) ↪ Fin d) :
    ‖anchorPoint π‖ ^ 2 = 16 * ((k + 1 : ℕ) : ℝ) ^ 3 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin d, (if j ∈ Finset.univ.map π then (4 * ((k + 1 : ℕ) : ℝ)) else 0)^2) = _
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_mem]
  simp
  ring

lemma raw_anchor (π : Fin (k + 1) ↪ Fin d) (s : Finset (Fin (k + 1))) :
    raw s (row π) (offset k) (anchorPoint π) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply ComponentHessianLink.link_flat
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [offset, row, anchorPoint, inner_neg_left, inner_sub_left, axes_inner, hiddenPoint_apply]

lemma raw_tail (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    3 * ((k + 1 : ℕ) : ℝ) - x (π (Fin.last k)) ≤ raw Finset.univ (row π) (offset k) x := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (k + 1)) _ =>
    ComponentHessianLink.link_ge (offset k j + ⟪row π j, x⟫))
  change _ ≤ raw Finset.univ (row π) (offset k) x at h
  have htel : (∑ j : Fin k, x (π j.castSucc)) - ∑ j : Fin k, x (π j.succ) =
      x (π 0) - x (π (Fin.last k)) := by
    have h₁ := Fin.sum_univ_castSucc (fun j : Fin (k + 1) => x (π j))
    have h₂ := Fin.sum_univ_succ (fun j : Fin (k + 1) => x (π j))
    linarith
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ] at h
  simp only [offset, row, Fin.cases_zero, Fin.cases_succ, inner_neg_left, inner_sub_left,
    axes_inner, zero_add, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  linarith

noncomputable def mean (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (x : EuclideanSpace ℝ (Fin d)) := (∑ i, part π (owned owner i) n x) / n

lemma mean_formula (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n)
    (hn : 0 < n) (x : EuclideanSpace ℝ (Fin d)) :
    mean π owner x = RelativeHessianCutoffSpatial.value (radius n (k + 1 : ℕ)) x *
      raw Finset.univ (row π) (offset k) x / n + ridge n (k + 1 : ℕ) / 2 * ‖x‖^2 := by
  unfold mean part masked raw FullGeneralizedSmoothZeroQuery.quadratic
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, partition_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_zero, add_div]
  field_simp

lemma mean_floor (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin d)) :
    ridge n (k + 1 : ℕ) / 2 * ‖x‖^2 ≤ mean π owner x := by
  rw [mean_formula π owner hn]
  apply le_add_of_nonneg_left
  exact div_nonneg (mul_nonneg (RelativeHessianCutoff.bounds _).1 (raw_nonneg _ _ _ _))
    (Nat.cast_nonneg _)

lemma mean_anchor (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (hn : 0 < n) :
    mean π owner (anchorPoint π) = (k + 1 : ℕ) / (8 * (n : ℝ)) := by
  rw [mean_formula π owner hn, raw_anchor, mul_zero, zero_div, zero_add, anchor_norm_sq]
  unfold ridge
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

lemma mean_exists_minimum (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (hn : 0 < n) :
    ∃ z, ‖z‖ ≤ ‖anchorPoint π‖ ∧ ∀ x, mean π owner z ≤ mean π owner x := by
  let z₀ := anchorPoint π
  have hc : Continuous (mean π owner) :=
    (continuous_finsetSum Finset.univ (fun i _ => (part_smooth π (owned owner i) n).continuous)).div_const _
  have hz₀ : z₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ‖z₀‖ := by simp
  obtain ⟨z, hz, hm⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) ‖z₀‖).exists_isMinOn
    ⟨z₀, hz₀⟩ hc.continuousOn
  refine ⟨z, by simpa using hz, fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ‖z₀‖
  · exact hm hx
  · refine (hm hz₀).trans ?_
    have hr : ‖z₀‖ ≤ ‖x‖ := by simpa using le_of_lt (lt_of_not_ge (by simpa using hx : ¬ ‖x‖ ≤ ‖z₀‖))
    refine le_trans ?_ (mean_floor π owner hn x)
    change mean π owner (anchorPoint π) ≤ _
    rw [mean_formula π owner hn, raw_anchor, mul_zero, zero_div, zero_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z₀) hr 2) (by unfold ridge; positivity)

lemma mean_hidden_gap (π : Fin (k + 1) ↪ Fin d) (owner : Fin (k + 1) → Fin n) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ radius n (k + 1 : ℕ) → |x (π (Fin.last k))| ≤ 1 / 40) :
    (k + 1 : ℕ) / (n : ℝ) ≤ mean π owner x - mean π owner (anchorPoint π) := by
  let K : ℝ := (k + 1 : ℕ)
  have hK : 1 ≤ K := by dsimp [K]; norm_num
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hB := (radius_bounds hn₁ hK).1
  rw [mean_anchor _ _ hn]
  by_cases hr : ‖x‖ ≤ radius n K
  · have hh := raw_tail π x
    have hz := (abs_le.mp (hx hr)).2
    have hb : 2 * K ≤ raw Finset.univ (row π) (offset k) x := by dsimp [K] at *; linarith
    rw [mean_formula _ _ hn, (RelativeHessianCutoffSpatial.inside_jets (lt_of_lt_of_le (by linarith : 0 < K) hB) x hr).1,
      one_mul]
    have := div_le_div_of_nonneg_right hb hn₀.le
    have hh₀ : 0 ≤ ridge n K / 2 * ‖x‖^2 := by unfold ridge; positivity
    change K / n ≤ _ + ridge n K / 2 * ‖x‖^2 - K / (8 * n)
    linarith only [this, hh₀, show K / (8 * n) = (K/n)/8 by ring,
      show 2*K/(n : ℝ) = 2*(K/n) by ring, div_nonneg (by linarith : 0 ≤ K) hn₀.le]
  · have hrad : 16 * K^2 ≤ radius n K := by
      unfold radius
      have hk := pow_le_pow_right₀ hK (by decide : 2 ≤ 4)
      nlinarith [mul_le_mul_of_nonneg_right hn₁ (pow_nonneg (by linarith : 0 ≤ K) 4)]
    have hscale : 2 * K / (n : ℝ) ≤ ridge n K / 2 * ‖x‖^2 := by
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 16 * K^2) (hrad.trans (le_of_not_ge hr)) 2
      unfold ridge
      field_simp
      nlinarith [pow_le_pow_right₀ hK (by decide : 3 ≤ 4)]
    have hh := hscale.trans (mean_floor π owner hn x)
    change K/n ≤ _ - K/(8*n)
    linarith only [hh, show K / (8 * n) = (K/n)/8 by ring, show 2*K/(n : ℝ) = 2*(K/n) by ring,
      div_nonneg (by linarith : 0 ≤ K) hn₀.le]

end LongTails.Proofs.ComponentHessianGap
