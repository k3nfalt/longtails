import LongTails.Proofs.CachedJacobianConvergence
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CachedJacobianCounts

open OracleTemplate LongTails.Setups.LipschitzJacobianMonotone
open LongTails.Algorithms.CachedJacobian
open CachedJacobianExecution CachedJacobianConvergence CachedJacobianTuning
open EnergyHessianExecution (counts)

lemma repeatOuter_eval (p : Params) (F : p.E → p.E) (n t : ℕ) :
    QueryPlan.eval (replies p F) (repeatOuter p n t (trajectory p F t)) =
      trajectory p F (t + n) := by
  induction n generalizing t with
  | zero => simp [repeatOuter, QueryPlan.eval]
  | succ n ih =>
    rw [repeatOuter, QueryPlan.eval_bind]
    change QueryPlan.eval (replies p F) (repeatOuter p n (t + 1) (trajectory p F (t + 1))) = _
    rw [ih]
    congr 1
    omega

lemma plan_eval (p : Params) (F : p.E → p.E) :
    QueryPlan.eval (replies p F) (plan p) = (trajectory p F (outerCount p)).point := by
  simp only [plan, QueryPlan.eval, replies, ite_true, readValue]
  norm_num only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp only [readJacobian, QueryPlan.eval_map]
  change (QueryPlan.eval (replies p F) (repeatOuter p (outerCount p) 0 (trajectory p F 0))).point = _
  rw [repeatOuter_eval, Nat.zero_add]

lemma repeatOuter_counts (p : Params) (F : p.E → p.E) (n t : ℕ) (i : Fin 2) :
    counts (replies p F) (repeatOuter p n t (trajectory p F t)) i =
      ∑ k ∈ Finset.range n, counts (replies p F)
        (outerStep p (t + k) (trajectory p F (t + k))) i := by
  induction n generalizing t with
  | zero => simp [repeatOuter, counts]
  | succ n ih =>
    rw [repeatOuter, EnergyHessianExecution.counts_bind]
    change counts (replies p F) (outerStep p t (trajectory p F t)) i +
      counts (replies p F) (repeatOuter p n (t + 1) (trajectory p F (t + 1))) i = _
    rw [ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1]
    omega

lemma plan_counts (p : Params) (F : p.E → p.E) (i : Fin 2) :
    counts (replies p F) (plan p) i =
      1 + ∑ t ∈ Finset.range (outerCount p),
        counts (replies p F) (outerStep p t (trajectory p F t)) i := by
  have h := repeatOuter_counts p F (outerCount p) 0 i
  simp only [Nat.zero_add] at h
  have hi : (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) = (1 : ℕ) := by
    fin_cases i <;> norm_num
  simp only [plan, counts, replies, ite_true, readValue,
    show ¬(1 : Fin 2) = 0 by decide, ite_false, readJacobian,
    EnergyHessianExecution.counts_map, ← Nat.add_assoc, hi]
  change 1 + counts (replies p F) (repeatOuter p (outerCount p) 0 (trajectory p F 0)) i = _
  rw [h]

lemma outer_ledger {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
    (t : ℕ) (ht : t < outerCount p) :
    cacheRadius p * (counts (replies p F) (outerStep p t (trajectory p F t)) 1 : ℝ) +
      ‖(trajectory p F (t + 1)).point - (trajectory p F (t + 1)).snapshot‖ ≤
      ‖(trajectory p F t).point - (trajectory p F t).snapshot‖ +
        (if t = 0 then 2 * p.D else 100 * p.D / t) := by
  have hc := trajectory_correct hv hF hmono t
  obtain ⟨y, hy, hyvi⟩ := proximal_exists hv hF hmono hJ t (center p t (trajectory p F t))
  have hdiam : ‖(trajectory p F t).point - y‖ ≤ p.D :=
    hv.2.2.2.2.2.2.2 _ hc.point_mem _ hy
  have hwarm (htp : 1 ≤ t) : ‖(trajectory p F t).point - y‖ ≤ 56 * p.D / t :=
    trajectory_warm_distance hv hF hmono htp ht.le
      (fun k hk => trajectory_error hv hF hmono hJ k (by omega)) hy hyvi
  have hsmall : stepSize p t * p.L * ‖(trajectory p F t).point - y‖ ≤ 1 / 64 := by
    by_cases hz : t = 0
    · subst t
      exact (mul_le_mul_of_nonneg_left hdiam
        (mul_nonneg (stepSize_pos hv.1 hv.2.1 hv.2.2.2.1 0).le hv.1.le)).trans
        (initial_root_scale hv.1 hv.2.1 hv.2.2.2.1)
    · exact warm_root_scale hv.1 hv.2.1 hv.2.2.2.1 (by omega) (hwarm (by omega))
  have hh := repeatInner_ledger t (center p t (trajectory p F t)) y
    ‖(trajectory p F t).point - y‖ hv hF hmono hJ ht hy hyvi hsmall
    (innerCount p) (trajectory p F t) hc le_rfl
  change cacheRadius p * (counts (replies p F) (outerStep p t (trajectory p F t)) 1 : ℝ) +
      ‖(trajectory p F (t + 1)).point - (trajectory p F (t + 1)).snapshot‖ +
      (5 / 3 : ℝ) * ‖(trajectory p F (t + 1)).point - y‖ ≤
      ‖(trajectory p F t).point - (trajectory p F t).snapshot‖ +
      (5 / 3 : ℝ) * ‖(trajectory p F t).point - y‖ at hh
  have hn := norm_nonneg ((trajectory p F (t + 1)).point - y)
  by_cases hz : t = 0
  · simp only [hz, ite_true] at *
    linarith [hv.2.1]
  · simp only [hz, ite_false]
    have hw := hwarm (by omega)
    have hD := hv.2.1
    have hp : 0 ≤ p.D / t := by positivity
    ring_nf at hh hn hw hp ⊢
    linarith

lemma outer_ledger_uniform {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
    (t : ℕ) (ht : t < outerCount p) :
    cacheRadius p * (counts (replies p F) (outerStep p t (trajectory p F t)) 1 : ℝ) +
      ‖(trajectory p F (t + 1)).point - (trajectory p F (t + 1)).snapshot‖ ≤
      ‖(trajectory p F t).point - (trajectory p F t).snapshot‖ + 200 * p.D / (t + 1) := by
  apply (outer_ledger hv hF hmono hJ t ht).trans
  apply add_le_add le_rfl
  have hD := hv.2.1
  by_cases hz : t = 0
  · simp only [hz, ite_true, Nat.cast_zero, zero_add, div_one]
    linarith
  · simp only [hz, ite_false]
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < t) (by positivity)).mpr
    nlinarith [mul_nonneg hD.le (show 0 ≤ (t : ℝ) - 1 by linarith)]

lemma prefix_ledger {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖)
    (n : ℕ) (hn : n ≤ outerCount p) :
    cacheRadius p * (∑ t ∈ Finset.range n,
      counts (replies p F) (outerStep p t (trajectory p F t)) 1 : ℕ) +
      ‖(trajectory p F n).point - (trajectory p F n).snapshot‖ ≤ 200 * p.D * (harmonic n : ℝ) := by
  induction n with
  | zero => simp [trajectory, initialState]
  | succ n ih =>
    have hh := outer_ledger_uniform hv hF hmono hJ n (by omega)
    have hi := ih (by omega)
    rw [Finset.sum_range_succ, harmonic_succ]
    push_cast
    push_cast at hi
    ring_nf at hh hi ⊢
    linarith

lemma jacobian_count_bound {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖) :
    (counts (replies p F) (plan p) 1 : ℝ) ≤
      1 + 3200 * p.L * p.D * stepSize p (outerCount p - 1) * (1 + Real.log (outerCount p)) := by
  have hh := prefix_ledger hv hF hmono hJ (outerCount p) le_rfl
  have hD := hv.2.1
  have hR := cacheRadius_pos hv.1 hv.2.1 hv.2.2.2.1
  have hη := stepSize_pos hv.1 hv.2.1 hv.2.2.2.1 (outerCount p - 1)
  have hL := hv.1
  have hlog := harmonic_le_one_add_log (outerCount p)
  have hn := norm_nonneg ((trajectory p F (outerCount p)).point -
    (trajectory p F (outerCount p)).snapshot)
  have hbound : cacheRadius p * (∑ t ∈ Finset.range (outerCount p),
      counts (replies p F) (outerStep p t (trajectory p F t)) 1 : ℕ) ≤
      200 * p.D * (1 + Real.log (outerCount p)) := by
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 200 * p.D by positivity)
    linarith
  rw [plan_counts]
  push_cast
  have hmul := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ 16 * p.L * stepSize p (outerCount p - 1) by positivity)
  have heq : 16 * p.L * stepSize p (outerCount p - 1) * cacheRadius p = 1 := by
    unfold cacheRadius
    field_simp
  rw [← mul_assoc, heq, one_mul] at hmul
  push_cast at hmul
  nlinarith only [hmul]

end LongTails.Proofs.CachedJacobianCounts
