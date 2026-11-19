import LongTails.Algorithms.CorruptedFirstOrderDescent
import LongTails.Proofs.GdConvex

open OracleTemplate LongTails.Setups.CorruptedFirstOrderNonconvex
open LongTails.Algorithms.CorruptedFirstOrderDescent
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CorruptedFirstOrderEstimates

lemma filter_mono_length {α : Type*} (xs : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp_all
    omega

lemma partition_length {α : Type*} (xs : List α) (p : α → Bool) :
    (xs.filter p).length + (xs.filter fun x => !(p x)).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [hp] <;> omega

noncomputable def valueErrors (vs : List ℝ) (z η : ℝ) :=
  (vs.filter fun v => decide (η < |v - z|)).length

lemma anchor_bounds (vs : List ℝ) (k : ℕ) (z η : ℝ) (hlen : vs.length = 2 * k + 1)
    (hbad : valueErrors vs z η ≤ k) :
    z + η ≤ startingBound vs k η ∧ startingBound vs k η ≤ z + 3 * η := by
  classical
  let U := {t : ℝ | k < (vs.filter (· ≤ t)).length}
  have lo : ∀ t ∈ U, z - η ≤ t := by
    intro t ht
    by_contra! h
    have hh := filter_mono_length vs (fun v => decide (v ≤ t))
      (fun v => decide (η < |v - z|)) (by
        intro x hx
        simp only [decide_eq_true_eq] at *
        exact lt_abs.mpr (Or.inr (by linarith)))
    change k < _ at ht
    unfold valueErrors at hbad
    omega
  have hu : z + η ∈ U := by
    change k < _
    have hh := filter_mono_length vs (fun v => !decide (v ≤ z + η))
      (fun v => decide (η < |v - z|)) (by
        intro x hx
        simp at hx ⊢
        exact lt_abs.mpr (Or.inl (by linarith)))
    have he := partition_length vs (fun v => decide (v ≤ z + η))
    unfold valueErrors at hbad
    omega
  have h₁ := le_csInf (Set.nonempty_of_mem hu) lo
  have h₂ := csInf_le (show BddBelow U from ⟨_, lo⟩) hu
  change z + η ≤ sInf U + 2 * η ∧ sInf U + 2 * η ≤ z + 3 * η
  constructor <;> linarith

lemma trial_decrease {p : Params} {f : Space p.d → ℝ} {x u : Space p.d}
    (hL : 0 < p.L) (he : 0 < p.ε)
    (hg : ∀ y, HasGradientAt f (gradient f y) y)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ p.L * ‖y - z‖)
    (herr : ‖u - gradient f x‖ ≤ p.ε / 8) (hu : (3 * p.ε / 4) < ‖u‖) :
    f (x - (1 / p.L) • u) ≤ f x - 5 * p.ε ^ 2 / (64 * p.L) := by
  have hs := Gradient.smooth_upper_bound hg hlip x (x - (1 / p.L) • u)
  have hd : x - (1 / p.L) • u - x = -((1 / p.L) • u) := by abel
  rw [hd, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity)] at hs
  have hc := real_inner_le_norm (u - gradient f x) u
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hc
  have hnoise := mul_le_mul_of_nonneg_right herr (norm_nonneg u)
  have hmul := mul_le_mul_of_nonneg_left hs hL.le
  field_simp [hL.ne'] at hmul ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hu.le) (sub_nonneg.mpr hu.le),
    mul_nonneg he.le (sub_nonneg.mpr hu.le)]

end LongTails.Proofs.CorruptedFirstOrderEstimates
