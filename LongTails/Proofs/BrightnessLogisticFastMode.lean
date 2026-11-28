import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.BrightnessLogisticFastMode

lemma forced_pair_difference (c s u h e : ℝ) :
    (c + u * s + h * e)^2 - (s + u * c)^2 =
      (1 - u^2) * (c^2 - s^2) + 2 * h * (c + u * s) * e + h^2 * e^2 := by
  ring

lemma kinetic_dissipation (p t β b : ℝ) (hb : |β| ≤ b) :
    let E := fun x y : ℝ => x^2+y^2+2*|x^2-y^2|
    E (p+β*t) (t+β*p) - E p t + β^2*(p^2+t^2) ≤
      4*β*p*t+4*b*|β*p*t| + 2*(|1-β^2|-(1-β^2))*|p^2-t^2| := by
  dsimp only
  rw [show (p+β*t)^2-(t+β*p)^2 = (1-β^2)*(p^2-t^2) by ring,abs_mul]
  have hw : p^2+t^2-|p^2-t^2| ≤ 2*|p*t| := by
    rcases le_total (|p|) (|t|) with h | h
    · have hh := mul_self_le_mul_self (abs_nonneg p) h
      have hpt : p^2 ≤ t^2 := by simpa [← sq, sq_abs] using hh
      rw [abs_of_nonpos (sub_nonpos.mpr hpt),abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg p),sq_abs p]
    · have hh := mul_self_le_mul_self (abs_nonneg t) h
      have hpt : t^2 ≤ p^2 := by simpa [← sq, sq_abs] using hh
      rw [abs_of_nonneg (sub_nonneg.mpr hpt),abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg t),sq_abs t]
  have he := mul_le_mul_of_nonneg_left hw (sq_nonneg β)
  have hc := mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg β) (abs_nonneg (p*t)))
  rw [mul_assoc β p t, abs_mul β (p*t)]
  nlinarith only [he,hc,sq_abs β,show |β| * (|β| * |p*t|) = β^2 * |p*t| by rw [← mul_assoc, ← sq, sq_abs]]

lemma small_branch {p t δ : ℝ} (hδ : 0 ≤ δ) (h : p^2-t^2 ≤ δ^2) :
    |p| ≤ min (|p|) (|t|)+δ := by
  rw [← min_add_add_right]
  apply le_min
  · linarith
  · by_contra! hn
    have hh := mul_self_lt_mul_self (add_nonneg (abs_nonneg t) hδ) hn
    nlinarith [sq_abs p,sq_abs t,mul_nonneg (abs_nonneg t) hδ]

lemma sum_discounted_imbalance (D β e : ℕ → ℝ) (K : ℕ)
    (h : ∀ j < K, max (-(D (j+1))) 0 ≤ (1-(β j)^2)*max (-(D j)) 0 + e j) :
    ∑ j ∈ Finset.range K, (β j)^2*max (-(D j)) 0 ≤
      max (-(D 0)) 0 - max (-(D K)) 0 + ∑ j ∈ Finset.range K, e j := by
  induction K with
  | zero => simp
  | succ k ih =>
    have hh := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hk := h k (Nat.lt_succ_self _)
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    linarith

lemma energy_and_dissipation (A d m : ℕ → ℝ) (C : ℝ) (K : ℕ) (hC : 0 ≤ C)
    (hA : 0 ≤ A 0) (hd : ∀ j, 0 ≤ d j) (hm : ∀ j, 0 ≤ m j)
    (h : ∀ j < K, A (j+1)+d j ≤ (1+C*m j)*A j) :
    A K + ∑ j ∈ Finset.range K, d j ≤
      Real.exp (C * ∑ j ∈ Finset.range K, m j) * A 0 := by
  induction K with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    let s := ∑ j ∈ Finset.range k, d j
    have hs : 0 ≤ s := Finset.sum_nonneg (fun j _ => hd j)
    have hcm := mul_nonneg hC (hm k)
    have hfac : 0 ≤ 1+C*m k := by linarith
    have hinc : A (k+1)+(s+d k) ≤ (1+C*m k)*(A k+s) := by
      nlinarith only [h k (Nat.lt_succ_self _),mul_nonneg hcm hs]
    rw [Finset.sum_range_succ,Finset.sum_range_succ,mul_add,Real.exp_add]
    calc
      _ ≤ (1+C*m k)*(A k+s) := hinc
      _ ≤ (1+C*m k)*(Real.exp (C*∑ j ∈ Finset.range k, m j)*A 0) :=
        mul_le_mul_of_nonneg_left hi hfac
      _ ≤ Real.exp (C*m k)*(Real.exp (C*∑ j ∈ Finset.range k, m j)*A 0) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.exp_pos _).le hA)
        linarith [Real.add_one_le_exp (C*m k)]
      _ = _ := by ring

end LongTails.Proofs.BrightnessLogisticFastMode
