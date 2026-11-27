import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace LongTails.Proofs.ExponentialMarginWork

open Finset

noncomputable def mass {ι : Type*} [Fintype ι] (β : ℝ) (m : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-β * m i)

lemma strictly_positive {ι : Type*} [Fintype ι] {β : ℝ} (hβ : 0 < β) {m : ι → ℝ}
    (hm : mass β m < 1) (i : ι) : 0 < m i := by
  by_contra! hn
  have hx : 1 ≤ Real.exp (-β*m i) := Real.one_le_exp (by nlinarith)
  have h := Finset.single_le_sum (f := fun j => Real.exp (-β*m j))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  exact (not_le_of_gt hm) (hx.trans h)

lemma increment {ι : Type*} [Fintype ι] {β a : ℝ} (hβ : 0 < β)
    {m m' l u d : ι → ℝ} (hl : ∀ i, l i ≤ Real.exp (-β*m i))
    (hu : ∀ i, Real.exp (-β*m i) ≤ u i) (hd : ∀ i, d i ≤ m' i-m i)
    (hw : (∑ i, let b := Real.exp (-β*d i)-a; max (l i*b) (u i*b)) ≤ 0) :
    mass β m' ≤ a*mass β m := by
  have H (i : ι) :
      Real.exp (-β*m' i)-a*Real.exp (-β*m i) ≤
      max (l i*(Real.exp (-β*d i)-a)) (u i*(Real.exp (-β*d i)-a)) := by
    have ha : Real.exp (-β*m' i) ≤ Real.exp (-β*m i)*Real.exp (-β*d i) := by
      rw [← Real.exp_add,Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left (hd i) hβ.le]
    have hh : Real.exp (-β*m i)*(Real.exp (-β*d i)-a) ≤ _ :=
      if hb : 0 ≤ Real.exp (-β*d i)-a then
        (mul_le_mul_of_nonneg_right (hu i) hb).trans (le_max_right _ _)
      else (mul_le_mul_of_nonpos_right (hl i) (le_of_not_ge hb)).trans (le_max_left _ _)
    linarith
  have h := (Finset.sum_le_sum fun i _ => H i).trans hw
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at h
  exact sub_nonpos.mp h

end LongTails.Proofs.ExponentialMarginWork
