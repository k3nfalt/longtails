import LongTails.Algorithms.DashaCyclic
import Mathlib.Tactic

namespace LongTails.Proofs.DashaCyclic

open LongTails.Algorithms.DashaCyclic

lemma prefix_sum {d : ℕ+} (k : Fin d) :
    (∑ j : Fin d, if j.val < k.val + 1 then (1 : ℝ) else 0) = k.val + 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k.val + 1 then (1 : ℝ) else 0) (d : ℕ)]
  rw [← Finset.sum_filter]
  have he : (Finset.range (d : ℕ)).filter (fun j => j < k.val + 1) = Finset.range (k.val + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  simp

lemma inclusion_sum {d : ℕ+} (k j : Fin d) :
    (∑ shift : Fin d, if selected k shift j then (1 : ℝ) else 0) = k.val + 1 := by
  let e : Fin d ≃ Fin d :=
    { toFun := fun shift => j - shift
      invFun := fun shift => j - shift
      left_inv := by intro shift; simp [sub_eq_add_neg, ← add_assoc]
      right_inv := by intro shift; simp [sub_eq_add_neg, ← add_assoc] }
  have he := e.sum_comp (fun a : Fin d => if a.val < k.val + 1 then (1 : ℝ) else 0)
  exact he.trans (prefix_sum k)

lemma coordinate_selected {d : ℕ+} (k shift : Fin d) (i : Fin (k.val + 1)) :
    selected k shift (coordinate k shift i) := by
  unfold selected coordinate
  rw [add_sub_cancel_left]
  exact i.isLt

lemma coordinate_injective {d : ℕ+} (k shift : Fin d) : Function.Injective (coordinate k shift) := by
  intro i j hij
  have he := add_left_cancel hij
  exact Fin.ext (congrArg (fun z : Fin d => z.val) he)

lemma scaled_mean {d : ℕ+} (k j : Fin d) (x : ℝ) :
    (1 / (d : ℝ)) * (∑ shift : Fin d, if selected k shift j then multiplier k * x else 0) = x := by
  have he : (∑ shift : Fin d, if selected k shift j then multiplier k * x else 0) =
      (∑ shift : Fin d, if selected k shift j then (1 : ℝ) else 0) * (multiplier k * x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro shift _
    split_ifs <;> simp
  rw [he, inclusion_sum]
  unfold multiplier
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast d.ne_zero
  have hk : (k.val : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma scaled_variance {d : ℕ+} (k j : Fin d) (x : ℝ) :
    (1 / (d : ℝ)) * (∑ shift : Fin d,
      ((if selected k shift j then multiplier k * x else 0) - x) ^ 2) =
      (multiplier k - 1) * x ^ 2 := by
  have he (shift : Fin d) : ((if selected k shift j then multiplier k * x else 0) - x) ^ 2 =
      (if selected k shift j then (1 : ℝ) else 0) * ((multiplier k) ^ 2 - 2 * multiplier k) * x ^ 2 + x ^ 2 := by
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, inclusion_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold multiplier
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast d.ne_zero
  have hk : (k.val : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end LongTails.Proofs.DashaCyclic
