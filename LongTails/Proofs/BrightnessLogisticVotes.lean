import LongTails.Proofs.BrightnessLogisticRawDynamics

open LongTails.Setups.BrightnessLogisticRaw

namespace LongTails.Proofs.BrightnessLogisticVotes

open BrightnessLogisticRawDynamics

lemma linear_work (s L : ℝ) : s*vote s ≤ L*vote s+Real.exp (-L) := by
  rcases le_or_gt s L with h | h
  · exact (mul_le_mul_of_nonneg_right h (confidence _).1).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hs : vote s ≤ (Real.exp s)⁻¹ := by
      rw [vote,one_div]
      exact inv_anti₀ (Real.exp_pos _) (by linarith)
    have hh := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr h.le)
    have hex : (s-L)*(Real.exp s)⁻¹ ≤ Real.exp (-L) := by
      rw [← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _),← Real.exp_add]
      have ht := Real.add_one_le_exp (s-L)
      rw [show -L+s = s-L by ring]
      linarith
    linarith [hh.trans hex]

lemma mass_floor {n : ℕ+} (s : Fin n → ℝ) (i : Fin n) (hi : s i ≤ 0) :
    (2*(n : ℝ))⁻¹ ≤ mean (fun j => vote (s j)) := by
  have hn : 0 < (n : ℝ) := by positivity
  have hv : (1:ℝ)/2 ≤ vote (s i) := by
    rw [vote,le_div_iff₀ (by positivity : 0 < 1+Real.exp (s i))]
    have h : Real.exp (s i) ≤ 1 := by simpa using Real.exp_le_exp.mpr hi
    linarith
  have hsum := Finset.single_le_sum (f := fun j => vote (s j))
    (fun j _ => (confidence _).1) (Finset.mem_univ i)
  rw [mean]
  have hh := mul_le_mul_of_nonneg_left (hv.trans hsum) (inv_nonneg.mpr hn.le)
  apply le_trans _ hh
  field_simp
  rfl

lemma prefit_work {n : ℕ+} (s : Fin n → ℝ) (i : Fin n) (hi : s i ≤ 0) :
    mean (fun j => s j*vote (s j)) ≤
      (1+Real.log (2*(n : ℝ)))*mean (fun j => vote (s j)) := by
  let L := Real.log (2*(n : ℝ))
  have hn : 0 < (n : ℝ) := by positivity
  have he : Real.exp (-L) = (2*(n : ℝ))⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by positivity : 0 < 2*(n : ℝ))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ => linear_work (s j) L
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,he] at hsum
  have hh := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
  have hcancel : (n : ℝ)⁻¹*((n : ℝ)*(2*(n : ℝ))⁻¹)=(2*(n : ℝ))⁻¹ := by field_simp
  rw [mul_add,hcancel] at hh
  have hm := mass_floor s i hi
  unfold mean at hm ⊢
  change _ ≤ (1+L)*_
  nlinarith only [hh,hm]

end LongTails.Proofs.BrightnessLogisticVotes
