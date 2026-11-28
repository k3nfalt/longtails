import LongTails.Proofs.BrightnessLogisticEnergy

namespace LongTails.Proofs.BrightnessLogisticOccupation

lemma charge_large {p t β δ b m h S : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hm : 0 ≤ m) (hmh : m ≤ h) (hS : min (|p|) (|t|) ≤ S)
    (hβ : δ < min (|p|) (|t|) → b ≤ |β|) :
    m*min (|p|) (|t|) ≤ m*δ+(h*S/(b^2*δ^2))*(β^2*(p^2+t^2)) := by
  have h0 : 0 ≤ min (|p|) (|t|) := le_min (abs_nonneg _) (abs_nonneg _)
  have hS0 := h0.trans hS
  have hh := hm.trans hmh
  have hpos : 0 < b^2*δ^2 := by positivity
  rcases le_or_gt (min (|p|) (|t|)) δ with hl | hl
  · exact (mul_le_mul_of_nonneg_left hl hm).trans (le_add_of_nonneg_right (by positivity))
  · have hβ2 := mul_self_le_mul_self hb.le (hβ hl)
    have hp2 := mul_self_le_mul_self hδ.le (hl.le.trans (min_le_left _ _))
    have hx : b^2 ≤ β^2 := by simpa [← sq,sq_abs] using hβ2
    have hy : δ^2 ≤ p^2+t^2 := by nlinarith only [hp2,sq_abs p,sq_nonneg t]
    have hkin := mul_le_mul hx hy (sq_nonneg δ) (sq_nonneg β)
    have hcost : h*S ≤ (h*S/(b^2*δ^2))*(β^2*(p^2+t^2)) := by
      calc
        _ = (h*S/(b^2*δ^2))*(b^2*δ^2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hkin (by positivity)
    linarith [mul_le_mul hmh hS h0 hh,mul_nonneg hm hδ.le]

lemma charge_velocity {x δ m h : ℝ} (hδ : 0 < δ) (hm : 0 ≤ m) (hmh : m ≤ h) :
    m*|x| ≤ m*δ + (h/δ)*x^2 := by
  have hx : |x| ≤ δ+x^2/δ := by
    rw [← sub_le_iff_le_add',le_div_iff₀ hδ]
    nlinarith [sq_nonneg (|x|-δ),sq_abs x,mul_nonneg (abs_nonneg x) hδ.le]
  have h1 := mul_le_mul_of_nonneg_left hx hm
  have h2 := mul_le_mul_of_nonneg_right hmh (div_nonneg (sq_nonneg x) hδ.le)
  nlinarith only [h1,h2,show (h/δ)*x^2 = h*(x^2/δ) by ring]

lemma imbalance_charge {p t β e δ Z m : ℝ} (hδ : 0 ≤ δ) (hβ : β^2 ≤ 1)
    (he : |e| ≤ m*Z) (hsmall : 2*|p+β*t| * |e| ≤ (1-β^2)*δ^2) :
    let D := p^2-t^2
    let D' := (p+β*t+e)^2-(t+β*p)^2
    max (-D') 0 ≤ (1-β^2)*max (-D) 0+
      2*m*Z*(min (|p|) (|t|)+δ+|β*t|) := by
  dsimp only
  have hc : 0 ≤ 1-β^2 := sub_nonneg.mpr hβ
  have hmZ := (abs_nonneg _).trans he
  have ha : 0 ≤ min (|p|) (|t|) := le_min (abs_nonneg _) (abs_nonneg _)
  have hprod := neg_abs_le ((p+β*t)*e)
  rw [abs_mul] at hprod
  have hD := BrightnessLogisticFastMode.forced_pair_difference p t β 1 e
  rw [one_mul,one_pow,one_mul] at hD
  rw [hD]
  by_cases h : δ^2 ≤ p^2-t^2
  · have hh := mul_le_mul_of_nonneg_left h hc
    rw [max_eq_right (by nlinarith only [hh,hsmall,hprod,sq_nonneg e])]
    exact add_nonneg (mul_nonneg hc (le_max_right _ _))
      (mul_nonneg (by linarith : 0 ≤ 2*m*Z) (by positivity))
  · have hp := BrightnessLogisticFastMode.small_branch hδ (le_of_not_ge h)
    have hh := (abs_add_le p (β*t)).trans (add_le_add_left hp _)
    have hi := mul_le_mul hh he (abs_nonneg e) (by positivity)
    have hpay := mul_le_mul_of_nonneg_left (le_max_left (-(p^2-t^2)) 0) hc
    apply max_le
    · nlinarith only [hpay,hi,hprod,sq_nonneg e]
    · exact add_nonneg (mul_nonneg hc (le_max_right _ _))
        (mul_nonneg (by linarith : 0 ≤ 2*m*Z) (by positivity))

end LongTails.Proofs.BrightnessLogisticOccupation
