import LongTails.Proofs.BrightnessLogisticField

namespace LongTails.Proofs.BrightnessLogisticTapWork

lemma kinetic {p t β b : ℝ} (hb : |β| ≤ b) :
    (β*t)^2 ≤ b*|β*p*t|+β^2*max (-(p^2-t^2)) 0 := by
  have hprice := mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg β) (abs_nonneg (p*t)))
  rw [mul_assoc β p t,abs_mul β (p*t),abs_mul p t]
  rw [abs_mul p t] at hprice
  have hβ : |β| * (|β| * (|p| * |t|)) = β^2*(|p| * |t|) := by
    rw [← mul_assoc,← sq,sq_abs]
  rw [hβ] at hprice
  rcases le_total (|p|) (|t|) with h | h
  · have hm := mul_self_le_mul_self (abs_nonneg p) h
    have hpt : p^2 ≤ t^2 := by simpa [← sq,sq_abs] using hm
    rw [max_eq_left (by linarith)]
    have hp : p^2 ≤ |p| * |t| := by
      simpa [← sq,sq_abs] using mul_le_mul_of_nonneg_left h (abs_nonneg p)
    nlinarith only [hprice,mul_le_mul_of_nonneg_left hp (sq_nonneg β)]
  · have hm := mul_self_le_mul_self (abs_nonneg t) h
    have hpt : t^2 ≤ p^2 := by simpa [← sq,sq_abs] using hm
    rw [max_eq_right (by linarith)]
    have ht : t^2 ≤ |p| * |t| := by
      simpa [← sq,sq_abs] using mul_le_mul_of_nonneg_right h (abs_nonneg t)
    nlinarith only [hprice,mul_le_mul_of_nonneg_left ht (sq_nonneg β)]

lemma tap_change {p q t β e f b W H : ℝ} (hb : |β| ≤ b) (hb1 : b ≤ 1) (hW : 0 ≤ W)
    (hwork : β*p*t+(p*e+q*f) ≤ W) (hslow : |p*e+q*f| ≤ H) :
    (p+β*t+e)^2+(q+f)^2-(p^2+q^2) ≤
      (2+2*b)*W+2*b*H+2*β^2*max (-(p^2-t^2)) 0+2*e^2+f^2 := by
  have h0 := (abs_nonneg _).trans hb
  have hH := (abs_nonneg _).trans hslow
  have hk := kinetic (p := p) (t := t) hb
  have he := sq_nonneg (β*t-e)
  have hx : 2*(β*p*t+(p*e+q*f))+2*b*|β*p*t| ≤ (2+2*b)*W+2*b*H := by
    rcases le_total 0 (β*p*t) with h | h
    · rw [abs_of_nonneg h]
      have hh : β*p*t ≤ W+H := by linarith [neg_abs_le (p*e+q*f)]
      nlinarith only [hwork,mul_le_mul_of_nonneg_left hh h0]
    · rw [abs_of_nonpos h]
      have hh := mul_le_mul_of_nonneg_left hwork (show 0 ≤ 1-b by linarith)
      nlinarith only [hh,mul_le_mul_of_nonneg_left ((le_abs_self _).trans hslow) h0,
        mul_nonneg h0 hW]
  nlinarith only [hk,he,hx]

end LongTails.Proofs.BrightnessLogisticTapWork
