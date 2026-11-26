import LongTails.Algorithms.TerminalClippingSingleLog
import Mathlib.Tactic

namespace OracleTemplate.TerminalClippingSingleLog

structure Tuning (T q M r k C b τ : ℝ) : Prop where
  time : 0 < T
  confidence : 1 ≤ q
  scale : 0 < M
  radius : 0 < r
  slope_pos : 0 < k
  level_pos : 0 < C
  direction_eq : b = 3*k*r
  multiplier_pos : 0 < τ
  small : 2*τ*C*b ≤ 1
  closes : r^2 + 2*k^2*(T*M^2/2 + (q+T*(2*M^2/C^2))*C^2) +
    T*(b*M^2/C) + (q+T*(τ^2*b^2*M^2))/τ ≤ 2*r^2
  accuracy : 2*r^2/k = 24*(r*T)*M*Real.sqrt (q/T)

lemma tuning {T q M r : ℝ} (hT : 0 < T) (hq : 1 ≤ q) (hM : 0 < M) (hr : 0 < r) :
    let k := r/(12*M*Real.sqrt (T*q))
    let C := M*Real.sqrt (T/q)
    let b := 3*k*r
    let τ := 1/(2*b*C)
    Tuning T q M r k C b τ := by
  have hq0 : 0 < q := by linarith
  let w := Real.sqrt (T*q)
  have hw : 0 < w := Real.sqrt_pos.mpr (mul_pos hT hq0)
  have hw2 : w^2 = T*q := Real.sq_sqrt (mul_pos hT hq0).le
  have hC : Real.sqrt (T/q) = w/q := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), div_pow, hw2]
    field_simp
  have hrate : Real.sqrt (q/T) = w/T := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), div_pow, hw2]
    field_simp
  dsimp only
  change Tuning T q M r (r/(12*M*w)) (M*Real.sqrt (T/q)) _ _
  rw [hC]
  refine ⟨hT,hq,hM,hr,by positivity,by positivity,rfl,by positivity,?_,?_,?_⟩
  · field_simp; rfl
  · have hrel : T = w^2/q := (eq_div_iff hq0.ne').mpr hw2.symm
    rw [hrel]
    field_simp
    ring_nf
    rw [Real.sqrt_sq hw.le]
    nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hq)]
  · rw [hrate]
    field_simp
    ring

end OracleTemplate.TerminalClippingSingleLog
