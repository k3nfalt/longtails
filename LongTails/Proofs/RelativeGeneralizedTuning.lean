import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OracleTemplate.RelativeGeneralized

lemma tuning_bounds {A B R L0 L1 : ℝ} (hA : 0 < A) (hB : 1 ≤ B)
    (hR : 0 < R) (h0 : 0 < L0) (h1 : 0 ≤ L1) :
    let D := B * R ^ 2 / A
    let a := A / (4096 * (1 + L1 * R * Real.sqrt B + Real.sqrt (L0 * A)))
    let η := 1 / (1024 * (L0 + L1 ^ 2 * D))
    0 < a ∧ 0 < η ∧ η * (L0 + L1 ^ 2 * D) = 1 / 1024 ∧
      L1 * (4 * R * a / (A + a)) ≤ 1 / 2 ∧
      L0 * (4 * R * a / (A + a)) ≤ Real.sqrt (L0 * D) / 2 ∧
      1024 * a ^ 2 ≤ η * (A + a) := by
  dsimp only
  let W := 1 + L1 * R * Real.sqrt B + Real.sqrt (L0 * A)
  let D := B * R ^ 2 / A
  let a := A / (4096 * W)
  let η := 1 / (1024 * (L0 + L1 ^ 2 * D))
  change 0 < a ∧ 0 < η ∧ η * (L0 + L1 ^ 2 * D) = 1 / 1024 ∧
    L1 * (4 * R * a / (A + a)) ≤ 1 / 2 ∧
    L0 * (4 * R * a / (A + a)) ≤ Real.sqrt (L0 * D) / 2 ∧
    1024 * a ^ 2 ≤ η * (A + a)
  have hB0 : 0 ≤ B := by linarith
  have hb : 1 ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) hB0).mpr (by simpa using hB)
  have hW : 0 < W := by dsimp [W]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have haeq : a * (4096 * W) = A := by dsimp [a]; field_simp
  have hηeq : η * (L0 + L1 ^ 2 * D) = 1 / 1024 := by dsimp [η]; field_simp
  refine ⟨ha, hη, hηeq, ?_, ?_, ?_⟩
  · have hq : L1 * R ≤ W := by
      have h := mul_le_mul_of_nonneg_left hb (mul_nonneg h1 hR.le)
      dsimp [W]; nlinarith [Real.sqrt_nonneg (L0 * A)]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < A + a by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq ha.le]
  · have hs := Real.sq_sqrt (mul_nonneg h0.le hA.le)
    have hd := Real.sq_sqrt (mul_nonneg h0.le hD.le)
    have hDrel : D * A = B * R ^ 2 := by dsimp [D]; field_simp
    have hprod : L0 * R ≤ Real.sqrt (L0 * A) * Real.sqrt (L0 * D) := by
      have hh : (L0 * R) ^ 2 ≤ (Real.sqrt (L0 * A) * Real.sqrt (L0 * D)) ^ 2 := by
        rw [mul_pow, mul_pow, hs, hd]
        nlinarith [mul_nonneg (sq_nonneg L0) (show 0 ≤ (B - 1) * R ^ 2 by positivity)]
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hh
    have hw : Real.sqrt (L0 * A) ≤ W := by
      dsimp [W]
      nlinarith [mul_nonneg (mul_nonneg h1 hR.le) (Real.sqrt_nonneg B)]
    have hh := mul_le_mul_of_nonneg_right hw (Real.sqrt_nonneg (L0 * D))
    have hk := mul_le_mul_of_nonneg_left (hprod.trans hh) ha.le
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < A + a by positivity)).mpr
    nlinarith [mul_nonneg ha.le (Real.sqrt_nonneg (L0 * D))]
  · have hWsq : L0 * A + L1 ^ 2 * B * R ^ 2 ≤ W ^ 2 := by
      have hbq := Real.sq_sqrt hB0
      have hsq := Real.sq_sqrt (mul_nonneg h0.le hA.le)
      have ht : (L1 * R * Real.sqrt B) ^ 2 = L1 ^ 2 * B * R ^ 2 := by
        rw [mul_pow, mul_pow, hbq]; ring
      dsimp [W]
      nlinarith [Real.sqrt_nonneg (L0 * A),
        mul_nonneg (mul_nonneg h1 hR.le) (Real.sqrt_nonneg B),
        mul_nonneg (show 0 ≤ L1 * R * Real.sqrt B by positivity)
          (Real.sqrt_nonneg (L0 * A))]
    have hDrel : D * A = B * R ^ 2 := by dsimp [D]; field_simp
    have hm : (L0 + L1 ^ 2 * D) * A ≤ W ^ 2 := by nlinarith
    have ham : a ^ 2 * (L0 + L1 ^ 2 * D) ≤ A / 4096 ^ 2 := by
      dsimp [a]
      rw [div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < (4096 * W) ^ 2)).mpr
      have hh := mul_le_mul_of_nonneg_left hm hA.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ham hη.le,
      mul_nonneg hη.le ha.le]

end OracleTemplate.RelativeGeneralized
