import Mathlib.Tactic

namespace OracleTemplate.VarianceReducedWeakMinty

lemma relative_error_transfer {s q v A B D R err : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hq : 0 ≤ q) (hv : 0 ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hqsmall : q ≤ s ^ 2 / 8192) (hvsmall : v ≤ s ^ 2 / 65536)
    (hR : R ≤ q * A + 8 * v * (A + B))
    (htriangle : A ≤ 2 * D + 2 * R)
    (herr : err ≤ 16 * q * A + 136 * v * (A + B)) :
    A ≤ 3 * D + 32 * v * B ∧ err ≤ s ^ 2 / 32 * D + 256 * v * B := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hq' : q ≤ 1 / 8192 := by linarith
  have hv' : v ≤ 1 / 65536 := by linarith
  have hc : 2 * q + 16 * v ≤ 1 / 3 := by linarith
  have hca := mul_le_mul_of_nonneg_right hc hA
  have htransfer : A ≤ 3 * D + 32 * v * B := by
    nlinarith [mul_nonneg hv hB]
  refine ⟨htransfer, ?_⟩
  have hecoef : 16 * q + 136 * v ≤ s ^ 2 / 96 := by linarith
  have hecoef' : 16 * q + 136 * v ≤ 1 / 96 := by linarith
  have hm := mul_le_mul_of_nonneg_left htransfer
    (by positivity : 0 ≤ 16 * q + 136 * v)
  have hd := mul_le_mul_of_nonneg_right hecoef (by positivity : 0 ≤ 3 * D)
  have hb := mul_le_mul_of_nonneg_right hecoef' (by positivity : 0 ≤ 32 * v * B)
  nlinarith [mul_nonneg hv hB]

lemma outer_absorption {s p D X Z err noise residual V base : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hZX : Z ≤ X)
    (herr : err ≤ s ^ 2 / 32 * D + p / 64 * Z)
    (hnoise : noise ≤ D / 32 + p / 32 * Z)
    (hres : residual ≤ 2 * D + 2 * err)
    (henergy : V ≤ base - p * (1 - p) * X - s ^ 2 / 2 * D + 2 * err + s ^ 2 * noise) :
    V + s ^ 2 / 16 * residual ≤ base := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hsD := mul_le_mul_of_nonneg_right hs2 hD
  have hpZ := mul_le_mul_of_nonneg_left hZX hp
  have hsZ := mul_le_mul_of_nonneg_right hs2 (mul_nonneg hp hZ)
  have hsX := mul_le_mul_of_nonneg_right hs2 (mul_nonneg hp hX)
  have hgap : p / 2 ≤ p * (1 - p) := by nlinarith
  have hgapX := mul_le_mul_of_nonneg_right hgap hX
  have hnoise' := mul_le_mul_of_nonneg_left hnoise (sq_nonneg s)
  have hV : V ≤ base - s ^ 2 / 4 * D - p / 4 * X := by
    nlinarith [mul_nonneg (sq_nonneg s) hD, mul_nonneg hp hX]
  have hres' : residual ≤ 3 * D + p / 2 * X := by nlinarith
  have hcharge := mul_le_mul_of_nonneg_left hres' (by positivity : 0 ≤ s ^ 2 / 16)
  nlinarith [mul_nonneg (sq_nonneg s) hD, mul_nonneg hp hX]

lemma noise_relaxation {s p α θ : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hθα : θ ≤ α)
    (hα : α ≤ s ^ 2 * p / 65536) :
    256 * α ≤ p / 64 ∧ 2 * θ ≤ 1 / 32 ∧ 2 * θ ≤ p / 32 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hs2 hp
  constructor
  · nlinarith
  constructor <;> nlinarith

end OracleTemplate.VarianceReducedWeakMinty
