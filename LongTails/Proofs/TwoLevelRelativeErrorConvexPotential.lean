import LongTails.Proofs.TwoLevelRelativeErrorConvexInner
import LongTails.Proofs.DampedAccelerated

open scoped RealInnerProductSpace
namespace LongTails.Proofs.TwoLevelRelativeErrorConvex
open OracleTemplate LongTails.Algorithms.TwoLevelRelativeErrorConvex
open RecursiveEnvelopeExecution RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def weight (q : ℝ) (k : ℕ) := q * (k : ℝ) * (k+1) / 4

noncomputable def energy (F : E → ℝ) (xs : E) (q : ℝ) (k : ℕ) (x z : E) :=
  weight q k * F x + ‖z-xs‖^2/2

lemma energy_step {F : E → ℝ} {xs x z u d : E} {q σ : ℝ} (k : ℕ)
    (hq : 0 < q) (hq6 : q ≤ 1/6) (hs2 : σ ≤ 1/2)
    (hF : 0 ≤ F x)
    (herr : ‖d - (center k x z-u)‖ ≤ σ*‖d‖)
    (hmodel : ∀ t, F u - F t ≤ ⟪d,center k x z-t⟫ - 3/8*‖d‖^2)
    (hstar : F xs = 0) :
    energy F xs q (k+1) u (z - (q * ((k : ℝ)+1)/2) • (center k x z-u)) ≤
      (1+3*q*σ^2)*energy F xs q k x z := by
  let y := center k x z
  let v := y-u
  let a := q*((k : ℝ)+1)/2
  let A := weight q k
  let B := weight q (k+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 ≤ A := by dsimp [A,weight]; positivity
  have hB : 0 < B := by dsimp [B,weight]; positivity
  have hsum : B = A+a := by dsimp [A,B,weight,a]; push_cast; ring
  have hasq : a^2 ≤ q*B := by
    dsimp [a,B,weight]; push_cast
    nlinarith only [mul_nonneg (sq_nonneg q) (by positivity : 0 ≤ (k:ℝ)+1)]
  have hcy : ((k:ℝ)+2) • y = (k:ℝ) • x + (2:ℝ) • z := by
    dsimp [y,center,RelativeErrorConvex.query]
    rw [smul_smul,mul_one_div_cancel (by positivity),one_smul]
  have hvect : A • (y-x) + a • (y-xs) = a • (z-xs) := by
    apply sub_eq_zero.mp
    calc _ = (q*((k:ℝ)+1)/4) • (((k:ℝ)+2) • y - ((k:ℝ) • x + (2:ℝ) • z)) := by
                dsimp [A,weight,a]; module
         _ = 0 := by rw [hcy,sub_self,smul_zero]
  have hi := congrArg (fun t : E => ⟪d,t⟫) hvect
  simp only [inner_add_right,real_inner_smul_right] at hi
  have hm1 := mul_le_mul_of_nonneg_left (hmodel x) hA
  have hm2 := mul_le_mul_of_nonneg_left (hmodel xs) ha.le
  rw [hstar,sub_zero] at hm2
  have hf : B*F u - A*F x ≤ a*⟪d,z-xs⟫ - 3/8*B*‖d‖^2 := by
    rw [hsum]; dsimp only [y] at hi; linarith only [hm1,hm2,hi]
  change ‖d-v‖ ≤ _ at herr
  have hv : ‖v‖ ≤ (3/2)*‖d‖ := by
    have ht := norm_sub_le d (d-v)
    rw [sub_sub_cancel] at ht
    linarith [mul_le_mul_of_nonneg_right hs2 (norm_nonneg d)]
  have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hquad : a^2 * ‖v‖^2 ≤ (3/8)*B*‖d‖^2 := by
    have h1 := mul_le_mul hasq hv2 (sq_nonneg _) (mul_nonneg hq.le hB.le)
    have h2 := mul_le_mul_of_nonneg_right hq6 (show 0 ≤ B*‖d‖^2 by positivity)
    nlinarith only [h1,h2]
  have hcross := (real_inner_le_norm (d-v) (z-xs)).trans
    (mul_le_mul_of_nonneg_right herr (norm_nonneg _))
  rw [inner_sub_left] at hcross
  have hyoung := RelativeErrorConvex.young_slack (X := ‖d‖) (Y := ‖z-xs‖)
    (show 0 < B/6 by positivity)
    (show (a*σ)^2 ≤ 4*(B/6)*(3/2*q*σ^2) by
      nlinarith only [mul_le_mul_of_nonneg_right hasq (sq_nonneg σ)])
  have he : z-a • v-xs = (z-xs)-a • v := by abel
  change B*F u + ‖z-a • v-xs‖^2/2 ≤ (1+3*q*σ^2)*(A*F x+‖z-xs‖^2/2)
  rw [he,norm_sub_sq_real,real_inner_smul_right,real_inner_comm v (z-xs),
    norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  nlinarith only [hf,hquad,mul_le_mul_of_nonneg_left hcross ha.le,hyoung,
    mul_nonneg (show 0 ≤ 3*q*σ^2 by positivity) (mul_nonneg hA hF),
    mul_nonneg hB.le (sq_nonneg ‖d‖)]

end LongTails.Proofs.TwoLevelRelativeErrorConvex
