import LongTails.Proofs.NoisyTwoSamplePerceptronSignal
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace
open LongTails.Proofs.NoisyTwoSamplePerceptronSignal

namespace LongTails.Proofs.NoisyTwoSamplePerceptronComplement

abbrev E := EuclideanSpace ℝ (Fin 4)

noncomputable def vec (a b c d : ℝ) : E := WithLp.toLp 2 ![a,b,c,d]

lemma norm_sq (x : E) : ‖x‖^2 = (x 0)^2+(x 1)^2+(x 2)^2+(x 3)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_four]

lemma inner_eq (x y : E) : ⟪x,y⟫ = x 0*y 0+x 1*y 1+x 2*y 2+x 3*y 3 := by
  simp [PiLp.inner_apply,Fin.sum_univ_four]
  ring

noncomputable def action (a b c : ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => vec (a*x 1+b*x 2) (a*x 0) (b*x 0) (c*x 3)
      map_add' := fun x y => by ext i; fin_cases i <;> simp [vec] <;> ring
      map_smul' := fun t x => by ext i; fin_cases i <;> simp [vec] <;> ring }

lemma action_symmetric (a b c : ℝ) (x y : E) : ⟪action a b c x,y⟫ = ⟪x,action a b c y⟫ := by
  rw [inner_eq,inner_eq]
  simp [action,vec]
  ring

lemma action_norm {a b c : ℝ} (hab : a^2+b^2 ≤ 1/4) (hc : c^2 ≤ 1/4) :
    ‖action a b c‖ ≤ 1/2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have H : ‖action a b c x‖^2 ≤ (1/2*‖x‖)^2 := by
    rw [mul_pow,norm_sq,norm_sq]
    change (a*x 1+b*x 2)^2+(a*x 0)^2+(b*x 0)^2+(c*x 3)^2 ≤ _
    nlinarith only [sq_nonneg (b*x 1-a*x 2),
      mul_le_mul_of_nonneg_right hab (add_nonneg (add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1))) (sq_nonneg (x 2))),
      mul_le_mul_of_nonneg_right hc (sq_nonneg (x 3))]
  nlinarith [norm_nonneg x,norm_nonneg (action a b c x)]

noncomputable def c : ℝ := Real.sqrt 2/4

noncomputable def matrix (δ a B : ℝ) (second : Bool) : E →L[ℝ] E :=
  if second then action (-(c+δ*a)) (δ*B) (-δ) else action c 0 0

lemma matrix_norm {δ a B : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/56)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hB : 0 ≤ B) (hB' : B ≤ 1) (b : Bool) :
    ‖matrix δ a B b‖ ≤ 1/2 := by
  have H := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc' : c ≤ 3/8 := by dsimp [c]; nlinarith
  have h₁ : 0 ≤ δ*a := mul_nonneg hδ ha
  have h₂ : 0 ≤ δ*B := mul_nonneg hδ hB
  have h₃ : δ*a ≤ 1/56 := (mul_le_of_le_one_right hδ ha').trans hδ'
  have h₄ : δ*B ≤ 1/56 := (mul_le_of_le_one_right hδ hB').trans hδ'
  cases b with
  | false => exact action_norm (by dsimp [c]; nlinarith) (by norm_num)
  | true =>
    apply action_norm
    · nlinarith [mul_nonneg (show 0 ≤ 2/5-(c+δ*a) by linarith) (show 0 ≤ 2/5+(c+δ*a) by linarith),
        mul_nonneg (show 0 ≤ 1/56-δ*B by linarith) (show 0 ≤ 1/56+δ*B by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ 1/56-δ by linarith) (show 0 ≤ 1/56+δ by linarith)]

abbrev F := EuclideanSpace ℝ (Fin 2)

noncomputable def pair (x y : ℝ) : F := WithLp.toLp 2 ![x,y]

lemma pair_sq (x y : ℝ) : ‖pair x y‖^2=x^2+y^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  rfl

lemma less_norm (x y : ℝ) : |x| ≤ ‖pair x y‖ ∧ |y| ≤ ‖pair x y‖ := by
  have H := pair_sq x y
  constructor <;> nlinarith [sq_abs x,sq_abs y,sq_nonneg x,sq_nonneg y,norm_nonneg (pair x y)]

lemma mixed_bound {δ a B v w : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/56)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hB : 0 ≤ B) (hB' : B ≤ 1)
    (hv : |v| ≤ c) (hw : |w| ≤ c) (x : E) :
    let A := 1-c*(c+δ*a)
    ‖vec (A*x 0-δ*a*x 1+δ*B*x 2)
      (A*x 1-δ*a*x 0+δ*B*x 2*v) (x 2+δ*B*(x 0+w*x 1)) ((1-δ)*x 3)‖ ≤
      (1+δ/2)*‖x‖ := by
  intro A
  let X := pair (x 0) (x 1)
  let Y := pair (x 1) (x 0)
  let W := pair 1 v
  let U := x 2
  let Z := pair (A*x 0-δ*a*x 1+δ*B*x 2) (A*x 1-δ*a*x 0+δ*B*x 2*v)
  have hZ : Z = A • X + (-(δ*a)) • Y + (δ*B*U) • W := by
    ext i
    fin_cases i <;> simp [X,Y,W,Z,U,pair] <;> ring
  have hY : ‖Y‖ = ‖X‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [pair_sq,pair_sq]; ring
  have hc₂ : c^2=1/8 := by
    dsimp [c]
    rw [div_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc' : c ≤ 2/5 := by nlinarith
  have hW : ‖W‖ ≤ 7/5 := by
    have H := pair_sq 1 v
    change ‖W‖^2 = _ at H
    nlinarith [pow_le_pow_left₀ (abs_nonneg _) hv 2,sq_abs v,norm_nonneg W]
  have h₁ := mul_le_of_le_one_right hδ ha'
  have h₂ := mul_le_of_le_one_right hδ hB'
  have hA : 0 ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left (show δ*a ≤ 1/56 by linarith) hc]
  have hA' : A+δ*a ≤ 7/8+7/5*δ := by
    dsimp [A]
    nlinarith [mul_nonneg hc (mul_nonneg hδ ha)]
  have hZX : ‖Z‖ ≤ (7/8+7/5*δ)*‖X‖+7/5*δ*|U| := by
    rw [hZ]
    calc
      _ ≤ (‖A • X‖+‖(-(δ*a)) • Y‖)+‖(δ*B*U) • W‖ := (norm_add_le ..).trans
        (add_le_add (norm_add_le ..) le_rfl)
      _ ≤ _ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg hA,
          abs_of_nonneg hδ,abs_of_nonneg ha,abs_of_nonneg hB,hY]
        nlinarith only [mul_le_mul_of_nonneg_right hA' (norm_nonneg X),
          mul_le_mul_of_nonneg_left hW (mul_nonneg (mul_nonneg hδ hB) (abs_nonneg U)),
          mul_le_mul_of_nonneg_right h₂ (abs_nonneg U)]
  have hx := less_norm (x 0) (x 1)
  have hterm : |x 0+w*x 1| ≤ (7/5)*‖X‖ := by
    have h := abs_add_le (x 0) (w*x 1)
    rw [abs_mul] at h
    nlinarith only [h,hx.1,mul_le_mul hw hx.2 (abs_nonneg _) hc,
      mul_le_mul_of_nonneg_right hc' (norm_nonneg X)]
  have huu : |U+δ*B*(x 0+w*x 1)| ≤ (7/5*δ)*‖X‖+|U| := by
    have h := abs_add_le U (δ*B*(x 0+w*x 1))
    rw [abs_mul,abs_of_nonneg (mul_nonneg hδ hB)] at h
    nlinarith only [h,mul_le_mul_of_nonneg_left hterm (mul_nonneg hδ hB),
      mul_le_mul_of_nonneg_right h₂ (norm_nonneg X)]
  have hmix := mixed_pair_norm (u := ‖X‖) (z := |U|) hδ hδ'
    (show 0 ≤ 7/8+7/5*δ by linarith) (show 0 ≤ 7/5*δ by linarith) le_rfl le_rfl
  have hsq := pow_le_pow_left₀ (norm_nonneg Z) hZX 2
  have usq := pow_le_pow_left₀ (abs_nonneg _) huu 2
  rw [sq_abs] at usq
  rw [sq_abs] at hmix
  rw [pair_sq] at hsq hmix
  change _ ≤ _ at hsq
  have hlast : ((1-δ)*x 3)^2 ≤ (1+δ/2)^2*(x 3)^2 := by
    rw [mul_pow]
    gcongr
    · linarith
    · linarith
  apply le_of_pow_le_pow_left₀ (by decide : (2:ℕ) ≠ 0) (by positivity : 0 ≤ (1+δ/2)*‖x‖)
  rw [mul_pow,norm_sq,norm_sq]
  change (A*x 0-δ*a*x 1+δ*B*x 2)^2 + (A*x 1-δ*a*x 0+δ*B*x 2*v)^2 +
    (x 2+δ*B*(x 0+w*x 1))^2+((1-δ)*x 3)^2 ≤ _
  dsimp [U] at usq hmix hsq
  nlinarith only [hsq,usq,hmix,hlast]

lemma mixed_moves {δ a B : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/56)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hB : 0 ≤ B) (hB' : B ≤ 1) (b : Bool) (x : E) :
    let y := x + matrix δ a B b x
    ‖y + matrix δ a B (!b) y‖ ≤ (1+δ/2)*‖x‖ := by
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have h₀ : |(0:ℝ)| ≤ c := by simpa
  have hc' : |c| ≤ c := (abs_of_nonneg hc).le
  cases b with
  | false =>
    apply le_trans _ (mixed_bound hδ hδ' ha ha' hB hB' h₀ hc' x)
    apply le_of_eq
    congr 1
    ext i
    fin_cases i <;> simp [matrix,action,vec] <;> ring
  | true =>
    apply le_trans _ (mixed_bound hδ hδ' ha ha' hB hB' hc' h₀ x)
    apply le_of_eq
    congr 1
    ext i
    fin_cases i <;> simp [matrix,action,vec] <;> ring

lemma mixed_noisy {δ a B : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/56)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hB : 0 ≤ B) (hB' : B ≤ 1) (b : Bool) (x y e f : E)
    (hy : y = x + matrix δ a B b x + e) :
    ‖y + matrix δ a B (!b) y + f‖ ≤ (1+δ/2)*‖x‖+2*‖e‖+‖f‖ := by
  let F := matrix δ a B (!b)
  let z := x + matrix δ a B b x
  have hh : y+F y = (z+F z)+(e+F e) := by rw [hy,map_add]; dsimp [z]; abel
  have hf : ‖F e‖ ≤ (1/2)*‖e‖ := (F.le_opNorm e).trans
    (mul_le_mul_of_nonneg_right (matrix_norm hδ hδ' ha ha' hB hB' (!b)) (norm_nonneg _))
  have hmix : ‖z+F z‖ ≤ _ := mixed_moves hδ hδ' ha ha' hB hB' b x
  change ‖y+F y+f‖ ≤ _
  rw [hh]
  linarith only [norm_add_le ((z+F z)+(e+F e)) f,norm_add_le (z+F z) (e+F e),
    norm_add_le e (F e),hmix,hf,norm_nonneg e]

end LongTails.Proofs.NoisyTwoSamplePerceptronComplement
