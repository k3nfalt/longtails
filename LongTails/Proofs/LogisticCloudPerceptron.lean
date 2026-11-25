import LongTails.Proofs.LogisticCloudModel

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudModel

namespace LongTails.Proofs.LogisticCloudPerceptron

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def meanNegative : Features p.d := G.e-p.μ • (axis G+G.v)

lemma raw_features :
    D.reference = (p.L/Real.sqrt 2) • G.e ∧
    ∀ i, D.negative i = (p.L/Real.sqrt 2) • (meanNegative G + (G.z i+G.y i)) := by
  have recover (b : Features p.d) : b = (Real.sqrt 2)⁻¹ • (sumFeature b + diffFeature b) := by
    rw [sumFeature,diffFeature,← smul_add,smul_smul,← mul_inv,← sq,Real.sq_sqrt (by norm_num)]
    rw [show b+_+(b-_) = (2:ℝ) • b by rw [two_smul]; abel,smul_smul]
    norm_num
  constructor
  · rw [recover D.reference,G.reference_sum,G.reference_diff,add_zero,smul_smul]
    congr 1; ring
  · intro i
    obtain ⟨hz,hy⟩ := actual_columns G i
    rw [recover (D.negative i),hz,hy,← smul_add,smul_smul]
    congr 1
    · ring
    · dsimp [zcol,ycol,meanNegative]
      rw [smul_add]; abel

noncomputable def batch (D : Data p) (η : ℝ) (w : Features p.d) :=
  w + (η/(2*p.n : ℝ)) •
    ((p.n:ℕ) • (if ⟪w,D.reference⟫ ≤ 0 then D.reference else 0) -
      ∑ i, if 0 ≤ ⟪w,D.negative i⟫ then D.negative i else 0)

include G in
lemma batch_delay (hp : spec.valid p) {η : ℝ} (hη : 0 < η) (k : ℕ)
    (hs : let w := (batch D η)^[k] 0
          0 < ⟪w,D.reference⟫ ∧ ∀ i, ⟪w,D.negative i⟫ < 0) :
    1+p.μ*p.a < (k:ℝ)*(p.μ*p.a+2*p.μ^2) := by
  let m := meanNegative G
  let c := p.L/Real.sqrt 2
  let γ := η*c/2
  let τ := p.μ*p.a
  let q := p.μ*p.a+2*p.μ^2
  have ha := hp.2.2.2.2.1
  have ha' := hp.2.2.2.2.2.1
  have hμ := hp.2.2.1
  have hc : 0 < c := div_pos hp.2.1 (Real.sqrt_pos.mpr (by norm_num))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hτ : 0 < τ := mul_pos hμ ha
  have hq : 0 < q := by dsimp [q]; positivity
  have huu := axis_unit G ha.le (by linarith)
  have huv := axis_ortho G
  have ue : ⟪G.u,G.e⟫ = 0 := (real_inner_comm _ _).trans G.eu
  have ve : ⟪G.v,G.e⟫ = 0 := (real_inner_comm _ _).trans G.ev
  have vu : ⟪G.v,axis G⟫ = 0 := (real_inner_comm _ _).trans huv
  have hue : ⟪axis G,G.e⟫ = -p.a := by
    rw [axis,inner_add_left,real_inner_smul_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      G.norm_e,ue]; ring
  have hm₁ : ⟪m,G.e⟫ = 1+τ := by
    simp [m,meanNegative,inner_sub_left,real_inner_smul_left,inner_add_left,hue,
      ve,G.norm_e,τ]
  have hm₂ : ⟪m,m⟫ = 1+τ+q := by
    have heax : ⟪G.e,axis G⟫ = -p.a := (real_inner_comm _ _).trans hue
    dsimp only [m,meanNegative]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      inner_add_left,inner_add_right]
    rw [heax,hue,G.ev,ve,huv,vu]
    simp only [real_inner_self_eq_norm_sq,huu,G.norm_v,G.norm_e,τ,q]
    ring
  let V := fun A B : ℕ => γ • ((A:ℝ) • G.e - (B:ℝ) • m)
  have proj (A B : ℕ) : ⟪V A B,D.reference⟫ = γ*c*((A:ℝ)-B*(1+τ)) ∧
      ∀ i, ⟪V A B,D.negative i⟫ = γ*c*((A:ℝ)*(1+τ)-B*(1+τ+q)) := by
    obtain ⟨he,hn⟩ := raw_features G
    constructor
    · rw [he]; dsimp only [V]; simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,
        real_inner_self_eq_norm_sq,G.norm_e,hm₁,c]; ring
    · intro i
      have ⟨ez,ey⟩ := G.orthogonal i G.e (by simp)
      have ⟨uz,uy⟩ := G.orthogonal i G.u (by simp)
      have ⟨vz,vy⟩ := G.orthogonal i G.v (by simp)
      have hz : ⟪m,G.z i⟫ = 0 := by
        simp [m,meanNegative,axis,inner_sub_left,inner_add_left,real_inner_smul_left,ez,uz,vz]
      have hy : ⟪m,G.y i⟫ = 0 := by
        simp [m,meanNegative,axis,inner_sub_left,inner_add_left,real_inner_smul_left,ey,uy,vy]
      rw [hn i]
      change ⟪V A B,c • (m + (G.z i+G.y i))⟫ = _
      dsimp only [V]
      simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_add_right,ez,ey,hz,hy,
        hm₂,(show ⟪G.e,m⟫ = 1+τ from (real_inner_comm _ _).trans hm₁)]
      ring
  have count (j : ℕ) : ∃ A B : ℕ, B ≤ j ∧ (batch D η)^[j] 0 = V A B := by
    induction j with
    | zero => exact ⟨0,0,le_rfl,by simp [V]⟩
    | succ j ih =>
      obtain ⟨A,B,hB,hV⟩ := ih
      rw [Function.iterate_succ_apply',hV,batch]
      obtain ⟨hpos,hneg⟩ := proj A B
      obtain ⟨he,hn⟩ := raw_features G
      simp only [hpos,hneg]
      have hsum : ∑ i, D.negative i = (p.n:ℕ) • (c • m) := by
        simp_rw [hn,smul_add,Finset.sum_add_distrib,← Finset.smul_sum]
        simp [m,c,G.centered_z,G.centered_y,smul_comm (p.L / Real.sqrt 2) (p.n:ℕ)]
      have hN : (p.n:ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
      by_cases P : γ*c*((A:ℝ)-B*(1+τ)) ≤ 0 <;>
        by_cases N : 0 ≤ γ*c*((A:ℝ)*(1+τ)-B*(1+τ+q))
      · refine ⟨A+1,B+1,by omega,?_⟩
        simp only [P,N,ite_true,hsum,he,V,Nat.cast_add,Nat.cast_one]
        rw [← Nat.cast_smul_eq_nsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ]
        dsimp [c,γ]
        match_scalars <;> field_simp; ring
      · refine ⟨A+1,B,by omega,?_⟩
        simp only [P,N,ite_true,ite_false,Finset.sum_const_zero,sub_zero,he,V,Nat.cast_add,Nat.cast_one]
        rw [← Nat.cast_smul_eq_nsmul ℝ]
        dsimp [c,γ]
        match_scalars <;> field_simp
      · refine ⟨A,B+1,by omega,?_⟩
        simp only [P,N,ite_false,ite_true,smul_zero,zero_sub,hsum,V,Nat.cast_add,Nat.cast_one]
        rw [← Nat.cast_smul_eq_nsmul ℝ]
        dsimp [c,γ]
        match_scalars <;> field_simp; ring
      · exact ⟨A,B,by omega,by simp [P,N]⟩
  obtain ⟨A,B,hBk,hV⟩ := count k
  dsimp only at hs
  rw [hV] at hs
  obtain ⟨hpos,hneg⟩ := proj A B
  have H := hs.2 0
  rw [hneg] at H
  have H' := hs.1
  rw [hpos] at H'
  have hdiff := pos_of_mul_pos_right H' (mul_pos hγ hc).le
  have hneg' := neg_of_mul_neg_right H (mul_pos hγ hc).le
  have hab : (B:ℝ) < A := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) B) hτ.le]
  have hab' : B+1 ≤ A := by exact_mod_cast (show B < A by exact_mod_cast hab)
  have hab'' : (B:ℝ)+1 ≤ A := by exact_mod_cast hab'
  have hk : (B:ℝ) ≤ k := by exact_mod_cast hBk
  change 1+τ < k*q
  nlinarith [mul_le_mul_of_nonneg_right hab'' (show 0 ≤ 1+τ by linarith),
    mul_le_mul_of_nonneg_right hk hq.le]

end LongTails.Proofs.LogisticCloudPerceptron
