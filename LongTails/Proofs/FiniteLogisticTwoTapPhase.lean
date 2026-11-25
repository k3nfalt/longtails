import LongTails.Proofs.FiniteLogisticTwoTapEntry

open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.FiniteLogisticPerceptronCrossing

namespace LongTails.Proofs.FiniteLogisticTwoTapPhase

structure Scales where
  k : ℝ
  B : ℝ
  L : ℝ
  μ : ℝ
  η : ℝ
  hk : 0 < k
  hk₂ : 3*k^2 ≤ 1
  hB : 0 < B
  hB₂ : B^2 = 1-2*k^2
  hL : L*k = Real.sqrt 2
  hμ : 0 < μ
  hμ' : μ ≤ 1/10
  hη : 0 < η
  hη' : η ≤ k / 2^40

noncomputable def angle (s : Scales) := min (19/20 : ℝ) (4*s.k)

def Cone (s : Scales) (z : Coords) : Prop :=
  0 < z.p+z.q ∧ -(angle s)*z.p ≤ z.q ∧ z.p/2 ≤ z.u ∧ z.u ≤ 50*(z.p+z.q) ∧ 0 < z.r*z.v

noncomputable def defect (s : Scales) (z : Coords) := s.μ*s.B*z.p*z.u+s.μ*z.r*z.v

noncomputable def advance (s : Scales) (z : Coords) : Coords :=
  let t := s.μ*s.k^2
  let a := Real.sigmoid (-(s.L*z.p*z.q))
  let b := Real.sigmoid ((1+t)*s.L*z.p*z.q-defect s z)
  let h := s.η/2*s.L*(a-(1+t)*b)
  let j := s.η/2*s.μ*s.B*b
  let l := s.η/2*s.μ*b
  ⟨z.p+h*z.q+j*z.u,z.q+h*z.p,z.u+j*z.p,z.r+l*z.v,z.v+l*z.r⟩

lemma scale_bounds (s : Scales) :
    0 < s.L ∧ 10*s.μ ≤ s.L ∧ s.η*s.L ≤ 1/2 ∧
    1/2 ≤ s.B ∧ s.B ≤ 1 ∧ s.μ*s.k^2 ≤ 1/30 := by
  obtain ⟨k,B,L,μ,η,hk,hk₂,hB,hB₂,hL,hμ,hμ',hη,hη'⟩ := s
  dsimp only
  have hf := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  have hf' := Real.sqrt_nonneg (2:ℝ)
  have hL' : 0 < L := pos_of_mul_pos_left (hL ▸ (by positivity : 0 < Real.sqrt 2)) hk.le
  have hk' : k ≤ 1 := by nlinarith
  have hL'' : 1 ≤ L := by nlinarith [mul_le_mul_of_nonneg_left hk' hL'.le]
  refine ⟨hL',by linarith,?_,by nlinarith,by nlinarith [sq_nonneg k],?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hη' hL'.le]
  · nlinarith [mul_le_mul_of_nonneg_right hk₂ hμ.le]

lemma cone_geometry (s : Scales) (z : Coords) (hz : Cone s z) (hq : z.q ≤ 0) :
    0 < z.p ∧ 0 ≤ z.u ∧ z.p+z.q+z.u ≤ 51*z.p ∧ z.p+z.u ≤ 3*(z.p+z.q+z.u) ∧
      -(4*s.k)*z.p ≤ z.q ∧ 0 < defect s z := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hz
  have hp : 0 < z.p := by linarith
  have hu : 0 < z.u := by linarith
  have ha : angle s ≤ 4*s.k := min_le_right _ _
  exact ⟨hp, hu.le, by linarith, by linarith, by nlinarith [mul_le_mul_of_nonneg_right ha hp.le],
    add_pos (mul_pos (mul_pos (mul_pos s.hμ s.hB) hp) hu) (by nlinarith [mul_pos s.hμ h₅])⟩

set_option maxHeartbeats 1200000 in
lemma cone_step (s : Scales) (z : Coords) (hz : Cone s z) (hq : z.q ≤ 0) :
    let Z := advance s z
    Cone s Z ∧ 0 < Z.p ∧ 0 ≤ Z.u ∧
      (1+s.η*s.μ/336)*(z.p+z.q+z.u) ≤ Z.p+Z.q+Z.u ∧
      Z.p+Z.u ≤ 2*(z.p+z.u) ∧ defect s z / 2 ≤ defect s Z ∧
      (4096*s.k ≤ z.p+z.q+z.u →
        z.q+8*s.η*s.μ*s.k*z.p ≤ Z.q ∧
        7*s.k*(Z.p+Z.u)-(Z.q) ≤ 7*s.k*(z.p+z.u)-z.q) := by
  obtain ⟨hp,hu,hG,hW,hangle,hD⟩ := cone_geometry s z hz hq
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hz
  obtain ⟨hL,hμ',hη',hB,hB',ht'⟩ := scale_bounds s
  let t := s.μ*s.k^2
  let x := -(s.L*z.p*z.q)
  let y := (1+t)*s.L*z.p*z.q-defect s z
  let a := Real.sigmoid x
  let b := Real.sigmoid y
  let h := s.η/2*s.L*(a-(1+t)*b)
  let j := s.η/2*s.μ*s.B*b
  let l := s.η/2*s.μ*b
  let P := z.p+h*z.q+j*z.u
  let Q := z.q+h*z.p
  let U := z.u+j*z.p
  let R := z.r+l*z.v
  let V := z.v+l*z.r
  let D := defect s z
  have ht : 0 ≤ t := mul_nonneg s.hμ.le (sq_nonneg _)
  have hx : 0 ≤ x := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hL.le hp.le) hq)
  have hy : y ≤ -D := by
    have H := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg
      (mul_nonneg (show 0 ≤ 1+t by linarith) hL.le) hp.le) hq
    dsimp [y,D]
    linarith only [H]
  obtain ⟨hh,hh',hj,hj',hc,hor⟩ := coefficients s.hη hL hη' ht ht' s.hμ hμ' hB hB' hx
    (hy.trans (neg_nonpos.mpr hD.le))
  have hc' : s.L*t/(s.μ*s.B) = Real.sqrt 2*s.k/s.B := by
    dsimp [t]
    rw [← s.hL]
    field_simp [s.hB.ne',s.hμ.ne']
  rw [hc'] at hc
  change -(1/2:ℝ) ≤ h at hh
  change h ≤ 1/2 at hh'
  change 0 ≤ j at hj
  change j ≤ 1/2 at hj'
  change -(Real.sqrt 2*s.k/s.B)*j ≤ h at hc
  change s.η*s.μ/16 ≤ j ∨ s.η*s.μ ≤ h at hor
  obtain ⟨ha,ha',hC,hC'⟩ := angle_constants s.hk s.hk₂ s.hB s.hB₂
  obtain ⟨hpos,hdiff,hQ,hU,hU',hinc⟩ := preserves_cone ha ha' hC hC' hh hh' hj
    (by linarith : j ≤ 1) hc h₁ hq h₂ h₃ h₄
  change 0 < P+Q at hpos
  change 0 < P-Q at hdiff
  have hP : 0 < P := by linarith
  have hPP : z.p/2 ≤ P := by
    change _ ≤ z.p+h*z.q+j*z.u
    have hhQ := mul_le_mul_of_nonpos_right (show h ≤ 1/2 from hh') hq
    nlinarith [mul_nonneg (show 0 ≤ j from hj) hu]
  have hUU : z.u ≤ U := by dsimp [U]; linarith [mul_nonneg (show 0 ≤ j from hj) hp.le]
  have hl : 0 ≤ l := by
    exact mul_nonneg (mul_nonneg (div_nonneg s.hη.le (by norm_num)) s.hμ.le) (Real.sigmoid_nonneg y)
  have hRV : z.r*z.v ≤ R*V := by
    dsimp [R,V]
    nlinarith [mul_nonneg hl (sq_nonneg z.r),mul_nonneg hl (sq_nonneg z.v),
      mul_nonneg (sq_nonneg l) h₅.le]
  refine ⟨⟨hpos,hQ,hU,hU',h₅.trans_le hRV⟩,hP,hu.trans hUU,
    phase_growth hq h₁ h₃ h₄ hj (mul_nonneg s.hη.le s.hμ.le) hor hinc,?_,?_,?_⟩
  · change P+U ≤ _
    dsimp [P,U]
    have hb₁ := mul_le_mul_of_nonpos_right (show -(1/2:ℝ) ≤ h from hh) hq
    have hb₂ := mul_le_mul_of_nonneg_right (show j ≤ 1/2 from hj') (add_nonneg hp.le hu)
    linarith
  · change D/2 ≤ s.μ*s.B*P*U+s.μ*R*V
    dsimp [D,defect]
    have hprod := mul_le_mul hPP hUU hu (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hprod (mul_nonneg s.hμ.le s.hB.le),
      mul_le_mul_of_nonneg_left hRV s.hμ.le,mul_nonneg s.hμ.le h₅.le]
  · intro hlarge
    have hpK : 80*s.k ≤ z.p := by linarith [s.hk]
    have hsq : (80*s.k)^2 ≤ z.p^2 := by
      exact pow_le_pow_left₀ (by linarith [s.hk]) hpK 2
    have hsmall : 256*t ≤ D := by
      have hpu := mul_le_mul_of_nonneg_left h₃ hp.le
      have hbu := mul_le_mul_of_nonneg_right hB (mul_nonneg hp.le hu)
      have hscale : 256*s.k^2 ≤ s.B*z.p*z.u := by nlinarith only [hpu,hbu,hsq,sq_nonneg s.k]
      dsimp [t,D,defect]
      nlinarith [mul_le_mul_of_nonneg_left hscale s.hμ.le,mul_nonneg s.hμ.le h₅.le]
    have hhgap := sigmoid_drift ht ht' hsmall hx hy
    have hf := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
    have hf₀ := Real.sqrt_nonneg (2:ℝ)
    have hroot : 4/3 ≤ s.L*s.k := by rw [s.hL]; nlinarith
    have he : 8*s.η*s.μ*s.k ≤ h := by
      dsimp [h,a,b]
      have H := mul_le_mul_of_nonneg_left hhgap (mul_nonneg s.hη.le hL.le)
      dsimp [t] at H
      nlinarith only [H,mul_le_mul_of_nonneg_right hroot
        (mul_nonneg (mul_nonneg s.hη.le s.hμ.le) s.hk.le)]
    have hscl : 84*s.k ≤ s.L*z.p^2 := by
      have H := mul_le_mul_of_nonneg_left hsq hL.le
      nlinarith only [H,mul_le_mul_of_nonneg_right hroot s.hk.le,s.hk]
    have hhW := high_drift s.hη.le hL.le s.hμ.le s.hB.le hp.le h₃
      (by linarith : 4*t ≤ D) (show s.μ*s.B*z.p*z.u ≤ D by
        dsimp [D,defect]; linarith [mul_pos s.hμ h₅]) hx hy hscl s.hk.le
    have hh₀ : 0 ≤ h := le_trans (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) s.hη.le) s.hμ.le) s.hk.le) he
    have HW := high_drift_size hq hh₀ s.hk hhW
    change 7*s.k*((P+U)-(z.p+z.u)) ≤ Q-z.q at HW
    change z.q+_ ≤ Q ∧ 7*s.k*(P+U)-Q ≤ _
    exact ⟨by dsimp [Q]; linarith [mul_le_mul_of_nonneg_right he hp.le], by linarith only [HW]⟩

end LongTails.Proofs.FiniteLogisticTwoTapPhase
