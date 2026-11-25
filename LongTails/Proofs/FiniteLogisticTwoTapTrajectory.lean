import LongTails.Proofs.FiniteLogisticTwoTapPhase
import LongTails.Proofs.FiniteLogisticPerceptronWarmup

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.FiniteLogisticTwoTapExecution
open LongTails.Proofs.FiniteLogisticTwoTapPhase
open LongTails.Proofs.FiniteLogisticTwoTapEntry
open LongTails.Proofs.TwoTapGaussianBounds
open LongTails.Proofs.FiniteLogisticTwoTapSpectrum
open LongTails.Proofs.FiniteLogisticPerceptronWarmup

namespace LongTails.Proofs.FiniteLogisticTwoTapTrajectory

noncomputable def stepsize (d : ℕ) := (1/Real.sqrt d)/2^40

noncomputable def scales (p : Params) (hp : spec.valid p) : Scales := by
  obtain ⟨hd,hμ,hμ',_⟩ := hp
  have hD : (3:ℝ) ≤ p.d := by exact_mod_cast hd
  have hd₀ : (0:ℝ) < p.d := by linarith
  have hsd := Real.sq_sqrt hd₀.le
  have hs := Real.sqrt_pos.mpr hd₀
  have he : 0 < 1-2/(p.d:ℝ) := sub_pos.mpr ((div_lt_one hd₀).mpr (by linarith))
  refine ⟨1/Real.sqrt p.d,Real.sqrt (1-2/(p.d:ℝ)),Real.sqrt 2*Real.sqrt p.d,p.μ,stepsize p.d,
    by positivity,?_,Real.sqrt_pos.mpr he,?_,?_,hμ,hμ',by dsimp [stepsize]; positivity,le_rfl⟩
  · rw [div_pow,one_pow,hsd]
    field_simp
    linarith
  · rw [Real.sq_sqrt he.le,div_pow,one_pow,hsd]
    ring
  · field_simp

lemma coordinate_step (p : Params) (hp : spec.valid p) (i : Fin p.d)
    (hi : finRotate p.d i ≠ i) (w : Weights p.d) :
    coords i (step p.μ (stepsize p.d) i w) = advance (scales p hp) (coords i w) := by
  have hd : 2 < p.d := hp.1
  obtain ⟨h₁,h₂⟩ := score_coordinates hd i p.μ w
  rw [step_coordinates hd i hi,h₁,h₂]
  dsimp only [advance,scales,defect]
  have hD : (0:ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
  have hs := Real.sqrt_pos.mpr hD
  have H : (1+p.μ*(1/Real.sqrt p.d)^2)*(Real.sqrt 2*Real.sqrt p.d) =
      Real.sqrt 2*Real.sqrt p.d+p.μ*(Real.sqrt 2/Real.sqrt p.d) := by field_simp
  rw [H]
  let z := coords i w
  let L := Real.sqrt 2*Real.sqrt p.d
  let J := p.μ*(Real.sqrt 2/Real.sqrt p.d)
  let B := Real.sqrt (1-2/(p.d:ℝ))
  have hy : -(-(L+J)*z.p*z.q+p.μ*B*z.p*z.u+p.μ*z.r*z.v) =
      (L+J)*z.p*z.q-(p.μ*B*z.p*z.u+p.μ*z.r*z.v) := by ring
  rw [hy]
  generalize Real.sigmoid (-(L*z.p*z.q)) = a
  generalize Real.sigmoid ((L+J)*z.p*z.q-(p.μ*B*z.p*z.u+p.μ*z.r*z.v)) = b
  have hcoef : Real.sqrt 2 * Real.sqrt p.d * (p.μ*(1/Real.sqrt p.d)^2) = J := by
    dsimp [J]; field_simp
  have hweight : stepsize p.d/2*(L*(a-b)-J*b) =
      stepsize p.d/2*L*(a-(1+p.μ*(1/Real.sqrt p.d)^2)*b) := by
    change L*(p.μ*(1/Real.sqrt p.d)^2) = J at hcoef
    linear_combination (stepsize p.d/2)*b*hcoef
  rw [hweight]

lemma coordinate_separates (p : Params) (hp : spec.valid p) (i : Fin p.d) (w : Weights p.d) :
    let s := scales p hp
    let z := coords i w
    0 < s.L*z.p*z.q ∧ 0 < defect s z - ((1+s.μ*s.k^2)*s.L)*z.p*z.q →
    Separates p.μ i w := by
  intro s z h
  obtain ⟨H,K⟩ := score_coordinates hp.1 i p.μ w
  unfold Separates
  rw [H,K]
  refine ⟨h.1,?_⟩
  obtain ⟨_,h₂⟩ := h
  dsimp only [s,scales,z,defect] at h₂
  have hD : (0:ℝ) < p.d := by exact_mod_cast (by have := hp.1; omega : 0 < p.d)
  have hs := Real.sqrt_pos.mpr hD
  have H' : (1+p.μ*(1/Real.sqrt p.d)^2)*(Real.sqrt 2*Real.sqrt p.d) =
      Real.sqrt 2*Real.sqrt p.d+p.μ*(Real.sqrt 2/Real.sqrt p.d) := by field_simp
  rw [H'] at h₂
  linarith

lemma scaled_mode {r ρ S M m : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hS : 1 ≤ S)
    (hM : 16384*S^2/ρ ≤ M) (hm : ρ/(32*S)*r < m) :
    let P := M*(m/Real.sqrt 2)
    let e := r*M*ρ/(1024*S^2)
    0 < P ∧ e ≤ (1/S)*P/20 ∧ 4*r ≤ P ∧ e < P := by
  have hS₀ : 0 < S := by linarith
  have hM₀ : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hm' : ρ*r < 32*S*m := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at hm
    linarith
  have hm₀ : 0 < m := lt_trans (by positivity) hm
  have hf := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hf₀ := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  have hf' : Real.sqrt 2 ≤ 3/2 := by nlinarith
  intro P e
  have hP : 0 < P := by dsimp [P]; positivity
  have he : e ≤ (1/S)*P/20 := by
    dsimp [e,P]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hf' (mul_nonneg hr.le hρ.le),
      hm',mul_nonneg hm₀.le hS₀.le]
  refine ⟨hP,he,?_,?_⟩
  · dsimp [P]
    rw [← mul_div_assoc, le_div_iff₀ hf₀]
    have H₁ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hρ).mp hM) hr.le
    have H₂ := mul_lt_mul_of_pos_right hm' hM₀
    have H₃ : 512*S*r ≤ M*m := by
      apply le_of_not_gt
      intro h
      nlinarith only [H₁,H₂,mul_lt_mul_of_pos_left h hS₀]
    nlinarith only [H₃,mul_le_mul_of_nonneg_right hS hr.le,mul_le_mul_of_nonneg_right hf' hr.le,hr]
  · have hrec : 1/S ≤ 1 := (div_le_one hS₀).mpr hS
    nlinarith only [he,mul_le_mul_of_nonneg_right hrec hP.le,hP]

set_option maxHeartbeats 1500000 in
lemma warm_entry (p : Params) (hp : spec.valid p) (i : Fin p.d) (hi : finRotate p.d i ≠ i)
    (w : Weights p.d) (hw : ‖w‖ ≤ p.r)
    (hplus : p.ρ/(32*Real.sqrt p.d)*p.r < ⟪mode i 1,w⟫)
    (hminus : p.ρ/(32*Real.sqrt p.d)*p.r < |⟪mode i (-1),w⟫|) :
    let s := scales p hp
    let q := 1+s.η*s.μ/4
    let n := ⌈Real.log (16384*(p.d:ℝ)/p.ρ)/Real.log q⌉₊
    let z := coords i ((step p.μ s.η i)^[n] w)
    Cone s z ∧ z.q ≤ 0 ∧ p.r ≤ z.p+z.q+z.u ∧ z.p+z.q+z.u ≤ 4096*s.k := by
  intro s q n z
  have hpvalid := hp
  obtain ⟨hd,hμ,hμ',hρ,hρ',hr,hcap⟩ := hpvalid
  let S := Real.sqrt p.d
  have hD : (3:ℝ) ≤ p.d := by exact_mod_cast hd
  have hd₀ : (0:ℝ) < p.d := by linarith
  have hS : 1 ≤ S := by dsimp [S]; simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ p.d by linarith)
  have hs₀ : 0 < S := by linarith
  have hs : S^2 = p.d := Real.sq_sqrt hd₀.le
  have hk : s.k = 1/S := rfl
  have hm : s.μ = p.μ := rfl
  have hηm : s.η*s.μ/4 ≤ 1 := by
    obtain ⟨hL,H,HH,_,_,_⟩ := scale_bounds s
    nlinarith [mul_le_mul_of_nonneg_left H s.hη.le]
  have hq : 1 < q := by dsimp [q]; linarith [mul_pos s.hη s.hμ]
  have hq' : q ≤ 2 := by dsimp [q]; linarith
  have hM := warmup_horizon hq hq' (show 1 ≤ 16384*(p.d:ℝ)/p.ρ by
    apply (le_div_iff₀ hρ).mpr; linarith)
  let M := q^n
  change 16384*(p.d:ℝ)/p.ρ ≤ M ∧ M ≤ 2*(16384*(p.d:ℝ)/p.ρ) at hM
  have hM₀ : 0 < M := pow_pos (by linarith) _
  have hMM : 16384*S^2/p.ρ ≤ M := hs ▸ hM.1
  let x := (step p.μ s.η i)^[n] w
  let e := p.r*M*p.ρ/(1024*(p.d:ℝ))
  let P := M*(⟪mode i 1,w⟫/Real.sqrt 2)
  have Herr : ‖x-M • growingPart i w‖ ≤ e := warmup_at_scale p hp i hi s.hη (by exact hηm) w hw
  obtain ⟨hP,he,hbig,_⟩ := scaled_mode hr hρ hS hMM hplus
  obtain ⟨_,_,_,hslow⟩ := scaled_mode hr hρ hS hMM hminus
  rw [hs] at he hslow
  have hslow' : e < |M*(⟪mode i (-1),w⟫/Real.sqrt 2)| := by
    rw [abs_mul,abs_div,abs_of_pos hM₀,abs_of_pos (by positivity : 0 < Real.sqrt 2)]
    exact hslow
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩ := aligned_entry hd i hi w x M e Herr hP he hslow'
  refine ⟨⟨h₁,h₃,h₄,h₅,h₆⟩,h₂,?_,?_⟩
  · have hrec : 1/S ≤ 1 := (div_le_one hs₀).mpr hS
    change e ≤ 1/S*P/20 at he
    change 4*p.r ≤ P at hbig
    change P-e ≤ z.p at h₇
    change 0 < z.p+z.q at h₁
    change z.p/2 ≤ z.u at h₄
    nlinarith only [he,hbig,h₇,h₁,h₄,mul_le_mul_of_nonneg_right hrec hP.le,hr]
  · have hb := (coordinate_bounds hd i hi (x-M • growingPart i w)).1.trans Herr
    rw [coord_sub,coord_smul,growing_coords hd i hi] at hb
    change |z.p-P| ≤ e at hb
    have H := abs_real_inner_le_norm (mode i 1) w
    rw [mode_unit i hi (by norm_num : (1:ℝ)^2=1),one_mul] at H
    have hF : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2,Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
    have hp' : P ≤ M*p.r := by
      apply mul_le_mul_of_nonneg_left _ hM₀.le
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [le_abs_self ⟪mode i 1,w⟫,mul_le_mul_of_nonneg_left hF hr.le]
    have hrec : 1/S ≤ 1 := (div_le_one hs₀).mpr hS
    change e ≤ 1/S*P/20 at he
    have hzp : z.p ≤ 2*(M*p.r) := by nlinarith [(abs_le.mp hb).2,mul_le_mul_of_nonneg_right hrec hP.le]
    have hnoise : Real.sqrt (p.μ*p.ρ) ≤ 1 := by
      nlinarith [Real.sq_sqrt (mul_nonneg hμ.le hρ.le),mul_le_mul_of_nonneg_left hρ'.le hμ.le]
    have hR : p.r*(2^24*(p.d:ℝ)^2) ≤ p.ρ := by
      exact ((le_div_iff₀ (by positivity)).mp hcap).trans (by nlinarith [mul_le_mul_of_nonneg_right hnoise hρ.le])
    have hMR : (M*p.r)*S^2 ≤ 1 := by
      rw [hs]
      have H₁ : M*p.ρ ≤ 32768*(p.d:ℝ) := by
        calc
          _ ≤ 2*(16384*(p.d:ℝ)/p.ρ)*p.ρ := mul_le_mul_of_nonneg_right hM.2 hρ.le
          _ = _ := by field_simp; ring
      have H₂ := mul_le_mul_of_nonneg_left hR hM₀.le
      by_contra! hh
      nlinarith only [mul_lt_mul_of_pos_right hh hd₀,H₁,H₂,hd₀]
    change z.q ≤ 0 at h₂
    change z.u ≤ 50*(z.p+z.q) at h₅
    rw [hk, mul_one_div, le_div_iff₀ hs₀]
    have hMR' : M*p.r*S ≤ 1 := le_trans (by
      nlinarith only [mul_nonneg (mul_nonneg hM₀.le hr.le) (mul_nonneg hs₀.le (sub_nonneg.mpr hS))]) hMR
    nlinarith [mul_le_mul_of_nonneg_right hzp hs₀.le,mul_le_mul_of_nonneg_right h₅ hs₀.le,
      mul_nonpos_of_nonpos_of_nonneg h₂ hs₀.le]

end LongTails.Proofs.FiniteLogisticTwoTapTrajectory
