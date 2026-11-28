import LongTails.Proofs.BrightnessDominantEnvelope
import Mathlib.Analysis.InnerProductSpace.Basic
import LongTails.Proofs.BrightnessFirstFitForces
import LongTails.Proofs.BrightnessFirstFitParameters

namespace LongTails.Proofs.BrightnessReadoutComparison

open scoped RealInnerProductSpace
open LongTails.Proofs.BrightnessImbalanceOccupation

lemma signed_work (c k z : ℝ) (hc : 0 ≤ c) (hk : 0 ≤ k) (hk' : k-1 = k*c) :
    (k-1)*z + k*c*|z|/2 ≤ 3*k*c*max z 0/2 := by
  rw [hk']
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h,max_eq_left h]
    ring_nf
    rfl
  · rw [abs_of_nonpos h,max_eq_right h]
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk hc) h]

lemma comparison_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w u d : E) (P T β e θ B k c z : ℝ)
    (hB : 0 ≤ B) (hk : 0 ≤ k) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hb : |β| ≤ c) (hw : B*β*P*T = z) (hk' : k-1 = k*c) :
    (‖w+θ • d-u‖^2 + k*B*max ((P+β*T+e)^2) ((T+β*P)^2))/2 -
      (‖w-u‖^2 + k*B*max (P^2) (T^2))/2 ≤
      (θ*⟪w,d⟫+z) - θ*⟪u,d⟫ + θ^2*‖d‖^2/2 + 3*k*c*max z 0/2 +
        k*B*(4*max |P| |T| * |e| + e^2)/2 := by
  have hdom := dominant_energy_forced P T β e (hb.trans hc')
  have ha : B*|β*P*T| = |z| := by
    rw [← hw,show B*β*P*T=B*(β*P*T) by ring,abs_mul B _,abs_of_nonneg hB]
  have hrem : k*B*(|β| * |β*P*T|) ≤ k*c*|z| := by
    rw [← ha]
    calc
      _ = k*(B*|β*P*T|)*|β| := by ring
      _ ≤ k*(B*|β*P*T|)*c := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hw' : k*B*(β*P*T) = k*z := by rw [← hw]; ring
  rw [show w+θ • d-u = (w-u)+θ • d by abel,norm_add_sq_real,real_inner_smul_right,
    inner_sub_left,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  nlinarith only [mul_le_mul_of_nonneg_left hdom (mul_nonneg hk hB),hrem,hw',
    signed_work c k z hc hk hk']

end LongTails.Proofs.BrightnessReadoutComparison

namespace LongTails.Proofs.BrightnessComparatorProgress

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma small_force (s F μ f W : ℝ) (h : s*F+|s| * μ ≤ W) (hf : |F| ≤ f)
    (hf' : f ≤ μ/2) (hμ : 0 < μ) : |s| ≤ 2*W/μ := by
  rw [le_div_iff₀ hμ]
  have H := neg_abs_le (s*F)
  rw [abs_mul] at H
  nlinarith only [h,H,mul_le_mul_of_nonneg_left (hf.trans hf') (abs_nonneg s)]

lemma good_step (w u d : E) (η M Γ U g L z : ℝ) (hη : 0 ≤ η)
    (hM : 0 ≤ M) (hg : 0 ≤ g) (hg' : g ≤ 1) (hU : 0 ≤ U)
    (hd : ‖d‖ ≤ U*g) (hm : 2*Γ*g ≤ ⟪u,d⟫) (hw : ⟪w,d⟫+z ≤ L*g)
    (hz : -z ≤ Γ*M*g/2) (hsize : L + η*U^2/2 ≤ Γ*M/2) :
    ‖w+η • d-M • u‖^2 + 2*η*Γ*M*g ≤ ‖w-M • u‖^2 := by
  rw [show w+η • d-M • u = (w-M • u)+η • d by abel,
    norm_add_sq_real,real_inner_smul_right,inner_sub_left,real_inner_smul_left,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hu : ‖d‖ ≤ U := hd.trans (by nlinarith only [mul_le_mul_of_nonneg_left hg' hU])
  have hs : ‖d‖^2 ≤ U^2*g := by
    nlinarith only [mul_le_mul hu hd (norm_nonneg d) hU]
  have HH : 2*(⟪w,d⟫-M*⟪u,d⟫)+η*‖d‖^2 ≤ -2*Γ*M*g := by
    nlinarith only [hw,hz,mul_le_mul_of_nonneg_left hm hM,
      mul_le_mul_of_nonneg_right hsize hg,mul_le_mul_of_nonneg_left hs hη]
  nlinarith only [mul_le_mul_of_nonneg_left HH hη]

lemma row_drift (u A C : E) (Q q P p J γ : ℝ) (hu : ‖u‖ ≤ 1)
    (hA : ‖A‖ ≤ J) (hC : ‖C‖ ≤ J) (hm : γ ≤ ⟪u,q • A+p • C⟫) :
    γ-(|Q-q|+|P-p|)*J ≤ ⟪u,Q • A+P • C⟫ := by
  have H (D : E) (hD : ‖D‖ ≤ J) (e : ℝ) : -( |e| *J) ≤ e*⟪u,D⟫ := by
    have hn := abs_real_inner_le_norm u D
    have H' : |⟪u,D⟫| ≤ J := hn.trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hu (norm_nonneg D),hD])
    have H'' := neg_abs_le (e*⟪u,D⟫)
    rw [abs_mul] at H''
    nlinarith only [H'',mul_le_mul_of_nonneg_left H' (abs_nonneg e)]
  simp only [inner_add_right,real_inner_smul_right] at hm ⊢
  nlinarith only [hm,H A hA (Q-q),H C hC (P-p)]

lemma post_step (w u d : E) (P T β e η R k c z U g L Γ M J δ : ℝ)
    (hη : 0 ≤ η) (hk : 0 ≤ k) (hk₂ : k ≤ 2)
    (hc : 0 ≤ c) (hc' : c ≤ 1/2) (hb : |β| ≤ c) (hz : R^2*β*P*T = z) (hk' : k-1 = k*c)
    (hU : 0 ≤ U) (hg : 0 ≤ g) (hg₁ : g ≤ 1) (hd : ‖d‖ ≤ U*g) (hM : 0 ≤ M)
    (hΓ : 0 ≤ Γ) (_hJ : 0 ≤ J) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hwork : η*⟪w,d⟫+z ≤ η*L*g) (hm : 2*Γ*g ≤ ⟪u,d⟫)
    (hforce : R^2 * |e| ≤ η*J*‖w‖*g) (he : |e| ≤ δ) (hpt : max |P| |T| ≤ δ)
    (hw : ‖w‖ ≤ 3*M) (hsize : 8*(L+η*U^2) ≤ Γ*M)
    (hsmall : 32*c*U ≤ Γ) (htiny : 128*δ*J ≤ Γ) :
    (‖w+η • d-M • u‖^2 + k*R^2*max ((P+β*T+e)^2) ((T+β*P)^2))/2 + η*Γ*M*g ≤
      (‖w-M • u‖^2+k*R^2*max (P^2) (T^2))/2 := by
  have H := BrightnessReadoutComparison.comparison_step w (M • u) d P T β e η
    (R^2) k c z (sq_nonneg R) hk hc (by linarith only [hc']) hb hz hk'
  rw [real_inner_smul_left] at H
  have dz : max z 0 ≤ η*(L+U*‖w‖)*g := by
    apply max_le
    · have ht := neg_abs_le ⟪w,d⟫
      have hd' := (abs_real_inner_le_norm w d).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg w))
      nlinarith only [hwork,mul_le_mul_of_nonneg_left ht hη,mul_le_mul_of_nonneg_left hd' hη]
    · positivity
  have hdu : ‖d‖ ≤ U := hd.trans (by nlinarith only [mul_le_mul_of_nonneg_left hg₁ hU])
  have ds : ‖d‖^2 ≤ U^2*g := by nlinarith only [mul_le_mul hdu hd (norm_nonneg d) hU]
  have r1 : 3*k*c*max z 0/2 ≤ 3*c*(η*(L+U*‖w‖)*g) := by
    have HH := mul_le_mul hk₂ dz (le_max_right z 0) (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [mul_le_mul_of_nonneg_left HH hc]
  have ef : 4*max |P| |T| * |e|+e^2 ≤ 5*δ * |e| := by
    nlinarith only [mul_le_mul_of_nonneg_right hpt (abs_nonneg e),
      mul_le_mul_of_nonneg_right he (abs_nonneg e),sq_abs e]
  have ef' : k*R^2*(4*max |P| |T| * |e|+e^2)/2 ≤ 5*δ*(η*J*‖w‖*g) := by
    have hn : 0 ≤ 4*max |P| |T| * |e|+e^2 := by positivity
    have HH := mul_le_mul hk₂ ef hn (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [mul_le_mul_of_nonneg_left HH (sq_nonneg R),
      mul_le_mul_of_nonneg_left hforce hδ]
  have cap : L+η*U^2/2+3*c*(L+U*‖w‖)+5*δ*J*‖w‖ ≤ Γ*M := by
    nlinarith only [hsize,mul_le_mul_of_nonneg_right hc' hL,
      mul_le_mul_of_nonneg_right hsmall (norm_nonneg w),
      mul_le_mul_of_nonneg_right htiny (norm_nonneg w),mul_le_mul_of_nonneg_left hw hΓ,
      hL,mul_nonneg hη (sq_nonneg U)]
  nlinarith only [H,hwork,r1,ef',mul_le_mul_of_nonneg_left ds (sq_nonneg η),
    mul_le_mul_of_nonneg_left hm (mul_nonneg hη hM),
    mul_le_mul_of_nonneg_right cap (mul_nonneg hη hg)]

end LongTails.Proofs.BrightnessComparatorProgress

namespace LongTails.Proofs.BrightnessFirstFitDescent

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open LongTails.Proofs.BrightnessFirstFitParameters
open LongTails.Proofs.BrightnessScaledCoordinates
open LongTails.Proofs.BrightnessScaledForces
open LongTails.Proofs.BrightnessFirstFitWork
open LongTails.Proofs.BrightnessComparatorProgress

lemma separator_average (p : Params) (x : Images p) (s : State p.d) (u : Features p.d)
    (a : ℝ) (hm : ∀ i, a ≤ ⟪u,readout s (x i)⟫) :
    a*mass p (votes p x s) ≤ ⟪u,readout s (mixture x (votes p x s))⟫ := by
  let g := votes p x s
  have he := mixture_map x g (readoutMap s)
  change readout s (mixture x g) = (p.n : ℝ)⁻¹ • ∑ i, g i • readout s (x i) at he
  change a*mass p g ≤ ⟪u,readout s (mixture x g)⟫
  rw [he,real_inner_smul_right,inner_sum]
  simp only [real_inner_smul_right]
  have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hm i) (show 0 ≤ g i from Real.sigmoid_nonneg _))
  rw [← Finset.sum_mul] at H
  unfold mass
  exact (show a*((∑ i, g i)/p.n) = (p.n:ℝ)⁻¹*((∑ i, g i)*a) by ring).le.trans
    (mul_le_mul_of_nonneg_left H (by positivity))

lemma good (p : Params) (x : Images p) (G : Geometry p x) (s : State p.d) (c : Scales)
    (h : Tuning p c) (u : Features p.d) (hf : |brightness (mixture x (votes p x s))| ≤ c.f)
    (hm : ∀ i, 2*c.Γ ≤ ⟪u,readout s (x i)⟫)
    (hU : max |s.Q| |s.P| * p.J ≤ c.U) (hw : ‖s.w‖ ≤ c.V*c.M)
    (hcen : ⟪axis p.d,s.w⟫ = 0) (hn : ¬Fitted p x (physical p s)) :
    let s' := advance p c.κ s (mixture x (votes p x s))
    ‖s'.w-c.M • u‖^2 + c.κ*c.Γ*c.M/p.n ≤ ‖s.w-c.M • u‖^2 := by
  let g := votes p x s
  let z := mixture x g
  let t := p.R^2*s.P*s.T
  let L := 1+Real.log (2*(p.n:ℝ))
  let D := readout s z
  have R : 0 < p.R := by linarith only [h.Rlarge]
  have Hmass := vote_mass p x s
  have Hfit : (2*(p.n:ℝ))⁻¹ ≤ mass p g := vote_mass_nonfit p x s hn
  have κ := h.κpos
  have Γ := h.Γpos
  have μ := h.μpos
  have U := h.Upos
  have M := h.Mpos
  have f := h.fpos
  have V : 1 ≤ c.V := by linarith only [h.Vge]
  have hn₀ : 0 < (p.n : ℝ) := by exact_mod_cast p.n.property
  have hscale := comparator_size h
  have M₁ : 1 ≤ c.M := by
    nlinarith only [hscale.1,norm_nonneg p.readout,
      mul_nonneg (mul_nonneg κ.le U.le) ((by norm_num : (0:ℝ) ≤ 1).trans h.Bge)]
  have Hs := restoring_at p x G s R hcen
  have hs : |t| ≤ 2*(1+c.U*(c.V*c.M))/p.μ := by
    apply small_force _ (brightness z) _ c.f _ _ hf (small_tunings h).2.2.2 μ
    exact Hs.trans (by nlinarith only [mul_le_mul hU hw (norm_nonneg _) U.le])
  have hd : ‖D‖ ≤ c.U*mass p g :=
    (readout_force p x G s g (fun _ => Real.sigmoid_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hU Hmass.1)
  have hprod : |t*brightness z| ≤ 2*(1+c.U*(c.V*c.M))/p.μ*c.f := by
    rw [abs_mul]
    exact mul_le_mul hs hf (abs_nonneg _) (by positivity)
  have hquiet : -(t*brightness z) ≤ c.Γ*c.M*mass p g/2 := by
    have hVM : 1 ≤ c.V*c.M := by nlinarith only [mul_le_mul V M₁ (by norm_num) (by positivity)]
    have eq := h.feq
    have hh : (2*(1+c.U*(c.V*c.M))/p.μ)*c.f ≤ (c.Γ*c.M/2)*(2*(p.n:ℝ))⁻¹ := by
      field_simp
      nlinarith only [mul_le_mul_of_nonneg_left hVM (mul_nonneg (by positivity : 0 ≤ 8*(p.n:ℝ)) f.le),
        congrArg (fun a : ℝ => a*c.M) eq,
        mul_nonneg f.le (by positivity : 0 ≤ (p.n:ℝ)*c.V*c.M*(1+c.U))]
    nlinarith only [neg_abs_le (t*brightness z),hprod,hh,
      mul_le_mul_of_nonneg_left Hfit (by positivity : 0 ≤ c.Γ*c.M/2)]
  have hsize : L+c.κ*c.U^2/2 ≤ c.Γ*c.M/2 := by
    have hh := hscale.2.2
    change 8*(L+c.κ*c.U^2) ≤ c.M*c.Γ at hh
    nlinarith only [hh,mul_nonneg κ.le (sq_nonneg c.U),mul_nonneg Γ.le M.le]
  have H := good_step s.w u D c.κ c.M c.Γ c.U (mass p g) L (t*brightness z)
    κ.le M.le Hmass.1 Hmass.2 U.le hd (separator_average p x s u _ hm)
    (by linarith only [work p x s R hcen hn]) hquiet hsize
  change ‖s.w+c.κ • D-c.M • u‖^2+_ ≤ _
  have H' := mul_le_mul_of_nonneg_left Hfit (by positivity : 0 ≤ 2*c.κ*c.Γ*c.M)
  rw [show (2*c.κ*c.Γ*c.M)*(2*(p.n:ℝ))⁻¹ = c.κ*c.Γ*c.M/p.n by field_simp] at H'
  linarith only [H,H']

end LongTails.Proofs.BrightnessFirstFitDescent
