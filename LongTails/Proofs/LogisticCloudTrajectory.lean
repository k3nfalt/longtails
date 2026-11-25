import LongTails.Proofs.LogisticCloudBatch
import LongTails.Proofs.LogisticCloudDrift

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudAverages
open LongTails.Proofs.LogisticCloudModel
open LongTails.Proofs.LogisticCloudBatch
open LongTails.Proofs.LogisticCloudCone (Point signal)

namespace LongTails.Proofs.LogisticCloudTrajectory

variable {p : Params} {D : Data p} (G : Geometry p D)

noncomputable def chart (s t : ℝ) (w : Weights p.d) : Point :=
  let x := coords G w
  ⟨s*x.p,s*x.q,s*x.u,t*x.t,t*x.v⟩

lemma score_components (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (w : Weights p.d) (i : Fin p.n) :
    let x := chart G s t w
    score G.e 0 w = x.p*x.q ∧ score (zcol G i) (ycol G i) w =
      (1+p.μ*p.a)*x.p*x.q - p.μ*signal (Real.sqrt (1-p.a^2)) x +
        ⟪localFeature G w i,transverse G w⟫ := by
  dsimp only
  rw [← local_ortho G w i]
  dsimp [chart,coords,score,axis,zcol,ycol,signal,localFeature]
  simp only [inner_zero_left,mul_zero,add_zero,inner_add_left,real_inner_smul_left,inner_sub_left,
    inner_neg_left]
  constructor <;> ring_nf <;> simp [hs,ht]
  ring

lemma raw_update (η : ℝ) (w : Weights p.d) :
    let x := coords G w
    let h := hCoeff G η w
    let l := slowCoeff G η w
    let j := Real.sqrt (1-p.a^2)*l
    coords G (gradientStep G η w) =
      ⟨x.p+h*x.q+j*x.u-η/2*⟪texture G w G.z,readout w⟫,x.q+h*x.p,x.u+j*x.p,
        x.t+l*x.v-η/2*⟪texture G w G.y,readout w⟫,x.v+l*x.t⟩ := by
  obtain ⟨_,_,_,hue,hve,hvu⟩ := orthonormal_axes G
  obtain ⟨ze,ye⟩ := texture_ortho G w (show G.e ∈ ({G.e,G.u,G.v} : Set _) by simp)
  obtain ⟨zu,yu⟩ := texture_ortho G w (show G.u ∈ ({G.e,G.u,G.v} : Set _) by simp)
  obtain ⟨zv,yv⟩ := texture_ortho G w (show G.v ∈ ({G.e,G.u,G.v} : Set _) by simp)
  dsimp only
  rw [averaged_update]
  dsimp only [coords,action]
  simp only [PiLp.add_apply,pack_first,pack_second,readout_add,readout_pack,inner_sub_left,
    inner_sub_right,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,G.norm_e,G.norm_u,G.norm_v,G.eu,G.ev,G.uv,hue,hve,hvu,
    ze,ye,zu,yu,zv,yv]
  congr 1 <;> ring

lemma transverse_update (η : ℝ) (w : Weights p.d) :
    transverse G (gradientStep G η w) = transverse G w -
      (η/2) • ((p.n : ℝ)⁻¹ • ∑ i, bweight G w i • localFeature G w i) := by
  let x := coords G w
  let X := coords G (gradientStep G η w)
  have H := raw_update G η w
  have hq := congrArg Point.q H
  have hu := congrArg Point.u H
  have hv := congrArg Point.v H
  change X.q = _ at hq
  change X.u = _ at hu
  change X.v = _ at hv
  change readout (gradientStep G η w)-(X.q • G.e+X.u • G.u+X.v • G.v) = _
  rw [hq,hu,hv,averaged_update]
  simp only [readout_add,action,readout_pack,transverse,coords,localFeature,smul_add,
    smul_comm (bweight G w _) (w (.inl 0)),smul_comm (bweight G w _) (w (.inl 1)),
    Finset.sum_add_distrib,← Finset.smul_sum,texture]
  module

noncomputable def err (w : Weights p.d) (s μ : ℝ) (f : Fin p.n → Features p.d) : ℝ :=
  -(s*⟪texture G w f,readout w⟫)/(μ*avgWeight G w)

lemma chart_update (η s t : ℝ) (w : Weights p.d) (hμ : 0 < p.μ)
    (hβ : 0 < Real.sqrt (1-p.a^2)) :
    let B := Real.sqrt (1-p.a^2)
    let l := slowCoeff G η w
    chart G s t (gradientStep G η w) = LogisticCloudCone.step (chart G s t w)
      (hCoeff G η w) (B*l) l (err G w s (p.μ*B) G.z) (err G w t p.μ G.y) := by
  have hw := (positive_weight G w).ne'
  dsimp only [chart]
  rw [raw_update]
  dsimp only [LogisticCloudCone.step,err,slowCoeff]
  congr 1 <;> field_simp [hw,hμ.ne',hβ.ne'] <;> ring

lemma texture_small (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (w : Weights p.d) :
    let x := chart G s t w
    |w (.inl 0)| = |x.p| ∧ |w (.inl 1)| = |x.t| := by
  have h₁ : |s| = 1 := by nlinarith [sq_abs s,abs_nonneg s]
  have h₂ : |t| = 1 := by nlinarith [sq_abs t,abs_nonneg t]
  simp [chart,coords,abs_mul,h₁,h₂]

lemma err_bound (s : ℝ) (hs : s^2 = 1) (w : Weights p.d) (μ : ℝ) (hμ : 0 < μ)
    (f : Fin p.n → Features p.d) (hf : ∀ i, ‖f i‖ ≤ 1)
    (ho : ∀ i, ⟪G.e,f i⟫ = 0 ∧ ⟪G.u,f i⟫ = 0 ∧ ⟪G.v,f i⟫ = 0) :
    |err G w s μ f| ≤ ‖transverse G w‖/μ := by
  have h₁ : |s| = 1 := by nlinarith [sq_abs s,abs_nonneg s]
  have hw := positive_weight G w
  rw [err,abs_div,abs_neg,abs_mul,h₁,one_mul,abs_of_pos (mul_pos hμ hw)]
  rw [div_le_div_iff₀ (mul_pos hμ hw) hμ]
  nlinarith [mul_le_mul_of_nonneg_right (texture_read G w f hf ho) hμ.le]


lemma transverse_nonexpansive (η : ℝ) (hη : 0 ≤ η) (w : Weights p.d)
    (hc : ∀ i, η/2*‖localFeature G w i‖^2 ≤ 8) :
    ‖transverse G (gradientStep G η w)‖ ≤ ‖transverse G w‖ := by
  let x := chart G 1 1 w
  let c := (1+p.μ*p.a)*x.p*x.q-p.μ*signal (Real.sqrt (1-p.a^2)) x
  have hb (i : Fin p.n) : bweight G w i =
      Real.sigmoid (c+⟪localFeature G w i,transverse G w⟫) := by
    exact congrArg Real.sigmoid (score_components G 1 1 (by norm_num) (by norm_num) w i).2
  rw [transverse_update]
  simp_rw [hb]
  simpa only [Fintype.card_fin] using mean_transverse (transverse G w) (localFeature G w) c
    (η := η/2) (by positivity) (local_centered G w) hc

lemma margin_noise (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (w : Weights p.d)
    (hμ : 0 < p.μ) (hβ : 4/5 ≤ Real.sqrt (1-p.a^2))
    (hc : LogisticCloudCone.Cone p.a (chart G s t w))
    (hp : 16*‖transverse G w‖ ≤ p.μ*(chart G s t w).p)
    (hv : 16*‖transverse G w‖ ≤ p.μ*(chart G s t w).v) (i : Fin p.n) :
    |⟪localFeature G w i,transverse G w⟫| ≤ p.μ*signal (Real.sqrt (1-p.a^2)) (chart G s t w)/4 := by
  let x := chart G s t w
  change LogisticCloudCone.Cone p.a x at hc
  change _ ≤ p.μ*x.p at hp
  change _ ≤ p.μ*x.v at hv
  obtain ⟨hP,_,hU,_,hV,hT,_⟩ := hc
  have ht₀ : 0 ≤ x.t := by linarith
  have hi := local_norm G w i
  obtain ⟨h1,h2⟩ := texture_small G s t hs ht w
  change _ = |x.p| at h1
  change _ = |x.t| at h2
  rw [h1,h2,abs_of_pos hP,abs_of_nonneg ht₀] at hi
  refine (abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans ?_)
  change _ ≤ p.μ*(Real.sqrt (1-p.a^2)*x.p*x.u+x.t*x.v)/4
  have hsig := mul_le_mul hβ (mul_le_mul_of_nonneg_left hU hP.le)
    (by positivity : 0 ≤ x.p*(x.p/2)) (by linarith : 0 ≤ Real.sqrt (1-p.a^2))
  nlinarith only [mul_le_mul_of_nonneg_left hp hP.le,mul_le_mul_of_nonneg_left hv ht₀,
    mul_le_mul_of_nonneg_left hsig hμ.le,mul_nonneg hμ.le (sq_nonneg x.p),
    mul_nonneg (mul_nonneg hμ.le ht₀) hV.le]

end LongTails.Proofs.LogisticCloudTrajectory
