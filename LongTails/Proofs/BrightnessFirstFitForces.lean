import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic
import LongTails.Proofs.BrightnessScaledCoordinates

namespace LongTails.Proofs.BrightnessVoteBounds

lemma logistic_work (x : ℝ) : x * Real.sigmoid (-x) ≤ 1 := by
  rw [Real.sigmoid_def, neg_neg, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  linarith [Real.add_one_le_exp x]

lemma row_restoring (x a : ℝ) :
    x * Real.sigmoid (-(x+a)) - min x 0 ≤ 1 + |a| := by
  have bound (v : ℝ) (hv : |v| ≤ 1) : -(a*v) ≤ |a| := calc
    _ ≤ |a*v| := neg_le_abs _
    _ = |a| * |v| := abs_mul _ _
    _ ≤ |a| := by simpa using mul_le_mul_of_nonneg_left hv (abs_nonneg a)
  let g := Real.sigmoid (-(x+a))
  have hg : 0 ≤ g := Real.sigmoid_nonneg _
  have hg' : g ≤ 1 := Real.sigmoid_le_one _
  change x*g - min x 0 ≤ _
  rcases le_total x 0 with hx | hx
  · rw [min_eq_left hx]
    have hw := logistic_work (-(x+a))
    rw [Real.sigmoid_neg (-(x+a))] at hw
    have hb := bound (g-1) (abs_le.mpr ⟨by linarith,by linarith⟩)
    change -(x+a) * (1-g) ≤ 1 at hw
    nlinarith only [hw,hb]
  · rw [min_eq_right hx]
    have hw : (x+a)*g ≤ 1 := logistic_work _
    nlinarith only [hw,bound g (by rwa [abs_of_nonneg hg])]

lemma restoring_sum {ι : Type*} [Fintype ι] (d a : ι → ℝ) (s : ℝ) :
    s * (∑ i, d i * Real.sigmoid (-(s*d i+a i))) - (∑ i, min (s*d i) 0) ≤
      ∑ i, (1+|a i|) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc] using row_restoring (s*d i) (a i)

lemma shifted_work (r L : ℝ) : (r-L)*Real.sigmoid (-r) ≤ Real.exp (-L) := by
  rw [Real.sigmoid_def,neg_neg,← div_eq_mul_inv,div_le_iff₀ (by positivity)]
  have H := Real.add_one_le_exp (r-L)
  rw [sub_eq_add_neg,Real.exp_add] at H
  nlinarith only [H,Real.exp_pos (-L)]

lemma work_before_fit {n : ℕ+} (r : Fin n → ℝ) (hf : ∃ i, r i ≤ 0) :
    (∑ i, r i*Real.sigmoid (-r i)) ≤
      (1+Real.log (2*(n : ℝ))) * ∑ i, Real.sigmoid (-r i) := by
  classical
  obtain ⟨i,hi⟩ := hf
  have hn : 0 < (n : ℝ) := by exact_mod_cast n.property
  have hi' := Real.sigmoid_le (a := 0) (b := -r i) (by linarith)
  rw [Real.sigmoid_zero] at hi'
  have hm := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => Real.sigmoid (-r j)) (fun j _ => Real.sigmoid_nonneg _) (Finset.mem_univ i)
  let L := Real.log (2*(n : ℝ))
  have hpoint (j : Fin n) : r j*Real.sigmoid (-r j) ≤
      L*Real.sigmoid (-r j)+(2*(n : ℝ))⁻¹ := by
    have h := shifted_work (r j) L
    rw [Real.exp_neg,Real.exp_log (show 0 < 2*(n : ℝ) by positivity)] at h
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hsum
  have hhalf : (n : ℝ)*(2*(n : ℝ))⁻¹ = 2⁻¹ := by field_simp
  rw [hhalf] at hsum
  change _ ≤ (1+L)*_
  nlinarith only [hsum,hm,hi']

end LongTails.Proofs.BrightnessVoteBounds

namespace LongTails.Proofs.BrightnessScaledForces

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.BrightnessScaledCoordinates

noncomputable def shiftMap (d : ℕ) : Features d →ₗ[ℝ] Features d where
  toFun := shift
  map_add' := shift_add
  map_smul' := shift_smul

noncomputable def contrastMap (d : ℕ) : Features d →ₗ[ℝ] Features d :=
  (Real.sqrt 2)⁻¹ • ((LinearMap.id - shiftMap d).comp (centeredMap d))

noncomputable def smoothMap (d : ℕ) : Features d →ₗ[ℝ] Features d :=
  (Real.sqrt 2)⁻¹ • ((LinearMap.id + shiftMap d).comp (centeredMap d))

noncomputable def brightnessMap (d : ℕ) : Features d →ₗ[ℝ] ℝ :=
  Real.sqrt 2 • (innerSL ℝ (axis d)).toLinearMap

lemma contrast_margin (p : Params) (x : Images p) (hg : Geometry p x) :
    ∃ u : Features p.d, ‖u‖ = 1 ∧ ∀ i, |p.Q| * p.γ ≤
      ⟪u,p.Q • contrast (x i)+(0:ℝ) • smooth (x i)⟫ := by
  obtain ⟨u,hu,hm⟩ := hg.2.2.2
  by_cases h : 0 ≤ p.Q
  · refine ⟨u,hu,fun i => ?_⟩
    simpa [real_inner_smul_right,abs_of_nonneg h] using mul_le_mul_of_nonneg_left (hm i) h
  · refine ⟨-u,by simpa using hu,fun i => ?_⟩
    simp only [zero_smul,add_zero,inner_neg_left,real_inner_smul_right,abs_of_neg (lt_of_not_ge h)]
    nlinarith only [mul_le_mul_of_nonneg_left (hm i) (neg_nonneg.mpr (le_of_not_ge h))]

noncomputable def mass (p : Params) (g : Fin p.n → ℝ) : ℝ := (∑ i, g i)/p.n

lemma mixture_norm (p : Params) (x : Images p) (g : Fin p.n → ℝ)
    (F : Features p.d →ₗ[ℝ] Features p.d) (hg : ∀ i, 0 ≤ g i)
    (hF : ∀ i, ‖F (x i)‖ ≤ p.J) :
    ‖F (mixture x g)‖ ≤ p.J * mass p g := by
  rw [mixture_map,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have H := norm_sum_le (Finset.univ : Finset (Fin p.n)) (fun i => g i • F (x i))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hg _)] at H
  have H' := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hF i) (hg i))
  rw [← Finset.sum_mul] at H'
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ((∑ i, g i)*p.J) := mul_le_mul_of_nonneg_left (H.trans H') (by positivity)
    _ = _ := by unfold mass; ring

lemma brightness_mixture (p : Params) (x : Images p) (g : Fin p.n → ℝ) :
    brightness (mixture x g) = (∑ i, brightness (x i)*g i)/p.n := by
  have H := mixture_map x g (brightnessMap p.d)
  change brightness (mixture x g) = (p.n : ℝ)⁻¹ * ∑ i, g i*brightness (x i) at H
  simpa only [div_eq_inv_mul,mul_comm (g _)] using H

lemma mass_bounds (p : Params) (g : Fin p.n → ℝ) (h : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    0 ≤ mass p g ∧ mass p g ≤ 1 := by
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast p.n.property
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => (h i).1)) hn.le,?_⟩
  change (∑ i, g i)/(p.n : ℝ) ≤ 1
  rw [div_le_iff₀ hn,one_mul]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).2)

lemma restoring (p : Params) (x : Images p) (G : Geometry p x)
    (a : Fin p.n → ℝ) (s M : ℝ) (ha : ∀ i, |a i| ≤ M) :
    let g := fun i => Real.sigmoid (-(s*brightness (x i)+a i))
    s*brightness (mixture x g)+|s| * p.μ ≤ 1+M := by
  dsimp only
  rw [brightness_mixture]
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast p.n.property
  have H := BrightnessVoteBounds.restoring_sum (fun i => brightness (x i)) a s
  have H' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => show 1+|a i| ≤ 1+M by linarith only [ha i])
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H'
  have Hm : (∑ i, min (s*brightness (x i)) 0) ≤ -(|s| * ((p.n : ℝ)*p.μ)) := by
    rcases le_total 0 s with h | h
    · have term (i : Fin p.n) : min (s*brightness (x i)) 0 = - (s*max (-brightness (x i)) 0) := by
        rcases le_total (brightness (x i)) 0 with hi | hi
        · rw [max_eq_left (neg_nonneg.mpr hi),min_eq_left (mul_nonpos_of_nonneg_of_nonpos h hi)]
          ring
        · rw [max_eq_right (neg_nonpos.mpr hi),min_eq_right (mul_nonneg h hi)]
          ring
      simp_rw [term,Finset.sum_neg_distrib,← Finset.mul_sum]
      rw [abs_of_nonneg h]
      exact neg_le_neg (mul_le_mul_of_nonneg_left G.2.2.1 h)
    · have term (i : Fin p.n) : min (s*brightness (x i)) 0 = s*max (brightness (x i)) 0 := by
        rcases le_total (brightness (x i)) 0 with hi | hi
        · rw [max_eq_right hi,min_eq_right (mul_nonneg_of_nonpos_of_nonpos h hi),mul_zero]
        · rw [max_eq_left hi,min_eq_left (mul_nonpos_of_nonpos_of_nonneg h hi)]
      simp_rw [term,← Finset.mul_sum]
      rw [abs_of_nonpos h,neg_mul,neg_neg]
      exact mul_le_mul_of_nonpos_left G.2.1 h
  field_simp
  nlinarith only [H,H',Hm]

end LongTails.Proofs.BrightnessScaledForces

namespace LongTails.Proofs.BrightnessFirstFitWork

open scoped RealInnerProductSpace

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features margin)
open LongTails.Proofs.BrightnessScaledCoordinates
open LongTails.Proofs.BrightnessScaledForces

noncomputable def readout {d : ℕ} (s : State d) (z : Features d) : Features d :=
  s.Q • contrast z+s.P • smooth z

noncomputable def readoutMap {d : ℕ} (s : State d) : Features d →ₗ[ℝ] Features d :=
  s.Q • contrastMap d + s.P • smoothMap d

lemma readout_row (p : Params) (x : Images p) (G : Geometry p x) (s : State p.d) (i : Fin p.n) :
    ‖readout s (x i)‖ ≤ max |s.Q| |s.P| * p.J := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have hcap : 0 ≤ max |s.Q| |s.P| := (abs_nonneg _).trans (le_max_left _ _)
  nlinarith only [mul_le_mul_of_nonneg_left (G.1 i).2 hcap,
    mul_le_mul_of_nonneg_right (le_max_left |s.Q| |s.P|) (norm_nonneg (contrast (x i))),
    mul_le_mul_of_nonneg_right (le_max_right |s.Q| |s.P|) (norm_nonneg (smooth (x i)))]

lemma readout_force (p : Params) (x : Images p) (G : Geometry p x) (s : State p.d)
    (g : Fin p.n → ℝ) (h : ∀ i, 0 ≤ g i) :
    ‖readout s (mixture x g)‖ ≤ (max |s.Q| |s.P| * p.J)*mass p g := by
  have H := mixture_map x g (readoutMap s)
  change readout s (mixture x g) = (p.n : ℝ)⁻¹ • ∑ i, g i • readout s (x i) at H
  rw [H,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have H' := norm_sum_le (Finset.univ : Finset (Fin p.n)) (fun i => g i • readout s (x i))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (h _)] at H'
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (readout_row p x G s i) (h i))
  rw [← Finset.sum_mul] at hsum
  exact (mul_le_mul_of_nonneg_left (H'.trans hsum) (by positivity)).trans_eq (by unfold mass; ring)

lemma score_mixture (p : Params) (x : Images p) (g : Fin p.n → ℝ)
    (s : State p.d) (hR : 0 < p.R) (hw : ⟪axis p.d,s.w⟫ = 0) :
    let z := mixture x g
    p.R^2*s.P*s.T*brightness z+⟪s.w,readout s z⟫ =
      (∑ i, margin .conv p.d (amplify p.R (x i)) (physical p s)*g i)/p.n := by
  let F := (p.R^2*s.P*s.T) • brightnessMap p.d + ((innerSL ℝ s.w).toLinearMap.comp (readoutMap s))
  have he (z : Features p.d) : F z = margin .conv p.d (amplify p.R z) (physical p s) := by
    rw [physical_margin p s z hR hw]
    change p.R^2*s.P*s.T*brightness z+⟪s.w,readout s z⟫ = _
    simp only [readout,inner_add_right,real_inner_smul_right,real_inner_comm s.w]
    ring
  have H := mixture_map x g F
  dsimp only
  change F (mixture x g) = _
  rw [H]
  simp only [he,smul_eq_mul,div_eq_inv_mul,mul_comm (g _)]

lemma work (p : Params) (x : Images p) (s : State p.d) (hR : 0 < p.R)
    (hw : ⟪axis p.d,s.w⟫ = 0) (hf : ¬ Fitted p x (physical p s)) :
    let g := votes p x s
    let z := mixture x g
    p.R^2*s.P*s.T*brightness z+⟪s.w,readout s z⟫ ≤
      (1+Real.log (2*(p.n : ℝ)))*mass p g := by
  dsimp only
  rw [score_mixture p x _ s hR hw]
  unfold Fitted at hf
  push Not at hf
  have H := BrightnessVoteBounds.work_before_fit (fun i => margin .conv p.d (amplify p.R (x i)) (physical p s)) hf
  have hn : 0 ≤ (p.n : ℝ) := by positivity
  exact (div_le_div_of_nonneg_right H hn).trans_eq (by unfold mass votes; ring)

lemma vote_mass (p : Params) (x : Images p) (s : State p.d) :
    0 ≤ mass p (votes p x s) ∧ mass p (votes p x s) ≤ 1 :=
  mass_bounds p _ (fun _ => ⟨Real.sigmoid_nonneg _,Real.sigmoid_le_one _⟩)

lemma vote_mass_nonfit (p : Params) (x : Images p) (s : State p.d)
    (hf : ¬ Fitted p x (physical p s)) :
    (2*(p.n : ℝ))⁻¹ ≤ mass p (votes p x s) := by
  classical
  unfold Fitted at hf
  push Not at hf
  obtain ⟨i,hi⟩ := hf
  have H := Finset.single_le_sum (s := Finset.univ) (f := votes p x s)
    (fun _ _ => Real.sigmoid_nonneg _) (Finset.mem_univ i)
  have hi' := Real.sigmoid_le (a := 0) (b := -margin .conv p.d (amplify p.R (x i))
    (physical p s)) (by linarith only [hi])
  rw [Real.sigmoid_zero] at hi'
  change 2⁻¹ ≤ votes p x s i at hi'
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast p.n.property
  change _ ≤ (∑ i, votes p x s i)/(p.n : ℝ)
  rw [le_div_iff₀ hn]
  exact le_trans (by field_simp; linarith only [hi']) H

lemma force_bounds (p : Params) (x : Images p) (G : Geometry p x) (s : State p.d) :
    let z := mixture x (votes p x s)
    |brightness z| ≤ p.D ∧ ‖contrast z‖ ≤ p.J*mass p (votes p x s) ∧
      ‖smooth z‖ ≤ p.J*mass p (votes p x s) := by
  dsimp only
  have hg (i : Fin p.n) : 0 ≤ votes p x s i := Real.sigmoid_nonneg _
  have hj₁ (i : Fin p.n) : ‖contrast (x i)‖ ≤ p.J := by linarith [(G.1 i).2,norm_nonneg (smooth (x i))]
  have hj₂ (i : Fin p.n) : ‖smooth (x i)‖ ≤ p.J := by linarith [(G.1 i).2,norm_nonneg (contrast (x i))]
  refine ⟨?_,mixture_norm p x _ (contrastMap p.d) hg hj₁,mixture_norm p x _ (smoothMap p.d) hg hj₂⟩
  have hd := (abs_nonneg _).trans (G.1 (0 : Fin p.n)).1
  rw [brightness_mixture,abs_div,abs_of_nonneg (by positivity : 0 ≤ (p.n : ℝ))]
  calc
    _ ≤ (∑ i, |brightness (x i)*votes p x s i|)/p.n :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (∑ i, p.D*votes p x s i)/p.n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (hg i)]
      exact mul_le_mul_of_nonneg_right (G.1 i).1 (hg i)
    _ = p.D*mass p (votes p x s) := by rw [← Finset.mul_sum]; unfold mass; ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left (vote_mass p x s).2 hd

lemma restoring_at (p : Params) (x : Images p) (G : Geometry p x) (s : State p.d)
    (hR : 0 < p.R) (hw : ⟪axis p.d,s.w⟫ = 0) :
    let t := p.R^2*s.P*s.T
    t*brightness (mixture x (votes p x s))+|t| * p.μ ≤
      1+(max |s.Q| |s.P| * p.J)*‖s.w‖ := by
  let t := p.R^2*s.P*s.T
  let a i := ⟪readout s (x i),s.w⟫
  have hmargin (i : Fin p.n) : margin .conv p.d (amplify p.R (x i)) (physical p s) =
      t*brightness (x i)+a i := by
    rw [physical_margin p s _ hR hw]
    simp only [t,a,readout,inner_add_left,real_inner_smul_left]
    ring
  have ha (i : Fin p.n) : |a i| ≤ (max |s.Q| |s.P| * p.J)*‖s.w‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (readout_row p x G s i) (norm_nonneg _))
  have he : votes p x s = fun i => Real.sigmoid (-(t*brightness (x i)+a i)) := by
    funext i
    rw [votes,hmargin]
  dsimp only
  rw [he]
  exact restoring p x G a t _ ha

end LongTails.Proofs.BrightnessFirstFitWork
