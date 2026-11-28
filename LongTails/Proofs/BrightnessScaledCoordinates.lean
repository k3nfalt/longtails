import LongTails.Algorithms.BrightnessScaledTwoTap
import LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
import LongTails.Proofs.Execution

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BrightnessScaledCoordinates

open LongTails.Setups.BrightnessScaledTwoTap
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space axis)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin direction)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry (axis_inner shift_axis axis_shift_inner)

structure State (d : ℕ) where
  P : ℝ
  T : ℝ
  Q : ℝ
  w : Features d

noncomputable def physical (p : Params) (s : State p.d) : Space p.d :=
  let B := Real.sqrt p.R
  ((B*(s.P+s.Q)/Real.sqrt 2,B*(s.P-s.Q)/Real.sqrt 2),
    (B*s.T) • axis p.d + B⁻¹ • s.w)

noncomputable def initial (p : Params) : State p.d :=
  ⟨p.P,⟪axis p.d,p.readout⟫/p.R^2,p.Q,centered p.readout⟩

lemma physical_initial (p : Params) (hR : 0 < p.R) :
    physical p (initial p) = start p := by
  have h := Real.sq_sqrt hR.le
  have hb := Real.sqrt_pos.mpr hR
  have he : Real.sqrt p.R * (⟪axis p.d,p.readout⟫ / p.R^2) =
      (Real.sqrt p.R)⁻¹ * (⟪axis p.d,p.readout⟫ / p.R) := by
    field_simp
    linear_combination ⟪axis p.d,p.readout⟫ * h
  simp only [physical,initial,start,smul_add,smul_smul,he,add_comm]

lemma centered_orthogonal {d : ℕ} (hd : 0 < d) (x : Features d) :
    ⟪axis d,centered x⟫ = 0 := by
  rw [centered,inner_sub_right,real_inner_smul_right,axis_inner hd,mul_one,sub_self]

lemma amplified_products (p : Params) (s : State p.d) (x : Features p.d)
    (hw : ⟪axis p.d,s.w⟫ = 0) :
    let B := Real.sqrt p.R
    let common := p.R * ⟪axis p.d,x⟫ * B * s.T
    ⟪amplify p.R x,(physical p s).2⟫ = common+B⁻¹*⟪centered x,s.w⟫ ∧
    ⟪shift (amplify p.R x),(physical p s).2⟫ =
      common+B⁻¹*⟪shift (centered x),s.w⟫ := by
  have haxis : ⟪axis p.d,axis p.d⟫ = 1 := axis_inner p.d.property
  have hx : ⟪axis p.d,centered x⟫ = 0 := centered_orthogonal p.d.property x
  have hx' : ⟪centered x,axis p.d⟫ = 0 := (real_inner_comm _ _).trans hx
  have hy : ⟪shift (centered x),axis p.d⟫ = 0 := (real_inner_comm _ _).trans ((axis_shift_inner _).trans hx)
  simp only [physical,amplify,shift_add,shift_smul,shift_axis,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,hw,hx',hy,haxis]
  constructor <;> ring

lemma physical_margin (p : Params) (s : State p.d) (x : Features p.d)
    (hR : 0 < p.R) (hw : ⟪axis p.d,s.w⟫ = 0) :
    margin .conv p.d (amplify p.R x) (physical p s) =
      p.R^2*s.P*s.T*brightness x+s.Q*⟪contrast x,s.w⟫+s.P*⟪smooth x,s.w⟫ := by
  obtain ⟨h₁,h₂⟩ := amplified_products p s x hw
  change (physical p s).1.1 * ⟪amplify p.R x,(physical p s).2⟫ +
    (physical p s).1.2 * ⟪shift (amplify p.R x),(physical p s).2⟫ = _
  rw [h₁,h₂]
  simp only [physical,brightness,contrast,smooth,real_inner_smul_left,
    inner_sub_left,inner_add_left]
  have hs := Real.sq_sqrt hR.le
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb := (Real.sqrt_pos.mpr hR).ne'
  field_simp
  ring_nf
  simp [hs,h₂]
  ring_nf
  simp


noncomputable def centeredMap (d : ℕ) : Features d →ₗ[ℝ] Features d where
  toFun := centered
  map_add' x y := by simp only [centered,inner_add_right,add_smul]; abel
  map_smul' r x := by simp only [centered,real_inner_smul_right,smul_sub,smul_smul,
    RingHom.id_apply]

noncomputable def amplification (d : ℕ) (R : ℝ) : Features d →ₗ[ℝ] Features d where
  toFun := amplify R
  map_add' x y := by
    change centeredMap d (x+y) + _ = centeredMap d x + _ + (centeredMap d y + _)
    rw [map_add,inner_add_right,mul_add,add_smul]
    abel
  map_smul' r x := by
    change centeredMap d (r • x) + _ = r • (centeredMap d x + _)
    rw [map_smul,real_inner_smul_right,smul_add,smul_smul,mul_left_comm]

noncomputable def gradientRow {d : ℕ} (θ : Space d) : Features d →ₗ[ℝ] Space d where
  toFun x := direction .conv d x θ
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext <;> simp [direction,inner_add_left,shift_add]
    · simp only [direction,Prod.snd_add,shift_add,smul_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · apply Prod.ext <;> simp [direction,real_inner_smul_left,shift_smul]
    · simp only [direction,Prod.smul_snd,RingHom.id_apply,shift_smul,smul_add,smul_smul]
      rw [mul_comm r,mul_comm r]

noncomputable def mixture {d n : ℕ} (x : Fin n → Features d) (g : Fin n → ℝ) :=
  (n : ℝ)⁻¹ • ∑ i, g i • x i

lemma mixture_map {d n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x : Fin n → Features d) (g : Fin n → ℝ) (F : Features d →ₗ[ℝ] E) :
    F (mixture x g) = (n : ℝ)⁻¹ • ∑ i, g i • F (x i) := by
  simp only [mixture,map_smul,map_sum]

lemma answer_descent (p : Params) (x : Images p) (θ : Space p.d) :
    (answer p x θ).descent = direction .conv p.d (amplify p.R (mixture x
      (fun i => Real.sigmoid (-margin .conv p.d (amplify p.R (x i)) θ)))) θ := by
  exact (mixture_map x _ ((gradientRow θ).comp (amplification p.d p.R))).symm


noncomputable def advance (p : Params) (κ : ℝ) (s : State p.d) (z : Features p.d) :
    State p.d where
  P := s.P + κ*brightness z*s.T + κ*⟪smooth z,s.w⟫/p.R^2
  T := s.T + κ*brightness z*s.P
  Q := s.Q + κ*⟪contrast z,s.w⟫/p.R^2
  w := s.w + κ • (s.Q • contrast z + s.P • smooth z)

lemma advance_centered (p : Params) (κ : ℝ) (s : State p.d) (z : Features p.d)
    (hw : ⟪axis p.d,s.w⟫ = 0) : ⟪axis p.d,(advance p κ s z).w⟫ = 0 := by
  have hz : ⟪axis p.d,centered z⟫ = 0 := centered_orthogonal p.d.property z
  simp only [advance,contrast,smooth,inner_add_right,inner_sub_right,real_inner_smul_right,
    axis_shift_inner,hz,hw,sub_zero,add_zero,mul_zero]


lemma physical_advance (p : Params) (κ : ℝ) (s : State p.d) (z : Features p.d)
    (hR : 0 < p.R) (hw : ⟪axis p.d,s.w⟫ = 0) :
    physical p (advance p κ s z) = physical p s +
      (κ/p.R) • direction .conv p.d (amplify p.R z) (physical p s) := by
  obtain ⟨h₁,h₂⟩ := amplified_products p s z hw
  have hs := Real.sq_sqrt hR.le
  have hj := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb := (Real.sqrt_pos.mpr hR).ne'
  apply Prod.ext
  · apply Prod.ext
    · change _ = (physical p s).1.1 + κ/p.R * ⟪amplify p.R z,(physical p s).2⟫
      rw [h₁]
      simp only [physical,advance,contrast,smooth,brightness,real_inner_smul_left,
        inner_add_left,inner_sub_left]
      field_simp
      ring_nf
      simp [hs,hj]
      ring_nf
    · change _ = (physical p s).1.2 + κ/p.R * ⟪shift (amplify p.R z),(physical p s).2⟫
      rw [h₂]
      simp only [physical,advance,contrast,smooth,brightness,real_inner_smul_left,
        inner_add_left,inner_sub_left]
      field_simp
      ring_nf
      simp [hs,hj]
      ring_nf
  · change _ = (physical p s).2 + (κ/p.R) •
      ((physical p s).1.1 • amplify p.R z + (physical p s).1.2 • shift (amplify p.R z))
    simp only [physical,advance,contrast,smooth,brightness,amplify,shift_add,shift_smul,shift_axis]
    match_scalars <;> field_simp <;> ring_nf <;> simp [hs,hj]
    all_goals ring_nf


noncomputable def votes (p : Params) (x : Images p) (s : State p.d) (i : Fin p.n) : ℝ :=
  Real.sigmoid (-margin .conv p.d (amplify p.R (x i)) (physical p s))

noncomputable def path (p : Params) (x : Images p) (κ : ℝ) : ℕ → State p.d
  | 0 => initial p
  | k+1 =>
    let s := path p x κ k
    advance p κ s (mixture x (votes p x s))

lemma path_centered (p : Params) (x : Images p) (κ : ℝ) (k : ℕ) :
    ⟪axis p.d,(path p x κ k).w⟫ = 0 := by
  induction k with
  | zero => exact centered_orthogonal p.d.property _
  | succ k ih => exact advance_centered p κ _ _ ih

lemma path_update (p : Params) (x : Images p) (κ : ℝ) (hR : 0 < p.R) (k : ℕ) :
    physical p (path p x κ (k+1)) = physical p (path p x κ k) +
      (κ/p.R) • (answer p x (physical p (path p x κ k))).descent := by
  rw [answer_descent]
  exact physical_advance p κ _ _ hR (path_centered p x κ k)

end LongTails.Proofs.BrightnessScaledCoordinates
