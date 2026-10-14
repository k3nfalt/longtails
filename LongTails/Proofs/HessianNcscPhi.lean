import LongTails.Proofs.HessianNcscLocal
import LongTails.Proofs.HessianNcscNormalization
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace
open Filter Topology Asymptotics

namespace OracleTemplate.HessianNcsc

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

noncomputable def Phi (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : ℝ := f x (ystar H x)

namespace Hyp

variable (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma gx_lip_x (x x' : E) (y : F) : ‖gx (x, y) - gx (x', y)‖ ≤ L * ‖x - x'‖ := by
  have h := H.gx_lip (x, y) (x', y)
  simpa [Real.sqrt_sq (norm_nonneg _)] using h

lemma f_upper (x x' : E) (y : F) :
    f x' y ≤ f x y + ⟪gx (x, y), x' - x⟫ + L / 2 * ‖x' - x‖ ^ 2 :=
  Gradient.smooth_upper_bound (oracle := fun x => gx (x, y)) (fun x => H.hgx x y)
    (fun a b => H.gx_lip_x a b y) x x'

lemma f_lower (x x' : E) (y : F) :
    f x y + ⟪gx (x, y), x' - x⟫ - 3 * L / 2 * ‖x' - x‖ ^ 2 ≤ f x' y := by
  have h := H.f_upper x' x y
  have hc : ⟪gx (x', y) - gx (x, y), x - x'⟫ ≤ L * ‖x' - x‖ ^ 2 := by
    have := real_inner_le_norm (gx (x', y) - gx (x, y)) (x - x')
    have h2 := H.gx_lip_x x' x y
    rw [norm_sub_rev x x'] at this
    nlinarith [norm_nonneg (x' - x)]
  have e : ⟪gx (x', y), x - x'⟫ = ⟪gx (x', y) - gx (x, y), x - x'⟫ - ⟪gx (x, y), x' - x⟫ := by
    rw [inner_sub_left]
    have : ⟪gx (x, y), x - x'⟫ = -⟪gx (x, y), x' - x⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  rw [e, norm_sub_rev] at h
  linarith

lemma Phi_upper (x x' : E) :
    Phi H x' ≤ Phi H x + ⟪Gs H x, x' - x⟫ + L * (L / μ + 1 / 2) * ‖x' - x‖ ^ 2 := by
  have h1 := H.f_upper x x' (ystar H x')
  have h2 := H.ystar_max x (ystar H x')
  have h3 : ⟪gx (x, ystar H x'), x' - x⟫ ≤ ⟪Gs H x, x' - x⟫ + L * (L / μ) * ‖x' - x‖ ^ 2 := by
    have e : ⟪gx (x, ystar H x'), x' - x⟫ = ⟪Gs H x, x' - x⟫ + ⟪gx (x, ystar H x') - Gs H x, x' - x⟫ := by
      rw [inner_sub_left]; ring
    rw [e]
    have hc := real_inner_le_norm (gx (x, ystar H x') - Gs H x) (x' - x)
    have hl := H.gx_lip_y x (ystar H x') (ystar H x)
    have hy := H.ystar_lip x' x
    have : ‖gx (x, ystar H x') - Gs H x‖ ≤ L * (L / μ) * ‖x' - x‖ := by
      calc ‖gx (x, ystar H x') - Gs H x‖ ≤ L * ‖ystar H x' - ystar H x‖ := hl
        _ ≤ L * ((L / μ) * ‖x' - x‖) := mul_le_mul_of_nonneg_left hy H.L_pos.le
        _ = L * (L / μ) * ‖x' - x‖ := by ring
    nlinarith [norm_nonneg (x' - x)]
  simp only [Phi]
  nlinarith

lemma Phi_lower (x x' : E) :
    Phi H x + ⟪Gs H x, x' - x⟫ - 3 * L / 2 * ‖x' - x‖ ^ 2 ≤ Phi H x' := by
  have h1 := H.f_lower x x' (ystar H x)
  have h2 := H.ystar_max x' (ystar H x)
  simp only [Phi, Gs, zs] at *
  linarith

lemma Phi_hasGradient (x : E) : HasGradientAt (Phi H) (Gs H x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hC : 0 ≤ L * (L / μ + 1 / 2) + 3 * L / 2 := by
    have := H.L_pos; have := H.μpos; positivity
  have hb : ∀ h : E, ‖Phi H (x + h) - Phi H x - (InnerProductSpace.toDual ℝ E (Gs H x)) h‖ ≤
      (L * (L / μ + 1 / 2) + 3 * L / 2) * ‖h‖ ^ 2 := by
    intro h
    have hu := H.Phi_upper x (x + h)
    have hl := H.Phi_lower x (x + h)
    simp only [add_sub_cancel_left] at hu hl
    rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs, abs_le]
    have h1 : 0 ≤ L * (L / μ + 1 / 2) * ‖h‖ ^ 2 := by have := H.L_pos; have := H.μpos; positivity
    have h2 : 0 ≤ 3 * L / 2 * ‖h‖ ^ 2 := by have := H.L_pos; positivity
    constructor
    · nlinarith
    · nlinarith
  have hbig : (fun h : E => Phi H (x + h) - Phi H x - (InnerProductSpace.toDual ℝ E (Gs H x)) h) =O[𝓝 0]
      (fun h : E => ‖h‖ ^ 2) := by
    refine IsBigO.of_bound (L * (L / μ + 1 / 2) + 3 * L / 2) (Eventually.of_forall fun h => ?_)
    rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖h‖ ^ 2)]
    exact hb h
  have hlit : (fun h : E => ‖h‖ ^ 2) =o[𝓝 0] (fun h : E => h) := by
    have h0 := (isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)).comp_tendsto
      (tendsto_norm_zero (E := E))
    exact isLittleO_norm_right.mp h0
  exact hbig.trans_isLittleO hlit

lemma contraction (x : E) (e : F) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ μ / L ^ 2) :
    ‖e + γ • gy (x, ystar H x + e)‖ ^ 2 ≤ (1 - γ * μ) * ‖e‖ ^ 2 := by
  have hm := H.gy_mono x (ystar H x) (ystar H x + e)
  rw [H.gy_ystar x, sub_zero, add_sub_cancel_left] at hm
  have hl := H.gy_lip_y x (ystar H x + e) (ystar H x)
  rw [H.gy_ystar x, sub_zero, add_sub_cancel_left] at hl
  rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_of_nonneg hγ0]
  have hL := H.L_pos
  have hgl : γ * L ^ 2 ≤ μ := by rwa [le_div_iff₀ (by positivity)] at hγ
  have hl2 : ‖gy (x, ystar H x + e)‖ ^ 2 ≤ L ^ 2 * ‖e‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hl 2
  have hin : ⟪e, gy (x, ystar H x + e)⟫ ≤ -(μ * ‖e‖ ^ 2) := by rw [real_inner_comm]; exact hm
  have h3 : (γ * ‖gy (x, ystar H x + e)‖) ^ 2 ≤ γ * μ * ‖e‖ ^ 2 := by
    rw [mul_pow]
    calc γ ^ 2 * ‖gy (x, ystar H x + e)‖ ^ 2 ≤ γ ^ 2 * (L ^ 2 * ‖e‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hl2 (by positivity)
      _ = γ * (γ * L ^ 2) * ‖e‖ ^ 2 := by ring
      _ ≤ γ * μ * ‖e‖ ^ 2 := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left hin (by positivity : (0:ℝ) ≤ 2 * γ)]

lemma phi_gap {x0 : E} {Δ : ℝ} (hΔ : ∀ x y, ∃ y', f x0 y - f x y' ≤ Δ) (x : E) :
    Phi H x0 - Phi H x ≤ Δ := by
  obtain ⟨y', hy'⟩ := hΔ x (ystar H x0)
  have := H.ystar_max x y'
  simp only [Phi]; linarith

lemma descent_step {η lam : ℝ} (hl : 0 < lam) (hη : 0 ≤ η) (w u : E) :
    Phi H (w + nphi η lam u) ≤ Phi H w - η * (‖Gs H w‖ - lam - 2 * ‖u - Gs H w‖) +
      L * (L / μ + 1 / 2) * η ^ 2 := by
  have h1 := H.Phi_upper w (w + nphi η lam u)
  rw [add_sub_cancel_left] at h1
  have h2 := nphi_descent hl hη (Gs H w) (u - Gs H w)
  rw [add_sub_cancel] at h2
  have h3 := nphi_norm hl hη u
  have h4 : ‖nphi η lam u‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hc : 0 ≤ L * (L / μ + 1 / 2) := by have := H.L_pos; have := H.μpos; positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 hc]

end Hyp

noncomputable def Cb (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : E →L[ℝ] F :=
  (Hy (zs H x)).comp (ContinuousLinearMap.inl ℝ E F)

noncomputable def Dyl [FiniteDimensional ℝ F] (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) (v : E) : F :=
  -(Jinv H x).symm (Cb H x v)

namespace Hyp

variable [FiniteDimensional ℝ F] (H : Hyp f gx gy Hx Hy L μ ρ)
include H

lemma Dyl_add (x v v' : E) : Dyl H x (v + v') = Dyl H x v + Dyl H x v' := by
  simp [Dyl, map_add]; abel

lemma Dyl_smul (x : E) (c : ℝ) (v : E) : Dyl H x (c • v) = c • Dyl H x v := by
  simp [Dyl, map_smul]

lemma Dyl_norm (x v : E) : ‖Dyl H x v‖ ≤ (L / μ) * ‖v‖ := by
  have h1 := H.hessy_bound (zs H x) (v, (0 : F))
  have hs : sq (v, (0 : F)) = ‖v‖ ^ 2 := by simp [sq]
  rw [hs, Real.sqrt_sq (norm_nonneg _)] at h1
  have h2 := H.Jinv_norm x (Cb H x v)
  simp only [Dyl, norm_neg]
  have hc : ‖Cb H x v‖ ≤ L * ‖v‖ := by simpa [Cb] using h1
  calc ‖(Jinv H x).symm (Cb H x v)‖ ≤ ‖Cb H x v‖ / μ := h2
    _ ≤ L * ‖v‖ / μ := by gcongr; exact H.μpos.le
    _ = (L / μ) * ‖v‖ := by ring

lemma ystar_lin (a b : E) :
    ‖ystar H a - ystar H b - Dyl H b (a - b)‖ ≤ (ρ / μ) * (1 + (L / μ) ^ 2) * ‖a - b‖ ^ 2 := by
  have hT := H.taylor_y (zs H b) (a - b, ystar H a - ystar H b)
  have hz : zs H b + (a - b, ystar H a - ystar H b) = zs H a := by simp [zs]
  rw [hz] at hT
  have h0a : gy (zs H a) = 0 := H.gy_ystar a
  have h0b : gy (zs H b) = 0 := H.gy_ystar b
  rw [h0a, h0b, sub_zero, zero_sub, norm_neg] at hT
  have hsplit : (Hy (zs H b)) (a - b, ystar H a - ystar H b) =
      Cb H b (a - b) + Jb H b (ystar H a - ystar H b) := by
    have : ((a - b, ystar H a - ystar H b) : E × F) = (a - b, 0) + (0, ystar H a - ystar H b) := by simp
    rw [this, map_add]; simp [Cb, Jb]
  rw [hsplit] at hT
  set Δy := ystar H a - ystar H b
  have key : Δy - Dyl H b (a - b) = (Jinv H b).symm (Cb H b (a - b) + Jb H b Δy) := by
    simp only [Dyl, sub_neg_eq_add, map_add, H.Jinv_Jb]; abel
  rw [key]
  have h2 := H.Jinv_norm b (Cb H b (a - b) + Jb H b Δy)
  have hsq : sq ((a - b, Δy) : E × F) ≤ (1 + (L / μ) ^ 2) * ‖a - b‖ ^ 2 := by
    have := H.zs_sq a b
    simpa [zs, sq, Δy] using this
  have hμ := H.μpos
  calc ‖(Jinv H b).symm (Cb H b (a - b) + Jb H b Δy)‖ ≤ ‖Cb H b (a - b) + Jb H b Δy‖ / μ := h2
    _ ≤ ρ * sq ((a - b, Δy) : E × F) / μ := by gcongr
    _ ≤ ρ * ((1 + (L / μ) ^ 2) * ‖a - b‖ ^ 2) / μ := by
        gcongr; exact H.ρnn
    _ = (ρ / μ) * (1 + (L / μ) ^ 2) * ‖a - b‖ ^ 2 := by ring

end Hyp

end OracleTemplate.HessianNcsc
