import LongTails.Proofs.CompositeGeneralizedLocal
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma tentative_displacement {a G J d : ℝ}
    (ha : 0 ≤ a) (hG : 0 ≤ G) (hJ : 0 ≤ J)
    (h : d ^ 2 / 2 ≤ a * G * d + a * J) :
    d ≤ 2 * a * G + Real.sqrt (2 * a * J) := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * a * J by positivity)
  have hn := Real.sqrt_nonneg (2 * a * J)
  by_contra! hh
  have hp : 0 < d - (2 * a * G + Real.sqrt (2 * a * J)) := by linarith
  have haG : 0 ≤ a * G := mul_nonneg ha hG
  have hprod := mul_pos hp (show 0 < d + Real.sqrt (2 * a * J) by nlinarith only [hh, hn, haG])
  nlinarith [mul_nonneg (show 0 ≤ a * G by positivity) hn]

lemma model_gradient_bound {h : E → ℝ} {x g : E} {M H Δ : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hΔ : 0 < Δ) (hHM : H * Δ ≤ M)
    (hnonneg : ∀ v, 0 ≤ h v) (hx : h x ≤ Δ)
    (hmodel : ∀ v, Real.sqrt H * ‖v - x‖ ≤ 1 →
      h v ≤ h x + ⟪g, v - x⟫ + M * ‖v - x‖ ^ 2) :
    ‖g‖ ^ 2 ≤ 16 * M * Δ := by
  let G := ‖g‖
  have hG : 0 ≤ G := norm_nonneg _
  by_contra! hbad
  have hGp : 0 < G := by dsimp [G]; nlinarith [mul_nonneg hM hΔ.le]
  have hrad : 2 * Real.sqrt H * Δ < G := by
    have hs : (Real.sqrt H * Δ) ^ 2 = H * Δ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hH]
    have ht := mul_le_mul_of_nonneg_right hHM hΔ.le
    have hh : (2 * Real.sqrt H * Δ) ^ 2 < G ^ 2 := by
      change 16 * M * Δ < G ^ 2 at hbad
      nlinarith [mul_nonneg hM hΔ.le]
    exact (sq_lt_sq₀ (by positivity) hG).mp hh
  let t := 2 * Δ / G ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hn : ‖x - t • g - x‖ = t * G := by
    rw [show x - t • g - x = -(t • g) by module]
    simp [norm_smul, abs_of_pos ht, G]
  have hr : Real.sqrt H * ‖x - t • g - x‖ ≤ 1 := by
    rw [hn]
    dsimp [t]
    field_simp
    nlinarith
  have hb := hmodel (x - t • g) hr
  rw [show x - t • g - x = -(t • g) by module,
    inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hb
  change h (x - t • g) ≤ h x - t * G ^ 2 + M * (t * G) ^ 2 at hb
  have he1 : t * G ^ 2 = 2 * Δ := by dsimp [t]; field_simp
  have he2 : (t * G) ^ 2 * G ^ 2 = 4 * Δ ^ 2 := by
    dsimp [t]; field_simp; ring
  rw [he1] at hb
  have hlow := hnonneg (x - t • g)
  have hh : Δ ≤ M * (t * G) ^ 2 := by linarith
  have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg G)
  have hbad' := mul_lt_mul_of_pos_left hbad hΔ
  nlinarith [mul_nonneg hM hΔ.le]

noncomputable def model (ψ : E → ℝ) (x0 : E) (A : ℝ) (v : E) (c : ℝ)
    (u : E) : ℝ := ‖u - x0‖ ^ 2 / 2 + ⟪v, u - x0⟫ + A * ψ u + c

lemma model_growth {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q)
    (hψ : ConvexOn ℝ Q ψ) {x0 z u v : E} {A c : ℝ} (hA : 0 ≤ A)
    (hz : z ∈ Q) (hu : u ∈ Q) (hm : IsMinOn (model ψ x0 A v c) Q z) :
    model ψ x0 A v c z + ‖u - z‖ ^ 2 / 2 ≤ model ψ x0 A v c u := by
  have hc : ConvexOn ℝ Q (fun w => A * ψ w) := by
    simpa only [smul_eq_mul] using hψ.smul hA
  have hm' : IsMinOn (fun w => ‖w - x0‖ ^ 2 / (2 * (1 : ℝ)) +
      ⟪v, w - x0⟫ + A * ψ w) Q z := by
    intro w hw
    have hh := hm hw
    dsimp [model] at hh ⊢
    linarith
  have hp := OracleTemplate.CompositeGeneralized.prox_three_point hQ hc
    (show (0 : ℝ) < 1 by norm_num) hz hm' hu
  simp only [one_mul] at hp
  have hi : ⟪v, z - u⟫ = ⟪v, z - x0⟫ - ⟪v, u - x0⟫ := by
    rw [← inner_sub_right]
    congr 1
    module
  rw [hi, norm_sub_rev x0 u, norm_sub_rev z u] at hp
  dsimp [model]
  linarith

lemma cumulative_step {f ψ Φ Ψ : E → ℝ} {x z p y w g : E} {A a M : ℝ}
    (hA : 0 ≤ A) (hB : 0 < A + a)
    (hy : (A + a) • y = A • x + a • z)
    (hw : (A + a) • w = A • x + a • p)
    (hx : f y + ⟪g, x - y⟫ ≤ f x)
    (hψ : (A + a) * ψ w ≤ A * ψ x + a * ψ p)
    (hupper : f w ≤ f y + ⟪g, w - y⟫ + M * ‖w - y‖ ^ 2)
    (hold : A * (f x + ψ x) ≤ Φ z)
    (hgrowth : Φ z + ‖p - z‖ ^ 2 / 2 ≤ Φ p)
    (hnew : Ψ p = Φ p + a * (f y + ⟪g, p - y⟫ + ψ p))
    (hweight : 2 * M * a ^ 2 ≤ A + a) :
    (A + a) * (f w + ψ w) ≤ Ψ p := by
  have hid : A • (x - y) + a • (p - y) = (A + a) • (w - y) := by
    calc
      _ = A • x + a • p - (A + a) • y := by module
      _ = _ := by rw [← hw]; module
  have hi := congrArg (fun v => ⟪g, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hdisp : (A + a) • (w - y) = a • (p - z) := by
    calc
      _ = (A + a) • w - (A + a) • y := by module
      _ = _ := by rw [hw, hy]; module
  have hn := congrArg (fun v : E => ‖v‖ ^ 2) hdisp
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hn
  have hsq : (A + a) * M * ‖w - y‖ ^ 2 ≤ ‖p - z‖ ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hweight (sq_nonneg ‖p - z‖)
    have he : (A + a) * ((A + a) * M * ‖w - y‖ ^ 2) =
        M * (a ^ 2 * ‖p - z‖ ^ 2) := by
      calc
        _ = M * ((A + a) ^ 2 * ‖w - y‖ ^ 2) := by ring
        _ = _ := by rw [hn]
    apply (mul_le_mul_iff_right₀ hB).mp
    nlinarith only [hmul, he]
  have hx' := mul_le_mul_of_nonneg_left hx hA
  have hu' := mul_le_mul_of_nonneg_left hupper hB.le
  rw [hnew]
  nlinarith only [hx', hu', hi, hsq, hold, hgrowth, hψ]

lemma model_shift (ψ : E → ℝ) (x0 v gs u s : E) (A c : ℝ) :
    model (fun w => ψ w - ψ s + ⟪gs, w - s⟫) x0 A (v - A • gs) c u =
      model ψ x0 A v c u + A * (-ψ s + ⟪gs, x0 - s⟫) := by
  simp only [model, inner_sub_left, real_inner_smul_left, inner_sub_right]
  ring

lemma nonsmooth_bound {j : E → ℝ} {Q : Set E} {x0 z v : E} {A c Δ R G : ℝ}
    (hA : 0 < A) (hG : 0 ≤ G) (hx0 : x0 ∈ Q)
    (hm : IsMinOn (model j x0 A v c) Q z)
    (hj : j x0 ≤ Δ) (hv : ‖v‖ ≤ A * G) (hd : ‖z - x0‖ ≤ 2 * R) :
    j z ≤ Δ + 2 * R * G := by
  have hh : model j x0 A v c z ≤ model j x0 A v c x0 := hm hx0
  simp only [model, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, inner_zero_right, zero_add] at hh
  have hi : -⟪v, z - x0⟫ ≤ 2 * A * R * G := by
    have hi := (neg_le_abs ⟪v, z - x0⟫).trans (abs_real_inner_le_norm _ _)
    have h₁ := mul_le_mul_of_nonneg_right hv (norm_nonneg (z - x0))
    have h₂ := mul_le_mul_of_nonneg_left hd (mul_nonneg hA.le hG)
    nlinarith only [hi, h₁, h₂]
  have hj' := mul_le_mul_of_nonneg_left hj hA.le
  apply (mul_le_mul_iff_right₀ hA).mp
  nlinarith [sq_nonneg ‖z - x0‖]

lemma model_append (ψ : E → ℝ) (x0 v g y u : E) (A a c fy : ℝ) :
    model ψ x0 (A + a) (v + a • g) (c + a * (fy - ⟪g, y - x0⟫)) u =
      model ψ x0 A v c u + a * (fy + ⟪g, u - y⟫ + ψ u) := by
  simp only [model, inner_add_left, real_inner_smul_left, inner_sub_right]
  ring

lemma cumulative_displacement_sq {Φ Ψ j : E → ℝ} {z p g : E} {a J G c : ℝ}
    (ha : 0 ≤ a)
    (hgrowth : Φ z + ‖p - z‖ ^ 2 / 2 ≤ Φ p)
    (hmin : Ψ p ≤ Ψ z)
    (hnew : ∀ u, Ψ u = Φ u + a * (c + ⟪g, u⟫ + j u))
    (hjp : 0 ≤ j p) (hjz : j z ≤ J) (hg : ‖g‖ ≤ G) :
    ‖p - z‖ ^ 2 / 2 ≤ a * G * ‖p - z‖ + a * J := by
  rw [hnew p, hnew z] at hmin
  have hi : ⟪g, z⟫ - ⟪g, p⟫ ≤ G * ‖p - z‖ := by
    rw [← inner_sub_right]
    have hh := (real_inner_le_norm g (z - p)).trans
      (mul_le_mul_of_nonneg_right hg (norm_nonneg (z - p)))
    simpa only [norm_sub_rev z p] using hh
  have hi' := mul_le_mul_of_nonneg_left hi ha
  have hj' := mul_le_mul_of_nonneg_left hjz ha
  have hpos := mul_nonneg ha hjp
  nlinarith only [hgrowth, hmin, hi', hj', hpos]

lemma initial_displacement {M Δ G d : ℝ} (hM : 0 < M) (hΔ : 0 < Δ)
    (hG : G ^ 2 ≤ 16 * M * Δ)
    (hstep : 8 * M * d ^ 2 ≤ G * d + Δ) : M * d ^ 2 ≤ Δ := by
  have hyoung : G * d ≤ 4 * M * d ^ 2 + Δ := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [sq_nonneg (G - 8 * M * d), hG]
  nlinarith only [hyoung, hstep, hΔ]

lemma initial_locality {M Δ G d H : ℝ} (hM : 0 < M) (hΔ : 0 < Δ)
    (hH : 0 ≤ H) (hHM : H * Δ ≤ M)
    (hG : G ^ 2 ≤ 16 * M * Δ)
    (hstep : 8 * M * d ^ 2 ≤ G * d + Δ) : Real.sqrt H * d ≤ 1 := by
  have hb := initial_displacement hM hΔ hG hstep
  have hh := mul_le_mul_of_nonneg_right hHM (sq_nonneg d)
  have hh' : H * d ^ 2 ≤ 1 := by nlinarith only [hh, hb, hΔ]
  have he := Real.sq_sqrt hH
  nlinarith [Real.sqrt_nonneg H]

lemma short_displacement {a G J d R : ℝ} (hR : 0 < R) (hd : 0 ≤ d)
    (hstep : d ^ 2 / 2 ≤ a * G * d + a * J)
    (hG : a * G ≤ R / 8) (hJ : a * J ≤ R ^ 2 / 4) : d ≤ R := by
  have hh := mul_le_mul_of_nonneg_right hG hd
  by_contra! hb
  have hp := mul_pos (show 0 < d - R by linarith) (show 0 < d + R by linarith)
  nlinarith

lemma localized_query_gap {hx hy jx jy jz G R M Δ τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 128)
    (hΔ : 0 < Δ) (hgap : hx + jx ≤ Δ)
    (hj : jz ≤ Δ + 2 * R * G) (hjx : 0 ≤ jx)
    (hquery : hy ≤ hx + 2 * R * τ * G + 4 * M * R ^ 2 * τ ^ 2)
    (hmix : jy ≤ (1 - τ) * jx + τ * jz)
    (hlinear : τ * R * G ≤ Δ / 16)
    (hquad : M * R ^ 2 * τ ^ 2 ≤ Δ / 16384) : hy + jy ≤ 2 * Δ := by
  have hh := mul_le_mul_of_nonneg_left hj hτ
  have hneg := mul_nonneg hτ hjx
  have ht := mul_le_mul_of_nonneg_right hτ1 hΔ.le
  nlinarith only [hgap, hquery, hmix, hh, hneg, ht, hlinear, hquad, hΔ]

lemma initial_model_lower {h j : E → ℝ} {Q : Set E} {x z g : E} {M H Δ : ℝ}
    (hM : 0 < M) (hH : 0 ≤ H) (hΔ : 0 < Δ) (hHM : H * Δ ≤ M)
    (hx : x ∈ Q) (hjz : 0 ≤ j z) (hjx : j x ≤ Δ)
    (hg : ‖g‖ ^ 2 ≤ 16 * M * Δ)
    (hm : IsMinOn (model j x (1 / (16 * M)) ((1 / (16 * M)) • g)
      ((1 / (16 * M)) * h x)) Q z)
    (hu : Real.sqrt H * ‖z - x‖ ≤ 1 →
      h z ≤ h x + ⟪g, z - x⟫ + M * ‖z - x‖ ^ 2) :
    (1 / (16 * M)) * (h z + j z) ≤
      model j x (1 / (16 * M)) ((1 / (16 * M)) • g)
        ((1 / (16 * M)) * h x) z := by
  have hmin : model j x (1 / (16 * M)) ((1 / (16 * M)) • g)
      ((1 / (16 * M)) * h x) z ≤
      model j x (1 / (16 * M)) ((1 / (16 * M)) • g)
        ((1 / (16 * M)) * h x) x := hm hx
  simp only [model, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, inner_zero_right, real_inner_smul_left, zero_add] at hmin
  have hi := (neg_le_abs ⟪g, z - x⟫).trans (abs_real_inner_le_norm g (z - x))
  have hs : 8 * M * ‖z - x‖ ^ 2 ≤ ‖g‖ * ‖z - x‖ + Δ := by
    have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 16 * M by positivity)
    field_simp at hh
    nlinarith only [hh, hi, hjz, hjx]
  have hr := initial_locality hM hΔ hH hHM hg hs
  have hh := mul_le_mul_of_nonneg_left (hu hr) (show 0 ≤ 1 / (16 * M) by positivity)
  dsimp [model]
  rw [real_inner_smul_left]
  have he : (1 / (16 * M)) * M = 1 / 16 := by field_simp
  nlinarith [sq_nonneg ‖z - x‖]

end LongTails.Proofs.CompositeGapGeometry
