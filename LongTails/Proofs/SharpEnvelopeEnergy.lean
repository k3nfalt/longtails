import LongTails.Proofs.InexactAcceleratedStep

open scoped RealInnerProductSpace

namespace OracleTemplate.SharpEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weighted_norm_identity (a b : E) (t : ℝ) :
    ‖(1 - t) • a + t • b‖ ^ 2 =
      (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, norm_sub_sq_real]
  ring

lemma inner_young (e v : E) {c : ℝ} (hc : 0 < c) :
    -⟪e, v⟫ ≤ c / 2 * ‖v‖ ^ 2 + 1 / (2 * c) * ‖e‖ ^ 2 := by
  have hs := sq_nonneg ‖v + (1 / c) • e‖
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm e v] at hs
  have hm := mul_nonneg (show 0 ≤ c / 2 by positivity) hs
  have hid : c / 2 * (‖v‖ ^ 2 + 2 * (1 / c * ⟪e, v⟫) + (1 / c) ^ 2 * ‖e‖ ^ 2) =
      c / 2 * ‖v‖ ^ 2 + ⟪e, v⟫ + 1 / (2 * c) * ‖e‖ ^ 2 := by
    field_simp
  rw [hid] at hm
  linarith

lemma raw_energy {fx fy fp fx' L μ θ : ℝ} {x z p y g G : E}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hyq : (1 + θ) • y = x + θ • z)
    (a1 : fx' ≤ fy + ⟪G, y - (1 / L) • g - y⟫ +
      L / 2 * ‖y - (1 / L) • g - y‖ ^ 2)
    (a2 : fy + ⟪G, p - y⟫ + μ / 2 * ‖p - y‖ ^ 2 ≤ fp)
    (a3 : fy + ⟪G, x - y⟫ + μ / 2 * ‖x - y‖ ^ 2 ≤ fx) :
    fx' - fp + μ / 2 * ‖(1 - θ) • z + θ • y - (θ / μ) • g - p‖ ^ 2 -
      (1 - θ) * (fx - fp + μ / 2 * ‖z - p‖ ^ 2) ≤
      -(μ * θ * (1 - θ ^ 2) / 2 * ‖y - z‖ ^ 2) -
      ‖G‖ ^ 2 / (2 * L) + ‖g - G‖ ^ 2 / (2 * L) +
      θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 -
      θ * ⟪g - G, (z - p) + θ • (y - z)⟫ := by
  let w : E := (1 - θ) • (z - p) + θ • (y - p)
  have hxy : x - y = θ • (y - z) := by
    have h := hyq
    have hid : x - y - θ • (y - z) = x + θ • z - (1 + θ) • y := by module
    apply sub_eq_zero.mp
    rw [hid, h, sub_self]
  have hw : w = (z - p) + θ • (y - z) := by dsimp [w]; module
  have hmix : θ • w = θ • (y - p) + (1 - θ) • (y - x) := by
    have hid : θ • w - (θ • (y - p) + (1 - θ) • (y - x)) =
        (1 - θ) • (x + θ • z - (1 + θ) • y) := by dsimp [w]; module
    apply sub_eq_zero.mp
    rw [hid, hyq, sub_self, smul_zero]
  have hi : θ * ⟪G, w⟫ = θ * ⟪G, y - p⟫ + (1 - θ) * ⟪G, y - x⟫ := by
    rw [← inner_smul_right, hmix, inner_add_right, inner_smul_right, inner_smul_right]
  have hpinner : ⟪G, p - y⟫ = -⟪G, y - p⟫ := by rw [← neg_sub, inner_neg_right]
  have hxinner : ⟪G, x - y⟫ = -⟪G, y - x⟫ := by rw [← neg_sub, inner_neg_right]
  have hxnorm : ‖x - y‖ ^ 2 = θ ^ 2 * ‖y - z‖ ^ 2 := by
    rw [hxy, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hpinner, norm_sub_rev p y] at a2
  rw [hxinner, hxnorm] at a3
  have b2 := mul_le_mul_of_nonneg_left a2 hθ0
  have b3 := mul_le_mul_of_nonneg_left a3 (show 0 ≤ 1 - θ by linarith)
  have hconv : fy - (1 - θ) * fx - θ * fp ≤ θ * ⟪G, w⟫ -
      μ / 2 * (θ * ‖y - p‖ ^ 2 + (1 - θ) * θ ^ 2 * ‖y - z‖ ^ 2) := by
    rw [hi]
    linarith only [b2, b3]
  have hdesc : fx' ≤ fy - ‖G‖ ^ 2 / (2 * L) + ‖g - G‖ ^ 2 / (2 * L) := by
    have he : y - (1 / L) • g - y = -((1 / L) • g) := by abel
    rw [he, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs] at a1
    rw [norm_sub_sq_real, real_inner_comm G g]
    have hid : fy + -(1 / L * ⟪G, g⟫) + L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) =
        fy - ‖G‖ ^ 2 / (2 * L) + (‖g‖ ^ 2 - 2 * ⟪G, g⟫ + ‖G‖ ^ 2) / (2 * L) := by
      field_simp
      ring
    linarith
  have hwnorm : ‖w‖ ^ 2 = (1 - θ) * ‖z - p‖ ^ 2 + θ * ‖y - p‖ ^ 2 -
      θ * (1 - θ) * ‖y - z‖ ^ 2 := by
    dsimp only [w]
    rw [weighted_norm_identity]
    have hid : z - p - (y - p) = z - y := by abel
    rw [hid, norm_sub_rev z y]
  have hz : (1 - θ) • z + θ • y - (θ / μ) • g - p = w - (θ / μ) • g := by
    dsimp [w]; module
  have hg : ⟪g, w⟫ = ⟪G, w⟫ + ⟪g - G, w⟫ := by
    rw [← inner_add_left, add_sub_cancel]
  have hstep : μ / 2 * ‖(1 - θ) • z + θ • y - (θ / μ) • g - p‖ ^ 2 =
      μ / 2 * ‖w‖ ^ 2 - θ * (⟪G, w⟫ + ⟪g - G, w⟫) + θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 := by
    rw [hz, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm g w, hg]
    field_simp
  rw [hstep, hwnorm, ← hw]
  linarith only [hdesc, hconv]

lemma sharp_energy {fx fy fp fx' L μ θ : ℝ} {x z p y g G : E}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hscale : θ ^ 2 / μ ≤ 1 / (4 * L))
    (hyq : (1 + θ) • y = x + θ • z)
    (a1 : fx' ≤ fy + ⟪G, y - (1 / L) • g - y⟫ +
      L / 2 * ‖y - (1 / L) • g - y‖ ^ 2)
    (a2 : fy + ⟪G, p - y⟫ + μ / 2 * ‖p - y‖ ^ 2 ≤ fp)
    (a3 : fy + ⟪G, x - y⟫ + μ / 2 * ‖x - y‖ ^ 2 ≤ fx) :
    fx' - fp + μ / 2 * ‖(1 - θ) • z + θ • y - (θ / μ) • g - p‖ ^ 2 -
      (fx - fp + μ / 2 * ‖z - p‖ ^ 2) + θ * (fx - fp) ≤
      (θ / (2 * μ) + 3 / (4 * L) + θ ^ 3 / (2 * μ * (1 - θ ^ 2))) *
        ‖g - G‖ ^ 2 - ‖G‖ ^ 2 / (4 * L) := by
  have ht : 0 < 1 - θ ^ 2 := by nlinarith
  have hr := raw_energy hL hμ hθ0.le hθ1.le hyq a1 a2 a3
  have he1 := mul_le_mul_of_nonneg_left (inner_young (g - G) (z - p) hμ) hθ0.le
  have hc : 0 < μ * (1 - θ ^ 2) / θ := by positivity
  have he2 := mul_le_mul_of_nonneg_left
    (inner_young (g - G) (y - z) hc) (sq_nonneg θ)
  have hid1 : θ * (μ / 2 * ‖z - p‖ ^ 2 + 1 / (2 * μ) * ‖g - G‖ ^ 2) =
      θ * μ / 2 * ‖z - p‖ ^ 2 + θ / (2 * μ) * ‖g - G‖ ^ 2 := by ring
  have hid2 : θ ^ 2 * (μ * (1 - θ ^ 2) / θ / 2 * ‖y - z‖ ^ 2 +
      1 / (2 * (μ * (1 - θ ^ 2) / θ)) * ‖g - G‖ ^ 2) =
      μ * θ * (1 - θ ^ 2) / 2 * ‖y - z‖ ^ 2 +
      θ ^ 3 / (2 * μ * (1 - θ ^ 2)) * ‖g - G‖ ^ 2 := by
    field_simp
  rw [hid1] at he1
  rw [hid2] at he2
  rw [inner_add_right, inner_smul_right] at hr
  have hg : ‖g‖ ^ 2 ≤ 2 * ‖G‖ ^ 2 + 2 * ‖g - G‖ ^ 2 := by
    have hi := InexactGradient.two_inner_le G (g - G)
    have he : ‖g‖ ^ 2 = ‖G‖ ^ 2 + 2 * ⟪G, g - G⟫ + ‖g - G‖ ^ 2 := by
      rw [← norm_add_sq_real, add_sub_cancel]
    linarith
  have hgm := mul_le_mul_of_nonneg_left hg (show 0 ≤ θ ^ 2 / (2 * μ) by positivity)
  have hbound := mul_le_mul_of_nonneg_right hscale
    (show 0 ≤ ‖G‖ ^ 2 + ‖g - G‖ ^ 2 by positivity)
  have heq : θ ^ 2 / (2 * μ) * (2 * ‖G‖ ^ 2 + 2 * ‖g - G‖ ^ 2) =
      θ ^ 2 / μ * (‖G‖ ^ 2 + ‖g - G‖ ^ 2) := by ring
  rw [heq] at hgm
  ring_nf at hr he1 he2 hgm hbound ⊢
  linarith only [hgm, hbound, he1, he2, hr]

omit [InnerProductSpace ℝ E] in
lemma relative_error_square {e a w G : E} {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 < τ)
    (he : ‖e‖ ≤ β * ‖w + a‖) (ha : ‖a‖ ≤ ‖G‖) :
    ‖e‖ ^ 2 ≤ (1 + τ) * β ^ 2 * ‖w‖ ^ 2 + (1 + 1 / τ) * β ^ 2 * ‖G‖ ^ 2 := by
  have hn : ‖w + a‖ ≤ ‖w‖ + ‖G‖ := (norm_add_le w a).trans (by linarith)
  have he' : ‖e‖ ≤ β * (‖w‖ + ‖G‖) :=
    he.trans (mul_le_mul_of_nonneg_left hn hβ)
  have hs := pow_le_pow_left₀ (norm_nonneg e) he' 2
  have hid : (1 + τ) * β ^ 2 * ‖w‖ ^ 2 + (1 + 1 / τ) * β ^ 2 * ‖G‖ ^ 2 -
      (β * (‖w‖ + ‖G‖)) ^ 2 = β ^ 2 / τ * (τ * ‖w‖ - ‖G‖) ^ 2 := by
    field_simp
    ring
  have hp : 0 ≤ β ^ 2 / τ * (τ * ‖w‖ - ‖G‖) ^ 2 := by positivity
  linarith

lemma absorb_relative_error {V V' H A θ L β τ r e G : ℝ}
    (hA : 0 ≤ A)
    (henergy : V' - V + θ * H ≤ A * e ^ 2 - G ^ 2 / (4 * L))
    (herr : e ^ 2 ≤ (1 + τ) * β ^ 2 * r ^ 2 + (1 + 1 / τ) * β ^ 2 * G ^ 2)
    (habsorb : A * (1 + 1 / τ) * β ^ 2 ≤ 1 / (4 * L)) :
    V' - V + θ * H ≤ A * (1 + τ) * β ^ 2 * r ^ 2 := by
  have he := mul_le_mul_of_nonneg_left herr hA
  have hg := mul_le_mul_of_nonneg_right habsorb (sq_nonneg G)
  ring_nf at henergy he hg ⊢
  linarith only [henergy, he, hg]

end OracleTemplate.SharpEnvelope
