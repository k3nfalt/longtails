import LongTails.Proofs.SharpEnvelopeEnergy

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SharpDistanceEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma shifted_energy {fx fy fx' μ θ : ℝ} {x z y G e : E}
    (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hy : (1 + θ) • y = x + θ • z)
    (hfy : 0 ≤ fy) (hzero : fy ≤ ⟪G, y⟫)
    (hconv : fy + ⟪G, x - y⟫ ≤ fx)
    (hdesc : fx' ≤ (1 - 4 * θ ^ 2) * fy - 2 * θ ^ 2 / μ * ‖G‖ ^ 2 +
      2 * θ ^ 2 / μ * ‖e‖ ^ 2) :
    fx' + μ / 2 * ‖(1 - θ) • z - (θ / μ) • (G + e)‖ ^ 2 ≤
      (1 - θ) * (fx + μ / 2 * ‖z‖ ^ 2) +
        θ / (2 * μ) * (1 + 14 * θ / 3) * ‖e‖ ^ 2 -
        3 * θ ^ 2 / (4 * μ) * ‖G‖ ^ 2 := by
  have hxy : x - y = θ • (y - z) := by
    apply sub_eq_zero.mp
    have he : x - y - θ • (y - z) = x + θ • z - (1 + θ) • y := by module
    rw [he, hy, sub_self]
  rw [hxy, inner_smul_right, inner_sub_right] at hconv
  have hc := mul_le_mul_of_nonneg_left hconv (sub_nonneg.mpr hθ1)
  have hz := mul_le_mul_of_nonneg_left hzero (mul_nonneg hθ (sub_nonneg.mpr hθ1))
  have hf := mul_nonneg (sq_nonneg θ) hfy
  have hmix : (1 - 4 * θ ^ 2) * fy - (1 - θ) * fx ≤
      θ * (1 - θ) * ⟪G, z⟫ := by nlinarith only [hc, hz, hf]
  have hez := mul_le_mul_of_nonneg_left
    (OracleTemplate.SharpEnvelope.inner_young e z hμ)
    (mul_nonneg hθ (sub_nonneg.mpr hθ1))
  have hge := OracleTemplate.SharpEnvelope.inner_young (-e) G (c := (3 : ℝ) / 2)
    (by norm_num)
  simp only [inner_neg_left, neg_neg, norm_neg] at hge
  rw [real_inner_comm] at hge
  norm_num at hge
  have hge' := mul_le_mul_of_nonneg_left hge (show 0 ≤ θ ^ 2 / μ by positivity)
  have hn : μ / 2 * ‖(1 - θ) • z - (θ / μ) • (G + e)‖ ^ 2 =
      μ / 2 * (1 - θ) ^ 2 * ‖z‖ ^ 2 -
        θ * (1 - θ) * (⟪G, z⟫ + ⟪e, z⟫) +
        θ ^ 2 / (2 * μ) * (‖G‖ ^ 2 + 2 * ⟪G, e⟫ + ‖e‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
      inner_add_right, norm_add_sq_real, real_inner_comm z G, real_inner_comm z e]
    field_simp
  rw [hn]
  ring_nf at hdesc hmix hez hge' ⊢
  linarith only [hdesc, hmix, hez, hge']

lemma filter_coefficients {a θ : ℝ} (hθ : 0 < θ) (ha : θ ^ 2 ≤ a)
    (haθ : a ≤ θ) (hθ1 : θ < 1) :
    0 ≤ a / θ ∧ a / θ ≤ 1 ∧
    0 ≤ (1 - a) / (1 + θ) ∧ (1 - a) / (1 + θ) ≤ 1 - θ ∧
    (1 - a) / (1 + θ) * (a / θ) + (θ ^ 2 - a) / (θ * (1 + θ)) =
      (1 - (1 - a) / (1 + θ)) * (1 - a / θ) := by
  have ha0 : 0 ≤ a := (sq_nonneg θ).trans ha
  refine ⟨div_nonneg ha0 hθ.le, (div_le_one hθ).mpr haθ,
    div_nonneg (by linarith) (by positivity), ?_, ?_⟩
  · apply (div_le_iff₀ (show 0 < 1 + θ by positivity)).mpr
    nlinarith
  · field_simp
    ring

lemma filter_update {a μ θ : ℝ} {x z y g : E}
    (hy : (1 + θ) • y = x + θ • z) :
    (θ * (1 + θ)) • (y - (a / μ) • g) =
      (θ * (1 - a)) • x + (a * (1 + θ)) •
        ((1 - θ) • z + θ • y - (θ / μ) • g) + (θ ^ 2 - a) • z := by
  apply sub_eq_zero.mp
  have he : (θ * (1 + θ)) • (y - (a / μ) • g) -
      ((θ * (1 - a)) • x + (a * (1 + θ)) •
        ((1 - θ) • z + θ • y - (θ / μ) • g) + (θ ^ 2 - a) • z) =
      (θ * (1 - a)) • ((1 + θ) • y - (x + θ • z)) := by module
  rw [he, hy, sub_self, smul_zero]

lemma absorb_shifted {V V' μ θ β τ r e G : ℝ}
    (hμ : 0 < μ) (hθ : 0 ≤ θ) (hτ : 0 < τ)
    (henergy : V' ≤ (1 - θ) * V + θ / (2 * μ) * (1 + 14 * θ / 3) * e ^ 2 -
      3 * θ ^ 2 / (4 * μ) * G ^ 2)
    (herr : e ^ 2 ≤ (1 + τ) * β ^ 2 * r ^ 2 + (1 + 1 / τ) * β ^ 2 * G ^ 2)
    (hgain : 1 + 14 * θ / 3 ≤ 1 + τ)
    (habsorb : θ / (2 * μ) * (1 + τ) * (1 + 1 / τ) * β ^ 2 ≤
      3 * θ ^ 2 / (4 * μ)) :
    V' ≤ (1 - θ) * V + θ / (2 * μ) * (1 + τ) ^ 2 * β ^ 2 * r ^ 2 := by
  have hg := mul_le_mul_of_nonneg_left hgain (show 0 ≤ θ / (2 * μ) by positivity)
  have hg' := mul_le_mul_of_nonneg_right hg (sq_nonneg e)
  have he := mul_le_mul_of_nonneg_left herr
    (show 0 ≤ θ / (2 * μ) * (1 + τ) by positivity)
  have ha := mul_le_mul_of_nonneg_right habsorb (sq_nonneg G)
  ring_nf at henergy hg' he ha ⊢
  linarith only [henergy, hg', he, ha]

lemma noise_coefficient {μ θ τ β : ℝ} (hμ : 0 < μ)
    (hθ : 0 ≤ θ) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) :
    θ / (2 * μ) * (1 + τ) * (1 + 1 / τ) * β ^ 2 ≤ 3 * θ ^ 2 / (4 * μ) := by
  have hc : 0 ≤ θ / (2 * μ) * (1 + τ) * (1 + 1 / τ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hnoise hc
  have he : (θ / (2 * μ) * (1 + τ) * (1 + 1 / τ)) * (τ * θ / 2) =
      θ ^ 2 / (4 * μ) * (1 + τ) ^ 2 := by field_simp; ring
  rw [he] at hh
  have hs : (1 + τ) ^ 2 ≤ 3 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hs (show 0 ≤ θ ^ 2 / (4 * μ) by positivity)
  calc
    _ ≤ θ ^ 2 / (4 * μ) * 3 := hh.trans ht
    _ = _ := by ring

end LongTails.Proofs.SharpDistanceEnergy
