import LongTails.Proofs.RecursiveEnvelopeGeometry
import LongTails.Proofs.SharpDistanceEnergy
import LongTails.Algorithms.SharpEnvelope

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SharpDistanceGeometry

open RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def shifted (f : E → ℝ) (g : E → E) (p x : E) : ℝ :=
  f x - f p - ⟪g p, x - p⟫

lemma shifted_model {L : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (p : E) : Model L (shifted f g p) (fun x => g x - g p) := by
  refine ⟨h.pos, ?_, ?_⟩
  · intro x y
    have hh := h.lower x y
    have he : ⟪g p, y - p⟫ = ⟪g p, x - p⟫ + ⟪g p, y - x⟫ := by
      rw [← inner_add_right]
      congr 1
      abel
    dsimp [shifted]
    rw [inner_sub_left, he]
    linarith
  · intro x y
    have hh := h.upper x y
    have he : ⟪g p, y - p⟫ = ⟪g p, x - p⟫ + ⟪g p, y - x⟫ := by
      rw [← inner_add_right]
      congr 1
      abel
    dsimp [shifted]
    rw [inner_sub_left, he]
    linarith

lemma shifted_nonneg {L : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (p x : E) : 0 ≤ shifted f g p x := by
  have hh := h.lower p x
  dsimp [shifted]
  linarith

lemma shifted_self (f : E → ℝ) (g : E → E) (p : E) : shifted f g p p = 0 := by
  simp [shifted]

lemma model_convex_combination {L : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (x p : E) :
    f ((1 - a) • x + a • p) ≤ (1 - a) * f x + a * f p := by
  let y := (1 - a) • x + a • p
  have hx := mul_le_mul_of_nonneg_left (h.lower y x) (sub_nonneg.mpr ha1)
  have hp := mul_le_mul_of_nonneg_left (h.lower y p) ha
  have he : (1 - a) * ⟪g y, x - y⟫ + a * ⟪g y, p - y⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hv : (1 - a) • (x - y) + a • (p - y) = 0 := by dsimp [y]; module
    rw [hv, inner_zero_right]
  change f y ≤ _
  nlinarith only [hx, hp, he]

lemma shifted_gap [CompleteSpace E] {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (c x : E) :
    shifted f g (prox g μ c) x + μ / 2 * ‖x - prox g μ c‖ ^ 2 =
      regularized f μ c x - envelope f g μ c := by
  let p := prox g μ c
  have hs := h.prox_stationary hμ c
  have hg : g p = -(μ • (p - c)) := eq_neg_of_add_eq_zero_left hs
  have hn := squared_shift p x c
  change f x - f p - ⟪g p, x - p⟫ + μ / 2 * ‖x - p‖ ^ 2 =
    (f x + μ / 2 * ‖x - c‖ ^ 2) - (f p + μ / 2 * ‖p - c‖ ^ 2)
  rw [hg, inner_neg_left, real_inner_smul_left, hn]
  ring

lemma noisy_descent {L : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (y e : E) :
    f (y - (1 / L) • (g y + e)) ≤ f y - ‖g y‖ ^ 2 / (2 * L) + ‖e‖ ^ 2 / (2 * L) := by
  have hh := h.upper y (y - (1 / L) • (g y + e))
  have hv : y - (1 / L) • (g y + e) - y = -((1 / L) • (g y + e)) := by abel
  rw [hv, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inner_add_right, real_inner_self_eq_norm_sq,
    norm_add_sq_real] at hh
  have he : f y - (1 / L) * (‖g y‖ ^ 2 + ⟪g y, e⟫) +
      L / 2 * ((1 / L) ^ 2 * (‖g y‖ ^ 2 + 2 * ⟪g y, e⟫ + ‖e‖ ^ 2)) =
      f y - ‖g y‖ ^ 2 / (2 * L) + ‖e‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  linarith only [hh, he]

lemma regularized_descent {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) {p : E} (hp : f p = 0) (y e : E) :
    f (y - (1 / (L + μ)) • (g y + μ • (y - p) + e)) ≤
      (1 - μ / (L + μ)) * f y - ‖g y‖ ^ 2 / (2 * (L + μ)) +
        ‖e‖ ^ 2 / (2 * (L + μ)) := by
  have hL := h.pos
  have hM : 0 < L + μ := by positivity
  have ha : 0 ≤ μ / (L + μ) := by positivity
  have ha1 : μ / (L + μ) ≤ 1 := (div_le_one hM).mpr (by linarith)
  let q := y - (1 / L) • (g y + e)
  have hc := model_convex_combination h ha ha1 q p
  rw [hp, mul_zero, add_zero] at hc
  have hd := mul_le_mul_of_nonneg_left (noisy_descent h y e) (sub_nonneg.mpr ha1)
  have hv : y - (1 / (L + μ)) • (g y + μ • (y - p) + e) =
      (1 - μ / (L + μ)) • q + (μ / (L + μ)) • p := by
    dsimp [q]
    have he : (1 - μ / (L + μ)) * (1 / L) = 1 / (L + μ) := by
      field_simp
      ring
    simp only [smul_sub, smul_add, smul_smul]
    rw [he]
    module
  rw [hv]
  have he : (1 - μ / (L + μ)) *
      (f y - ‖g y‖ ^ 2 / (2 * L) + ‖e‖ ^ 2 / (2 * L)) =
      (1 - μ / (L + μ)) * f y - ‖g y‖ ^ 2 / (2 * (L + μ)) +
        ‖e‖ ^ 2 / (2 * (L + μ)) := by
    field_simp
    ring
  rw [he] at hd
  exact hc.trans hd

noncomputable def energy (f : E → ℝ) (g : E → E) (μ : ℝ) (c : E) (s : E × E) : ℝ :=
  shifted f g (prox g μ c) s.1 + μ / 2 * ‖s.2 - prox g μ c‖ ^ 2

lemma energy_nonneg {L μ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 ≤ μ) (c : E) (s : E × E) :
    0 ≤ energy f g μ c s := by
  exact add_nonneg (shifted_nonneg h _ _) (mul_nonneg (by positivity) (sq_nonneg _))

lemma step_energy [CompleteSpace E] {L μ θ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hscale : μ / (L + μ) = 4 * θ ^ 2) (c : E) (s : E × E) (reply : E) :
    energy f g μ c (LongTails.Algorithms.SharpEnvelope.step (L + μ) μ θ s
      (reply + μ • (OracleTemplate.InexactGradient.query θ s - c))) ≤
      (1 - θ) * energy f g μ c s + θ / (2 * μ) * (1 + 14 * θ / 3) *
        ‖reply - g (OracleTemplate.InexactGradient.query θ s)‖ ^ 2 -
        3 * θ ^ 2 / (4 * μ) *
          ‖g (OracleTemplate.InexactGradient.query θ s) - g (prox g μ c)‖ ^ 2 := by
  let p := prox g μ c
  let y := OracleTemplate.InexactGradient.query θ s
  let G := g y - g p
  let e := reply - g y
  have hL := h.pos
  have hM : 0 < L + μ := by positivity
  have hp : g p = -(μ • (p - c)) := eq_neg_of_add_eq_zero_left (h.prox_stationary hμ c)
  have hv : G + μ • (y - p) + e = reply + μ • (y - c) := by
    dsimp [G, e]
    rw [hp]
    module
  have hy : (1 + θ) • y = s.1 + θ • s.2 := by
    dsimp [y, OracleTemplate.InexactGradient.query]
    rw [smul_smul, mul_one_div_cancel (by positivity : (1 + θ) ≠ 0), one_smul]
  have hy' : (1 + θ) • (y - p) = (s.1 - p) + θ • (s.2 - p) := by
    have he : (1 + θ) • (y - p) - ((s.1 - p) + θ • (s.2 - p)) =
        (1 + θ) • y - (s.1 + θ • s.2) := by module
    apply sub_eq_zero.mp
    rw [he, hy, sub_self]
  have hd := regularized_descent (shifted_model h p) hμ (shifted_self f g p) y e
  change shifted f g p (y - (1 / (L + μ)) • (G + μ • (y - p) + e)) ≤ _ at hd
  rw [hv, hscale] at hd
  have hr : 1 / (2 * (L + μ)) = 2 * θ ^ 2 / μ := by
    have hs := (div_eq_iff (ne_of_gt hM)).mp hscale
    field_simp
    nlinarith only [hs]
  simp only [div_eq_mul_inv] at hr
  have hd' : shifted f g p (y - (1 / (L + μ)) • (reply + μ • (y - c))) ≤
      (1 - 4 * θ ^ 2) * shifted f g p y - 2 * θ ^ 2 / μ * ‖G‖ ^ 2 +
        2 * θ ^ 2 / μ * ‖e‖ ^ 2 := by
    change _ ≤ (1 - 4 * θ ^ 2) * shifted f g p y - ‖G‖ ^ 2 / (2 * (L + μ)) +
      ‖e‖ ^ 2 / (2 * (L + μ)) at hd
    simp only [div_eq_mul_inv] at hd ⊢
    nlinarith only [hd, congrArg (fun a => a * ‖G‖ ^ 2) hr,
      congrArg (fun a => a * ‖e‖ ^ 2) hr]
  have hz : shifted f g p y ≤ ⟪G, y - p⟫ := by
    have hh := (shifted_model h p).lower y p
    rw [shifted_self] at hh
    change shifted f g p y + ⟪G, p - y⟫ ≤ 0 at hh
    rw [← neg_sub y p, inner_neg_right] at hh
    linarith
  have hc : shifted f g p y + ⟪G, (s.1 - p) - (y - p)⟫ ≤ shifted f g p s.1 := by
    have he : (s.1 - p) - (y - p) = s.1 - y := by abel
    rw [he]
    exact (shifted_model h p).lower y s.1
  have hh := SharpDistanceEnergy.shifted_energy hμ hθ hθ1 hy'
    (shifted_nonneg h p y) hz hc hd'
  have he : (1 - θ) • s.2 + θ • y - (θ / μ) • (reply + μ • (y - c)) - p =
      (1 - θ) • (s.2 - p) - (θ / μ) • (G + e) := by
    rw [← hv]
    have hm : θ / μ * μ = θ := div_mul_cancel₀ θ hμ.ne'
    simp only [smul_add, smul_smul, hm]
    module
  simpa only [energy, LongTails.Algorithms.SharpEnvelope.step, he, p, y, G, e] using hh

lemma relative_step [CompleteSpace E] {L μ θ β τ : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hμ : 0 < μ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 8) (hsmall : θ ≤ τ / 8)
    (hnoise : β ^ 2 ≤ τ * θ / 2) (hscale : μ / (L + μ) = 4 * θ ^ 2)
    (c : E) (s : E × E) (reply : E)
    (herr : ‖reply - g (OracleTemplate.InexactGradient.query θ s)‖ ≤
      β * ‖g (OracleTemplate.InexactGradient.query θ s)‖) :
    energy f g μ c (LongTails.Algorithms.SharpEnvelope.step (L + μ) μ θ s
      (reply + μ • (OracleTemplate.InexactGradient.query θ s - c))) ≤
      (1 - θ) * energy f g μ c s +
        θ / (2 * μ) * (1 + τ) ^ 2 * β ^ 2 * ‖g (prox g μ c)‖ ^ 2 := by
  have ht1 : θ ≤ 1 := by linarith
  have he := step_energy h hμ hθ.le ht1 hscale c s reply
  have herr' : ‖reply - g (OracleTemplate.InexactGradient.query θ s)‖ ≤
      β * ‖g (prox g μ c) +
        (g (OracleTemplate.InexactGradient.query θ s) - g (prox g μ c))‖ := by
    rw [add_sub_cancel]
    exact herr
  have hs := OracleTemplate.SharpEnvelope.relative_error_square hβ hτ herr' le_rfl
  exact SharpDistanceEnergy.absorb_shifted hμ hθ.le hτ he hs (by linarith)
    (SharpDistanceEnergy.noise_coefficient hμ hθ.le hτ hτ1 hnoise)

end LongTails.Proofs.SharpDistanceGeometry
