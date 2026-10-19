import LongTails.Proofs.SymmetricReverseFisherGradient
import LongTails.Proofs.SymmetricReverseFisherGeometry
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherLoss
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherGradient
noncomputable def gdStep {p : Params} (μ : Space p) (η : ℝ) (x : Space p) : Space p :=
  x - η • gradient (loss μ) x
lemma gdStep_eq {p : Params} (μ x : Space p) (η : ℝ) :
    gdStep μ η x = (1 - η * alpha ‖x‖) • x + (η * ridgeForce ‖μ‖ ⟪x, μ⟫) • μ := by
  rw [gdStep, gradient_loss]
  module
lemma lambda_bounds {η r : ℝ} (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) :
    1 / 2 ≤ 1 - η * alpha r ∧ 1 - η * alpha r ≤ 1 := by
  have h0 := alpha_nonneg r
  have h4 := (alpha_le_four_min r).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0:ℝ) ≤ 4))
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h4 hη]
  · nlinarith [mul_nonneg hη h0]
lemma ridgeForce_abs_le_four (a c : ℝ) : |ridgeForce a c| ≤ 4 := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg (ridgeForce_nonneg hc)]
    exact ridgeForce_le_four hc
  · have hn := ridgeForce_nonneg (a := a) (neg_nonneg.mpr hc)
    have hb := ridgeForce_le_four (a := a) (neg_nonneg.mpr hc)
    rw [ridgeForce_neg] at hn hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
lemma gdStep_norm_bound {p : Params} (μ x : Space p) {η : ℝ}
    (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) :
    ‖gdStep μ η x‖ ≤ (1 - η * alpha ‖x‖) * ‖x‖ + 4 * η * ‖μ‖ := by
  rw [gdStep_eq]
  have hl := (lambda_bounds (r := ‖x‖) hη hη48).1
  calc
    _ ≤ ‖(1 - η * alpha ‖x‖) • x‖ + ‖(η * ridgeForce ‖μ‖ ⟪x, μ⟫) • μ‖ := norm_add_le _ _
    _ = (1 - η * alpha ‖x‖) * ‖x‖ + η * |ridgeForce ‖μ‖ ⟪x, μ⟫| * ‖μ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_mul, abs_of_nonneg hη]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (ridgeForce_abs_le_four ‖μ‖ ⟪x, μ⟫) (mul_nonneg hη (norm_nonneg μ))]
lemma gdStep_radius {p : Params} (μ x : Space p) {η : ℝ}
    (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) (hx : ‖x‖ ≤ 1 + 600 * ‖μ‖) :
    ‖gdStep μ η x‖ ≤ 1 + 600 * ‖μ‖ := by
  have hb := gdStep_norm_bound μ x hη hη48
  have hl := lambda_bounds (r := ‖x‖) hη hη48
  by_cases hr : ‖x‖ ≤ 1
  · have ht : (1 - η * alpha ‖x‖) * ‖x‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_right hl.2 (norm_nonneg x)).trans (by simpa using hr)
    nlinarith [norm_nonneg μ, mul_le_mul_of_nonneg_right hη48 (norm_nonneg μ)]
  · have hr1 : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hr)
    have hα := alpha_lower (norm_nonneg x)
    have hsq : 1 ≤ ‖x‖ ^ 2 := by nlinarith
    rw [min_eq_right hsq] at hα
    have hR := mul_le_mul_of_nonneg_left hx (show 0 ≤ 1 - η * alpha ‖x‖ by linarith)
    have hαR := mul_le_mul_of_nonneg_left hα (mul_nonneg hη (show 0 ≤ 1 + 600 * ‖μ‖ by positivity))
    nlinarith [norm_nonneg μ]
lemma gdStep_norm_multiplicative {p : Params} (μ x : Space p) {η : ℝ}
    (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) :
    ‖gdStep μ η x‖ ≤ (1 - η * alpha ‖x‖ + 4 * η * ‖μ‖ ^ 2) * ‖x‖ := by
  have hβ := beta_le_four ‖μ‖ ⟪x, μ⟫
  have hβ0 := beta_nonneg ‖μ‖ ⟪x, μ⟫
  have hi := abs_real_inner_le_norm x μ
  have hl := (lambda_bounds (r := ‖x‖) hη hη48).1
  have hB : |ridgeForce ‖μ‖ ⟪x, μ⟫| ≤ 4 * (‖x‖ * ‖μ‖) := by
    rw [← beta_mul, abs_mul, abs_of_nonneg hβ0]
    exact (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hi (by norm_num))
  rw [gdStep_eq]
  calc
    _ ≤ ‖(1 - η * alpha ‖x‖) • x‖ + ‖(η * ridgeForce ‖μ‖ ⟪x, μ⟫) • μ‖ := norm_add_le _ _
    _ = (1 - η * alpha ‖x‖) * ‖x‖ + η * |ridgeForce ‖μ‖ ⟪x, μ⟫| * ‖μ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_mul, abs_of_nonneg hη]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hB (mul_nonneg hη (norm_nonneg μ))]
lemma squared_multiplier_bound {l η a α : ℝ}
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hη : 0 ≤ η) (ha : 0 ≤ a)
    (heq : l = 1 - η * α) (hsmall : 16 * η * a ≤ 1) :
    (l + 4 * η * a) ^ 2 ≤ 1 - η * α + 9 * η * a := by
  have hlsq : l ^ 2 ≤ l := by nlinarith
  have hcross : 8 * l * η * a ≤ 8 * η * a := by nlinarith [mul_nonneg hη ha, mul_nonneg (sub_nonneg.mpr hl1) (mul_nonneg hη ha)]
  have hquart : 16 * η ^ 2 * a ^ 2 ≤ η * a := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (mul_nonneg hη ha)]
  nlinarith
lemma gdStep_norm_sq {p : Params} (μ x : Space p) {η : ℝ}
    (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) (hsmall : 16 * η * ‖μ‖ ^ 2 ≤ 1) :
    ‖gdStep μ η x‖ ^ 2 ≤
      (1 - η * min (‖x‖ ^ 2) 1 / 120 + 9 * η * ‖μ‖ ^ 2) * ‖x‖ ^ 2 := by
  have hn := gdStep_norm_multiplicative μ x hη hη48
  have hl := lambda_bounds (r := ‖x‖) hη hη48
  have hp : 0 ≤ 1 - η * alpha ‖x‖ + 4 * η * ‖μ‖ ^ 2 := by
    nlinarith [mul_nonneg hη (sq_nonneg ‖μ‖)]
  have hs := sq_le_sq₀ (norm_nonneg (gdStep μ η x)) (mul_nonneg hp (norm_nonneg x))
  have hsq := hs.mpr hn
  have hm := squared_multiplier_bound (show 0 ≤ 1 - η * alpha ‖x‖ by linarith)
    hl.2 hη (sq_nonneg ‖μ‖) rfl hsmall
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖x‖)
  have hα := mul_le_mul_of_nonneg_left (alpha_lower (norm_nonneg x)) hη
  have hc : 1 - η * alpha ‖x‖ + 9 * η * ‖μ‖ ^ 2 ≤
      1 - η * min (‖x‖ ^ 2) 1 / 120 + 9 * η * ‖μ‖ ^ 2 := by linarith
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
  nlinarith
lemma small_signal_capped {t t' a η ε : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48)
    (_hε : 0 < ε) (hε1 : ε ≤ 1) (haε : a ≤ ε / 10000)
    (hstep : t' ≤ (1 - η * min t 1 / 120 + 9 * η * a) * t) :
    t' ≤ max ((1 - η * ε / 960) * t) (ε / 2) := by
  by_cases htε : ε / 4 ≤ t
  · have hm : ε / 4 ≤ min t 1 := le_min htε (by linarith)
    have hc : 1 - η * min t 1 / 120 + 9 * η * a ≤ 1 - η * ε / 960 := by
      have h1 := mul_le_mul_of_nonneg_left hm hη
      have h2 := mul_le_mul_of_nonneg_left haε hη
      nlinarith
    exact (hstep.trans (mul_le_mul_of_nonneg_right hc ht)).trans (le_max_left _ _)
  · have hm : 0 ≤ min t 1 := le_min ht (by norm_num)
    have hnoise : 9 * η * a ≤ 1 := by
      have ha1 : a ≤ 1 / 10000 := by linarith
      have h1 := mul_le_mul_of_nonneg_left ha1 hη
      nlinarith
    have hc : 1 - η * min t 1 / 120 + 9 * η * a ≤ 2 := by
      nlinarith [mul_nonneg hη hm]
    have hb := mul_le_mul_of_nonneg_right hc ht
    exact (show t' ≤ ε / 2 by nlinarith).trans (le_max_right _ _)

lemma orthogonal_norm_sq {p : Params} (e v : Space p) (u : ℝ)
    (he : ‖e‖ = 1) (hv : ⟪v, e⟫ = 0) :
    ‖u • e + v‖ ^ 2 = u ^ 2 + ‖v‖ ^ 2 := by
  have hev : ⟪e, v⟫ = 0 := by rw [real_inner_comm, hv]
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, he, mul_one,
    real_inner_smul_left, hev, mul_zero, mul_zero, add_zero, sq_abs]
lemma coordinate_inner {p : Params} (e v : Space p) (u a : ℝ)
    (he : ‖e‖ = 1) (hv : ⟪v, e⟫ = 0) :
    ⟪u • e + v, a • e⟫ = a * u := by
  rw [inner_add_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he, real_inner_smul_right, hv]
  ring
lemma cone_preserved {u v l b η ζ : ℝ}
    (hu : 0 ≤ u) (_hv : 0 ≤ v) (hl : 0 ≤ l) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hζ : ζ ^ 2 ≤ 1) (hcone : v ^ 2 * ζ ^ 2 ≤ u ^ 2 * (1 - ζ ^ 2)) :
    (l * v) ^ 2 * ζ ^ 2 ≤ ((l + η * b) * u) ^ 2 * (1 - ζ ^ 2) := by
  have h := mul_le_mul_of_nonneg_left hcone (sq_nonneg l)
  have hprod : l * u ≤ (l + η * b) * u := by
    nlinarith [mul_nonneg (mul_nonneg hη hb) hu]
  have hsq : (l * u) ^ 2 ≤ ((l + η * b) * u) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hl hu) (by positivity)).mpr hprod
  have hmul := mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr hζ)
  nlinarith

lemma iterate_radius {p : Params} (μ x : Space p) {η : ℝ}
    (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) (hx : ‖x‖ ≤ 1 + 600 * ‖μ‖) (k : ℕ) :
    ‖(gdStep μ η)^[k] x‖ ≤ 1 + 600 * ‖μ‖ := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact gdStep_radius μ _ hη hη48 ih
lemma iterate_small_signal {p : Params} (μ x : Space p) {η ε : ℝ}
    (hη : 0 ≤ η) (hη48 : η ≤ 1 / 48) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (haε : ‖μ‖ ^ 2 ≤ ε / 10000) (k : ℕ) :
    ‖(gdStep μ η)^[k] x‖ ^ 2 ≤
      max ((1 - η * ε / 960) ^ k * ‖x‖ ^ 2) (ε / 2) := by
  have hsmall : 16 * η * ‖μ‖ ^ 2 ≤ 1 := by
    have ha1 : ‖μ‖ ^ 2 ≤ 1 / 10000 := by linarith
    have hh := mul_le_mul_of_nonneg_left ha1 hη
    nlinarith
  have hd : 0 ≤ 1 - η * ε / 960 := by
    have hh := mul_le_mul_of_nonneg_left hε1 hη
    nlinarith
  have hd1 : 1 - η * ε / 960 ≤ 1 := by nlinarith [mul_nonneg hη hε.le]
  have hs (j : ℕ) : ‖(gdStep μ η)^[j + 1] x‖ ^ 2 ≤
      max ((1 - η * ε / 960) * ‖(gdStep μ η)^[j] x‖ ^ 2) (ε / 2) := by
    rw [Function.iterate_succ_apply']
    exact small_signal_capped (sq_nonneg _) (sq_nonneg _) hη hη48 hε hε1 haε
      (gdStep_norm_sq μ _ hη hη48 hsmall)
  simpa using LongTails.Proofs.SymmetricReverseFisherGeometry.capped_decay
    (fun j => ‖(gdStep μ η)^[j] x‖ ^ 2) hd hd1 (by positivity) hs k
open LongTails.Proofs.SymmetricReverseFisherGeometry

lemma gdStep_coordinates {p : Params} (e v : Space p) (a u η : ℝ)
    (ha : 0 ≤ a) (he : ‖e‖ = 1) (hv : ⟪v, e⟫ = 0) :
    gdStep (a • e) η (u • e + v) =
      ((1 - η * alpha ‖u • e + v‖ + η * beta a (a * u) * a ^ 2) * u) • e +
      (1 - η * alpha ‖u • e + v‖) • v := by
  rw [gdStep_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, he, mul_one,
    coordinate_inner e v u a he hv, ← beta_mul]
  module
lemma strength_lower {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcR : c ≤ a * (1 + 600 * a)) :
    a ^ 2 / (100000 * (1 + a ^ 2)) ≤ beta a c * a ^ 2 := by
  have hd : 0 < 150 * (1 + a + c) := by positivity
  have hd' : 0 < 100000 * (1 + a ^ 2) := by positivity
  have hden : 150 * (1 + a + c) ≤ 100000 * (1 + a ^ 2) := by
    nlinarith [sq_nonneg (a - 1)]
  have hi : 1 / (100000 * (1 + a ^ 2)) ≤ 1 / (150 * (1 + a + c)) :=
    one_div_le_one_div_of_le hd hden
  have hb := hi.trans (beta_lower ha hc)
  simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hb (sq_nonneg a)
lemma strength_bounds {a : ℝ} (ha : 0 < a) :
    0 < a ^ 2 / (100000 * (1 + a ^ 2)) ∧
      a ^ 2 / (100000 * (1 + a ^ 2)) ≤ min (a ^ 2) 1 := by
  have hd : 0 < 100000 * (1 + a ^ 2) := by positivity
  constructor
  · positivity
  · apply le_min
    · apply (div_le_iff₀ hd).mpr
      nlinarith [sq_nonneg (a ^ 2)]
    · apply (div_le_iff₀ hd).mpr
      nlinarith [sq_nonneg a]

lemma small_signal_accuracy {p : Params} (μ x : Space p) {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ‖x‖ ^ 2 ≤ ε / 2) (hμ : ‖μ‖ ^ 2 ≤ ε / 10000) :
    ‖x - μ‖ ^ 2 ≤ ε := by
  have hn := norm_sub_le x μ
  have hs := (sq_le_sq₀ (norm_nonneg (x - μ)) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖x‖ / 2 - 2 * ‖μ‖)]
lemma iterate_small_signal_accuracy {p : Params} (μ x : Space p) {η ε : ℝ}
    (hη : 0 < η) (hη48 : η ≤ 1 / 48) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : ‖x‖ = 1) (haε : ‖μ‖ ^ 2 ≤ ε / 10000) {k : ℕ}
    (hk : 960 / (η * ε) * Real.log (4 / ε) ≤ k) :
    ‖(gdStep μ η)^[k] x - μ‖ ^ 2 ≤ ε := by
  have ht : 0 < η * ε / 960 := by positivity
  have ht1 : η * ε / 960 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hε1 hη.le
    nlinarith
  have hk' : Real.log (4 / ε) / (η * ε / 960) ≤ k := by
    convert hk using 1
    field_simp
  have hp := power_small_of_log ht ht1 hε hk'
  have hb := iterate_small_signal μ x hη.le hη48 hε hε1 haε k
  rw [hx, one_pow, mul_one] at hb
  apply small_signal_accuracy μ _ hε.le _ haε
  exact hb.trans (max_le (by linarith) le_rfl)

lemma cone_radius {u v r ζ : ℝ} (hu : 0 ≤ u) (hr : 0 ≤ r) (hζ : 0 ≤ ζ)
    (hnorm : r ^ 2 = u ^ 2 + v ^ 2)
    (hcone : v ^ 2 * ζ ^ 2 ≤ u ^ 2 * (1 - ζ ^ 2)) : ζ * r ≤ u := by
  have hs : (ζ * r) ^ 2 ≤ u ^ 2 := by
    nlinarith [congrArg (fun t : ℝ => t * ζ ^ 2) hnorm]
  exact (sq_le_sq₀ (mul_nonneg hζ hr) hu).mp hs
lemma escape_floor_step {u u' r ρ ζ : ℝ}
    (hfloor : ρ * ζ / 2 ≤ u) (hcone : ζ * r ≤ u) (hζ : 0 ≤ ζ)
    (hhalf : u / 2 ≤ u') (hgrow : r ≤ ρ → u ≤ u') :
    ρ * ζ / 2 ≤ u' := by
  rcases le_total r ρ with hr | hr
  · exact hfloor.trans (hgrow hr)
  · have h := mul_le_mul_of_nonneg_left hr hζ
    linarith
lemma phase_two_capped {u u' r ell g : ℝ} (hell : 0 ≤ ell)
    (hu : 0 ≤ u) (_hr : 0 ≤ r) (hcone : r ^ 2 ≤ 2 * u ^ 2)
    (hhalf : u / 2 ≤ u') (hgrow : r ^ 2 ≤ 8 * ell ^ 2 → g * u ≤ u') :
    min (g * u) ell ≤ u' := by
  by_cases hsmall : u ≤ 2 * ell
  · have hsq : r ^ 2 ≤ 8 * ell ^ 2 := by nlinarith
    exact (min_le_left _ _).trans (hgrow hsq)
  · exact (min_le_right _ _).trans (by linarith)

end LongTails.Proofs.SymmetricReverseFisherDynamics
