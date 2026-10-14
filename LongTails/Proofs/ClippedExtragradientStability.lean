import LongTails.Algorithms.ClippedExtragradient
import LongTails.Proofs.Clipping
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma extragradient_identity (x p g q e : E) (γ : ℝ) :
    ‖x - γ • (q + e) - p‖ ^ 2 =
      ‖x - p‖ ^ 2 - ‖γ • g‖ ^ 2 -
        2 * γ * ⟪q, x - γ • g - p⟫ + γ ^ 2 * ‖q - g‖ ^ 2 -
        2 * γ * ⟪e, x - γ • q - p⟫ + γ ^ 2 * ‖e‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm p x, real_inner_comm q x,
    real_inner_comm e x, real_inner_comm p q,
    real_inner_comm p e, real_inner_comm q g, real_inner_comm e q]
  ring

omit [InnerProductSpace ℝ E] in
lemma distance_split (x p s : E) :
    ‖x - p‖ ^ 2 ≤ 2 * ‖s‖ ^ 2 + 2 * ‖x - s - p‖ ^ 2 := by
  have h := norm_add_le s (x - s - p)
  have he : s + (x - s - p) = x - p := by abel
  rw [he] at h
  nlinarith [sq_nonneg (‖s‖ - ‖x - s - p‖), norm_nonneg (x - p),
    norm_nonneg s, norm_nonneg (x - s - p)]

omit [InnerProductSpace ℝ E] in
lemma small_step_drift {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hcap : γ * μ ≤ 1 / 4) (x p s : E) :
    γ * μ * ‖x - p‖ ^ 2 ≤
      1 / 2 * ‖s‖ ^ 2 + 2 * γ * μ * ‖x - s - p‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (distance_split x p s) (mul_nonneg hγ hμ)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcap) (sq_nonneg ‖s‖)]

omit [InnerProductSpace ℝ E] in
lemma stepSize_pos {b S : ℝ} (hS : 0 < S) (g : E) :
    0 < stepSize b S g := by
  unfold stepSize
  have : 0 < max S (b * ‖g‖) := lt_of_lt_of_le hS (le_max_left _ _)
  positivity

omit [InnerProductSpace ℝ E] in
lemma stepSize_le {b S : ℝ} (hS : 0 < S) (g : E) :
    stepSize b S g ≤ 1 / (16 * S) := by
  unfold stepSize
  exact one_div_le_one_div_of_le (by positivity) (by gcongr; exact le_max_left _ _)

omit [InnerProductSpace ℝ E] in
lemma stepSize_mul_norm_le {b S : ℝ} (hb : 0 < b) (hS : 0 < S) (g : E) :
    stepSize b S g * ‖g‖ ≤ 1 / (16 * b) := by
  have hm : 0 < max S (b * ‖g‖) := lt_of_lt_of_le hS (le_max_left _ _)
  unfold stepSize
  apply (le_div_iff₀ (by positivity : 0 < 16 * b)).mpr
  calc
    (1 / (16 * max S (b * ‖g‖)) * ‖g‖) * (16 * b) =
        (16 * b * ‖g‖) / (16 * max S (b * ‖g‖)) := by ring
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by
      nlinarith [le_max_right S (b * ‖g‖)])

lemma finishStep_distance {d : ℝ} (hd : 0 ≤ d) (γ : ℝ) (c x g p : E)
    (hp : ‖p - c‖ ≤ 2 * d) :
    ‖finishStep d γ c x g - p‖ ≤ ‖x - γ • g - p‖ := by
  have h := norm_clip_sub_le (by positivity : 0 ≤ 2 * d) hp (x - γ • g - c)
  have he : finishStep d γ c x g - p = clip (2 * d) (x - γ • g - c) - (p - c) := by
    unfold finishStep
    abel
  rw [he]
  convert h using 1
  congr 1
  abel

lemma finishStep_ball {d : ℝ} (hd : 0 ≤ d) (γ : ℝ) (c x g : E) :
    ‖finishStep d γ c x g - c‖ ≤ 2 * d := by
  simpa only [finishStep, add_sub_cancel_left] using
    norm_clip_le (by positivity : 0 ≤ 2 * d) (x - γ • g - c)

lemma clipped_drift {b S μ d : ℝ} (hb : 0 < b) (hS : 0 < S)
    (hμ : 0 ≤ μ) (hd : 0 ≤ d) (hμS : μ ≤ S) (hscale : μ * b ^ 2 * d ^ 2 ≤ S)
    (x p g : E) (hx : ‖x - p‖ ≤ 3 * d) :
    μ / (4608 * S) * ‖x - p‖ ^ 2 ≤
      1 / 2 * ‖stepSize b S g • g‖ ^ 2 +
        2 * stepSize b S g * μ * ‖halfStep b S x g - p‖ ^ 2 := by
  have hγ := stepSize_pos (b := b) hS g
  by_cases hsmall : b * ‖g‖ ≤ S
  · have he : stepSize b S g = 1 / (16 * S) := by
      simp only [stepSize, max_eq_left hsmall]
    have hcap : stepSize b S g * μ ≤ 1 / 4 := by
      rw [he]
      have hh : μ / (16 * S) ≤ 1 / 4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      convert hh using 1; ring
    have h := small_step_drift hγ.le hμ hcap x p (stepSize b S g • g)
    have hc : μ / (4608 * S) ≤ stepSize b S g * μ := by
      rw [he]
      have hh : μ / (4608 * S) ≤ μ / (16 * S) :=
        div_le_div_of_nonneg_left hμ (by positivity) (by linarith)
      convert hh using 1; ring
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans h
  · have hbig : S ≤ b * ‖g‖ := le_of_lt (lt_of_not_ge hsmall)
    have hg : 0 < ‖g‖ := by nlinarith
    have he : ‖stepSize b S g • g‖ = 1 / (16 * b) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      unfold stepSize
      rw [max_eq_right hbig]
      field_simp
    have hrad : ‖x - p‖ ^ 2 ≤ 9 * d ^ 2 := by nlinarith [norm_nonneg (x - p)]
    have hh := mul_le_mul_of_nonneg_left hrad (mul_nonneg hμ (sq_nonneg b))
    have hp : μ * ‖x - p‖ ^ 2 * b ^ 2 ≤ 9 * S := by nlinarith
    have hc : μ / (4608 * S) * ‖x - p‖ ^ 2 ≤ 1 / (512 * b ^ 2) := by
      have hh : μ * ‖x - p‖ ^ 2 / (4608 * S) ≤ 1 / (512 * b ^ 2) :=
        (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)
      convert hh using 1; ring
    rw [he]
    have hid : 1 / (512 * b ^ 2) = 1 / 2 * (1 / (16 * b)) ^ 2 := by ring
    rw [hid] at hc
    exact hc.trans (le_add_of_nonneg_right (by positivity))

lemma clipped_local_error {a b S : ℝ} (hb : 0 < b) (hS : 0 < S)
    (haS : a ≤ S) (H : E → E) (x g : E)
    (hl : ‖H (halfStep b S x g) - H x‖ ≤
      2 * (a + b * ‖H x‖) * ‖x - halfStep b S x g‖) :
    stepSize b S g * ‖H (halfStep b S x g) - g‖ ≤
      1 / 4 * ‖stepSize b S g • g‖ +
        9 / 8 * stepSize b S g * ‖g - H x‖ := by
  let γ := stepSize b S g
  have hγ : 0 < γ := stepSize_pos hS g
  have hγS : γ ≤ 1 / (16 * S) := stepSize_le hS g
  have ht : ‖γ • g‖ = γ * ‖g‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hγa : γ * a ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_left haS hγ.le
    have hs : γ * S ≤ 1 / 16 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 16 * S)).mp hγS
      nlinarith
    exact hh.trans hs
  have hbt : b * ‖γ • g‖ ≤ 1 / 16 := by
    have hh := stepSize_mul_norm_le hb hS g
    change γ * ‖g‖ ≤ 1 / (16 * b) at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 16 * b)).mp hh
    rw [ht]
    nlinarith
  have hga : γ * b * ‖g‖ ≤ 1 / 16 := by rw [ht] at hbt; nlinarith
  have hnorm : ‖H x‖ ≤ ‖g‖ + ‖g - H x‖ := by
    have h := norm_add_le g (H x - g)
    have he : g + (H x - g) = H x := by abel
    rw [he, norm_sub_rev (H x) g] at h
    exact h
  have hd : x - halfStep b S x g = γ • g := by
    dsimp [halfStep, γ]
    abel
  rw [hd] at hl
  have htri : ‖H (halfStep b S x g) - g‖ ≤
      ‖H (halfStep b S x g) - H x‖ + ‖g - H x‖ := by
    have h := norm_add_le (H (halfStep b S x g) - H x) (H x - g)
    rw [sub_add_sub_cancel, norm_sub_rev (H x) g] at h
    exact h
  have hl' : ‖H (halfStep b S x g) - g‖ ≤
      2 * (a + b * (‖g‖ + ‖g - H x‖)) * ‖γ • g‖ + ‖g - H x‖ := by
    apply htri.trans
    gcongr
    exact hl.trans (by gcongr)
  have hmain := mul_le_mul_of_nonneg_left hl' hγ.le
  have h1 := mul_le_mul_of_nonneg_right hγa (norm_nonneg (γ • g))
  have h2 := mul_le_mul_of_nonneg_right hga (norm_nonneg (γ • g))
  have h3 := mul_le_mul_of_nonneg_right hbt
    (mul_nonneg hγ.le (norm_nonneg (g - H x)))
  change γ * ‖H (halfStep b S x g) - g‖ ≤ _
  nlinarith

lemma clipped_local_error_sq {a b S : ℝ} (hb : 0 < b) (hS : 0 < S)
    (haS : a ≤ S) (H : E → E) (x g : E)
    (hl : ‖H (halfStep b S x g) - H x‖ ≤
      2 * (a + b * ‖H x‖) * ‖x - halfStep b S x g‖) :
    (stepSize b S g) ^ 2 * ‖H (halfStep b S x g) - g‖ ^ 2 ≤
      1 / 8 * ‖stepSize b S g • g‖ ^ 2 +
        81 / 32 * (stepSize b S g) ^ 2 * ‖g - H x‖ ^ 2 := by
  have h := clipped_local_error hb hS haS H x g hl
  have hγ := stepSize_pos (b := b) hS g
  have hs := pow_le_pow_left₀ (by positivity) h 2
  have hh := sq_nonneg (1 / 4 * ‖stepSize b S g • g‖ -
    9 / 8 * stepSize b S g * ‖g - H x‖)
  nlinarith

lemma one_step {a b S μ d : ℝ} (hb : 0 < b) (hS : 0 < S)
    (haS : a ≤ S) (hμ : 0 ≤ μ) (hd : 0 ≤ d) (hμS : μ ≤ S)
    (hscale : μ * b ^ 2 * d ^ 2 ≤ S) (H : E → E) (c x p g e : E)
    (hp : ‖p - c‖ ≤ 2 * d) (hx : ‖x - p‖ ≤ 3 * d)
    (hm : μ * ‖halfStep b S x g - p‖ ^ 2 ≤
      ⟪H (halfStep b S x g), halfStep b S x g - p⟫)
    (hl : ‖H (halfStep b S x g) - H x‖ ≤
      2 * (a + b * ‖H x‖) * ‖x - halfStep b S x g‖) :
    ‖finishStep d (stepSize b S g) c x (H (halfStep b S x g) + e) - p‖ ^ 2 ≤
      (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2 +
        81 / 32 * (stepSize b S g) ^ 2 * ‖g - H x‖ ^ 2 +
        (stepSize b S g) ^ 2 * ‖e‖ ^ 2 -
        2 * stepSize b S g * ⟪e, x - stepSize b S g • H (halfStep b S x g) - p⟫ := by
  have hdist := finishStep_distance hd (stepSize b S g) c x
    (H (halfStep b S x g) + e) p hp
  have hdist2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hid := extragradient_identity x p g (H (halfStep b S x g)) e (stepSize b S g)
  rw [hid] at hdist2
  have herr := clipped_local_error_sq hb hS haS H x g hl
  have hdrift := clipped_drift hb hS hμ hd hμS hscale x p g hx
  have hγ := stepSize_pos (b := b) hS g
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * stepSize b S g)
  change μ * ‖x - stepSize b S g • g - p‖ ^ 2 ≤ _ at hm
  change 2 * stepSize b S g * (μ * ‖x - stepSize b S g • g - p‖ ^ 2) ≤ _ at hm'
  dsimp only [halfStep] at hdist2 herr hdrift hm' ⊢
  nlinarith [sq_nonneg ‖stepSize b S g • g‖]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurable_stepSize (b S : ℝ) : Measurable (stepSize (E := E) b S) := by
  unfold stepSize
  fun_prop

lemma measurable_halfStep (b S : ℝ) :
    Measurable (fun w : E × E => halfStep b S w.1 w.2) := by
  exact measurable_fst.sub (((measurable_stepSize b S).comp measurable_snd).smul measurable_snd)

lemma measurable_finishStep (d : ℝ) :
    Measurable (fun w : ℝ × E × E × E => finishStep d w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  exact measurable_snd.fst.add ((measurable_clip (2 * d)).comp
    ((measurable_snd.snd.fst.sub (measurable_fst.smul measurable_snd.snd.snd)).sub
      measurable_snd.fst))

end OracleTemplate.ClippedExtragradient
