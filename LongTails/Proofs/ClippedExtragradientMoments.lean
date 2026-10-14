import LongTails.Proofs.ClippedExtragradientStability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma integrable_finish_distance {d γ : ℝ} (hd : 0 ≤ d) (c x p : E)
    {G : Ω → E} (hG : Measurable G) :
    Integrable (fun ω => ‖finishStep d γ c x (G ω) - p‖ ^ 2) P := by
  have hm : Measurable (fun ω => finishStep d γ c x (G ω)) :=
    (measurable_finishStep d).comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk hG)))
  apply Integrable.of_bound ((hm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    ((2 * d + ‖p - c‖) ^ 2)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  change ‖finishStep d γ c x (G ω) - p‖ ≤ 2 * d + ‖p - c‖
  have ht := norm_sub_le_norm_sub_add_norm_sub (finishStep d γ c x (G ω)) c p
  rw [norm_sub_rev c p] at ht
  linarith [finishStep_ball hd γ c x (G ω)]

lemma one_step_integral_second {a b S μ d v : ℝ}
    (hb : 0 < b) (hS : 0 < S) (haS : a ≤ S)
    (hμ : 0 ≤ μ) (hd : 0 ≤ d) (hμS : μ ≤ S) (hscale : μ * b ^ 2 * d ^ 2 ≤ S)
    (H : E → E) (c x p g : E)
    (hp : ‖p - c‖ ≤ 2 * d) (hx : ‖x - p‖ ≤ 3 * d)
    (hm : μ * ‖halfStep b S x g - p‖ ^ 2 ≤
      ⟪H (halfStep b S x g), halfStep b S x g - p⟫)
    (hl : ‖H (halfStep b S x g) - H x‖ ≤
      2 * (a + b * ‖H x‖) * ‖x - halfStep b S x g‖)
    {G : Ω → E} (hG : Measurable G) (hGi : Integrable G P)
    (hmean : (∫ ω, G ω ∂P) = H (halfStep b S x g))
    (hvi : Integrable (fun ω => ‖G ω - H (halfStep b S x g)‖ ^ 2) P)
    (hv : (∫ ω, ‖G ω - H (halfStep b S x g)‖ ^ 2 ∂P) ≤ v) :
    (∫ ω, ‖finishStep d (stepSize b S g) c x (G ω) - p‖ ^ 2 ∂P) ≤
      (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2 +
        81 / 32 * (stepSize b S g) ^ 2 * ‖g - H x‖ ^ 2 +
        (stepSize b S g) ^ 2 * v := by
  let γ := stepSize b S g
  let y := halfStep b S x g
  let e : Ω → E := fun ω => G ω - H y
  let z := x - γ • H y - p
  let C := (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2 +
    81 / 32 * γ ^ 2 * ‖g - H x‖ ^ 2
  have hei : Integrable e P := hGi.sub (integrable_const _)
  have hei2 : Integrable (fun ω => ‖e ω‖ ^ 2) P := hvi
  have hem : (∫ ω, e ω ∂P) = 0 := by
    dsimp [e, y]
    rw [integral_sub hGi (integrable_const _), hmean]
    simp
  have heinner : (∫ ω, ⟪e ω, z⟫ ∂P) = 0 := by
    calc
      _ = ∫ ω, ⟪z, e ω⟫ ∂P := integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => (real_inner_comm (e ω) z).symm))
      _ = 0 := by rw [integral_inner hei, hem]; simp
  have hBi : Integrable (fun ω => C + γ ^ 2 * ‖e ω‖ ^ 2 - 2 * γ * ⟪e ω, z⟫) P :=
    ((integrable_const _).add (hvi.const_mul _)).sub ((hei.inner_const _).const_mul _)
  have hpt (ω : Ω) : ‖finishStep d γ c x (G ω) - p‖ ^ 2 ≤
      C + γ ^ 2 * ‖e ω‖ ^ 2 - 2 * γ * ⟪e ω, z⟫ := by
    have hh := one_step hb hS haS hμ hd hμS hscale H c x p g (e ω) hp hx hm hl
    have he : H y + e ω = G ω := by dsimp [e]; abel
    change ‖finishStep d γ c x (H y + e ω) - p‖ ^ 2 ≤ _ at hh
    rw [he] at hh
    exact hh
  have hi := integral_mono (integrable_finish_distance hd c x p hG) hBi hpt
  have hsub := integral_sub ((integrable_const C).add (hei2.const_mul (γ ^ 2)))
    ((hei.inner_const z).const_mul (2 * γ))
  have hadd := integral_add (integrable_const C) (hei2.const_mul (γ ^ 2))
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, integral_const_mul, heinner] at hi
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero] at hi
  have hv' : (∫ ω, ‖e ω‖ ^ 2 ∂P) ≤ v := hv
  have hh := mul_le_mul_of_nonneg_left hv' (sq_nonneg γ)
  change _ ≤ C + γ ^ 2 * v
  linarith

lemma one_step_integral {a b S μ d v : ℝ}
    (hb : 0 < b) (hS : 0 < S) (haS : a ≤ S)
    (hμ : 0 ≤ μ) (hd : 0 ≤ d) (hμS : μ ≤ S) (hscale : μ * b ^ 2 * d ^ 2 ≤ S)
    (hv0 : 0 ≤ v) (H : E → E) (c x p : E)
    (hp : ‖p - c‖ ≤ 2 * d) (hx : ‖x - p‖ ≤ 3 * d)
    (hm : ∀ y, μ * ‖y - p‖ ^ 2 ≤ ⟪H y, y - p⟫)
    (hl : ∀ g, ‖H (halfStep b S x g) - H x‖ ≤
      2 * (a + b * ‖H x‖) * ‖x - halfStep b S x g‖)
    {G1 : Ω → E} (hG1 : Measurable G1)
    (hv1i : Integrable (fun ω => ‖G1 ω - H x‖ ^ 2) P)
    (hv1 : (∫ ω, ‖G1 ω - H x‖ ^ 2 ∂P) ≤ v)
    {G2 : E → Ω → E} (hG2 : Measurable (Function.uncurry G2))
    (hG2i : ∀ y, Integrable (G2 y) P)
    (hmean : ∀ y, (∫ ω, G2 y ω ∂P) = H y)
    (hv2i : ∀ y, Integrable (fun ω => ‖G2 y ω - H y‖ ^ 2) P)
    (hv2 : ∀ y, (∫ ω, ‖G2 y ω - H y‖ ^ 2 ∂P) ≤ v) :
    (∫ w : Ω × Ω,
      ‖finishStep d (stepSize b S (G1 w.1)) c x
        (G2 (halfStep b S x (G1 w.1)) w.2) - p‖ ^ 2 ∂P.prod P) ≤
      (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2 + v / (64 * S ^ 2) := by
  let F : Ω × Ω → ℝ := fun w =>
    ‖finishStep d (stepSize b S (G1 w.1)) c x
      (G2 (halfStep b S x (G1 w.1)) w.2) - p‖ ^ 2
  let C := (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2
  let A := (81 : ℝ) / (8192 * S ^ 2)
  let B := v / (256 * S ^ 2)
  have hFm : Measurable F := by
    have hg : Measurable (fun w : Ω × Ω => G1 w.1) := hG1.comp measurable_fst
    have hy : Measurable (fun w : Ω × Ω => halfStep b S x (G1 w.1)) :=
      (measurable_halfStep b S).comp (measurable_const.prodMk hg)
    have hq : Measurable (fun w : Ω × Ω => G2 (halfStep b S x (G1 w.1)) w.2) :=
      hG2.comp (hy.prodMk measurable_snd)
    have hf : Measurable (fun w : Ω × Ω => finishStep d (stepSize b S (G1 w.1)) c x
        (G2 (halfStep b S x (G1 w.1)) w.2)) := (measurable_finishStep d).comp
      (((measurable_stepSize b S).comp hg).prodMk
        (measurable_const.prodMk (measurable_const.prodMk hq)))
    exact (hf.sub measurable_const).norm.pow_const 2
  have hFi : Integrable F (P.prod P) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable ((2 * d + ‖p - c‖) ^ 2)
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity)]
    dsimp [F]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hh := norm_sub_le_norm_sub_add_norm_sub
      (finishStep d (stepSize b S (G1 w.1)) c x (G2 (halfStep b S x (G1 w.1)) w.2)) c p
    rw [norm_sub_rev c p] at hh
    linarith [finishStep_ball hd (stepSize b S (G1 w.1)) c x
      (G2 (halfStep b S x (G1 w.1)) w.2)]
  have hUi : Integrable (fun ω => C + A * ‖G1 ω - H x‖ ^ 2 + B) P :=
    ((integrable_const _).add (hv1i.const_mul _)).add (integrable_const _)
  have hpt (ω : Ω) : (∫ η, F (ω, η) ∂P) ≤ C + A * ‖G1 ω - H x‖ ^ 2 + B := by
    have h := one_step_integral_second hb hS haS hμ hd hμS hscale H c x p (G1 ω)
      hp hx (hm _) (hl _) (hG2.comp measurable_prodMk_left) (hG2i _) (hmean _)
      (hv2i _) (hv2 _)
    have hγ := stepSize_pos (b := b) hS (G1 ω)
    have hs := pow_le_pow_left₀ hγ.le (stepSize_le (b := b) hS (G1 ω)) 2
    have he : (1 / (16 * S)) ^ 2 = 1 / (256 * S ^ 2) := by ring
    rw [he] at hs
    have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖G1 ω - H x‖)
    have h2 := mul_le_mul_of_nonneg_right hs hv0
    change (∫ η, F (ω, η) ∂P) ≤ C +
      81 / 32 * (stepSize b S (G1 ω)) ^ 2 * ‖G1 ω - H x‖ ^ 2 +
      (stepSize b S (G1 ω)) ^ 2 * v at h
    dsimp [A, B]
    rw [show (81 : ℝ) / (8192 * S ^ 2) = 81 / 32 * (1 / (256 * S ^ 2)) by ring,
      show v / (256 * S ^ 2) = (1 / (256 * S ^ 2)) * v by ring]
    nlinarith
  have hi := integral_mono hFi.integral_prod_left hUi hpt
  have ha1 := integral_add ((integrable_const C).add (hv1i.const_mul A)) (integrable_const B)
  have ha2 := integral_add (integrable_const C) (hv1i.const_mul A)
  simp only [Pi.add_apply] at ha1 ha2
  rw [ha1, ha2, integral_const_mul A] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hvar := mul_le_mul_of_nonneg_left hv1 (show 0 ≤ A by dsimp [A]; positivity)
  change (∫ w, F w ∂P.prod P) ≤ C + v / (64 * S ^ 2)
  rw [integral_prod F hFi]
  have he : A * v + B ≤ v / (64 * S ^ 2) := by
    dsimp [A, B]
    have hh : 0 ≤ v / S ^ 2 := by positivity
    field_simp
    nlinarith
  linarith

end OracleTemplate.ClippedExtragradient
