import LongTails.Algorithms.ProjectedClippedExtragradient
import LongTails.Proofs.ProjectedClippedTuning
import LongTails.Proofs.ProjectedClippedStability
import LongTails.Proofs.ConstrainedRegularization
import LongTails.Proofs.ClippedExtragradientBatch
import LongTails.Proofs.ClippedExtragradientConfidence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ProjectedClippedExtragradient

open ConstrainedMonotone (Proj)
open ClippedExtragradient (stepSize stepSize_pos stepSize_le measurable_stepSize)
open ContinuizedSimilarQuasar (iterateSamples)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma halfStep_cap {X : Set E} {P : E → E} (hP : Proj X P) {b S : ℝ}
    (hb : 0 ≤ b) (hS : 0 < S) {x : E} (hx : x ∈ X) (g : E) :
    b * ‖x - halfStep P b S x g‖ ≤ 1 / 16 := by
  have hdist := hP.dist_le (x - stepSize b S g • g) hx
  have he : x - stepSize b S g • g - x = -(stepSize b S g • g) := by abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (stepSize_pos hS g)] at hdist
  by_cases hzero : b = 0
  · simp [hzero]
  · have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
    have hcap := ClippedExtragradient.stepSize_mul_norm_le hpos hS g
    have hm := mul_le_mul_of_nonneg_left hdist hb
    have hm' := mul_le_mul_of_nonneg_left hcap hb
    have he' : b * (1 / (16 * b)) = (1 : ℝ) / 16 := by field_simp
    rw [he'] at hm'
    simpa only [halfStep, norm_sub_rev x] using hm.trans hm'

lemma halfStep_regularized_local {X : Set E} {P F : E → E}
    (hP : Proj X P) {L0 L1 r S C : ℝ} (hF : GeneralizedMonotone.Hyp F L0 L1)
    (hr : 0 ≤ r) (hS : 0 < S) (anchor x : E) (hx : x ∈ X)
    (hC : r * ‖x - anchor‖ ≤ C) (g : E) :
    ‖HolderMonotone.reg F r anchor (halfStep P L1 S x g) - HolderMonotone.reg F r anchor x‖ ≤
      2 * (L0 + r + L1 * C + L1 * ‖HolderMonotone.reg F r anchor x‖) *
        ‖x - halfStep P L1 S x g‖ := by
  have hcap := halfStep_cap hP hF.L1_nonneg hS hx g
  have hl := ConstrainedMonotone.regularized_local_bound hF hr anchor x
    (halfStep P L1 S x g) (le_refl _) (by linarith : L1 * ‖x - halfStep P L1 S x g‖ ≤ 1 / 2)
  have hm := mul_le_mul_of_nonneg_left hC hF.L1_nonneg
  have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (x - halfStep P L1 S x g))
  unfold HolderMonotone.reg
  nlinarith

lemma regularized_coercivity_bounded {X : Set E} {F : E → E}
    {L0 L1 r d h M ε : ℝ} (hF : GeneralizedMonotone.Hyp F L0 L1)
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hh : 0 < h) (hhd : h ≤ 3 * d)
    (hcap : L1 * h ≤ 1 / 2) (anchor x p : E) (hx : x ∈ X)
    (hp : ConstrainedMonotone.Normal X p (-(F p + r • (p - anchor))))
    (hxp : ‖x - p‖ ≤ 3 * d) (hM : ‖F p‖ ≤ M) (hbias : r * ‖p - anchor‖ ≤ ε) :
    h * ‖HolderMonotone.reg F r anchor x‖ ≤
      h * (M + ε + 3 * r * d + 12 * (L0 + L1 * M) * d) +
        ⟪HolderMonotone.reg F r anchor x, x - p⟫ := by
  have hc := ConstrainedMonotone.regularized_coercivity hF anchor hx hp hr hh hcap hxp
  have hL : 0 ≤ L0 + L1 * M := by
    have hM0 := (norm_nonneg (F p)).trans hM
    have := hF.L0_pos
    have := hF.L1_nonneg
    positivity
  have hm := mul_le_mul_of_nonneg_left hM hF.L1_nonneg
  have hm' := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 3 * d + h)
  have hp' := mul_le_mul_of_nonneg_left hhd hL
  have hB : ‖F p‖ + r * (‖p - anchor‖ + 3 * d) +
      2 * (L0 + L1 * ‖F p‖) * (3 * d + h) ≤
      M + ε + 3 * r * d + 12 * (L0 + L1 * M) * d := by nlinarith
  have hBh := mul_le_mul_of_nonneg_left hB hh.le
  change h * ‖F x + r • (x - anchor)‖ ≤ _
  change _ ≤ h * (M + ε + 3 * r * d + 12 * (L0 + L1 * M) * d) +
    ⟪F x + r • (x - anchor), x - p⟫
  linarith

lemma finish_distance (P : E → E) {d : ℝ} (hd : 0 ≤ d) (γ : ℝ) (c x g p : E)
    (hp : ‖p - c‖ ≤ 2 * d) :
    ‖finishStep P d γ c x g - p‖ ≤ ‖P (x - γ • g) - p‖ := by
  have ht := norm_clip_sub_le (by positivity : 0 ≤ 2 * d) hp (P (x - γ • g) - c)
  have he : finishStep P d γ c x g - p = clip (2 * d) (P (x - γ • g) - c) - (p - c) := by
    unfold finishStep
    abel
  rw [he]
  convert ht using 1
  congr 1
  abel

lemma finish_ball (P : E → E) {d : ℝ} (hd : 0 ≤ d) (γ : ℝ) (c x g : E) :
    ‖finishStep P d γ c x g - c‖ ≤ 2 * d := by
  simpa only [finishStep, add_sub_cancel_left] using
    norm_clip_le (by positivity : 0 ≤ 2 * d) (P (x - γ • g) - c)

lemma centered_clip_mem {X : Set E} (hX : Convex ℝ X) {c v : E} (hc : c ∈ X) (hv : v ∈ X)
    {B : ℝ} (hB : 0 ≤ B) : c + clip B (v - c) ∈ X := by
  unfold clip
  split_ifs with h
  · simpa using hv
  · have hn : 0 < ‖v - c‖ := hB.trans_lt (lt_of_not_ge h)
    have ht : B / ‖v - c‖ ≤ 1 := (div_le_one hn).mpr (le_of_not_ge h)
    have he : c + (B / ‖v - c‖) • (v - c) =
        (1 - B / ‖v - c‖) • c + (B / ‖v - c‖) • v := by module
    rw [he]
    exact hX hc hv (sub_nonneg.mpr ht) (by positivity) (by ring)

lemma finish_mem {X : Set E} {P : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    {d : ℝ} (hd : 0 ≤ d) (γ : ℝ) {c : E} (hc : c ∈ X) (x g : E) :
    finishStep P d γ c x g ∈ X :=
  centered_clip_mem hX hc (hP.mem _) (by positivity)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_halfStep {P : E → E} (hP : Measurable P) (b S : ℝ) :
    Measurable (fun w : E × E => halfStep P b S w.1 w.2) :=
  hP.comp (ClippedExtragradient.measurable_halfStep b S)

lemma measurable_finishStep {P : E → E} (hP : Measurable P) (d : ℝ) :
    Measurable (fun w : ℝ × E × E × E => finishStep P d w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  exact measurable_snd.fst.add ((measurable_clip (2 * d)).comp
    ((hP.comp (measurable_snd.snd.fst.sub (measurable_fst.smul measurable_snd.snd.snd))).sub
      measurable_snd.fst))

lemma integrable_finish_distance {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {P : E → E} (hP : Measurable P) {d γ : ℝ} (hd : 0 ≤ d)
    (c x p : E) {G : Ω → E} (hG : Measurable G) :
    Integrable (fun ω => ‖finishStep P d γ c x (G ω) - p‖ ^ 2) Q := by
  have hm : Measurable (fun ω => finishStep P d γ c x (G ω)) :=
    (measurable_finishStep hP d).comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk hG)))
  apply Integrable.of_bound ((hm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    ((2 * d + ‖p - c‖) ^ 2)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  change ‖finishStep P d γ c x (G ω) - p‖ ≤ 2 * d + ‖p - c‖
  have ht := norm_sub_le_norm_sub_add_norm_sub (finishStep P d γ c x (G ω)) c p
  rw [norm_sub_rev c p] at ht
  linarith [finish_ball P hd γ c x (G ω)]

variable [CompleteSpace E]

lemma one_step_integral_second {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Set E} {P : E → E} (hP : Proj X P)
    {A b S μ h B D d v : ℝ} (hb : 0 ≤ b) (hS : 0 < S) (hμ : 0 ≤ μ)
    (hμS : μ ≤ S) (hAS : A ≤ S) (hh : 0 < h) (hhd : h ≤ D) (hd : 0 ≤ d)
    (hB : 4 * b * B ≤ S) (hscale : μ * D ^ 2 * (1 + 16 * b * D) ^ 2 ≤ S * h ^ 2)
    (H : E → E) (c x p g : E) (hp : p ∈ X) (hx : x ∈ X)
    (hpc : ‖p - c‖ ≤ 2 * d) (hxp : ‖x - p‖ ≤ D)
    (hcoerce : h * ‖H x‖ ≤ h * B + ⟪H x, x - p⟫)
    (hm : μ * ‖halfStep P b S x g - p‖ ^ 2 ≤ ⟪H (halfStep P b S x g), halfStep P b S x g - p⟫)
    (hl : ‖H (halfStep P b S x g) - H x‖ ≤ 2 * (A + b * ‖H x‖) * ‖x - halfStep P b S x g‖)
    {G : Ω → E} (hG : Measurable G) (hGi : Integrable G Q)
    (hmean : (∫ ω, G ω ∂Q) = H (halfStep P b S x g))
    (hvi : Integrable (fun ω => ‖G ω - H (halfStep P b S x g)‖ ^ 2) Q)
    (hv : (∫ ω, ‖G ω - H (halfStep P b S x g)‖ ^ 2 ∂Q) ≤ v) :
    (∫ ω, ‖finishStep P d (ClippedExtragradient.stepSize b S g) c x (G ω) - p‖ ^ 2 ∂Q) ≤
      (1 - μ / (16 * S)) * ‖x - p‖ ^ 2 +
        97 / 8 * (ClippedExtragradient.stepSize b S g) ^ 2 * ‖g - H x‖ ^ 2 +
        4 * (ClippedExtragradient.stepSize b S g) ^ 2 * v := by
  let γ := ClippedExtragradient.stepSize b S g
  let y := halfStep P b S x g
  let e : Ω → E := fun ω => G ω - H y
  let z := y - p
  let C := (1 - μ / (16 * S)) * ‖x - p‖ ^ 2 + 97 / 8 * γ ^ 2 * ‖g - H x‖ ^ 2
  have hei : Integrable e Q := hGi.sub (integrable_const _)
  have hei2 : Integrable (fun ω => ‖e ω‖ ^ 2) Q := hvi
  have hem : (∫ ω, e ω ∂Q) = 0 := by
    dsimp [e, y]
    rw [integral_sub hGi (integrable_const _), hmean]
    simp
  have heinner : (∫ ω, ⟪e ω, z⟫ ∂Q) = 0 := by
    calc
      _ = ∫ ω, ⟪z, e ω⟫ ∂Q := integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => (real_inner_comm (e ω) z).symm))
      _ = 0 := by rw [integral_inner hei, hem]; simp
  have hBi : Integrable (fun ω => C + 4 * γ ^ 2 * ‖e ω‖ ^ 2 - 2 * γ * ⟪e ω, z⟫) Q :=
    ((integrable_const _).add (hei2.const_mul _)).sub ((hei.inner_const _).const_mul _)
  have hpt (ω : Ω) : ‖finishStep P d γ c x (G ω) - p‖ ^ 2 ≤
      C + 4 * γ ^ 2 * ‖e ω‖ ^ 2 - 2 * γ * ⟪e ω, z⟫ := by
    have hh := hP.clipped_one_step hp hx H g (e ω) hb hS hμ hμS hAS hh hhd hxp hB hscale hcoerce hm hl
    have he : H y + e ω = G ω := by dsimp [e]; abel
    change ‖P (x - γ • (H y + e ω)) - p‖ ^ 2 ≤ _ at hh
    rw [he] at hh
    have hdist := pow_le_pow_left₀ (norm_nonneg _) (finish_distance P hd γ c x (G ω) p hpc) 2
    exact hdist.trans hh
  have hi := integral_mono (integrable_finish_distance hP.lipschitz.continuous.measurable hd c x p hG) hBi hpt
  have hsub := integral_sub ((integrable_const C).add (hei2.const_mul (4 * γ ^ 2)))
    ((hei.inner_const z).const_mul (2 * γ))
  have hadd := integral_add (integrable_const C) (hei2.const_mul (4 * γ ^ 2))
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, integral_const_mul, heinner] at hi
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero] at hi
  have hv' : (∫ ω, ‖e ω‖ ^ 2 ∂Q) ≤ v := hv
  have hmul := mul_le_mul_of_nonneg_left hv' (by positivity : 0 ≤ 4 * γ ^ 2)
  change _ ≤ C + 4 * γ ^ 2 * v
  linarith

lemma one_step_integral {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : Set E} {P : E → E} (hP : Proj X P)
    {a b S μ h B D d v : ℝ} (hb : 0 ≤ b) (hS : 0 < S) (hμ : 0 ≤ μ)
    (hμS : μ ≤ S) (haS : a ≤ S) (hh : 0 < h) (hhd : h ≤ D) (hd : 0 ≤ d)
    (hB : 4 * b * B ≤ S) (hscale : μ * D ^ 2 * (1 + 16 * b * D) ^ 2 ≤ S * h ^ 2)
    (hv0 : 0 ≤ v) (H : E → E) (c x p : E) (hp : p ∈ X) (hx : x ∈ X)
    (hpc : ‖p - c‖ ≤ 2 * d) (hxp : ‖x - p‖ ≤ D)
    (hcoerce : h * ‖H x‖ ≤ h * B + ⟪H x, x - p⟫)
    (hm : ∀ g, μ * ‖halfStep P b S x g - p‖ ^ 2 ≤ ⟪H (halfStep P b S x g), halfStep P b S x g - p⟫)
    (hl : ∀ g, ‖H (halfStep P b S x g) - H x‖ ≤ 2 * (a + b * ‖H x‖) * ‖x - halfStep P b S x g‖)
    {G1 : Ω → E} (hG1 : Measurable G1)
    (hv1i : Integrable (fun ω => ‖G1 ω - H x‖ ^ 2) Q)
    (hv1 : (∫ ω, ‖G1 ω - H x‖ ^ 2 ∂Q) ≤ v)
    {G2 : E → Ω → E} (hG2 : Measurable (Function.uncurry G2))
    (hG2i : ∀ y, Integrable (G2 y) Q)
    (hmean : ∀ y, (∫ ω, G2 y ω ∂Q) = H y)
    (hv2i : ∀ y, Integrable (fun ω => ‖G2 y ω - H y‖ ^ 2) Q)
    (hv2 : ∀ y, (∫ ω, ‖G2 y ω - H y‖ ^ 2 ∂Q) ≤ v) :
    (∫ w : Ω × Ω, ‖finishStep P d (stepSize b S (G1 w.1)) c x
      (G2 (halfStep P b S x (G1 w.1)) w.2) - p‖ ^ 2 ∂Q.prod Q) ≤
      (1 - μ / (16 * S)) * ‖x - p‖ ^ 2 + v / (8 * S ^ 2) := by
  have hPm : Measurable P := hP.lipschitz.continuous.measurable
  let F : Ω × Ω → ℝ := fun w =>
    ‖finishStep P d (stepSize b S (G1 w.1)) c x
      (G2 (halfStep P b S x (G1 w.1)) w.2) - p‖ ^ 2
  let C := (1 - μ / (16 * S)) * ‖x - p‖ ^ 2
  let A := (97 : ℝ) / (2048 * S ^ 2)
  let B := v / (64 * S ^ 2)
  have hFm : Measurable F := by
    have hg : Measurable (fun w : Ω × Ω => G1 w.1) := hG1.comp measurable_fst
    have hy : Measurable (fun w : Ω × Ω => halfStep P b S x (G1 w.1)) :=
      (measurable_halfStep hPm b S).comp (measurable_const.prodMk hg)
    have hq : Measurable (fun w : Ω × Ω => G2 (halfStep P b S x (G1 w.1)) w.2) :=
      hG2.comp (hy.prodMk measurable_snd)
    have hf : Measurable (fun w : Ω × Ω => finishStep P d (stepSize b S (G1 w.1)) c x
        (G2 (halfStep P b S x (G1 w.1)) w.2)) := (measurable_finishStep hPm d).comp
      (((measurable_stepSize b S).comp hg).prodMk
        (measurable_const.prodMk (measurable_const.prodMk hq)))
    exact (hf.sub measurable_const).norm.pow_const 2
  have hFi : Integrable F (Q.prod Q) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable ((2 * d + ‖p - c‖) ^ 2)
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity)]
    dsimp [F]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hh := norm_sub_le_norm_sub_add_norm_sub
      (finishStep P d (stepSize b S (G1 w.1)) c x (G2 (halfStep P b S x (G1 w.1)) w.2)) c p
    rw [norm_sub_rev c p] at hh
    linarith [finish_ball P hd (stepSize b S (G1 w.1)) c x
      (G2 (halfStep P b S x (G1 w.1)) w.2)]
  have hUi : Integrable (fun ω => C + A * ‖G1 ω - H x‖ ^ 2 + B) Q :=
    ((integrable_const _).add (hv1i.const_mul _)).add (integrable_const _)
  have hpt (ω : Ω) : (∫ η, F (ω, η) ∂Q) ≤ C + A * ‖G1 ω - H x‖ ^ 2 + B := by
    have h := one_step_integral_second hP hb hS hμ hμS haS hh hhd hd hB hscale H c x p (G1 ω)
      hp hx hpc hxp hcoerce (hm _) (hl _) (hG2.comp measurable_prodMk_left) (hG2i _) (hmean _)
      (hv2i _) (hv2 _)
    have hγ := stepSize_pos (b := b) hS (G1 ω)
    have hs := pow_le_pow_left₀ hγ.le (stepSize_le (b := b) hS (G1 ω)) 2
    have he : (1 / (16 * S)) ^ 2 = 1 / (256 * S ^ 2) := by ring
    rw [he] at hs
    have h1 := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖G1 ω - H x‖)
    have h2 := mul_le_mul_of_nonneg_right hs hv0
    change (∫ η, F (ω, η) ∂Q) ≤ C +
      97 / 8 * (stepSize b S (G1 ω)) ^ 2 * ‖G1 ω - H x‖ ^ 2 +
      4 * (stepSize b S (G1 ω)) ^ 2 * v at h
    dsimp [A, B]
    rw [show (97 : ℝ) / (2048 * S ^ 2) = 97 / 8 * (1 / (256 * S ^ 2)) by ring,
      show v / (64 * S ^ 2) = 4 * (1 / (256 * S ^ 2)) * v by ring]
    nlinarith
  have hi := integral_mono hFi.integral_prod_left hUi hpt
  have ha1 := integral_add ((integrable_const C).add (hv1i.const_mul A)) (integrable_const B)
  have ha2 := integral_add (integrable_const C) (hv1i.const_mul A)
  simp only [Pi.add_apply] at ha1 ha2
  rw [ha1, ha2, integral_const_mul A] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hvar := mul_le_mul_of_nonneg_left hv1 (show 0 ≤ A by dsimp [A]; positivity)
  change (∫ w, F w ∂Q.prod Q) ≤ C + v / (8 * S ^ 2)
  rw [integral_prod F hFi]
  have he : A * v + B ≤ v / (8 * S ^ 2) := by
    dsimp [A, B]
    have hh : 0 ≤ v / S ^ 2 := by positivity
    field_simp
    nlinarith
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma measurable_batchStep_of {A : Type*} [MeasurableSpace A]
    {P : E → E} (hP : Measurable P) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (n : ℕ) (b S d r : ℝ) {anchor center x : A → E}
    {samples : A → (Fin n → Ω) × (Fin n → Ω)}
    (ha : Measurable anchor) (hc : Measurable center) (hx : Measurable x)
    (hs : Measurable samples) :
    Measurable (fun w => batchStep P n b S d r (anchor w) (center w) g (x w) (samples w)) := by
  have hfirst : Measurable (fun w => ClippedExtragradient.regularizedReply r (anchor w) (x w)
      ((1 / (n : ℝ)) • ∑ i, g (x w) ((samples w).1 i))) := by
    unfold ClippedExtragradient.regularizedReply
    apply Measurable.add
    · apply Measurable.const_smul
      apply Finset.measurable_sum
      intro i _
      exact hg.comp (hx.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp hs)))
    · exact (hx.sub ha).const_smul r
  have hy := (measurable_halfStep hP b S).comp (hx.prodMk hfirst)
  have hsecond : Measurable (fun w => ClippedExtragradient.regularizedReply r (anchor w)
      (halfStep P b S (x w) (ClippedExtragradient.regularizedReply r (anchor w) (x w)
        ((1 / (n : ℝ)) • ∑ i, g (x w) ((samples w).1 i))))
      ((1 / (n : ℝ)) • ∑ i, g
        (halfStep P b S (x w) (ClippedExtragradient.regularizedReply r (anchor w) (x w)
          ((1 / (n : ℝ)) • ∑ j, g (x w) ((samples w).1 j)))) ((samples w).2 i))) := by
    unfold ClippedExtragradient.regularizedReply
    apply Measurable.add
    · apply Measurable.const_smul
      apply Finset.measurable_sum
      intro i _
      exact hg.comp (hy.prodMk ((measurable_pi_apply i).comp (measurable_snd.comp hs)))
    · exact (hy.sub ha).const_smul r
  exact (measurable_finishStep hP d).comp
    (((measurable_stepSize b S).comp hfirst).prodMk (hc.prodMk (hx.prodMk hsecond)))

omit [CompleteSpace E] in
lemma measurable_batchStep {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (n : ℕ) (b S d r : ℝ)
    (anchor center : E) :
    Measurable (fun w : E × ((Fin n → Ω) × (Fin n → Ω)) =>
      batchStep P n b S d r anchor center g w.1 w.2) := by
  have hfirst : Measurable (fun w : E × ((Fin n → Ω) × (Fin n → Ω)) =>
      ClippedExtragradient.regularizedReply r anchor w.1 ((1 / (n : ℝ)) • ∑ i, g w.1 (w.2.1 i))) :=
    (ClippedExtragradient.measurable_batch_reply hg n r anchor).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hγ := (measurable_stepSize b S).comp hfirst
  have hy := (measurable_halfStep hP b S).comp (measurable_fst.prodMk hfirst)
  have hsecond := (ClippedExtragradient.measurable_batch_reply hg n r anchor).comp
    (hy.prodMk (measurable_snd.comp measurable_snd))
  exact (measurable_finishStep hP d).comp
    (hγ.prodMk (measurable_const.prodMk (measurable_fst.prodMk hsecond)))

lemma batchStep_integral {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P : E → E} (hP : Proj X P) {g : E → Ω → E} {F : E → E}
    {σ a b S r h B D d : ℝ} (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) Q) (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) Q)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂Q) ≤ σ ^ 2)
    (n : ℕ) (hn : 0 < n) (hb : 0 ≤ b) (hS : 0 < S) (hr : 0 ≤ r)
    (hrS : r ≤ S) (haS : a ≤ S) (hh : 0 < h) (hhd : h ≤ D) (hd : 0 ≤ d)
    (hB : 4 * b * B ≤ S) (hscale : r * D ^ 2 * (1 + 16 * b * D) ^ 2 ≤ S * h ^ 2)
    (anchor center x p : E) (hp : p ∈ X) (hx : x ∈ X)
    (hpc : ‖p - center‖ ≤ 2 * d) (hxp : ‖x - p‖ ≤ D)
    (hcoerce : h * ‖HolderMonotone.reg F r anchor x‖ ≤
      h * B + ⟪HolderMonotone.reg F r anchor x, x - p⟫)
    (hm : ∀ first, r * ‖halfStep P b S x first - p‖ ^ 2 ≤
      ⟪HolderMonotone.reg F r anchor (halfStep P b S x first), halfStep P b S x first - p⟫)
    (hl : ∀ first, ‖HolderMonotone.reg F r anchor (halfStep P b S x first) -
        HolderMonotone.reg F r anchor x‖ ≤
      2 * (a + b * ‖HolderMonotone.reg F r anchor x‖) * ‖x - halfStep P b S x first‖) :
    (∫ samples : (Fin n → Ω) × (Fin n → Ω),
      ‖batchStep P n b S d r anchor center g x samples - p‖ ^ 2
      ∂(Measure.pi (fun _ : Fin n => Q)).prod (Measure.pi (fun _ : Fin n => Q))) ≤
      (1 - r / (16 * S)) * ‖x - p‖ ^ 2 + (σ ^ 2 / n) / (8 * S ^ 2) := by
  let G : E → (Fin n → Ω) → E := fun y ξ =>
    ClippedExtragradient.regularizedReply r anchor y ((1 / (n : ℝ)) • ∑ i, g y (ξ i))
  have hG : Measurable (Function.uncurry G) := ClippedExtragradient.measurable_batch_reply hg n r anchor
  have hmoment (y : E) := ClippedExtragradient.batch_reply_moments hg hgi hmean hvi hv n hn anchor y (r := r)
  change (∫ w : (Fin n → Ω) × (Fin n → Ω),
    ‖finishStep P d (stepSize b S (G x w.1)) center x
      (G (halfStep P b S x (G x w.1)) w.2) - p‖ ^ 2
    ∂(Measure.pi (fun _ : Fin n => Q)).prod (Measure.pi (fun _ : Fin n => Q))) ≤ _
  exact one_step_integral (Q := Measure.pi (fun _ : Fin n => Q))
    (G1 := G x) (G2 := G) hP hb hS hr hrS haS hh hhd hd hB hscale (by positivity)
    (HolderMonotone.reg F r anchor) center x p hp hx hpc hxp hcoerce hm hl
    (hG.comp measurable_prodMk_left) (hmoment x).2.2.1 (hmoment x).2.2.2 hG
    (fun y => (hmoment y).1) (fun y => (hmoment y).2.1)
    (fun y => (hmoment y).2.2.1) (fun y => (hmoment y).2.2.2)

lemma tuned_batch_integral {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) {g : E → Ω → E}
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε)
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) Q)
    (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) Q)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂Q) ≤ t.σ ^ 2)
    (s : ℕ) (anchor center x p : E) (hp : p ∈ X) (hx : x ∈ X)
    (hpc : ‖p - center‖ ≤ radius t s) (hxc : ‖x - center‖ ≤ 2 * radius t s)
    (hnp : ConstrainedMonotone.Normal X p (-(F p + regularization t s • (p - anchor))))
    (hM : ‖F p‖ ≤ rootBound t) (hbias : regularization t s * ‖p - anchor‖ ≤ t.ε) :
    (∫ samples : (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω),
      ‖batchStep P (batchSize t s) t.L1 (localScale t s) (radius t s)
        (regularization t s) anchor center g x samples - p‖ ^ 2
      ∂(Measure.pi (fun _ : Fin (batchSize t s) => Q)).prod
        (Measure.pi (fun _ : Fin (batchSize t s) => Q))) ≤
      (1 - regularization t s / (16 * localScale t s)) * ‖x - p‖ ^ 2 +
        (t.σ ^ 2 / batchSize t s) / (8 * localScale t s ^ 2) := by
  have hC := (curvature_pos t hF.L0_pos hF.L1_nonneg hR.le hG hε.le).le
  have hr := regularization_pos t hR hε s
  have hd := radius_pos t hR s
  have hrS := localScale_lower t hC hF.L1_nonneg hR hε s
  have hS := hr.trans_le hrS
  have hprobe := probe_properties hF.L1_nonneg hd
  have hxp : ‖x - p‖ ≤ 3 * radius t s := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x center p
    rw [norm_sub_rev center p] at ht
    linarith
  have hc := regularized_coercivity_bounded hF hr.le hd.le hprobe.1 hprobe.2.1
    hprobe.2.2 anchor x p hx hnp hxp hM hbias
  apply batchStep_integral hP hg hgi hmean hvi hv (batchSize t s) (batchSize_pos t s)
    hF.L1_nonneg hS hr.le hrS
    (localScale_smoothness t hF.L0_pos.le hF.L1_nonneg hR hG hε s)
    hprobe.1 hprobe.2.1 hd.le
    (localScale_coercivity t hF.L0_pos.le hF.L1_nonneg hR hG hε s)
    (tuned_saturation_scale t hC hF.L1_nonneg hR hε s)
    anchor center x p hp hx (by linarith) hxp hc
  · intro first
    exact ConstrainedMonotone.regularized_strong_vi hF.mono hnp
      (hP.mem (x - stepSize t.L1 (localScale t s) first • first))
  · intro first
    have ha : regularization t s * ‖x - anchor‖ ≤
        t.ε + 3 * regularization t s * radius t s := by
      have ht := norm_sub_le_norm_sub_add_norm_sub x p anchor
      have hm := mul_le_mul_of_nonneg_left ht hr.le
      have hm' := mul_le_mul_of_nonneg_left hxp hr.le
      nlinarith
    have hl := halfStep_regularized_local hP hF hr.le hS anchor x hx ha first
    convert hl using 1; ring

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma iterate_distance_bound_on {Q : Measure Ω} [IsProbabilityMeasure Q]
    {advance : E → Ω → E} (ha : Measurable (Function.uncurry advance)) {X : Set E}
    {μ S d v : ℝ} (hμ : 0 < μ) (hμS : μ ≤ S) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hnoise : 8 * v ≤ μ * S * d ^ 2 / 2 ^ 20) (c p : E) (hc : c ∈ X)
    (hmem : ∀ x ∈ X, ∀ ω, advance x ω ∈ X)
    (hball : ∀ x ω, ‖advance x ω - c‖ ≤ 2 * d) (hp : ‖p - c‖ ≤ d)
    (hstep : ∀ x ∈ X, ‖x - c‖ ≤ 2 * d →
      (∫ ω, ‖advance x ω - p‖ ^ 2 ∂Q) ≤
        (1 - μ / (16 * S)) * ‖x - p‖ ^ 2 + v / (8 * S ^ 2))
    {n : ℕ} (hn : 2 ^ 16 * S / μ ≤ (n : ℝ)) :
    (∫ ξ : Fin n → Ω, ‖iterateSamples advance n c ξ - p‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => Q)) ≤ d ^ 2 / 4096 := by
  have hS : 0 < S := hμ.trans_le hμS
  have hq : 0 ≤ 1 - μ / (4608 * S) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hbound (x : E) (hx : x ∈ X ∧ ‖x - c‖ ≤ 2 * d) : ‖‖x - p‖ ^ 2‖ ≤ (3 * d) ^ 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x c p
    rw [norm_sub_rev c p] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [hx.2]) 2
  have hstep' (x : E) (hx : x ∈ X ∧ ‖x - c‖ ≤ 2 * d) :
      (∫ ω, ‖advance x ω - p‖ ^ 2 ∂Q) ≤
        (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2 + (8 * v) / (64 * S ^ 2) := by
    have ht := hstep x hx.1 hx.2
    have hk : μ / (4608 * S) ≤ μ / (16 * S) :=
      div_le_div_of_nonneg_left hμ.le (by positivity) (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖x - p‖)
    have he : 8 * v / (64 * S ^ 2) = v / (8 * S ^ 2) := by ring
    rw [he]
    nlinarith
  have hi := ClippedExtragradient.bounded_iterate_integral ha Q (fun x => ‖x - p‖ ^ 2)
    (by fun_prop) (Inv := fun x => x ∈ X ∧ ‖x - c‖ ≤ 2 * d)
    (fun x hx ω => ⟨hmem x hx.1 ω, hball x ω⟩) hbound hq hstep' n c
    ⟨hc, by simpa using (show 0 ≤ 2 * d by positivity)⟩
  have hinit : ‖c - p‖ ^ 2 ≤ d ^ 2 := by
    rw [norm_sub_rev]
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hmul := mul_le_mul_of_nonneg_left hinit (pow_nonneg hq n)
  have hfinal := ClippedExtragradient.stage_moment_bound hμ hμS (by positivity : 0 ≤ 8 * v) hnoise hn
  linarith

omit [CompleteSpace E] in
lemma measurable_trialOutput {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (n m : ℕ) (b S d r : ℝ) (anchor center : E) :
    Measurable (trialOutput P n m b S d r anchor center g) :=
  (ClippedExtragradient.measurable_iterateSamples
    (measurable_batchStep hP hg m b S d r anchor center) n).comp measurable_prodMk_left

omit [CompleteSpace E] in
lemma trial_integrable {Q : Measure Ω} [IsProbabilityMeasure Q]
    {P : E → E} (hP : Measurable P) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (n m : ℕ) (b S d r : ℝ) (hd : 0 ≤ d)
    (anchor center p : E) (hp : ‖p - center‖ ≤ d) :
    Integrable (fun ξ => ‖trialOutput P n m b S d r anchor center g ξ - p‖ ^ 2)
      (Measure.pi (fun _ : Fin n => (Measure.pi (fun _ : Fin m => Q)).prod
        (Measure.pi (fun _ : Fin m => Q)))) := by
  exact ClippedExtragradient.iterate_distance_integrable
    (measurable_batchStep hP hg m b S d r anchor center) hd center p
    (fun x ξ => finish_ball P hd _ center _ _) hp n

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] in
lemma trial_mem {X : Set E} {P : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (g : E → Ω → E) (n m : ℕ) (b S d r : ℝ) (hd : 0 ≤ d)
    (anchor center : E) (hc : center ∈ X)
    (ξ : Fin n → (Fin m → Ω) × (Fin m → Ω)) :
    trialOutput P n m b S d r anchor center g ξ ∈ X := by
  apply ClippedExtragradient.iterateSamples_invariant (Inv := fun x => x ∈ X) _ n center hc ξ
  intro x hx samples
  exact finish_mem hP hX hd _ hc _ _

lemma tuned_trial_integral {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X) {g : E → Ω → E}
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε)
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) Q)
    (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) Q)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂Q) ≤ t.σ ^ 2)
    (s : ℕ) (anchor center p : E) (hp : p ∈ X) (hc : center ∈ X)
    (hpc : ‖p - center‖ ≤ radius t s)
    (hnp : ConstrainedMonotone.Normal X p (-(F p + regularization t s • (p - anchor))))
    (hM : ‖F p‖ ≤ rootBound t) (hbias : regularization t s * ‖p - anchor‖ ≤ t.ε) :
    (∫ samples : Fin (innerSteps t s) →
        (Fin (batchSize t s) → Ω) × (Fin (batchSize t s) → Ω),
      ‖trialOutput P (innerSteps t s) (batchSize t s) t.L1 (localScale t s) (radius t s)
        (regularization t s) anchor center g samples - p‖ ^ 2
      ∂Measure.pi (fun _ : Fin (innerSteps t s) =>
        (Measure.pi (fun _ : Fin (batchSize t s) => Q)).prod
          (Measure.pi (fun _ : Fin (batchSize t s) => Q)))) ≤ radius t s ^ 2 / 4096 := by
  have hC := (curvature_pos t hF.L0_pos hF.L1_nonneg hR.le hG hε.le).le
  have hd := radius_pos t hR s
  apply iterate_distance_bound_on
    (measurable_batchStep hP.lipschitz.continuous.measurable hg _ _ _ _ _ _ _)
    (regularization_pos t hR hε s) (localScale_lower t hC hF.L1_nonneg hR hε s)
    hd.le (by positivity) (batchSize_variance t hC hF.L1_nonneg hR hε s)
    center p hc
  · intro x hx samples
    exact finish_mem hP hX hd.le _ hc _ _
  · intro x samples
    exact finish_ball P hd.le _ center _ _
  · exact hpc
  · intro x hx hxc
    exact tuned_batch_integral hP t hF hR hG hε hg hgi hmean hvi hv s
      anchor center x p hp hx hpc hxc hnp hM hbias
  · exact innerSteps_lower t s

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma firstPilot_choice {k : ℕ} (d : ℝ) (v : Fin k → E) (l : List (Fin k)) :
    RobustGradient.firstPilot d v l = 0 ∨ ∃ i, RobustGradient.firstPilot d v l = v i := by
  induction l with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    unfold RobustGradient.firstPilot
    split_ifs
    · exact Or.inr ⟨i, rfl⟩
    · exact ih

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma aggregate_mem {X : Set E} (hX : Convex ℝ X) {k : ℕ} {d : ℝ} (hd : 0 ≤ d)
    {c : E} (hc : c ∈ X) {v : Fin k → E} (hv : ∀ i, v i ∈ X) : aggregate d c v ∈ X := by
  obtain he | ⟨i, he⟩ := firstPilot_choice d (fun i => v i - c) (List.finRange k)
  · change c + clip (2 * d) (RobustGradient.firstPilot d (fun i => v i - c) (List.finRange k)) ∈ X
    rw [he]
    simpa [clip] using hc
  · change c + clip (2 * d) (RobustGradient.firstPilot d (fun i => v i - c) (List.finRange k)) ∈ X
    rw [he]
    exact centered_clip_mem hX hc (hv i) (by positivity)

omit [CompleteSpace E] in
lemma aggregate_failure {Q : Measure Ω} [IsProbabilityMeasure Q] {V : Ω → E}
    (hV : Measurable V) {d : ℝ} (hd : 0 < d) (c p : E) (hp : ‖p - c‖ ≤ d)
    (hvi : Integrable (fun ω => ‖V ω - p‖ ^ 2) Q)
    (hv : (∫ ω, ‖V ω - p‖ ^ 2 ∂Q) ≤ d ^ 2 / 4096) (k : ℕ) :
    (Measure.pi fun _ : Fin k => Q)
      {ξ | d / 2 < ‖aggregate d c (fun i => V (ξ i)) - p‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have he (ω : Ω) : (V ω - c) - (p - c) = V ω - p := by abel
  have hvi' : Integrable (fun ω => ‖(V ω - c) - (p - c)‖ ^ 2) Q := by
    simpa only [he] using hvi
  have hv' : (∫ ω, ‖(V ω - c) - (p - c)‖ ^ 2 ∂Q) ≤ d ^ 2 / 4096 := by
    simpa only [he] using hv
  have ht := ClippedExtragradient.projected_pilot_failure (hV.sub measurable_const) hd 0 (p - c)
    (by simpa using hp) hvi' hv' k
  have hout (ξ : Fin k → Ω) :
      RobustGradient.centeredClip (2 * d) 0
        (RobustGradient.pilotCenter d (fun i => V (ξ i) - c)) - (p - c) =
          aggregate d c (fun i => V (ξ i)) - p := by
    simp only [RobustGradient.centeredClip, aggregate, sub_zero, zero_add]
    abel
  simpa only [Pi.sub_apply, hout] using ht

lemma tuned_stage_confidence {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X) {g : E → Ω → E}
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε)
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) Q)
    (hmean : ∀ x, (∫ ω, g x ω ∂Q) = F x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - F x‖ ^ 2) Q)
    (hv : ∀ x, (∫ ω, ‖g x ω - F x‖ ^ 2 ∂Q) ≤ t.σ ^ 2)
    (s : ℕ) (anchor center p : E) (hp : p ∈ X) (hc : center ∈ X)
    (hpc : ‖p - center‖ ≤ radius t s)
    (hnp : ConstrainedMonotone.Normal X p (-(F p + regularization t s • (p - anchor))))
    (hM : ‖F p‖ ≤ rootBound t) (hbias : regularization t s * ‖p - anchor‖ ≤ t.ε) :
    (Measure.pi (fun _ : Fin (repetitions t) => Measure.pi (fun _ : Fin (innerSteps t s) =>
      (Measure.pi (fun _ : Fin (batchSize t s) => Q)).prod
        (Measure.pi (fun _ : Fin (batchSize t s) => Q)))))
      {ξ | radius t s / 2 < ‖confidenceOutput P (innerSteps t s) (batchSize t s)
        (repetitions t) t.L1 (localScale t s) (radius t s) (regularization t s)
        anchor center g ξ - p‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ repetitions t) := by
  exact aggregate_failure (measurable_trialOutput hP.lipschitz.continuous.measurable hg
    _ _ _ _ _ _ _ _) (radius_pos t hR s) center p hpc
    (trial_integrable hP.lipschitz.continuous.measurable hg _ _ _ _ _ _
      (radius_pos t hR s).le anchor center p hpc)
    (tuned_trial_integral hP hX t hF hR hG hε hg hgi hmean hvi hv s
      anchor center p hp hc hpc hnp hM hbias) (repetitions t)

end OracleTemplate.ProjectedClippedExtragradient
