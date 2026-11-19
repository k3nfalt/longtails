import LongTails.Proofs.HessianAdaptiveCubicResidual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LocalNonlinearExtragradientMoments

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace Ω]

lemma root_taylor_bound (F : E → E) (J : E → E →L[ℝ] E) (p x : E) {M : ℝ}
    (hd : ∀ z, HasFDerivAt F (J z) z)
    (hJ : ∀ u v, ‖J u - J v‖ ≤ M * ‖u - v‖) (hp : F p = 0) :
    ‖F x - J p (x - p)‖ ≤ M / 2 * ‖x - p‖ ^ 2 := by
  have h := HessianAdaptiveCubicResidual.gradient_taylor_on
    (C := Set.univ) (convex_univ) hd (fun u _ v _ => hJ u v)
    p (x - p) (Set.mem_univ _) (Set.mem_univ _)
  simpa only [add_sub_cancel, hp, sub_zero, div_mul_eq_mul_div] using h

lemma integral_root_remainder (F : E → E) (J : E → E →L[ℝ] E) (p : E)
    {M : ℝ} {P : Measure Ω} {X : Ω → E}
    (hd : ∀ z, HasFDerivAt F (J z) z)
    (hJ : ∀ u v, ‖J u - J v‖ ≤ M * ‖u - v‖) (hp : F p = 0)
    (hX : AEStronglyMeasurable X P)
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P) :
    Integrable (fun ω => F (X ω) - J p (X ω - p)) P ∧
      ‖∫ ω, F (X ω) - J p (X ω - p) ∂P‖ ≤
        M / 2 * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun z => (hd z).continuousAt
  have hr : Continuous (fun x => F x - J p (x - p)) :=
    hc.sub ((J p).continuous.comp (continuous_id.sub continuous_const))
  have hb (ω : Ω) := root_taylor_bound F J p (X ω) hd hJ hp
  have hi : Integrable (fun ω => F (X ω) - J p (X ω - p)) P :=
    (hX2.const_mul (M / 2)).mono' (hr.comp_aestronglyMeasurable hX)
      (Filter.Eventually.of_forall hb)
  refine ⟨hi, (norm_integral_le_integral_norm _).trans ?_⟩
  calc
    _ ≤ ∫ ω, M / 2 * ‖X ω - p‖ ^ 2 ∂P :=
      integral_mono hi.norm (hX2.const_mul (M / 2)) hb
    _ = _ := integral_const_mul _ _

lemma integral_linearization [CompleteSpace E] (F : E → E) (A : E →L[ℝ] E) (p : E)
    {P : Measure Ω} {X : Ω → E}
    (hX : Integrable (fun ω => X ω - p) P)
    (hR : Integrable (fun ω => F (X ω) - A (X ω - p)) P) :
    Integrable (fun ω => F (X ω)) P ∧
      (∫ ω, F (X ω) ∂P) = A (∫ ω, X ω - p ∂P) +
        ∫ ω, F (X ω) - A (X ω - p) ∂P := by
  have he : (fun ω => F (X ω)) =
      (fun ω => A (X ω - p) + (F (X ω) - A (X ω - p))) := by
    funext ω
    abel
  constructor
  · rw [he]
    exact (A.integrable_comp hX).add hR
  · conv_lhs => rw [he]
    rw [integral_add (A.integrable_comp hX) hR, A.integral_comp_comm hX]

lemma integral_update_square [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    (x p : E) (η : ℝ) {g : Ω → E}
    (hg : Integrable g P) (hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) P) :
    Integrable (fun ω => ‖x - η • g ω - p‖ ^ 2) P ∧
      (∫ ω, ‖x - η • g ω - p‖ ^ 2 ∂P) = ‖x - p‖ ^ 2 -
        2 * η * ⟪x - p, ∫ ω, g ω ∂P⟫ + η ^ 2 * ∫ ω, ‖g ω‖ ^ 2 ∂P := by
  have he (ω : Ω) : ‖x - η • g ω - p‖ ^ 2 =
      ‖x - p‖ ^ 2 - 2 * η * ⟪x - p, g ω⟫ + η ^ 2 * ‖g ω‖ ^ 2 := by
    rw [show x - η • g ω - p = (x - p) - η • g ω by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hi := (hg.const_inner (x - p)).const_mul (2 * η)
  have hc : Integrable (fun _ : Ω => ‖x - p‖ ^ 2) P := integrable_const _
  have hn := hg2.const_mul (η ^ 2)
  have hci : Integrable (fun ω => ‖x - p‖ ^ 2 - 2 * η * ⟪x - p, g ω⟫) P := hc.sub hi
  constructor
  · simp_rw [he]
    exact (hc.sub hi).add hn
  · simp_rw [he]
    rw [integral_add hci hn, integral_sub hc hi, integral_const_mul,
      integral_const_mul, integral_inner hg]
    simp

lemma extragradient_mean_recursion [CompleteSpace E] (F : E → E) (A : E →L[ℝ] E)
    (p : E) (η : ℝ) {P : Measure Ω} {X Y g q : Ω → E}
    (hX : Integrable (fun ω => X ω - p) P)
    (hg : Integrable g P) (hq : Integrable q P)
    (hY : ∀ ω, Y ω = X ω - η • g ω)
    (hRX : Integrable (fun ω => F (X ω) - A (X ω - p)) P)
    (hRY : Integrable (fun ω => F (Y ω) - A (Y ω - p)) P)
    (hfirst : (∫ ω, g ω ∂P) = ∫ ω, F (X ω) ∂P)
    (hsecond : (∫ ω, q ω ∂P) = ∫ ω, F (Y ω) ∂P) :
    (∫ ω, X ω - η • q ω - p ∂P) =
      (∫ ω, X ω - p ∂P) - η • A (∫ ω, X ω - p ∂P) +
        η ^ 2 • A (A (∫ ω, X ω - p ∂P)) +
        η ^ 2 • A (∫ ω, F (X ω) - A (X ω - p) ∂P) -
        η • (∫ ω, F (Y ω) - A (Y ω - p) ∂P) := by
  have hy (ω : Ω) : Y ω - p = (X ω - p) - η • g ω := by rw [hY]; abel
  have hgi : Integrable (fun ω => η • g ω) P := hg.smul η
  have hqi : Integrable (fun ω => η • q ω) P := hq.smul η
  have hyi : Integrable (fun ω => Y ω - p) P := by
    simp_rw [hy]
    exact hX.sub hgi
  have hymean : (∫ ω, Y ω - p ∂P) = (∫ ω, X ω - p ∂P) - η • ∫ ω, g ω ∂P := by
    simp_rw [hy]
    rw [integral_sub hX hgi, integral_smul]
  have hz (ω : Ω) : X ω - η • q ω - p = (X ω - p) - η • q ω := by abel
  simp_rw [hz]
  rw [integral_sub hX hqi, integral_smul, hsecond,
    (integral_linearization F A p hyi hRY).2, hymean, hfirst,
    (integral_linearization F A p hX hRX).2]
  simp only [map_sub, map_add, map_smul, smul_sub, smul_add, smul_smul]
  module

lemma stochastic_gradient_contraction [CompleteSpace E] {P : Measure Ω}
    [IsProbabilityMeasure P] (x p v : E) {L μ ρ : ℝ} {g : Ω → E}
    (hL : 0 < L) (hρ : 0 < ρ) (hμ : 0 ≤ μ)
    (hg : Integrable g P) (hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    (hmean : (∫ ω, g ω ∂P) = v)
    (hsgc : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ ρ * ‖v‖ ^ 2)
    (hmono : μ * ‖x - p‖ ^ 2 ≤ ⟪x - p, v⟫)
    (hlip : ‖v‖ ^ 2 ≤ L ^ 2 * ‖x - p‖ ^ 2) :
    (∫ ω, ‖x - (μ / (ρ * L ^ 2)) • g ω - p‖ ^ 2 ∂P) ≤
      (1 - μ ^ 2 / (ρ * L ^ 2)) * ‖x - p‖ ^ 2 := by
  let η := μ / (ρ * L ^ 2)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 * η by positivity)
  have hb := hsgc.trans (mul_le_mul_of_nonneg_left hlip hρ.le)
  have hn := mul_le_mul_of_nonneg_left hb (sq_nonneg η)
  have he := (integral_update_square x p η hg hg2).2
  rw [hmean] at he
  have halg : 2 * η * μ - η ^ 2 * (ρ * L ^ 2) = μ ^ 2 / (ρ * L ^ 2) := by
    dsimp [η]
    field_simp
    ring
  change (∫ ω, ‖x - η • g ω - p‖ ^ 2 ∂P) ≤ _
  rw [← halg]
  nlinarith

lemma stochastic_half_growth [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    (x p v : E) {L ρ : ℝ} {g : Ω → E} (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hg : Integrable g P) (hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    (hmean : (∫ ω, g ω ∂P) = v)
    (hsgc : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ ρ * ‖v‖ ^ 2)
    (hmono : 0 ≤ ⟪x - p, v⟫) (hlip : ‖v‖ ^ 2 ≤ L ^ 2 * ‖x - p‖ ^ 2) :
    (∫ ω, ‖x - (1 / (4 * L)) • g ω - p‖ ^ 2 ∂P) ≤
      (1 + ρ / 16) * ‖x - p‖ ^ 2 := by
  let η : ℝ := 1 / (4 * L)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have he := (integral_update_square x p η hg hg2).2
  rw [hmean] at he
  have hb := mul_le_mul_of_nonneg_left
    (hsgc.trans (mul_le_mul_of_nonneg_left hlip hρ)) (sq_nonneg η)
  have hi : η ^ 2 * (ρ * (L ^ 2 * ‖x - p‖ ^ 2)) = ρ / 16 * ‖x - p‖ ^ 2 := by
    dsimp [η]
    field_simp
    ring
  rw [hi] at hb
  have hn := mul_nonneg (show 0 ≤ 2 * η by positivity) hmono
  change (∫ ω, ‖x - η • g ω - p‖ ^ 2 ∂P) ≤ _
  nlinarith

lemma stochastic_full_growth [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    (x p : E) {L ρ : ℝ} {q : Ω → E} (hL : 0 < L)
    (hq : Integrable q P) (hq2 : Integrable (fun ω => ‖q ω‖ ^ 2) P)
    (hb : (∫ ω, ‖q ω‖ ^ 2 ∂P) ≤ ρ * L ^ 2 * ((1 + ρ / 16) * ‖x - p‖ ^ 2)) :
    (∫ ω, ‖x - (1 / (4 * L)) • q ω - p‖ ^ 2 ∂P) ≤
      (2 + ρ / 8 + ρ ^ 2 / 128) * ‖x - p‖ ^ 2 := by
  let η : ℝ := 1 / (4 * L)
  have hstep (ω : Ω) : ‖x - η • q ω - p‖ ^ 2 ≤
      2 * ‖x - p‖ ^ 2 + 2 * η ^ 2 * ‖q ω‖ ^ 2 := by
    have ht := norm_sub_le (x - p) (η • q ω)
    have hn := norm_nonneg ((x - p) - η • q ω)
    have he : x - η • q ω - p = (x - p) - η • q ω := by abel
    rw [he]
    have hs : ‖η • q ω‖ ^ 2 = η ^ 2 * ‖q ω‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [sq_nonneg (‖x - p‖ - ‖η • q ω‖), norm_nonneg (x - p),
      norm_nonneg (η • q ω)]
  have hc : Integrable (fun _ : Ω => 2 * ‖x - p‖ ^ 2) P := integrable_const _
  have hi : Integrable (fun ω => 2 * ‖x - p‖ ^ 2 + 2 * η ^ 2 * ‖q ω‖ ^ 2) P :=
    hc.add (hq2.const_mul (2 * η ^ 2))
  have ht := integral_mono (integral_update_square x p η hq hq2).1 hi hstep
  rw [integral_add hc (hq2.const_mul (2 * η ^ 2)), integral_const_mul (2 * η ^ 2)] at ht
  simp only [integral_const, probReal_univ, one_smul] at ht
  have hn := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * η ^ 2 by positivity)
  have he : 2 * η ^ 2 * (ρ * L ^ 2 * ((1 + ρ / 16) * ‖x - p‖ ^ 2)) =
      (ρ / 8 + ρ ^ 2 / 128) * ‖x - p‖ ^ 2 := by
    dsimp [η]
    field_simp
    ring
  rw [he] at hn
  change (∫ ω, ‖x - η • q ω - p‖ ^ 2 ∂P) ≤ _
  nlinarith

omit [InnerProductSpace ℝ E] in
lemma fresh_oracle_second_moment {Ξ : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} {Q : Measure Ξ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (g : E → Ξ → E) {X : Ω → E} {C : ℝ}
    (hX : Measurable X) (hg : Measurable (Function.uncurry g))
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hg2 : ∀ x, Integrable (fun ξ => ‖g x ξ‖ ^ 2) Q)
    (hb : ∀ x, (∫ ξ, ‖g x ξ‖ ^ 2 ∂Q) ≤ C * ‖x - p‖ ^ 2) :
    Integrable (fun w : Ω × Ξ => ‖g (X w.1) w.2‖ ^ 2) (P.prod Q) ∧
      (∫ w : Ω × Ξ, ‖g (X w.1) w.2‖ ^ 2 ∂P.prod Q) ≤
        C * ∫ ω, ‖X ω - p‖ ^ 2 ∂P := by
  let V : Ω × Ξ → ℝ := fun w => ‖g (X w.1) w.2‖ ^ 2
  have hm : Measurable V :=
    ((hg.comp ((hX.comp measurable_fst).prodMk measurable_snd)).norm).pow_const 2
  have he (ω : Ω) : (∫ ξ, ‖V (ω, ξ)‖ ∂Q) = ∫ ξ, V (ω, ξ) ∂Q := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => Real.norm_of_nonneg (sq_nonneg _)
  have ho : Integrable (fun ω => ∫ ξ, ‖V (ω, ξ)‖ ∂Q) P := by
    apply (hX2.const_mul C).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_of_nonneg (integral_nonneg fun ξ => norm_nonneg _), he]
    exact hb (X ω)
  have hi : Integrable V (P.prod Q) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall (fun ω => hg2 (X ω)), ho⟩
  refine ⟨hi, ?_⟩
  change (∫ w, V w ∂P.prod Q) ≤ _
  rw [integral_prod V hi]
  calc
    _ ≤ ∫ ω, C * ‖X ω - p‖ ^ 2 ∂P :=
      integral_mono hi.integral_prod_left (hX2.const_mul C) (fun ω => hb (X ω))
    _ = _ := integral_const_mul _ _

lemma fresh_oracle_mean {Ξ : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p : E) (F : E → E) (g : E → Ξ → E) {X : Ω → E} {C : ℝ}
    (hX : Measurable X) (hg : Measurable (Function.uncurry g))
    (hX2 : Integrable (fun ω => ‖X ω - p‖ ^ 2) P)
    (hg2 : ∀ x, Integrable (fun ξ => ‖g x ξ‖ ^ 2) Q)
    (hb : ∀ x, (∫ ξ, ‖g x ξ‖ ^ 2 ∂Q) ≤ C * ‖x - p‖ ^ 2)
    (hmean : ∀ x, (∫ ξ, g x ξ ∂Q) = F x) :
    Integrable (fun w : Ω × Ξ => g (X w.1) w.2) (P.prod Q) ∧
      (∫ w : Ω × Ξ, g (X w.1) w.2 ∂P.prod Q) = ∫ ω, F (X ω) ∂P := by
  have hm : Measurable (fun w : Ω × Ξ => g (X w.1) w.2) :=
    hg.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have h2 := (fresh_oracle_second_moment p g hX hg hX2 hg2 hb).1
  have hi : Integrable (fun w : Ω × Ξ => g (X w.1) w.2) (P.prod Q) := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    dsimp
    nlinarith [sq_nonneg (‖g (X w.1) w.2‖ - 1 / 2)]
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hmean (X ω))

end LongTails.Proofs.LocalNonlinearExtragradientMoments
