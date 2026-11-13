import LongTails.Proofs.StructuredGaussianVariationalNoise
import LongTails.Proofs.GaussianVariationalGuarantee

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StructuredGaussianVariational

open LongTails.Setups.GaussianVariationalInference
open LongTails.Setups.StructuredGaussianVariationalInference
open OracleTemplate.GaussianVariational

variable {d : ℕ} {S : Fin d → Finset (Fin d)} {L μ : ℝ} {V : Point d → ℝ}

noncomputable def patternNoise (L μ : ℝ) (d w : ℕ) : ℝ := (2 + patternTau d w (L / μ)) * L * d

lemma continuous_maskedStep (h : Potential L μ V) (S : Fin d → Finset (Fin d)) (η : ℝ) :
    Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) =>
      maskedStep S η x.1 (gradient V (sample x.1.1 x.1.2 x.2)) x.2) := by
  have hG : Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) =>
      gradient V (sample x.1.1 x.1.2 x.2)) := h.continuous_grad.comp continuous_sample
  have hGi : ∀ i, Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) =>
      gradient V (sample x.1.1 x.1.2 x.2) i) := fun i =>
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).comp hG
  unfold maskedStep proxScale gradLoc gradScale maskScale
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    dsimp only
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_apply i).comp (continuous_fst.comp continuous_fst)).sub
      (continuous_const.mul (hGi i))
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    dsimp only
    have hC : Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) => x.1.2 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
    have hCii : Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) => x.1.2 i i) :=
      (continuous_apply i).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
    have hxi : ∀ k, Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) => x.2 k) :=
      fun k => (continuous_apply k).comp continuous_snd
    have hgs : ∀ k l, Continuous (fun x : (Location d × Scale d) × (Fin d → ℝ) =>
        if l ∈ S k then (if l ≤ k then gradient V (sample x.1.1 x.1.2 x.2) k * x.2 l else 0)
        else 0) := by
      intro k l
      by_cases hl : l ∈ S k
      · by_cases hlk : l ≤ k
        · simp only [hl, hlk, ↓reduceIte]
          exact (hGi k).mul (hxi l)
        · simp only [hl, hlk, ↓reduceIte]
          exact continuous_const
      · simp only [hl, ↓reduceIte]
        exact continuous_const
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact (continuous_proxLog η).comp (hCii.sub (continuous_const.mul (hgs i i)))
    · simp only [hij, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hC.sub (continuous_const.mul (hgs i j))

lemma measurable_maskedStep_fixed (h : Potential L μ V) (S : Fin d → Finset (Fin d)) (η : ℝ)
    (z : Location d × Scale d) :
    Measurable (fun ξ : Fin d → ℝ => maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) :=
  (continuous_maskedStep h S η).measurable.comp (measurable_const.prodMk measurable_id)

lemma masked_step_deterministic (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hCs : IsCholesky Cs) {z : Location d × Scale d} (hz : IsCholesky z.2)
    {η : ℝ} (hη : 0 < η) (hηL : η * L ≤ 1) (ghat : Location d × Scale d)
    (hpC : IsCholesky (proxPair η (z - η • ghat)).2) :
    objectivePair V (proxPair η (z - η • ghat)) - objective V ms Cs ≤
      1 / (2 * η) * ((1 - η * μ) * sqd z (ms, Cs) - sqd (proxPair η (z - η • ghat)) (ms, Cs)) +
      pin (meanPair V z - ghat) (proxPair η (z - η • ghat) - (ms, Cs)) := by
  set gbar := meanPair V z with hgbar
  set y := z - η • ghat with hy
  set p := proxPair η y with hpdef
  set w : Location d × Scale d := (ms, Cs) with hw
  have hp : p = proxPair η y := rfl
  have hlow1 : IsLower (p.2 - z.2) := isLower_sub hpC.1 hz.1
  have hlow2 : IsLower (Cs - z.2) := isLower_sub hCs.1 hz.1
  have hEu : energy V p.1 p.2 ≤ energy V z.1 z.2 + pin gbar (p - z) + L / 2 * sqd p z :=
    energy_upper h z.1 p.1 hlow1
  have hEl : energy V z.1 z.2 + pin gbar (w - z) + μ / 2 * sqd w z ≤ energy V ms Cs :=
    energy_lower h z.1 ms hlow2
  have hlog := prox_log_ineq hη y hCs.2 ms
  rw [← hp] at hlog
  have hobj : objectivePair V p - objective V ms Cs =
      energy V p.1 p.2 - energy V ms Cs + (-∑ i, Real.log (p.2 i i) - -∑ i, Real.log (Cs i i)) := by
    unfold objectivePair
    rw [objective_eq, objective_eq]
    ring
  have e1 : pin gbar (p - z) - pin gbar (w - z) = pin gbar (p - w) := by
    rw [pin_sub_right, pin_sub_right, pin_sub_right]
    ring
  have hyp : y - p = (z - p) - η • ghat := by
    rw [hy]
    abel
  have e2 : pin (y - p) (w - p) = pin (z - p) (w - p) - η * pin ghat (w - p) := by
    rw [hyp, pin_sub_left, pin_smul_left]
  have e3 : pin (z - p) (w - p) = -pin (z - p) (p - w) := by
    rw [pin_sub_right, pin_sub_right]
    ring
  have e4 : pin ghat (w - p) = -pin ghat (p - w) := by
    rw [pin_sub_right, pin_sub_right]
    ring
  have e5 : pin (gbar - ghat) (p - w) = pin gbar (p - w) - pin ghat (p - w) := pin_sub_left _ _ _
  have e6 := pin_three z p w
  have e7 : sqd p z = sqd z p := sqd_comm _ _
  have e8 : sqd w z = sqd z w := sqd_comm _ _
  have hs := sqd_nonneg z p
  have hL : L ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
  have hLs : L / 2 * sqd z p ≤ 1 / (2 * η) * sqd z p := by
    have : L / 2 ≤ 1 / (2 * η) := by
      rw [show 1 / (2 * η) = (1 / η) / 2 by ring]
      linarith
    exact mul_le_mul_of_nonneg_right this hs
  have hinv : 1 / η * (pin (z - p) (w - p) - η * pin ghat (w - p)) =
      1 / η * pin (z - p) (w - p) - pin ghat (w - p) := by
    field_simp
  have hA : 1 / η * pin (z - p) (p - w) = 1 / (2 * η) * (sqd z w - sqd p w - sqd z p) := by
    rw [← e6]
    field_simp
  rw [e2, hinv, e3, e4] at hlog
  rw [hobj, e5]
  have hfin : 1 / (2 * η) * ((1 - η * μ) * sqd z w - sqd p w) =
      1 / (2 * η) * (sqd z w - sqd p w) - μ / 2 * sqd z w := by
    field_simp; ring1
  rw [hfin]
  have hsplit : 1 / (2 * η) * (sqd z w - sqd p w - sqd z p) =
      1 / (2 * η) * (sqd z w - sqd p w) - 1 / (2 * η) * sqd z p := by ring
  rw [e7] at hEu
  rw [e8] at hEl
  linarith [hA, hsplit]


lemma pattern_bregmanMean_le_gap (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsPatternOptimal V S ms Cs) (m : Location d) {C : Scale d} (hC : InFamily S C) :
    bregmanMean V ms Cs m C ≤ objective V m C - objective V ms Cs := by
  have hlow : IsLower (C - Cs) := isLower_sub hC.1.1 hopt.1.1.1
  rw [bregmanMean_identity h ms Cs m hlow,
    pattern_opt_pinner h hopt (m - ms) hlow (isSupported_sub hC.2 hopt.1.2), objective_eq,
    objective_eq]
  have hterm : ∀ i, (C - Cs) i i / Cs i i ≥ Real.log (C i i) - Real.log (Cs i i) := by
    intro i
    have hc := hC.1.2 i
    have hs := hopt.1.1.2 i
    rw [← Real.log_div hc.ne' hs.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hc hs)
    simp only [Pi.sub_apply]
    have he : (C i i - Cs i i) / Cs i i = C i i / Cs i i - 1 := by field_simp
    linarith
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib] at hs
  linarith

lemma masked_step_expectation (h : Potential L μ V) {w : ℕ} (hS : IsPattern S w)
    {ms : Location d} {Cs : Scale d} (hopt : IsPatternOptimal V S ms Cs)
    {z : Location d × Scale d} (hz : InFamily S z.2) {η : ℝ} (hη : 0 < η) (hηL : η * L ≤ 1) :
    Integrable (fun ξ => objectivePair V (maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) -
      objective V ms Cs) (noiseLaw d) ∧
    Integrable (fun ξ => sqd (maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs))
      (noiseLaw d) ∧
    ∫ ξ, (objectivePair V (maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) -
      objective V ms Cs) ∂noiseLaw d ≤
      1 / (2 * η) * ((1 - η * μ) * sqd z (ms, Cs) -
        ∫ ξ, sqd (maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs) ∂noiseLaw d) +
      η * (4 * patternSmooth L μ d w * bregmanMean V ms Cs z.1 z.2 +
        2 * patternNoise L μ d w) := by
  set wp : Location d × Scale d := (ms, Cs) with hwp
  set gbar := meanPair V z
  set gS := maskPair S gbar
  set G := optPair Cs
  set gz := fun ξ => maskPair S (sampleGrad V z ξ)
  set q := proxPair η (z - η • gS)
  set p := fun ξ => maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ
  set Q := fun ξ => pin (gz ξ - gS) (gz ξ - gS)
  set N := fun ξ => pin (gS - gz ξ) (q - wp)
  set r := sqd z wp
  set D := bregmanMean V ms Cs z.1 z.2
  set σ2 := patternNoise L μ d w
  set 𝓛 := patternSmooth L μ d w
  have hGl : IsLower G.2 := isLower_optScale Cs
  have hGS : IsSupported S G.2 := isSupported_optScale hS Cs
  have hzwS : IsSupported S (z - wp).2 := isSupported_sub hz.2 hopt.1.2
  have hzwL : IsLower (z - wp).2 := isLower_sub hz.1.1 hopt.1.1.1
  have hpF : ∀ ξ, InFamily S (p ξ).2 := fun ξ => maskedStep_family hS hη hz _ ξ
  have hpeq : ∀ ξ, p ξ = proxPair η (z - η • gz ξ) := fun ξ => rfl
  have hmean : ∀ c : Location d × Scale d, Integrable (fun ξ => pin (gz ξ) c) (noiseLaw d) ∧
      ∫ ξ, pin (gz ξ) c ∂noiseLaw d = pin gS c := by
    intro c
    have hc := integral_pin_sampleGrad h z (maskPair S c)
    have he : ∀ ξ, pin (gz ξ) c = pin (sampleGrad V z ξ) (maskPair S c) := fun ξ => pin_maskPair _ _
    simp_rw [he]
    refine ⟨hc.1, ?_⟩
    rw [hc.2, ← pin_maskPair]
  have hQeq : ∀ ξ, Q ξ = maskNormSq S (sampleGrad V z ξ - gbar) := by
    intro ξ
    simp only [Q, gz, gS, maskNormSq]
    rw [maskPair_sub]
  have hQm : Measurable Q := by
    have he : Q = fun ξ => maskNormSq S (sampleGrad V z ξ - gbar) := funext hQeq
    rw [he]
    exact ((continuous_maskNormSq S).comp (continuous_id.sub continuous_const)).measurable.comp
      (measurable_sampleGrad h z)
  have hQi : Integrable Q (noiseLaw d) := by
    refine Integrable.mono' (integrable_pin_sampleGrad_sub h z gbar) hQm.aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pin_self_nonneg _)]
    change Q ξ ≤ _
    rw [hQeq]
    exact pin_maskPair_self_le _
  have hNi : Integrable N (noiseLaw d) := by
    have he : N = fun ξ => pin gS (q - wp) - pin (gz ξ) (q - wp) := by
      funext ξ
      exact pin_sub_left _ _ _
    rw [he]
    exact (integrable_const _).subL (hmean (q - wp)).1
  have hN0 : ∫ ξ, N ξ ∂noiseLaw d = 0 := by
    have he : N = fun ξ => pin gS (q - wp) - pin (gz ξ) (q - wp) := by
      funext ξ
      exact pin_sub_left _ _ _
    rw [he, integral_sub (integrable_const _) (hmean (q - wp)).1, (hmean (q - wp)).2]
    simp only [integral_const, probReal_univ, one_smul]
    exact sub_self _
  have hpw : ∀ ξ, pin (gbar - gz ξ) (p ξ - wp) = pin (gS - gz ξ) (p ξ - wp) := by
    intro ξ
    have hsup : IsSupported S (p ξ - wp).2 := isSupported_sub (hpF ξ).2 hopt.1.2
    have e : pin gS (p ξ - wp) = pin gbar (p ξ - wp) := pin_maskPair_supported gbar hsup
    rw [pin_sub_left, pin_sub_left, e]
  have hpq : ∀ ξ, pin (gS - gz ξ) (p ξ - wp) ≤ η * Q ξ + N ξ := by
    intro ξ
    have hsplit : pin (gS - gz ξ) (p ξ - wp) = pin (gS - gz ξ) (p ξ - q) + N ξ := by
      simp only [N]
      rw [pin_sub_right, pin_sub_right, pin_sub_right]
      ring
    have hy := pin_young (gS - gz ξ) (p ξ - q) hη
    have hlip : pin (p ξ - q) (p ξ - q) ≤ η ^ 2 * Q ξ := by
      have h1 := proxPair_sq_lip hη (z - η • gz ξ) (z - η • gS)
      rw [sqd_eq_pin, sqd_eq_pin] at h1
      have he : z - η • gz ξ - (z - η • gS) = η • (gS - gz ξ) := by
        rw [smul_sub]
        abel
      rw [he, pin_smul_self] at h1
      have hQ' : pin (gS - gz ξ) (gS - gz ξ) = Q ξ := pin_swap_self _ _
      rw [hQ'] at h1
      rw [hpeq ξ]
      exact h1
    have hQ : pin (gS - gz ξ) (gS - gz ξ) = Q ξ := pin_swap_self _ _
    rw [hsplit]
    rw [hQ] at hy
    have : 1 / (2 * η) * pin (p ξ - q) (p ξ - q) ≤ 1 / (2 * η) * (η ^ 2 * Q ξ) :=
      mul_le_mul_of_nonneg_left hlip (by positivity)
    have he2 : 1 / (2 * η) * (η ^ 2 * Q ξ) = η / 2 * Q ξ := by field_simp
    linarith
  have hdet : ∀ ξ, objectivePair V (p ξ) - objective V ms Cs ≤
      1 / (2 * η) * ((1 - η * μ) * r - sqd (p ξ) wp) + η * Q ξ + N ξ := by
    intro ξ
    have h1 := masked_step_deterministic h (ms := ms) hopt.1.1 hz.1 hη hηL (gz ξ) (hpF ξ).1
    rw [← hpeq ξ] at h1
    have := hpq ξ
    have := hpw ξ
    linarith
  have hfix := proxPair_fixed (ms := ms) hη hopt.1.1
  have hrbound : ∀ ξ, sqd (p ξ) wp ≤ 2 * r + 2 * (η ^ 2 * pin (gz ξ - G) (gz ξ - G)) := by
    intro ξ
    have h1 := proxPair_sq_lip hη (z - η • gz ξ) (wp - η • G)
    have hfix' : proxPair η (wp - η • G) = wp := hfix
    rw [hfix'] at h1
    rw [sqd_eq_pin (z - η • gz ξ) (wp - η • G)] at h1
    have he : z - η • gz ξ - (wp - η • G) = (z - wp) + -(η • (gz ξ - G)) := by
      rw [smul_sub]
      abel
    rw [he] at h1
    have h2 := pin_add_le (z - wp) (-(η • (gz ξ - G)))
    have h3 : pin (-(η • (gz ξ - G))) (-(η • (gz ξ - G))) =
        η ^ 2 * pin (gz ξ - G) (gz ξ - G) := by
      rw [← neg_smul, pin_smul_self]
      ring
    have h4 : pin (z - wp) (z - wp) = r := (sqd_eq_pin z wp).symm
    rw [hpeq ξ]
    linarith
  have hgzw : ∀ ξ, gz ξ - G = maskPair S (sampleGrad V z ξ - sampleGrad V wp ξ) +
      maskPair S (sampleGrad V wp ξ - G) := by
    intro ξ
    simp only [gz]
    rw [maskPair_sub, maskPair_sub, maskPair_of_supported hGS]
    abel
  have hGle : ∀ ξ, pin (gz ξ - G) (gz ξ - G) ≤
      2 * maskNormSq S (sampleGrad V z ξ - sampleGrad V wp ξ) +
        2 * maskNormSq S (sampleGrad V wp ξ - G) := by
    intro ξ
    rw [hgzw]
    exact pin_add_le _ _
  have hES := pattern_expected_smoothness h hS ms (Cs := Cs) z.1 (C := z.2) hzwL hzwS
  have hVar := pattern_variance h hS hopt
  have hWp : ∀ ξ, maskNormSq S (sampleGrad V wp ξ - G) =
      maskNormSq S (sampleGrad V wp ξ) - 2 * pin (sampleGrad V wp ξ) G + pin G G := by
    intro ξ
    unfold maskNormSq
    rw [maskPair_sub, maskPair_of_supported hGS, pin_sub_self_expand,
      pin_maskPair_supported _ hGS]
  have hcw := integral_pin_sampleGrad h wp G
  have hWpi : Integrable (fun ξ => maskNormSq S (sampleGrad V wp ξ - G)) (noiseLaw d) := by
    simp_rw [hWp]
    exact (hVar.1.subL (hcw.1.const_mul 2)).addL (integrable_const _)
  have hWpv : ∫ ξ, maskNormSq S (sampleGrad V wp ξ - G) ∂noiseLaw d ≤ σ2 := by
    simp_rw [hWp]
    rw [integral_add (hVar.1.subL (hcw.1.const_mul 2)) (integrable_const _),
      integral_sub hVar.1 (hcw.1.const_mul 2), integral_const_mul, hcw.2,
      pattern_opt_pin h hopt hGl hGS]
    simp only [integral_const, probReal_univ, one_smul]
    have := hVar.2
    have := pin_self_nonneg G
    change _ ≤ (2 + patternTau d w (L / μ)) * L * d
    linarith
  have hGm : Measurable (fun ξ => pin (gz ξ - G) (gz ξ - G)) := by
    have he : (fun ξ => pin (gz ξ - G) (gz ξ - G)) =
        fun ξ => maskNormSq S (sampleGrad V z ξ - G) := by
      funext ξ
      simp only [gz, maskNormSq]
      rw [maskPair_sub, maskPair_of_supported hGS]
    rw [he]
    exact ((continuous_maskNormSq S).comp (continuous_id.sub continuous_const)).measurable.comp
      (measurable_sampleGrad h z)
  have hGi : Integrable (fun ξ => pin (gz ξ - G) (gz ξ - G)) (noiseLaw d) := by
    refine Integrable.mono' ((hES.1.const_mul 2).addL (hWpi.const_mul 2))
      hGm.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pin_self_nonneg _)]
    exact hGle ξ
  have hGv : ∫ ξ, pin (gz ξ - G) (gz ξ - G) ∂noiseLaw d ≤ 4 * 𝓛 * D + 2 * σ2 := by
    have := integral_mono hGi ((hES.1.const_mul 2).addL (hWpi.const_mul 2)) hGle
    rw [integral_add (hES.1.const_mul 2) (hWpi.const_mul 2), integral_const_mul,
      integral_const_mul] at this
    have h1 := hES.2
    linarith
  have hQv : ∫ ξ, Q ξ ∂noiseLaw d ≤ ∫ ξ, pin (gz ξ - G) (gz ξ - G) ∂noiseLaw d := by
    have hexp : ∀ ξ, pin (gz ξ - G) (gz ξ - G) =
        Q ξ + 2 * (pin (gz ξ) (gS - G) - pin gS (gS - G)) + pin (gS - G) (gS - G) := by
      intro ξ
      have h1 := pin_add_self (gz ξ - gS) (gS - G)
      have he : gz ξ - gS + (gS - G) = gz ξ - G := by abel
      rw [he] at h1
      have h2 : pin (gz ξ - gS) (gS - G) = pin (gz ξ) (gS - G) - pin gS (gS - G) :=
        pin_sub_left _ _ _
      simp only [Q]
      linarith
    simp_rw [hexp]
    have h2 := hmean (gS - G)
    have h3 : Integrable (fun ξ => 2 * (pin (gz ξ) (gS - G) - pin gS (gS - G))) (noiseLaw d) :=
      (h2.1.subL (integrable_const _)).const_mul 2
    rw [integral_add (hQi.addL h3) (integrable_const _), integral_add hQi h3, integral_const_mul,
      integral_sub h2.1 (integrable_const _), h2.2]
    simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero, add_zero]
    linarith [pin_self_nonneg (gS - G)]
  have hri : Integrable (fun ξ => sqd (p ξ) wp) (noiseLaw d) := by
    refine Integrable.mono' ((integrable_const (2 * r)).addL ((hGi.const_mul (η ^ 2)).const_mul 2))
      ((measurable_sqd wp).comp (measurable_maskedStep_fixed h S η z)).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sqd_nonneg _ _)]
    have := hrbound ξ
    linarith
  have hgap0 : ∀ ξ, 0 ≤ objectivePair V (p ξ) - objective V ms Cs := fun ξ =>
    sub_nonneg.mpr (hopt.2 _ _ (hpF ξ))
  have hoi : Integrable (fun ξ => objectivePair V (p ξ) - objective V ms Cs) (noiseLaw d) := by
    have hB : Integrable (fun ξ => 1 / (2 * η) * ((1 - η * μ) * r) + η * Q ξ + N ξ) (noiseLaw d) :=
      ((integrable_const _).addL (hQi.const_mul η)).addL hNi
    refine Integrable.mono' hB (((measurable_objectivePair h).comp
      (measurable_maskedStep_fixed h S η z)).sub_const _).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgap0 ξ)]
    have h1 := hdet ξ
    have h2 := sqd_nonneg (p ξ) wp
    have h3 : 0 ≤ 1 / (2 * η) * sqd (p ξ) wp := by positivity
    have : 1 / (2 * η) * ((1 - η * μ) * r - sqd (p ξ) wp) =
        1 / (2 * η) * ((1 - η * μ) * r) - 1 / (2 * η) * sqd (p ξ) wp := by ring
    linarith
  refine ⟨hoi, hri, ?_⟩
  have hR : Integrable (fun ξ => 1 / (2 * η) * ((1 - η * μ) * r - sqd (p ξ) wp) + η * Q ξ + N ξ)
      (noiseLaw d) :=
    ((((integrable_const _).subL hri).const_mul _).addL (hQi.const_mul η)).addL hNi
  have hm := integral_mono hoi hR hdet
  rw [integral_add (((integrable_const _).subL hri).const_mul _ |>.addL (hQi.const_mul η)) hNi,
    integral_add (((integrable_const _).subL hri).const_mul _) (hQi.const_mul η), hN0,
    integral_const_mul, integral_sub (integrable_const _) hri, integral_const_mul] at hm
  simp only [integral_const, probReal_univ, one_smul, add_zero] at hm
  have hQint : ∫ ξ, η * Q ξ ∂noiseLaw d = η * ∫ ξ, Q ξ ∂noiseLaw d := integral_const_mul _ _
  rw [hQint] at hm
  have hfinal : η * ∫ ξ, Q ξ ∂noiseLaw d ≤ η * (4 * 𝓛 * D + 2 * σ2) :=
    mul_le_mul_of_nonneg_left (hQv.trans hGv) hη.le
  change ∫ ξ, (objectivePair V (p ξ) - objective V ms Cs) ∂noiseLaw d ≤
    1 / (2 * η) * ((1 - η * μ) * r - ∫ ξ, sqd (p ξ) wp ∂noiseLaw d) + η * (4 * 𝓛 * D + 2 * σ2)
  linarith only [hm, hfinal]

lemma family_combo {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {z z' : Location d × Scale d}
    (hz : InFamily S z.2) (hz' : InFamily S z'.2) : InFamily S (θ • z + (1 - θ) • z').2 := by
  refine ⟨isCholesky_combo hθ0 hθ1 hz.1 hz'.1, fun i j hj => ?_⟩
  simp [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, hz.2 i j hj, hz'.2 i j hj]

noncomputable def patternStepAt (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) (k : ℕ) (z : Location d × Scale d)
    (ξ : Fin d → ℝ) : Location d × Scale d :=
  maskedStep S (stepSize μ a k) z (gradient V (sample z.1 z.2 ξ)) ξ

noncomputable def patternPot (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (ms : Location d) (Cs : Scale d) (μ a : ℝ) :
    (k0 n : ℕ) → (Location d × Scale d) → (Fin n → Fin d → ℝ) → ℝ
  | _, 0, _, _ => 0
  | k0, n + 1, z, ξ =>
      averageWeight a k0 / 2 * gap V ms Cs (patternStepAt V S μ a k0 z (ξ 0)) +
        patternPot V S ms Cs μ a (k0 + 1) n (patternStepAt V S μ a k0 z (ξ 0)) (fun i => ξ i.succ)

noncomputable def patternWsum (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) :
    (k0 n : ℕ) → (Location d × Scale d) → (Fin n → Fin d → ℝ) → Location d × Scale d
  | _, 0, _, _ => 0
  | k0, n + 1, z, ξ =>
      averageWeight a k0 • patternStepAt V S μ a k0 z (ξ 0) +
        patternWsum V S μ a (k0 + 1) n (patternStepAt V S μ a k0 z (ξ 0)) (fun i => ξ i.succ)

lemma patternStepAt_family {w : ℕ} (hS : IsPattern S w) (hμ : 0 < μ) {a : ℝ} (ha : 2 ≤ a) (k : ℕ) {z : Location d × Scale d}
    (hz : InFamily S z.2) (ξ : Fin d → ℝ) : InFamily S (patternStepAt V S μ a k z ξ).2 :=
  maskedStep_family hS (stepSize_pos hμ ha k) hz _ ξ

lemma measurable_patternStepAt (h : Potential L μ V) (S : Fin d → Finset (Fin d)) (a : ℝ) (k : ℕ) :
    Measurable (fun x : (Location d × Scale d) × (Fin d → ℝ) => patternStepAt V S μ a k x.1 x.2) :=
  (continuous_maskedStep h S (stepSize μ a k)).measurable

lemma measurable_patternPot (h : Potential L μ V) (S : Fin d → Finset (Fin d)) (ms : Location d) (Cs : Scale d) (a : ℝ) (n : ℕ) :
    ∀ k0, Measurable (fun x : (Location d × Scale d) × (Fin n → Fin d → ℝ) =>
      patternPot V S ms Cs μ a k0 n x.1 x.2) := by
  induction n with
  | zero => intro k0; exact measurable_const
  | succ n ih =>
    intro k0
    have ht : Measurable (fun x : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
        (patternStepAt V S μ a k0 x.1 (x.2 0), fun i : Fin n => x.2 i.succ)) := by
      have hs : Measurable (fun x : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
          patternStepAt V S μ a k0 x.1 (x.2 0)) :=
        (measurable_patternStepAt h S a k0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
          measurable_snd))
      exact hs.prodMk (by fun_prop)
    exact (((measurable_gap h ms Cs).comp ht.fst).const_mul _).add ((ih (k0 + 1)).comp ht)

lemma patternPot_nonneg {w : ℕ} (hS : IsPattern S w) {ms : Location d} {Cs : Scale d} (hopt : IsPatternOptimal V S ms Cs) (hμ : 0 < μ)
    {a : ℝ} (ha : 2 ≤ a) (n : ℕ) :
    ∀ k0 z ξ, InFamily S (z : Location d × Scale d).2 → 0 ≤ patternPot V S ms Cs μ a k0 n z ξ := by
  induction n with
  | zero => intro k0 z ξ _; simp [patternPot]
  | succ n ih =>
    intro k0 z ξ hz
    unfold patternPot
    have hc := patternStepAt_family (V := V) hS hμ ha k0 hz (ξ 0)
    have h1 : 0 ≤ gap V ms Cs (patternStepAt V S μ a k0 z (ξ 0)) := sub_nonneg.mpr (hopt.2 _ _ hc)
    have h2 := ih (k0 + 1) _ (fun i => ξ i.succ) hc
    have h3 := averageWeight_pos ha k0
    positivity

lemma patternPot_bound (h : Potential L μ V) {w : ℕ} (hS : IsPattern S w) {ms : Location d} {Cs : Scale d} (hopt : IsPatternOptimal V S ms Cs)
    (n : ℕ) : ∀ k0 (z : Location d × Scale d), InFamily S z.2 →
      Integrable (patternPot V S ms Cs μ (patternOffset L μ d w) k0 n z) (Measure.pi fun _ : Fin n => noiseLaw d) ∧
      ∫ ξ, patternPot V S ms Cs μ (patternOffset L μ d w) k0 n z ξ ∂Measure.pi (fun _ : Fin n => noiseLaw d) ≤
        μ / 4 * (((k0 : ℝ) + patternOffset L μ d w - 1) * ((k0 : ℝ) + patternOffset L μ d w - 2)) * sqd z (ms, Cs) +
          8 * patternSmooth L μ d w / μ * bregmanMean V ms Cs z.1 z.2 +
          4 * n * patternNoise L μ d w / μ := by
  set a := patternOffset L μ d w with ha_def
  set 𝓛 := patternSmooth L μ d w
  set σ2 := patternNoise L μ d w
  have hadef : a = 16 * 𝓛 / μ + 2 := rfl
  have h𝓛def : 𝓛 = L * (2 + patternTau d w (L / μ)) := rfl
  have hσdef : σ2 = (2 + patternTau d w (L / μ)) * L * d := rfl
  clear_value a 𝓛 σ2
  have hμ := h.pos
  have hL := h.L_pos
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr h.le
  have hτ := patternTau_nonneg d w hκ
  have h𝓛 : 2 * L ≤ 𝓛 := by
    have e : L * (2 + patternTau d w (L / μ)) = 2 * L + L * patternTau d w (L / μ) := by ring
    rw [h𝓛def, e]
    linarith [mul_nonneg hL.le hτ]
  have h𝓛0 : 0 < 𝓛 := by linarith
  have ha : 2 ≤ a := by
    rw [hadef]
    have : 0 ≤ 16 * 𝓛 / μ := div_nonneg (by linarith) hμ.le
    linarith
  have hσ : 0 ≤ σ2 := by
    rw [hσdef]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  induction n with
  | zero =>
    intro k0 z hz
    refine ⟨by simp [patternPot], ?_⟩
    simp only [patternPot, integral_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    have hk : (0 : ℝ) ≤ k0 := Nat.cast_nonneg k0
    have h1 : 0 ≤ ((k0 : ℝ) + a - 1) * ((k0 : ℝ) + a - 2) := by nlinarith
    have h2 := sqd_nonneg z (ms, Cs)
    have h3 := bregmanMean_lower h (ms := ms) (Cs := Cs) z.1 (isLower_sub hz.1.1 hopt.1.1.1)
    have h4 : 0 ≤ μ / 2 * sqDist z.1 ms z.2 Cs := by
      have := sqDist_nonneg z.1 ms z.2 Cs
      positivity
    have h5 : 0 ≤ 8 * 𝓛 / μ * bregmanMean V ms Cs z.1 z.2 := by
      have : 0 ≤ 8 * 𝓛 / μ := by positivity
      exact mul_nonneg this (by linarith)
    have h6 : 0 ≤ μ / 4 * (((k0 : ℝ) + a - 1) * ((k0 : ℝ) + a - 2)) * sqd z (ms, Cs) := by
      have : 0 ≤ μ / 4 := by positivity
      exact mul_nonneg (mul_nonneg this h1) h2
    linarith
  | succ n ih =>
    intro k0 z hz
    set η := stepSize μ a k0
    have hη : 0 < η := stepSize_pos hμ ha k0
    have hk : (0 : ℝ) ≤ k0 := Nat.cast_nonneg k0
    have hηa : η * (μ * ((k0 : ℝ) + a)) = 2 := by
      simp only [η, stepSize]
      field_simp
    have hηL : η * L ≤ 1 := by
      have h1 : 16 * 𝓛 / μ ≤ (k0 : ℝ) + a := by rw [hadef]; linarith
      have h2 : 16 * 𝓛 ≤ μ * ((k0 : ℝ) + a) := by
        rw [div_le_iff₀ hμ] at h1
        linarith
      nlinarith
    have hstep := masked_step_expectation h hS hopt hz hη hηL
    set p := fun ξ : Fin d → ℝ => patternStepAt V S μ a k0 z ξ
    have hpC : ∀ ξ, InFamily S (p ξ).2 := fun ξ => patternStepAt_family hS hμ ha k0 hz ξ
    let q := Measure.pi (fun _ : Fin n => noiseLaw d)
    let F := fun x : (Fin d → ℝ) × (Fin n → Fin d → ℝ) =>
      averageWeight a k0 / 2 * gap V ms Cs (p x.1) + patternPot V S ms Cs μ a (k0 + 1) n (p x.1) x.2
    have hFm : Measurable F := by
      have hp : Measurable (fun x : (Fin d → ℝ) × (Fin n → Fin d → ℝ) => p x.1) :=
        (measurable_patternStepAt h S a k0).comp (measurable_const.prodMk measurable_fst)
      exact (((measurable_gap h ms Cs).comp hp).const_mul _).add
        ((measurable_patternPot h S ms Cs a n (k0 + 1)).comp (hp.prodMk measurable_snd))
    have hFnn : ∀ x, 0 ≤ F x := by
      intro x
      have h1 : 0 ≤ gap V ms Cs (p x.1) := sub_nonneg.mpr (hopt.2 _ _ (hpC x.1))
      have h2 := patternPot_nonneg (V := V) hS hopt hμ ha n (k0 + 1) (p x.1) x.2 (hpC x.1)
      have h3 := averageWeight_pos ha k0
      positivity
    let B := fun ω : Fin d → ℝ => averageWeight a k0 / 2 * gap V ms Cs (p ω) +
      (μ / 4 * (((k0 + 1 : ℕ) : ℝ) + a - 1) * ((((k0 + 1 : ℕ) : ℝ) + a - 2)) * sqd (p ω) (ms, Cs) +
        8 * 𝓛 / μ * bregmanMean V ms Cs (p ω).1 (p ω).2 + 4 * n * σ2 / μ)
    have hsec : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q := by
      intro ω
      simp only [F]
      exact (integrable_const _).addL (ih (k0 + 1) (p ω) (hpC ω)).1
    have hsecb : ∀ ω, ∫ ξ, F (ω, ξ) ∂q ≤ B ω := by
      intro ω
      simp only [F, B]
      rw [integral_add (integrable_const _) (ih (k0 + 1) (p ω) (hpC ω)).1]
      simp only [integral_const, probReal_univ, one_smul]
      have := (ih (k0 + 1) (p ω) (hpC ω)).2
      push_cast at this ⊢
      linarith
    have hgapi : Integrable (fun ω => gap V ms Cs (p ω)) (noiseLaw d) := hstep.1
    have hri : Integrable (fun ω => sqd (p ω) (ms, Cs)) (noiseLaw d) := hstep.2.1
    have hDle : ∀ ω, bregmanMean V ms Cs (p ω).1 (p ω).2 ≤ gap V ms Cs (p ω) := fun ω =>
      pattern_bregmanMean_le_gap h hopt (p ω).1 (hpC ω)
    have hD0 : ∀ ω, 0 ≤ bregmanMean V ms Cs (p ω).1 (p ω).2 := by
      intro ω
      have := bregmanMean_lower h (ms := ms) (Cs := Cs) (p ω).1 (isLower_sub (hpC ω).1.1 hopt.1.1.1)
      have := sqDist_nonneg (p ω).1 ms (p ω).2 Cs
      nlinarith
    have hDi : Integrable (fun ω => bregmanMean V ms Cs (p ω).1 (p ω).2) (noiseLaw d) := by
      refine Integrable.mono' hgapi (((measurable_bregmanMean h ms Cs).comp
        (measurable_maskedStep_fixed h S η z)).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 ω)]
      exact hDle ω
    have hBi : Integrable B (noiseLaw d) :=
      (hgapi.const_mul _).addL (((hri.const_mul _).addL (hDi.const_mul _)).addL (integrable_const _))
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) (noiseLaw d) := by
      refine hBi.mono' hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ξ => norm_nonneg _)]
      simp only [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]
      exact hsecb ω
    have hFi : Integrable F ((noiseLaw d).prod q) :=
      (integrable_prod_iff hFm.aestronglyMeasurable).mpr
        ⟨Filter.Eventually.of_forall hsec, hint⟩
    have hmp : Measurable (patternPot V S ms Cs μ a k0 (n + 1) z) :=
      (measurable_patternPot h S ms Cs a (n + 1) k0).of_uncurry_left
    have heq : (fun x : (Fin d → ℝ) × (Fin n → Fin d → ℝ) =>
        patternPot V S ms Cs μ a k0 (n + 1) z (Fin.cons x.1 x.2)) = F := by
      funext x
      simp only [patternPot, Fin.cons_zero, Fin.cons_succ, F, p]
    have hcons := StochasticGradient.cons_measurePreserving (noiseLaw d) n
    have hpi : Integrable (patternPot V S ms Cs μ a k0 (n + 1) z) (Measure.pi fun _ : Fin (n + 1) => noiseLaw d) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, heq] using hFi)
    refine ⟨hpi, ?_⟩
    have hcalc : ∫ ξ, patternPot V S ms Cs μ a k0 (n + 1) z ξ ∂Measure.pi (fun _ : Fin (n + 1) => noiseLaw d) ≤
        ∫ ω, B ω ∂noiseLaw d := by
      calc _ = ∫ x, F x ∂(noiseLaw d).prod q := by
            rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable,
              heq]
        _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂noiseLaw d := integral_prod F hFi
        _ ≤ ∫ ω, B ω ∂noiseLaw d := integral_mono hFi.integral_prod_left hBi hsecb
    have hBval : ∫ ω, B ω ∂noiseLaw d ≤
        (((k0 : ℝ) + a - 1) * ∫ ω, gap V ms Cs (p ω) ∂noiseLaw d) +
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d +
          4 * n * σ2 / μ := by
      have hpt : ∀ ω, B ω ≤ ((k0 : ℝ) + a - 1) * gap V ms Cs (p ω) +
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * sqd (p ω) (ms, Cs) + 4 * n * σ2 / μ := by
        intro ω
        simp only [B, averageWeight]
        push_cast
        have h1 : 8 * 𝓛 / μ ≤ ((k0 : ℝ) + a - 1) / 2 := by
          rw [hadef]
          have e : 16 * 𝓛 / μ = 2 * (8 * 𝓛 / μ) := by ring
          rw [e]
          have : 0 ≤ (k0 : ℝ) := hk
          linarith
        have h2 := mul_le_mul_of_nonneg_right h1 (hD0 ω)
        have h3 := mul_le_mul_of_nonneg_left (hDle ω) (by linarith : (0 : ℝ) ≤ ((k0 : ℝ) + a - 1) / 2)
        have he : (k0 : ℝ) + 1 + a - 1 = (k0 : ℝ) + a := by ring
        have he2 : (k0 : ℝ) + 1 + a - 2 = (k0 : ℝ) + a - 1 := by ring
        rw [he, he2]
        nlinarith
      have hRi : Integrable (fun ω => ((k0 : ℝ) + a - 1) * gap V ms Cs (p ω) +
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * sqd (p ω) (ms, Cs) + 4 * n * σ2 / μ)
          (noiseLaw d) := ((hgapi.const_mul _).addL (hri.const_mul _)).addL (integrable_const _)
      have := integral_mono hBi hRi hpt
      rw [integral_add ((hgapi.const_mul _).addL (hri.const_mul _)) (integrable_const _),
        integral_add (hgapi.const_mul _) (hri.const_mul _), integral_const_mul,
        integral_const_mul] at this
      simpa only [integral_const, probReal_univ, one_smul] using this
    have hstep2 := hstep.2.2
    have hgap_eq : ∫ ω, gap V ms Cs (p ω) ∂noiseLaw d =
        ∫ ξ, (objectivePair V (maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) -
          objective V ms Cs) ∂noiseLaw d := rfl
    have hr_eq : ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d =
        ∫ ξ, sqd (maskedStep S η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs) ∂noiseLaw d := rfl
    rw [← hgap_eq, ← hr_eq] at hstep2
    have hpos : 0 < (k0 : ℝ) + a := by linarith
    have hημ : η * μ * ((k0 : ℝ) + a) = 2 := by rw [← hηa]; ring
    have hinv : 1 / (2 * η) = μ * ((k0 : ℝ) + a) / 4 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      have e : μ * ((k0 : ℝ) + a) * (2 * η) = 2 * (η * μ * ((k0 : ℝ) + a)) := by ring
      rw [e, hημ]
      norm_num
    have hone : 1 - η * μ = ((k0 : ℝ) + a - 2) / ((k0 : ℝ) + a) := by
      rw [eq_div_iff hpos.ne']
      have e : (1 - η * μ) * ((k0 : ℝ) + a) = ((k0 : ℝ) + a) - η * μ * ((k0 : ℝ) + a) := by ring
      rw [e, hημ]
    have hwη : ((k0 : ℝ) + a - 1) * η ≤ 2 / μ := by
      rw [le_div_iff₀ hμ]
      have e : ((k0 : ℝ) + a - 1) * η * μ = η * μ * ((k0 : ℝ) + a) - η * μ := by ring
      rw [e, hημ]
      have : 0 ≤ η * μ := by positivity
      linarith
    rw [hinv, hone] at hstep2
    have hscale := mul_le_mul_of_nonneg_left hstep2 (by linarith : (0 : ℝ) ≤ (k0 : ℝ) + a - 1)
    have hA : ((k0 : ℝ) + a - 1) * (μ * ((k0 : ℝ) + a) / 4 *
        (((k0 : ℝ) + a - 2) / ((k0 : ℝ) + a) * sqd z (ms, Cs) -
          ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d)) =
        μ / 4 * (((k0 : ℝ) + a - 1) * ((k0 : ℝ) + a - 2)) * sqd z (ms, Cs) -
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d := by
      field_simp
    have hDz0 : 0 ≤ bregmanMean V ms Cs z.1 z.2 := by
      have := bregmanMean_lower h (ms := ms) (Cs := Cs) z.1 (isLower_sub hz.1.1 hopt.1.1.1)
      have := sqDist_nonneg z.1 ms z.2 Cs
      nlinarith
    rw [mul_add ((k0 : ℝ) + a - 1), hA] at hscale
    have hnoise : ((k0 : ℝ) + a - 1) * (η * (4 * patternSmooth L μ d w *
        bregmanMean V ms Cs z.1 z.2 + 2 * patternNoise L μ d w)) ≤
        8 * 𝓛 / μ * bregmanMean V ms Cs z.1 z.2 + 4 * σ2 / μ := by
      have e1 : patternSmooth L μ d w = 𝓛 := by rw [h𝓛def]; rfl
      have e2 : patternNoise L μ d w = σ2 := by rw [hσdef]; rfl
      rw [e1, e2]
      have hX : 0 ≤ 4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2 :=
        add_nonneg (mul_nonneg (by linarith) hDz0) (by linarith)
      have := mul_le_mul_of_nonneg_right hwη hX
      calc ((k0 : ℝ) + a - 1) * (η * (4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2)) =
            ((k0 : ℝ) + a - 1) * η * (4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2) := by ring
        _ ≤ 2 / μ * (4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2) := this
        _ = 8 * 𝓛 / μ * bregmanMean V ms Cs z.1 z.2 + 4 * σ2 / μ := by ring
    have hsplitn : 4 * ((n : ℝ) + 1) * σ2 / μ = 4 * n * σ2 / μ + 4 * σ2 / μ := by ring
    push_cast
    linarith only [hcalc, hBval, hscale, hnoise, hsplitn]

lemma patternAvg_bound (h : Potential L μ V) {w : ℕ} (hS : IsPattern S w) (ms : Location d) (Cs : Scale d)
    {a : ℝ} (ha : 2 ≤ a) (n : ℕ) (hn : 0 < n) :
    ∀ k0 (z : Location d × Scale d) ξ, InFamily S z.2 →
      InFamily S ((wmass a k0 n)⁻¹ • patternWsum V S μ a k0 n z ξ).2 ∧
      gap V ms Cs ((wmass a k0 n)⁻¹ • patternWsum V S μ a k0 n z ξ) ≤
        2 * patternPot V S ms Cs μ a k0 n z ξ / wmass a k0 n := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro k0 z ξ hz
    have hμ := h.pos
    set z1 := patternStepAt V S μ a k0 z (ξ 0)
    have hz1 : InFamily S z1.2 := patternStepAt_family hS hμ ha k0 hz (ξ 0)
    have hw := averageWeight_pos ha k0
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hm : wmass a k0 1 = averageWeight a k0 := by simp [wmass]
      have hs : patternWsum V S μ a k0 1 z ξ = averageWeight a k0 • z1 := by simp [patternWsum, z1]
      have hp : patternPot V S ms Cs μ a k0 1 z ξ = averageWeight a k0 / 2 * gap V ms Cs z1 := by
        simp [patternPot, z1]
      rw [hm, hs, hp, smul_smul, inv_mul_cancel₀ hw.ne', one_smul]
      refine ⟨hz1, le_of_eq ?_⟩
      field_simp
    · obtain ⟨hA, hgap⟩ := ih hnpos (k0 + 1) z1 (fun i => ξ i.succ) hz1
      set M' := wmass a (k0 + 1) n
      set S' := patternWsum V S μ a (k0 + 1) n z1 (fun i => ξ i.succ)
      set P' := patternPot V S ms Cs μ a (k0 + 1) n z1 (fun i => ξ i.succ)
      have hM' : 0 < M' := wmass_pos ha (k0 + 1) hnpos
      have hm : wmass a k0 (n + 1) = averageWeight a k0 + M' := rfl
      have hs : patternWsum V S μ a k0 (n + 1) z ξ = averageWeight a k0 • z1 + S' := rfl
      have hp : patternPot V S ms Cs μ a k0 (n + 1) z ξ = averageWeight a k0 / 2 * gap V ms Cs z1 + P' := rfl
      set w0 := averageWeight a k0 with hw0
      have hsum : 0 < w0 + M' := by linarith
      have hsumne : w0 + M' ≠ 0 := hsum.ne'
      have hM'ne : M' ≠ 0 := hM'.ne'
      set θ := w0 / (w0 + M') with hθ
      have hθ0 : 0 ≤ θ := by positivity
      have hθ1 : θ ≤ 1 := by
        rw [hθ, div_le_one hsum]
        linarith
      have h1θ : 1 - θ = M' / (w0 + M') := by
        rw [hθ]
        field_simp; ring1
      have hcomb : (w0 + M')⁻¹ • (w0 • z1 + S') = θ • z1 + (1 - θ) • (M'⁻¹ • S') := by
        rw [h1θ, smul_add, smul_smul, smul_smul]
        congr 2
        · rw [hθ]
          ring
        · field_simp
      rw [hm, hs, hp, hcomb]
      refine ⟨family_combo hθ0 hθ1 hz1 hA, ?_⟩
      have hc := gap_combo h ms Cs hθ0 hθ1 hz1.1 hA.1
      have h1 : (1 - θ) * gap V ms Cs (M'⁻¹ • S') ≤ (1 - θ) * (2 * P' / M') :=
        mul_le_mul_of_nonneg_left hgap (by linarith)
      have hfin : θ * gap V ms Cs z1 + (1 - θ) * (2 * P' / M') =
          2 * (w0 / 2 * gap V ms Cs z1 + P') / (w0 + M') := by
        rw [h1θ, hθ]
        field_simp
      linarith

noncomputable def patternLast (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) :
    (k0 n : ℕ) → (Location d × Scale d) → (Fin n → Fin d → ℝ) → Location d × Scale d
  | _, 0, z, _ => z
  | k0, n + 1, z, ξ => patternLast V S μ a (k0 + 1) n (patternStepAt V S μ a k0 z (ξ 0)) (fun i => ξ i.succ)

noncomputable def patternStep (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) (s : MaskedState d) : MaskedState d :=
  ⟨s.seeds, s.count + 1, patternStepAt V S μ a s.count s.current (s.seeds s.count),
    s.total + averageWeight a s.count • patternStepAt V S μ a s.count s.current (s.seeds s.count),
    s.mass + averageWeight a s.count⟩

lemma patternStep_trace (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) (n : ℕ) :
    ∀ (ω : ℕ → Fin d → ℝ) k0 z T M,
      (patternStep V S μ a)^[n] (⟨ω, k0, z, T, M⟩ : MaskedState d) =
      ⟨ω, k0 + n, patternLast V S μ a k0 n z (fun i => ω (k0 + i)),
        T + patternWsum V S μ a k0 n z (fun i => ω (k0 + i)), M + wmass a k0 n⟩ := by
  induction n with
  | zero =>
    intro ω k0 z T M
    simp only [Function.iterate_zero, id_eq, patternLast, patternWsum, wmass, add_zero]
  | succ n ih =>
    intro ω k0 z T M
    rw [Function.iterate_succ_apply]
    have hstep : patternStep V S μ a ⟨ω, k0, z, T, M⟩ =
        ⟨ω, k0 + 1, patternStepAt V S μ a k0 z (ω k0), T + averageWeight a k0 • patternStepAt V S μ a k0 z (ω k0),
          M + averageWeight a k0⟩ := rfl
    rw [hstep, ih]
    have hseq : (fun i : Fin n => ω (k0 + 1 + i)) = fun i : Fin n => ω (k0 + (i.succ : ℕ)) := by
      funext i
      congr 1
      simp only [Fin.val_succ]
      omega
    have h0 : ω (k0 + ((0 : Fin (n + 1)) : ℕ)) = ω k0 := by simp
    simp only [patternLast, patternWsum, wmass, h0, hseq]
    congr 1
    all_goals first | omega | abel

lemma pattern_trace (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) (m0 : Location d) (C0 : Scale d) (n : ℕ)
    (ω : ℕ → Fin d → ℝ) (k0 : ℕ) (z T : Location d × Scale d) (M : ℝ) :
      (fun s => (structuredProxSgd S μ a m0 C0).update s
        (gradient V ((structuredProxSgd S μ a m0 C0).query s).2))^[n]
        (⟨ω, k0, z, T, M⟩ : MaskedState d) =
      ⟨ω, k0 + n, patternLast V S μ a k0 n z (fun i => ω (k0 + i)),
        T + patternWsum V S μ a k0 n z (fun i => ω (k0 + i)), M + wmass a k0 n⟩ :=
  patternStep_trace V S μ a n ω k0 z T M

lemma measurable_patternWsum (h : Potential L μ V) (S : Fin d → Finset (Fin d)) (a : ℝ) (n : ℕ) :
    ∀ k0, Measurable (fun x : (Location d × Scale d) × (Fin n → Fin d → ℝ) =>
      patternWsum V S μ a k0 n x.1 x.2) := by
  induction n with
  | zero => intro k0; exact measurable_const
  | succ n ih =>
    intro k0
    have ht : Measurable (fun x : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
        (patternStepAt V S μ a k0 x.1 (x.2 0), fun i : Fin n => x.2 i.succ)) := by
      have hs : Measurable (fun x : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
          patternStepAt V S μ a k0 x.1 (x.2 0)) :=
        (measurable_patternStepAt h S a k0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
          measurable_snd))
      exact hs.prodMk (by fun_prop)
    have h1 := ht.fst
    have h2 := (ih (k0 + 1)).comp ht
    exact ((h1.fst.const_smul (averageWeight a k0)).add h2.fst).prodMk
      ((h1.snd.const_smul (averageWeight a k0)).add h2.snd)

noncomputable def patternOutput (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ a : ℝ) (m0 : Location d) (C0 : Scale d) (K : ℕ)
    (ω : ℕ → Fin d → ℝ) : Location d × Scale d :=
  (structuredProxSgd S μ a m0 C0).output
    ((fun s => (structuredProxSgd S μ a m0 C0).update s
      (gradient V ((structuredProxSgd S μ a m0 C0).query s).2))^[K]
      ((structuredProxSgd S μ a m0 C0).initial ω))

lemma patternOutput_eq (V : Point d → ℝ) (S : Fin d → Finset (Fin d)) (μ : ℝ) {a : ℝ} (ha : 2 ≤ a) (m0 : Location d) (C0 : Scale d)
    {K : ℕ} (hK : 0 < K) (ω : ℕ → Fin d → ℝ) :
    patternOutput V S μ a m0 C0 K ω = (wmass a 0 K)⁻¹ • patternWsum V S μ a 0 K (m0, C0) (fun i => ω i) := by
  unfold patternOutput
  have hi : (structuredProxSgd S μ a m0 C0).initial ω = (⟨ω, 0, (m0, C0), 0, 0⟩ : MaskedState d) :=
    rfl
  rw [hi, pattern_trace]
  have hm := wmass_pos ha 0 hK
  simp only [zero_add]
  change (if wmass a 0 K = 0 then _ else (wmass a 0 K)⁻¹ • patternWsum V S μ a 0 K (m0, C0) _) = _
  simp only [hm.ne', ↓reduceIte]

lemma pattern_main_guarantee (h : Potential L μ V) {w : ℕ} (hS : IsPattern S w) {ms : Location d} {Cs : Scale d}
    (hopt : IsPatternOptimal V S ms Cs) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) {m0 : Location d}
    {C0 : Scale d} (hC0 : InFamily S C0) (hdist : sqDist m0 ms C0 Cs ≤ R ^ 2) {K : ℕ}
    (hK1 : 1 ≤ K)
    (hK : (2 + patternTau d w (L / μ)) * (26 * L * R / Real.sqrt (μ * ε) + 32 * d * L / (μ * ε)) ≤ K) :
    Measurable (patternOutput V S μ (patternOffset L μ d w) m0 C0 K) ∧
    (∀ ω, InFamily S (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2) ∧
    Integrable (fun ω => objective V (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).1
      (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 - objective V ms Cs)
      (Measure.infinitePi fun _ : ℕ => noiseLaw d) ∧
    (∫ ω, objective V (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).1
      (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 - objective V ms Cs
      ∂Measure.infinitePi fun _ : ℕ => noiseLaw d) ≤ ε := by
  have hμ := h.pos
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr h.le
  have hτ : 0 ≤ patternTau d w (L / μ) := patternTau_nonneg d w hκ
  have ha : 2 ≤ patternOffset L μ d w := by
    have : 0 ≤ 16 * patternSmooth L μ d w / μ := by
      unfold patternSmooth
      have := h.L_pos
      positivity
    unfold patternOffset
    linarith
  have hK0 : 0 < K := hK1
  have hpre := StochasticGradient.prefix_measurePreserving (noiseLaw d) K
  have hout : ∀ ω, patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω =
      (wmass (patternOffset L μ d w) 0 K)⁻¹ • patternWsum V S μ (patternOffset L μ d w) 0 K (m0, C0) (fun i => ω i) :=
    fun ω => patternOutput_eq V S μ ha m0 C0 hK0 ω
  have hz0 : InFamily S (m0, C0).2 := hC0
  have havg := fun ω : ℕ → Fin d → ℝ =>
    patternAvg_bound h hS ms Cs ha K hK0 0 (m0, C0) (fun i : Fin K => ω i) hz0
  have hW := wmass_pos ha 0 hK0
  have hwsm : Measurable (fun ω : ℕ → Fin d → ℝ =>
      patternWsum V S μ (patternOffset L μ d w) 0 K (m0, C0) (fun i : Fin K => ω i)) :=
    (measurable_patternWsum h S (patternOffset L μ d w) K 0).comp (measurable_const.prodMk hpre.measurable)
  have hmeas : Measurable (patternOutput V S μ (patternOffset L μ d w) m0 C0 K) := by
    have he : patternOutput V S μ (patternOffset L μ d w) m0 C0 K = fun ω =>
        (wmass (patternOffset L μ d w) 0 K)⁻¹ • patternWsum V S μ (patternOffset L μ d w) 0 K (m0, C0) (fun i => ω i) :=
      funext hout
    rw [he]
    exact (hwsm.fst.const_smul (wmass (patternOffset L μ d w) 0 K)⁻¹).prodMk
      (hwsm.snd.const_smul (wmass (patternOffset L μ d w) 0 K)⁻¹)
  refine ⟨hmeas, fun ω => by rw [hout]; exact (havg ω).1, ?_⟩
  have hpot := patternPot_bound h hS hopt K 0 (m0, C0) hz0
  have hgap_le : ∀ ω, objective V (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).1
      (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 - objective V ms Cs ≤
      2 / wmass (patternOffset L μ d w) 0 K *
        patternPot V S ms Cs μ (patternOffset L μ d w) 0 K (m0, C0) (fun i => ω i) := by
    intro ω
    have h2 := (havg ω).2
    rw [hout ω]
    unfold gap objectivePair at h2
    exact h2.trans (le_of_eq (by ring))
  have hgap_nn : ∀ ω, 0 ≤ objective V (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).1
      (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 - objective V ms Cs := by
    intro ω
    have hc : InFamily S (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 := by
      rw [hout]
      exact (havg ω).1
    exact sub_nonneg.mpr (hopt.2 _ _ hc)
  have hpm : Measurable (fun ξ : Fin K → Fin d → ℝ =>
      patternPot V S ms Cs μ (patternOffset L μ d w) 0 K (m0, C0) ξ) :=
    (measurable_patternPot h S ms Cs (patternOffset L μ d w) K 0).of_uncurry_left
  have hpotP : Integrable (fun ω : ℕ → Fin d → ℝ =>
      patternPot V S ms Cs μ (patternOffset L μ d w) 0 K (m0, C0) (fun i => ω i))
      (Measure.infinitePi fun _ : ℕ => noiseLaw d) :=
    hpre.integrable_comp_of_integrable hpot.1
  have hpotval : ∫ ω, patternPot V S ms Cs μ (patternOffset L μ d w) 0 K (m0, C0) (fun i => ω i)
      ∂Measure.infinitePi (fun _ : ℕ => noiseLaw d) =
      ∫ ξ, patternPot V S ms Cs μ (patternOffset L μ d w) 0 K (m0, C0) ξ ∂Measure.pi (fun _ : Fin K => noiseLaw d) := by
    have hm := integral_map (μ := Measure.infinitePi fun _ : ℕ => noiseLaw d)
      hpre.measurable.aemeasurable
      (f := fun ξ : Fin K → Fin d → ℝ => patternPot V S ms Cs μ (patternOffset L μ d w) 0 K (m0, C0) ξ)
      (by rw [hpre.map_eq]; exact hpm.aestronglyMeasurable)
    rw [hpre.map_eq] at hm
    exact hm.symm
  have hgmeas : Measurable (fun ω => objective V (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).1
      (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 - objective V ms Cs) :=
    ((measurable_objectivePair h).comp hmeas).sub_const _
  have hint : Integrable (fun ω => objective V (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).1
      (patternOutput V S μ (patternOffset L μ d w) m0 C0 K ω).2 - objective V ms Cs)
      (Measure.infinitePi fun _ : ℕ => noiseLaw d) := by
    refine Integrable.mono' (hpotP.const_mul (2 / wmass (patternOffset L μ d w) 0 K))
      hgmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgap_nn ω)]
    exact hgap_le ω
  refine ⟨hint, ?_⟩
  have hm := integral_mono hint (hpotP.const_mul (2 / wmass (patternOffset L μ d w) 0 K)) hgap_le
  rw [integral_const_mul, hpotval] at hm
  have hD := bregmanMean_upper h (ms := ms) (Cs := Cs) m0 (isLower_sub hC0.1.1 hopt.1.1.1)
  have hD0 : 0 ≤ bregmanMean V ms Cs m0 C0 := by
    have := bregmanMean_lower h (ms := ms) (Cs := Cs) m0 (isLower_sub hC0.1.1 hopt.1.1.1)
    have := sqDist_nonneg m0 ms C0 Cs
    nlinarith
  have hDR : bregmanMean V ms Cs m0 C0 ≤ L / 2 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_left hdist (by have := h.L_pos; positivity : (0 : ℝ) ≤ L / 2)
    exact hD.trans this
  have hbound := hpot.2
  simp only [Nat.cast_zero] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound
    (by positivity : (0 : ℝ) ≤ 2 / wmass (patternOffset L μ d w) 0 K)
  have halg := budget_algebra (L := L) (μ := μ) (τ := patternTau d w (L / μ)) (R := R) (ε := ε)
    (dd := d) (K := K) (W := wmass (patternOffset L μ d w) 0 K) (r := sqd (m0, C0) (ms, Cs))
    (D := bregmanMean V ms Cs m0 C0) (A := patternOffset L μ d w) hμ h.le hτ (Nat.cast_nonneg d) hR hε
    (by exact_mod_cast hK1) (wmass_ge ha K) (sqd_nonneg _ _) hdist hD0 hDR rfl hK
  have hsm : patternSmooth L μ d w = L * (2 + patternTau d w (L / μ)) := rfl
  have hns : patternNoise L μ d w = (2 + patternTau d w (L / μ)) * L * d := rfl
  rw [hsm, hns] at hscaled
  linarith


end OracleTemplate.StructuredGaussianVariational
