import Mathlib.Tactic
import LongTails.Setups.RipmGeneral
import LongTails.Proofs.RipmSmoothGeometry
import LongTails.Proofs.RipmConditional
import LongTails.Proofs.RipmRegularity
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmVariance

noncomputable section

lemma variance_difference {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ) (xs : Core.Vec d)
    (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x : Core.Vec d) :
    (∫ i, ‖I.grad i x - I.grad i xs‖ ^ 2 ∂I.law.toMeasure) ≤
      2 * L * (Core.objective I x - Core.objective I xs) := by
  have hmy := LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp I L Lg xs sigmaSq hS x
  have hmz := LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp I L Lg xs sigmaSq hS xs
  have hzI := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hmz
  have hd : MemLp (fun i => I.grad i x - I.grad i xs) 2 I.law.toMeasure := by
    simpa only [Pi.sub_def] using hmy.sub hmz
  have hdI := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hiI := hzI.inner_const (𝕜 := ℝ) (x - xs)
  have hrI := ((hS.componentIntegrable x).sub' (hS.componentIntegrable xs)).sub' hiI
  have hinter :
      (∫ i, inner ℝ (I.grad i xs) (x - xs) ∂I.law.toMeasure) =
        inner ℝ (Core.meanGradient I xs) (x - xs) := by
    calc
      _ = ∫ i, inner ℝ (x - xs) (I.grad i xs) ∂I.law.toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun i => real_inner_comm _ _)
      _ = inner ℝ (x - xs) (Core.meanGradient I xs) := integral_inner hzI (x - xs)
      _ = _ := real_inner_comm _ _
  have hb := integral_mono_ae hdI (hrI.const_mul (2 * L))
    (Filter.Eventually.of_forall (fun i =>
      LongTails.Proofs.RipmSmoothGeometry.cocoercivity (I.component i) (I.grad i) L hS.smoothPos
        (hS.componentGradient i) (hS.componentSmooth i) (hS.componentConvex i) x xs))
  rw [integral_const_mul, integral_sub
      ((hS.componentIntegrable x).sub' (hS.componentIntegrable xs)) hiI,
    integral_sub (hS.componentIntegrable x) (hS.componentIntegrable xs), hinter,
    ← hS.averageEq x, ← hS.averageEq xs] at hb
  have hopt := LongTails.Proofs.RipmSmoothGeometry.composite_optimality
    I L Lg xs sigmaSq hS xs x hS.minimizer
  have hbreg : I.average x - I.average xs -
      inner ℝ (Core.meanGradient I xs) (x - xs) ≤
        Core.objective I x - Core.objective I xs := by
    change _ ≤ (I.average x + Core.regularizer I x) -
      (I.average xs + Core.regularizer I xs)
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hbreg (by
    have hL := hS.smoothPos
    positivity))


lemma variance_transfer {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ) (xs : Core.Vec d)
    (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x : Core.Vec d) (gamma : ℝ) (hgamma : 0 < gamma) :
    Integrable (fun i => ‖I.grad i x‖ ^ 2) I.law.toMeasure ∧
      (∫ i, ‖I.grad i x‖ ^ 2 ∂I.law.toMeasure) ≤
        2 * L * (1 + gamma) * (Core.objective I x - Core.objective I xs) +
          (1 + 1 / gamma) * sigmaSq := by
  have hx := LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp I L Lg xs sigmaSq hS x
  have hs := LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp I L Lg xs sigmaSq hS xs
  have hdiff : MemLp (fun i => I.grad i x - I.grad i xs) 2 I.law.toMeasure := by
    simpa only [Pi.sub_def] using hx.sub hs
  have hxI := (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  have hdI := (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
  have hstar := LongTails.Proofs.RipmSmoothGeometry.solution_moment_transfer
    I L Lg xs sigmaSq hS xs hS.minimizer
  have hpoint (a b : Core.Vec d) :
      ‖a + b‖ ^ 2 ≤ (1 + gamma) * ‖a‖ ^ 2 + (1 + 1 / gamma) * ‖b‖ ^ 2 := by
    have hc : 2 * ‖a‖ * ‖b‖ ≤ gamma * ‖a‖ ^ 2 + ‖b‖ ^ 2 / gamma := by
      apply (mul_le_mul_iff_right₀ hgamma).mp
      have hd := div_mul_cancel₀ (‖b‖ ^ 2) hgamma.ne'
      nlinarith [sq_nonneg (gamma * ‖a‖ - ‖b‖)]
    rw [norm_add_sq_real]
    have hi := real_inner_le_norm a b
    simp only [div_eq_mul_inv] at hc ⊢
    nlinarith
  have hb := integral_mono_ae hxI
    ((hdI.const_mul (1 + gamma)).fun_add (hstar.1.const_mul (1 + 1 / gamma)))
    (Filter.Eventually.of_forall (fun i => by
      simpa only [sub_add_cancel] using hpoint (I.grad i x - I.grad i xs) (I.grad i xs)))
  rw [integral_add (hdI.const_mul (1 + gamma)) (hstar.1.const_mul (1 + 1 / gamma)),
    integral_const_mul, integral_const_mul, hstar.2] at hb
  have hd := mul_le_mul_of_nonneg_left (variance_difference I L Lg xs sigmaSq hS x)
    (by positivity : 0 ≤ 1 + gamma)
  exact ⟨hxI, by nlinarith⟩


lemma variance_centered {d m : ℕ} (I : Core.Problem d m) (L Lg : ℝ) (xs : Core.Vec d)
    (sigmaSq : ℝ) (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (x : Core.Vec d) :
    Integrable (fun i => ‖I.grad i x - Core.meanGradient I x‖ ^ 2) I.law.toMeasure ∧
      (∫ i, ‖I.grad i x - Core.meanGradient I x‖ ^ 2 ∂I.law.toMeasure) ≤
        ∫ i, ‖I.grad i x‖ ^ 2 ∂I.law.toMeasure := by
  let g := Core.meanGradient I x
  have hx := LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp I L Lg xs sigmaSq hS x
  have hxI := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hx
  have hxSq := (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  have hc : MemLp (fun i => I.grad i x - g) 2 I.law.toMeasure := by
    simpa only [Pi.sub_def] using hx.sub (memLp_const g)
  have hcSq := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  have hiI := hxI.inner_const (𝕜 := ℝ) g
  have hi : (∫ i, inner ℝ (I.grad i x) g ∂I.law.toMeasure) = ‖g‖ ^ 2 := by
    calc
      _ = ∫ i, inner ℝ g (I.grad i x) ∂I.law.toMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun i => real_inner_comm _ _)
      _ = inner ℝ g g := integral_inner hxI g
      _ = _ := real_inner_self_eq_norm_sq g
  refine ⟨hcSq, ?_⟩
  change (∫ i, ‖I.grad i x - g‖ ^ 2 ∂I.law.toMeasure) ≤ _
  calc
    _ = (∫ i, ‖I.grad i x‖ ^ 2 ∂I.law.toMeasure) - 2 * ‖g‖ ^ 2 + ‖g‖ ^ 2 := by
      simp_rw [norm_sub_sq_real]
      rw [integral_add (hxSq.sub' (hiI.const_mul 2)) (integrable_const _),
        integral_sub hxSq (hiI.const_mul 2), integral_const_mul, hi, integral_const]
      simp only [probReal_univ, one_smul]
    _ ≤ _ := by nlinarith [sq_nonneg ‖g‖]


lemma conditional_variance_transfer {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg eta : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (heta : 0 < eta)
    (hSamples : Core.Sampling I P eta x0 i j) (t : ℕ) (z : Ω → Core.Vec d)
    (hz : @Measurable Ω (Core.Vec d) (Core.iterateHistory I eta x0 i j t) _ z)
    (hz2 : MemLp z 2 P.toMeasure) (gamma : ℝ) (hgamma : 0 < gamma) :
    Integrable (fun omega => ‖I.grad (i t omega) (z omega)‖ ^ 2) P.toMeasure ∧
      ∀ᵐ omega ∂P.toMeasure,
        MeasureTheory.condExp (Core.iterateHistory I eta x0 i j t) P.toMeasure
          (fun omega => ‖I.grad (i t omega) (z omega)‖ ^ 2) omega ≤
            2 * L * (1 + gamma) * (Core.objective I (z omega) - Core.objective I xs) +
              (1 + 1 / gamma) * sigmaSq := by
  have hgrad (k : ℕ) (z : Ω → Core.Vec d) (hz : Measurable z)
      (hz2 : MemLp z 2 P.toMeasure) :
      MemLp (fun omega => I.grad (i k omega) (z omega)) 2 P.toMeasure := by
    have hbase := (LongTails.Proofs.RipmSmoothGeometry.component_gradient_memLp
      I L Lg xs sigmaSq hS 0).comp_measurePreserving
        (show MeasurePreserving (i k) P.toMeasure I.law.toMeasure from
          ⟨hSamples.1.measurable k, hSamples.1.marginal k⟩)
    have hbound := (hz2.norm.const_mul L).add hbase.norm
    apply hbound.mono'
      (hS.gradientMeasurable.comp ((hSamples.1.measurable k).prodMk hz)).aestronglyMeasurable
    filter_upwards [] with omega
    have hn := norm_add_le
      (I.grad (i k omega) (z omega) - I.grad (i k omega) 0) (I.grad (i k omega) 0)
    rw [sub_add_cancel] at hn
    have hs := hS.componentSmooth (i k omega) (z omega) 0
    rw [sub_zero] at hs
    exact hn.trans (add_le_add hs le_rfl)
  have hM := (LongTails.Proofs.RipmRegularity.trajectory_adapted
    I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t).1
  have hzM : Measurable z := hz.mono hM le_rfl
  have hg := hgrad t z hzM hz2
  have hgI := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  let k := fun (x : Core.Vec d) (s : I.Sample) => ‖I.grad s x‖ ^ 2
  have hk : Measurable (Function.uncurry k) :=
    ((hS.gradientMeasurable.comp measurable_swap).norm).pow_const 2
  have havgM : Measurable (fun omega => ∫ s, k (z omega) s ∂I.law.toMeasure) :=
    (hk.stronglyMeasurable.integral_prod_right.measurable).comp hzM
  have hobj := (LongTails.Proofs.RipmRegularity.reference_integrable
    I P L Lg eta x0 xs sigmaSq i j hS heta hSamples t z hz hz2).1
  have hRI := ((hobj.sub' (integrable_const (Core.objective I xs))).const_mul
    (2 * L * (1 + gamma))).fun_add (integrable_const ((1 + 1 / gamma) * sigmaSq))
  have havgI : Integrable (fun omega => ∫ s, k (z omega) s ∂I.law.toMeasure)
      P.toMeasure := by
    apply hRI.mono' havgM.aestronglyMeasurable
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg (fun s => sq_nonneg ‖I.grad s (z omega)‖))]
    exact (variance_transfer I L Lg xs sigmaSq hS (z omega) gamma hgamma).2
  have he := LongTails.Proofs.RipmConditional.conditional_kernel P I.law
    (Core.iterateHistory I eta x0 i j t) hM (i t) z k
    (hSamples.1.measurable t) hz hk (hSamples.2 t).2.1
    (hSamples.1.marginal t) hgI havgI
  refine ⟨hgI, ?_⟩
  filter_upwards [he] with omega homega
  rw [homega]
  exact (variance_transfer I L Lg xs sigmaSq hS (z omega) gamma hgamma).2


end

end LongTails.Proofs.RipmVariance
