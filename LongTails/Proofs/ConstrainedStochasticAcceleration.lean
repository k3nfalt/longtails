import LongTails.Proofs.FrankWolfeDescent
import LongTails.Proofs.ScalarClippedAcceleration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedStochasticAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma projected_energy_step {C : Set E} {f : E → ℝ} {L D A a : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hLD : 2 * L ≤ D)
    (hc : ConvexOn ℝ C f)
    (hg : ∀ x ∈ C, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x z u g next : E) (hx : x ∈ C) (hz : z ∈ C) (hu : u ∈ C) (hn : next ∈ C)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a) (haB : a ^ 2 ≤ A + a)
    (hproj : a * ⟪g, next - u⟫ ≤
      D / 2 * (‖z - u‖ ^ 2 - ‖next - u‖ ^ 2 - ‖next - z‖ ^ 2)) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    let out := (A / (A + a)) • x + (a / (A + a)) • next
    let e := gradient f y - g
    (A + a) * (f out - f u) + D / 2 * ‖next - u‖ ^ 2 ≤
      A * (f x - f u) + D / 2 * ‖z - u‖ ^ 2 + a * ⟪e, z - u⟫ +
        a ^ 2 * ‖e‖ ^ 2 / D := by
  let B := A + a
  let y := (A / B) • x + (a / B) • z
  let out := (A / B) • x + (a / B) • next
  have hweights : A / B + a / B = 1 := by
    rw [← add_div]
    exact div_self hB.ne'
  have hy : y ∈ C := hc.1 hx hz (div_nonneg hA hB.le) (div_nonneg ha hB.le) hweights
  have houtmem : out ∈ C := hc.1 hx hn (div_nonneg hA hB.le) (div_nonneg ha hB.le) hweights
  have hx0 := OracleTemplate.FrankWolfe.convex_support_on hc hy hx (hg y hy)
  have hu0 := OracleTemplate.FrankWolfe.convex_support_on hc hy hu (hg y hy)
  have hx1 : f y + ⟪gradient f y, x - y⟫ ≤ f x := by linarith
  have hu1 : f y + ⟪gradient f y, u - y⟫ ≤ f u := by linarith
  have hd := OracleTemplate.FrankWolfe.smooth_upper_bound_on hc.1 hg hlip hy houtmem
  have hout : out - y = (a / B) • (next - z) := by dsimp [out, y]; module
  rw [hout] at hd
  have hcoef : L * a ^ 2 / (2 * B) ≤ D / 4 := by
    apply (div_le_iff₀ (by dsimp [B]; positivity : 0 < 2 * B)).mpr
    have h1 := mul_le_mul_of_nonneg_left haB hL
    have h2 := mul_le_mul_of_nonneg_right hLD hB.le
    dsimp [B]
    nlinarith only [h1, h2]
  have hs := ScalarClippedAcceleration.accelerated_step hA ha hB hD hcoef hx1 hu1 hd hproj
  rw [show g - gradient f y = -(gradient f y - g) by module,
    norm_neg, inner_neg_left] at hs
  simpa only [mul_neg, sub_neg_eq_add, add_right_comm] using hs

lemma integrate_projected_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (energy : Ω → ℝ) (e : Ω → E)
    (v : E) {c a D V : ℝ} (hD : 0 < D)
    (henergy : Integrable energy (μ : Measure Ω))
    (he : Integrable e (μ : Measure Ω))
    (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) (μ : Measure Ω))
    (hmean : (∫ ω, e ω ∂(μ : Measure Ω)) = 0)
    (hvar : (∫ ω, ‖e ω‖ ^ 2 ∂(μ : Measure Ω)) ≤ V)
    (hstep : ∀ ω, energy ω ≤ c + a * ⟪e ω, v⟫ + (a ^ 2 / D) * ‖e ω‖ ^ 2) :
    (∫ ω, energy ω ∂(μ : Measure Ω)) ≤ c + (a ^ 2 / D) * V := by
  have hlin : Integrable (fun ω => a * ⟪e ω, v⟫) (μ : Measure Ω) :=
    (he.inner_const v).const_mul a
  have hquad : Integrable (fun ω => (a ^ 2 / D) * ‖e ω‖ ^ 2) (μ : Measure Ω) :=
    he2.const_mul _
  have hbase : Integrable (fun ω => c + a * ⟪e ω, v⟫) (μ : Measure Ω) :=
    (integrable_const _).add hlin
  have hzero : (∫ ω, ⟪e ω, v⟫ ∂(μ : Measure Ω)) = 0 := by
    calc
      _ = ∫ ω, ⟪v, e ω⟫ ∂(μ : Measure Ω) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
      _ = ⟪v, ∫ ω, e ω ∂(μ : Measure Ω)⟫ := integral_inner he v
      _ = 0 := by rw [hmean, inner_zero_right]
  have hi := integral_mono henergy (hbase.add hquad) hstep
  simp only [Pi.add_apply] at hi
  rw [integral_add hbase hquad, integral_add (integrable_const c) hlin,
    integral_const_mul, hzero, mul_zero, add_zero, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  exact hi.trans (add_le_add (le_refl c) (mul_le_mul_of_nonneg_left hvar
    (div_nonneg (sq_nonneg a) hD.le)))

lemma integrable_compact_image {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure Ω) {C : Set X} (hcompact : IsCompact C)
    (f : X → ℝ) (hf : ContinuousOn f C) (x : Ω → X)
    (hx : Measurable x) (hmem : ∀ ω, x ω ∈ C) :
    Integrable (fun ω => f (x ω)) (μ : Measure Ω) := by
  have hxm : Measurable (fun ω => (⟨x ω, hmem ω⟩ : C)) := hx.subtype_mk
  have hm : Measurable (fun ω => f (x ω)) := hf.domRestrict.measurable.comp hxm
  obtain ⟨B, hB⟩ := (hcompact.image_of_continuousOn hf).isBounded.exists_norm_le
  exact (integrable_const B).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => hB _ (Set.mem_image_of_mem f (hmem ω))))

lemma energy_recursion_bound (energy : ℕ → ℝ) {D V : ℝ} (hD : 0 < D)
    (hstep : ∀ k : ℕ, energy (k + 1) ≤ energy k + (((k : ℝ) + 1) / 2) ^ 2 * V / D)
    (n : ℕ) :
    energy n ≤ energy 0 + (n : ℝ) * (n + 1) * (2 * n + 1) * V / (24 * D) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      energy (n + 1) ≤ energy n + (((n : ℝ) + 1) / 2) ^ 2 * V / D := hstep n
      _ ≤ (energy 0 + (n : ℝ) * (n + 1) * (2 * n + 1) * V / (24 * D)) +
          (((n : ℝ) + 1) / 2) ^ 2 * V / D := add_le_add ih (le_refl _)
      _ = energy 0 + ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) *
          (2 * ((n + 1 : ℕ) : ℝ) + 1) * V / (24 * D) := by
        push_cast
        field_simp [hD.ne']
        ring

lemma rate_of_energy_recursion (energy : ℕ → ℝ) {D V r2 gap : ℝ}
    (hD : 0 < D) (hV : 0 ≤ V) (hinit : energy 0 ≤ D / 2 * r2)
    (hstep : ∀ k : ℕ, energy (k + 1) ≤ energy k + (((k : ℝ) + 1) / 2) ^ 2 * V / D)
    {n : ℕ} (hn : 0 < n)
    (hgap : (n : ℝ) * (n + 1) / 4 * gap ≤ energy n) :
    gap ≤ 2 * D * r2 / ((n : ℝ) * (n + 1)) + (n : ℝ) * V / D := by
  let t : ℝ := n
  have ht : 1 ≤ t := by
    dsimp [t]
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have ht0 : 0 < t := by linarith
  have hA : 0 < t * (t + 1) / 4 := by positivity
  have hB : t * (t + 1) ≠ 0 := by positivity
  have he := energy_recursion_bound energy hD hstep n
  have he' : energy n ≤ D / 2 * r2 + t * (t + 1) * (2 * t + 1) * V / (24 * D) :=
    he.trans (add_le_add hinit (le_refl _))
  have hnoise : t * (t + 1) * (2 * t + 1) * V / (24 * D) ≤
      (t * (t + 1) / 4) * (t * V / D) := by
    apply (div_le_iff₀ (by positivity : 0 < 24 * D)).2
    have heq : (t * (t + 1) / 4 * (t * V / D)) * (24 * D) =
        6 * t ^ 2 * (t + 1) * V := by field_simp [hD.ne']; ring
    rw [heq]
    have hm := mul_le_mul_of_nonneg_left (show 2 * t + 1 ≤ 6 * t by linarith)
      (show 0 ≤ t * (t + 1) * V by positivity)
    nlinarith only [hm]
  have heq : (t * (t + 1) / 4) * (2 * D * r2 / (t * (t + 1)) + t * V / D) =
      D / 2 * r2 + (t * (t + 1) / 4) * (t * V / D) := by
    field_simp [hD.ne', hB]
    ring
  change gap ≤ 2 * D * r2 / (t * (t + 1)) + t * V / D
  have hfinal := hgap.trans (he'.trans (add_le_add (le_refl _) hnoise))
  rw [← heq] at hfinal
  nlinarith only [hfinal, hA]


lemma restart_tuning {S V d μ t r2 : ℝ}
    (hS : 0 < S) (hV : 0 ≤ V) (hd : 0 < d) (hμ : 0 < μ) (ht : 0 < t)
    (hr : r2 ≤ 2 * d / μ)
    (htS : 64 * S / μ ≤ t ^ 2) (htV : 256 * V / (μ * d) ≤ t) :
    let D := 2 * S + 8 * t * V / d
    2 * D * r2 / (t * (t + 1)) + t * V / D ≤ 3 * d / 8 := by
  let D := 2 * S + 8 * t * V / d
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : 0 < t * (t + 1) := by positivity
  have hS' : 64 * S ≤ t ^ 2 * μ := (div_le_iff₀ hμ).1 htS
  have hV' : 256 * V ≤ t * (μ * d) := (div_le_iff₀ (by positivity)).1 htV
  have hdet : 4 * D * d ≤ d / 4 * (t * (t + 1)) * μ := by
    have h1 := mul_le_mul_of_nonneg_right hS' hd.le
    have h2 := mul_le_mul_of_nonneg_left hV' ht.le
    have h3 : 0 ≤ d * t * μ := by positivity
    have hDd : D * d = 2 * S * d + 8 * t * V := by
      dsimp [D]
      field_simp
    nlinarith only [h1, h2, h3, hDd]
  have hr' : r2 * μ ≤ 2 * d := (le_div_iff₀ hμ).1 hr
  have hinit : 2 * D * r2 / (t * (t + 1)) ≤ d / 4 := by
    apply (div_le_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hr' (show 0 ≤ 2 * D by positivity)
    nlinarith only [hm, hdet, hμ]
  have hnoise : t * V / D ≤ d / 8 := by
    apply (div_le_iff₀ hD).2
    have hDd : D * d = 2 * S * d + 8 * t * V := by
      dsimp [D]
      field_simp
    have hSd : 0 ≤ S * d := by positivity
    nlinarith only [hDd, hSd]
  change 2 * D * r2 / (t * (t + 1)) + t * V / D ≤ 3 * d / 8
  linarith

end LongTails.Proofs.ConstrainedStochasticAcceleration
